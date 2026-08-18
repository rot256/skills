#!/usr/bin/env sage
"""Bounded exact rewriting of XAG maximal fanout-free cones.

The prototype considers one-output cones with at most six boundary signals,
resynthesizes their truth tables exactly, and accepts a replacement only when
the selected whole-network backend cost tuple improves.  The default tuple is
``(AND count, AND depth)`` and deliberately ignores XOR count.

No arguments runs deterministic self-tests.  This is intentionally a bounded
prototype, not a complete cut-enumeration or industrial resubstitution pass.
"""

import argparse
import json
import operator
import os
import shutil
import subprocess
import sys
import tempfile

from sage.repl.load import load as sage_load

_cwd_scripts = os.path.join(os.getcwd(), "scripts")
if os.path.isdir(_cwd_scripts) and _cwd_scripts not in sys.path:
    sys.path.insert(0, _cwd_scripts)
try:
    from xag import affine, load_xag, make_xag, save_xag, truth_tables, xag_metrics
except ImportError:
    from scripts.xag import affine, load_xag, make_xag, save_xag, truth_tables, xag_metrics


def _xor_forms(forms):
    constant = 0
    terms = set()
    for form in forms:
        constant = operator.xor(int(constant), int(form["constant"]))
        for term in form["terms"]:
            if term in terms:
                terms.remove(term)
            else:
                terms.add(term)
    return affine(constant, sorted(terms))


def _substitute_form(form, signal_forms):
    pieces = [affine(form["constant"], [])]
    pieces.extend(signal_forms[term] for term in form["terms"])
    return _xor_forms(pieces)


def _fanouts(obj):
    n = obj["num_inputs"]
    counts = [0] * (n + len(obj["gates"]))
    for gate in obj["gates"]:
        for side in (gate["left"], gate["right"]):
            for signal in side["terms"]:
                counts[signal] += 1
    for output in obj["outputs"]:
        for signal in output["terms"]:
            counts[signal] += 1
    return counts


def _mffc(obj, root_index):
    """Return the maximal fanout-free gate cone rooted at ``root_index``."""
    n = obj["num_inputs"]
    fanouts = _fanouts(obj)
    cone = {root_index}
    stack = [root_index]
    while stack:
        gate_index = stack.pop()
        gate = obj["gates"][gate_index]
        for side in (gate["left"], gate["right"]):
            for signal in side["terms"]:
                if signal < n:
                    continue
                predecessor = signal - n
                if predecessor not in cone and fanouts[signal] == 1:
                    cone.add(predecessor)
                    stack.append(predecessor)
    leaves = set()
    for gate_index in cone:
        gate = obj["gates"][gate_index]
        for side in (gate["left"], gate["right"]):
            leaves.update(signal for signal in side["terms"] if signal < n or signal - n not in cone)
    return cone, sorted(leaves)


def _enumerate_cuts(obj, root_index, max_cut, max_window_ands, max_cuts):
    """Enumerate bounded cuts whose removed gates have no external fanout.

    This is a conservative k-feasible-cut enumerator: a non-root gate is
    expanded only when its graph-wide fanout is one.  Stopping at that gate
    makes its output a boundary leaf.  Consequently every returned cone can be
    deleted while preserving only the root function.
    """
    n = obj["num_inputs"]
    fanouts = _fanouts(obj)
    memo = {}

    def expanded(gate_index):
        if gate_index in memo:
            return memo[gate_index]
        gate = obj["gates"][gate_index]
        dependencies = sorted(set(gate["left"]["terms"] + gate["right"]["terms"]))
        states = [(frozenset([gate_index]), frozenset())]
        for signal in dependencies:
            alternatives = [(frozenset(), frozenset([signal]))]
            if signal >= n and fanouts[signal] == 1:
                alternatives.extend(expanded(signal - n))
            combined = set()
            for cone, leaves in states:
                for added_cone, added_leaves in alternatives:
                    new_cone = cone | added_cone
                    new_leaves = (leaves | added_leaves) - {
                        n + index for index in new_cone
                    }
                    if len(new_cone) <= max_window_ands and len(new_leaves) <= max_cut:
                        combined.add((new_cone, new_leaves))
            # Prefer larger removable cones, then smaller interfaces when the
            # cap truncates an exponential family.
            states = sorted(combined, key=lambda item: (-len(item[0]), len(item[1]), tuple(item[1])))[:max_cuts]
        memo[gate_index] = states
        return states

    cuts = [item for item in expanded(root_index) if len(item[0]) > 1]
    return [(set(cone), sorted(leaves)) for cone, leaves in cuts[:max_cuts]]


def _cone_table(obj, root_index, cone, leaves):
    n = obj["num_inputs"]
    table = []
    leaf_positions = {signal: i for i, signal in enumerate(leaves)}
    for assignment in range(1 << len(leaves)):
        values = {signal: (assignment >> position) & 1 for signal, position in leaf_positions.items()}

        def eval_form(form):
            value = form["constant"]
            for signal in form["terms"]:
                value = operator.xor(value, values[signal])
            return value

        for gate_index in sorted(cone):
            gate = obj["gates"][gate_index]
            values[n + gate_index] = eval_form(gate["left"]) & eval_form(gate["right"])
        table.append(values[n + root_index])
    return table


def _prune_xag(obj):
    n = obj["num_inputs"]
    gates = obj["gates"]
    needed = set()
    stack = [term for out in obj["outputs"] for term in out["terms"] if term >= n]
    while stack:
        old_signal = stack.pop()
        old_index = old_signal - n
        if old_index in needed:
            continue
        needed.add(old_index)
        gate = gates[old_index]
        for side in (gate["left"], gate["right"]):
            stack.extend(signal for signal in side["terms"] if signal >= n)

    remap = {old: new for new, old in enumerate(sorted(needed))}

    def map_form(form):
        return affine(
            form["constant"],
            [signal if signal < n else n + remap[signal - n] for signal in form["terms"]],
        )

    gates = [
        {"left": map_form(obj["gates"][old]["left"]),
         "right": map_form(obj["gates"][old]["right"])}
        for old in sorted(needed)
    ]
    return make_xag(n, gates, [map_form(out) for out in obj["outputs"]], obj.get("metadata"))


def _splice_replacement(obj, root_index, cone, leaves, replacement):
    """Replace a fanout-free cone and rebuild signal IDs topologically."""
    n = obj["num_inputs"]
    if replacement["num_inputs"] != len(leaves) or len(replacement["outputs"]) != 1:
        raise ValueError("local replacement has the wrong interface")

    new_gates = []
    # Every old signal that remains meaningful maps to an affine expression in
    # the rebuilt graph.  Inputs are initially identities.
    old_forms = [affine(0, [i]) for i in range(n)] + [None] * len(obj["gates"])

    for old_index, old_gate in enumerate(obj["gates"]):
        if old_index in cone:
            if old_index != root_index:
                continue
            local_forms = [old_forms[leaf] for leaf in leaves]
            for local_gate in replacement["gates"]:
                left = _substitute_form(local_gate["left"], local_forms)
                right = _substitute_form(local_gate["right"], local_forms)
                new_signal = n + len(new_gates)
                new_gates.append({"left": left, "right": right})
                local_forms.append(affine(0, [new_signal]))
            old_forms[n + root_index] = _substitute_form(replacement["outputs"][0], local_forms)
            continue

        left = _substitute_form(old_gate["left"], old_forms)
        right = _substitute_form(old_gate["right"], old_forms)
        new_signal = n + len(new_gates)
        new_gates.append({"left": left, "right": right})
        old_forms[n + old_index] = affine(0, [new_signal])

    outputs = [_substitute_form(output, old_forms) for output in obj["outputs"]]
    return _prune_xag(make_xag(n, new_gates, outputs, obj.get("metadata")))


def _load_exact_search():
    candidates = [
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "exact_xag.sage"),
        os.path.join(os.getcwd(), "scripts", "exact_xag.sage"),
    ]
    path = next((candidate for candidate in candidates if os.path.exists(candidate)), None)
    if path is None:
        raise RuntimeError("exact_xag.sage is required for rewriting")
    # The Sage preparser emits names such as Integer; seed the isolated namespace
    # with this module's Sage globals while changing __name__ to keep the loaded
    # command-line entry point dormant.
    namespace = dict(globals())
    namespace["__name__"] = "xag_exact_library"
    sage_load(path, namespace, attach=False)
    if "search_minimum" not in namespace:
        raise RuntimeError("exact_xag.sage does not export search_minimum")
    return namespace["search_minimum"]


def _call_exact(search, num_inputs, table, max_ands):
    """Call the shared exact API, accepting its documented keyword variants."""
    try:
        return search(num_inputs, [table], max_ands=max_ands, mode="full")
    except TypeError as first_error:
        try:
            return search(num_inputs, [table], care_masks=None, max_ands=max_ands, mode="full")
        except TypeError:
            raise first_error


def _cost(obj, profile):
    metrics = xag_metrics(obj)
    if profile == "and-only":
        return (metrics["and_count"],)
    if profile == "and-depth":
        return (metrics["and_count"], metrics["and_depth"])
    if profile == "and-depth-xor":
        return (metrics["and_count"], metrics["and_depth"], metrics["xor_count"])
    raise ValueError("unknown cost profile: " + profile)


def _smt_form(prefix, form):
    atoms = ["true"] if form["constant"] else []
    atoms.extend("%s_s%d" % (prefix, signal) for signal in form["terms"])
    if not atoms:
        return "false"
    expression = atoms[0]
    for atom in atoms[1:]:
        expression = "(xor %s %s)" % (expression, atom)
    return expression


def _smt_network(obj, prefix):
    n = obj["num_inputs"]
    lines = []
    for gate_index, gate in enumerate(obj["gates"]):
        signal = n + gate_index
        lines.append("(define-fun %s_s%d () Bool (and %s %s))" % (
            prefix, signal, _smt_form(prefix, gate["left"]), _smt_form(prefix, gate["right"])
        ))
    for output_index, output in enumerate(obj["outputs"]):
        lines.append("(define-fun %s_o%d () Bool %s)" % (
            prefix, output_index, _smt_form(prefix, output)
        ))
    return lines


def verify_miter(before, after, method="auto", exhaustive_limit=12):
    """Prove whole-network equivalence with cvc5, or exhaustively when small."""
    if before["num_inputs"] != after["num_inputs"] or len(before["outputs"]) != len(after["outputs"]):
        raise AssertionError("miter interfaces differ")
    if not before["outputs"]:
        return "trivial-empty-interface"
    use_cvc5 = method in ("auto", "cvc5") and shutil.which("cvc5") is not None
    if use_cvc5:
        n = before["num_inputs"]
        lines = ["(set-logic QF_UF)"]
        lines.extend("(declare-fun a_s%d () Bool)" % i for i in range(n))
        lines.extend("(define-fun b_s%d () Bool a_s%d)" % (i, i) for i in range(n))
        lines.extend(_smt_network(before, "a"))
        lines.extend(_smt_network(after, "b"))
        differences = ["(xor a_o%d b_o%d)" % (i, i) for i in range(len(before["outputs"]))]
        assertion = differences[0] if len(differences) == 1 else "(or %s)" % " ".join(differences)
        lines.extend(["(assert %s)" % assertion, "(check-sat)"])
        path = None
        try:
            with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as handle:
                path = handle.name
                handle.write("\n".join(lines) + "\n")
            result = subprocess.run(["cvc5", path], text=True, capture_output=True, timeout=60)
        finally:
            if path and os.path.exists(path):
                os.unlink(path)
        if result.returncode != 0 or result.stdout.strip() != "unsat":
            raise AssertionError("cvc5 miter failed: stdout=%r stderr=%r" % (result.stdout, result.stderr))
        return "cvc5"

    if method == "cvc5":
        raise RuntimeError("cvc5 was requested but is unavailable")
    if before["num_inputs"] > int(exhaustive_limit):
        raise RuntimeError("cvc5 unavailable and exhaustive miter exceeds input limit")
    if truth_tables(before) != truth_tables(after):
        raise AssertionError("exhaustive whole-network miter found a mismatch")
    return "exhaustive"


def rewrite_xag(obj, max_cut=6, max_window_ands=6, max_cuts_per_root=64, passes=1,
                cost_profile="and-depth", verification="auto", exact_search=None):
    """Run bounded fanout-free-cone rewriting and return a verified XAG."""
    max_cut = int(max_cut)
    max_window_ands = int(max_window_ands)
    max_cuts_per_root = int(max_cuts_per_root)
    passes = int(passes)
    if max_cut < 0 or max_cut > 6:
        raise ValueError("this prototype requires 0 <= max_cut <= 6")
    if max_window_ands < 1 or max_cuts_per_root < 1 or passes < 0:
        raise ValueError("window size and cuts per root must be positive; passes must be non-negative")
    search = exact_search or _load_exact_search()
    current = _prune_xag(obj)
    original = current
    cache = {}
    accepted = 0
    attempted = 0
    verification_method = None

    for _pass in range(passes):
        changed = False
        # Recompute cones after every accepted rewrite; signal IDs and fanouts
        # change, so stale cuts would be unsafe.
        root_index = len(current["gates"]) - 1
        while root_index >= 0:
            cuts = _enumerate_cuts(
                current, root_index, max_cut, max_window_ands, max_cuts_per_root
            )
            accepted_at_root = False
            for cone, leaves in cuts:
                attempted += 1
                table = _cone_table(current, root_index, cone, leaves)
                key = (len(leaves), tuple(table), len(cone))
                if key not in cache:
                    cache[key] = _call_exact(search, len(leaves), table, len(cone))
                replacement = cache[key]
                if replacement is not None:
                    if truth_tables(replacement) != [table]:
                        raise AssertionError("exact local synthesis failed exhaustive verification")
                    candidate = _splice_replacement(current, root_index, cone, leaves, replacement)
                    if _cost(candidate, cost_profile) < _cost(current, cost_profile):
                        verification_method = verify_miter(current, candidate, verification)
                        current = candidate
                        accepted += 1
                        changed = True
                        accepted_at_root = True
                        root_index = len(current["gates"]) - 1
                        break
            if accepted_at_root:
                continue
            root_index -= 1
        if not changed:
            break

    # One final independent whole-network check covers the entire rewrite chain.
    verification_method = verify_miter(original, current, verification)
    metadata = dict(current.get("metadata", {}))
    metadata["rewriter"] = {
        "tool": "xag_rewrite.sage",
        "prototype": "bounded fanout-safe cuts; not complete general cut enumeration",
        "max_cut": max_cut,
        "max_window_ands": max_window_ands,
        "max_cuts_per_root": max_cuts_per_root,
        "passes": passes,
        "cost_profile": cost_profile,
        "attempted_windows": int(attempted),
        "accepted_rewrites": int(accepted),
        "whole_network_verification": verification_method,
    }
    current["metadata"] = metadata
    return current


def _self_test_search(num_inputs, outputs, max_ands=None, mode="full", **_kwargs):
    table = outputs[0]
    # Tiny exact fixtures used only to test splicing.  Production always loads
    # exact_xag.sage.
    if num_inputs == 2 and table == [0, 0, 0, 1] and max_ands >= 1:
        return make_xag(2, [{"left": affine(0, [0]), "right": affine(0, [1])}], [affine(0, [2])])
    return None


def self_test():
    # Deliberately duplicate x&y so the second AND is dangling after substitution.
    redundant = make_xag(
        2,
        [
            {"left": affine(0, [0]), "right": affine(0, [1])},
            {"left": affine(0, [0]), "right": affine(0, [1])},
            {"left": affine(0, [2]), "right": affine(0, [3])},
        ],
        [affine(0, [4])],
    )
    rewritten = rewrite_xag(redundant, exact_search=_self_test_search)
    assert truth_tables(rewritten) == truth_tables(redundant)
    assert xag_metrics(rewritten)["and_count"] == 1
    assert rewritten["metadata"]["rewriter"]["accepted_rewrites"] == 1

    # Sharing prevents an internal node from entering the MFFC; it must remain a
    # boundary leaf and no unsafe deletion may occur.
    shared = make_xag(
        2,
        [
            {"left": affine(0, [0]), "right": affine(0, [1])},
            {"left": affine(0, [2]), "right": affine(0, [0])},
        ],
        [affine(0, [2, 3])],
    )
    untouched = rewrite_xag(shared, exact_search=_self_test_search)
    assert truth_tables(untouched) == truth_tables(shared)
    print("PASS: xag_rewrite.sage self-tests")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="input XAG JSON")
    parser.add_argument("output", help="output XAG JSON")
    parser.add_argument("--max-cut", type=int, default=6)
    parser.add_argument("--max-window-ands", type=int, default=6)
    parser.add_argument("--max-cuts-per-root", type=int, default=64)
    parser.add_argument("--passes", type=int, default=1)
    parser.add_argument("--cost-profile", choices=("and-only", "and-depth", "and-depth-xor"),
                        default="and-depth")
    parser.add_argument("--verification", choices=("auto", "cvc5", "exhaustive"), default="auto")
    args = parser.parse_args(argv)
    rewritten = rewrite_xag(
        load_xag(args.input), args.max_cut, args.max_window_ands, args.max_cuts_per_root, args.passes,
        args.cost_profile, args.verification,
    )
    save_xag(rewritten, args.output)
    print(json.dumps({"before": xag_metrics(load_xag(args.input)), "after": xag_metrics(rewritten)}, sort_keys=True))


if os.path.basename(sys.argv[0]).startswith("xag_rewrite.sage"):
    if len(sys.argv) == 1:
        self_test()
    else:
        main()
