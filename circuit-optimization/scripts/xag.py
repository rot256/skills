"""Versioned JSON helpers for XOR-AND graphs with affine fan-in.

The representation deliberately counts AND gates separately from XORs.  Signal
IDs ``0 .. num_inputs-1`` are primary inputs and signal
``num_inputs + i`` is the output of ``gates[i]``.  An affine form is a constant
bit XOR a sorted set of signal IDs.

This module is plain Python so it can be imported by both Python and Sage
scripts without preprocessing.
"""

from __future__ import annotations

import json


FORMAT = "xag"
VERSION = 1


def affine(constant=0, terms=()):
    """Return a normalized affine form, cancelling duplicate terms mod 2."""
    parity = set()
    for raw in terms:
        signal = int(raw)
        if signal in parity:
            parity.remove(signal)
        else:
            parity.add(signal)
    return {"constant": int(constant) & 1, "terms": sorted(parity)}


def _normalize_form(form):
    if not isinstance(form, dict):
        raise ValueError("an affine form must be an object")
    extra = set(form) - {"constant", "terms"}
    if extra:
        raise ValueError("unknown affine-form fields: %s" % sorted(extra))
    return affine(form.get("constant", 0), form.get("terms", ()))


def _xor_cost(form):
    # This is informational: it prices one binary XOR per extra summand in an
    # explicitly materialized affine form, including the constant when set.
    summands = len(form["terms"]) + form["constant"]
    return max(0, summands - 1)


def xag_metrics(xag):
    """Compute, rather than trust, the AND count/depth and informational XORs."""
    n = xag["num_inputs"]
    depths = [0] * n
    xor_count = 0
    for gate in xag["gates"]:
        left, right = gate["left"], gate["right"]
        xor_count += _xor_cost(left) + _xor_cost(right)
        support = left["terms"] + right["terms"]
        depth = 1 + max([depths[s] for s in support] or [0])
        depths.append(depth)
    for output in xag["outputs"]:
        xor_count += _xor_cost(output)
    return {
        "and_count": len(xag["gates"]),
        "and_depth": max(depths[n:] or [0]),
        "xor_count": xor_count,
    }


def normalize_xag(obj):
    """Return a normalized copy and reject malformed or forward references."""
    if not isinstance(obj, dict):
        raise ValueError("XAG must be a JSON object")
    if obj.get("format") != FORMAT or obj.get("version") != VERSION:
        raise ValueError("expected %s JSON version %d" % (FORMAT, VERSION))
    allowed = {
        "format", "version", "num_inputs", "gates", "outputs", "metrics",
        "metadata",
    }
    extra = set(obj) - allowed
    if extra:
        raise ValueError("unknown XAG fields: %s" % sorted(extra))
    n = int(obj["num_inputs"])
    if n < 0:
        raise ValueError("num_inputs must be non-negative")

    gates = []
    for i, raw_gate in enumerate(obj.get("gates", [])):
        if not isinstance(raw_gate, dict) or set(raw_gate) != {"left", "right"}:
            raise ValueError("gate %d must contain exactly left and right" % i)
        gate = {
            "left": _normalize_form(raw_gate["left"]),
            "right": _normalize_form(raw_gate["right"]),
        }
        limit = n + i
        for side in ("left", "right"):
            if any(s < 0 or s >= limit for s in gate[side]["terms"]):
                raise ValueError("gate %d %s has a forward/invalid reference" % (i, side))
        gates.append(gate)

    outputs = [_normalize_form(form) for form in obj.get("outputs", [])]
    limit = n + len(gates)
    for i, output in enumerate(outputs):
        if any(s < 0 or s >= limit for s in output["terms"]):
            raise ValueError("output %d has an invalid signal reference" % i)

    normalized = {
        "format": FORMAT,
        "version": VERSION,
        "num_inputs": n,
        "gates": gates,
        "outputs": outputs,
    }
    if "metadata" in obj:
        normalized["metadata"] = obj["metadata"]
    normalized["metrics"] = xag_metrics(normalized)
    return normalized


def validate_xag(obj):
    """Validate ``obj`` and return True; metrics, when present, must be exact."""
    normalized = normalize_xag(obj)
    if "metrics" in obj and obj["metrics"] != normalized["metrics"]:
        raise ValueError("stored XAG metrics do not match the graph")
    return True


def make_xag(num_inputs, gates, outputs, metadata=None):
    obj = {
        "format": FORMAT,
        "version": VERSION,
        "num_inputs": int(num_inputs),
        "gates": list(gates),
        "outputs": list(outputs),
    }
    if metadata is not None:
        obj["metadata"] = metadata
    return normalize_xag(obj)


def evaluate_xag(obj, inputs):
    """Evaluate an XAG and return its output bits."""
    xag = normalize_xag(obj)
    if len(inputs) != xag["num_inputs"] or any(int(x) not in (0, 1) for x in inputs):
        raise ValueError("inputs must contain exactly num_inputs bits")
    values = [int(x) for x in inputs]

    def eval_form(form):
        value = form["constant"]
        for signal in form["terms"]:
            value ^= values[signal]
        return value

    for gate in xag["gates"]:
        values.append(eval_form(gate["left"]) & eval_form(gate["right"]))
    return [eval_form(output) for output in xag["outputs"]]


def truth_tables(obj):
    """Return little-endian truth tables (table index bits are input bits)."""
    xag = normalize_xag(obj)
    tables = [[] for _ in xag["outputs"]]
    for index in range(1 << xag["num_inputs"]):
        inputs = [(index >> i) & 1 for i in range(xag["num_inputs"])]
        for table, bit in zip(tables, evaluate_xag(xag, inputs)):
            table.append(bit)
    return tables


def load_xag(path):
    with open(path, "r", encoding="utf-8") as handle:
        return normalize_xag(json.load(handle))


def save_xag(obj, path):
    normalized = normalize_xag(obj)
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(normalized, handle, indent=2, sort_keys=True)
        handle.write("\n")


def dumps_xag(obj):
    return json.dumps(normalize_xag(obj), indent=2, sort_keys=True)
