#!/usr/bin/env python3
"""Report which recorded leads are still open, by grepping the live seed trees.

Nothing in the fleet records which workqueue item a job took, so a lead that was
attempted and failed is indistinguishable from one nobody ever tried. What IS
observable is the tree: most leads cite a concrete Lean constant, and that
constant is present exactly while the lead is open. This turns "do we still
remember this?" into "is it still in the tree?".
"""
import json, os, re, glob, sys

ROOT = os.path.dirname(os.path.abspath(__file__))

def seed_dir(slug):
    """The tree a lead should be checked against, in priority order.

    There are THREE tree locations and they are NOT interchangeable:

      records/<slug>/   the LEADER's tree, reseeded by check_records from
                        whoever currently holds the record. This is what jobs
                        are seeded from, so it is what a lead must beat.
      projs/<slug>/     OUR working tree. Equals records/ only on slugs where
                        we lead; on keccak-f1600 ours is theta 3200 while the
                        record is 2240, so reading the wrong one inverts the
                        answer completely.
      out/<slug>/       per-job scratch. tick.py wipes and re-extracts it for
                        the very next job, so a constant read here belongs to
                        whichever job landed last. This is a proxy witness --
                        it reports the directory changing, not the lead
                        landing -- and reading it was the original bug.
    """
    for cand in (os.path.join(ROOT, "records", slug),
                 os.path.join(ROOT, "projs", slug)):
        if os.path.isdir(cand) and glob.glob(os.path.join(cand, "**", "*.lean"), recursive=True):
            return cand
    for d in glob.glob(os.path.join(ROOT, "out", slug, "*_aristotle")):
        if os.path.isdir(d):
            return d
    return None

def witness_files(d, rel):
    """Resolve a witness path, tolerating flat and Solution/-nested layouts."""
    hits = glob.glob(os.path.join(d, rel))
    if not hits:   # records/ stores the .lean files flat
        hits = glob.glob(os.path.join(d, "**", os.path.basename(rel)), recursive=True)
    return hits

def check(lead):
    w = lead.get("witness")
    if not w:
        return "unverifiable", "no mechanical witness — check by hand"
    d = seed_dir(lead["slug"])
    if not d:
        return "no-seed", "no extracted tree on disk; cannot check"
    files = witness_files(d, w["file"])
    if not files:
        return "moved", f"witness file {w['file']} not found — the tree was restructured, RE-CHECK BY HAND"
    pat = re.compile(w["pattern"])
    for f in files:
        try:
            txt = open(f, errors="replace").read()
        except OSError:
            continue
        if pat.search(txt):
            return "open", os.path.relpath(f, d)
    return "landed", f"pattern gone from {len(files)} file(s) — RE-PRICE THE SIBLINGS"

def main():
    only_open = "--open" in sys.argv
    data = json.load(open(os.path.join(ROOT, "leads.json")))
    rows, total_open = [], 0
    for lead in data["leads"]:
        status, detail = check(lead)
        if only_open and status != "open":
            continue
        if status == "open":
            total_open += lead.get("price", 0)
        rows.append((status, lead, detail))
    order = {"landed": 0, "moved": 1, "open": 2, "unverifiable": 3, "no-seed": 4}
    rows.sort(key=lambda r: (order.get(r[0], 9), -r[1].get("price", 0)))
    for status, lead, detail in rows:
        print(f"[{status.upper():>12}] {lead['price']:>6}  {lead['id']:<20} {lead['slug']}")
        print(f"{'':>15} {lead['summary']}")
        print(f"{'':>15} -> {detail}")
        if lead.get("note"):
            print(f"{'':>15} !! {lead['note']}")
        print()
    print(f"open leads total: {total_open}")
    if any(s == "landed" for s, _, _ in rows):
        print("ACTION: a lead flipped to landed. Re-price its siblings against the new tree "
              "before requeueing them — a pattern that paid once is a reason to CHECK the next "
              "instance, never a reason to assume it.")

if __name__ == "__main__":
    main()
