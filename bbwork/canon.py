"""Canonical forms of standard-format TMs under the full machine symmetry group.

A symmetry is (state permutation, symbol permutation, mirror L<->R).  Two
machines with the same canonical form are the *same machine* up to renaming,
so they have identical halting behaviour from any corresponding configuration.
This is exact equivalence, not a merge search.
"""

from __future__ import annotations

import itertools
import sys

import bb


def transform_trans(tm: bb.TM, sp, yp, mirror):
    n, m = tm.n, tm.m
    out = [[None] * m for _ in range(n)]
    for s in range(n):
        for v in range(m):
            tr = tm.trans[s][v]
            ns, nv = sp[s], yp[v]
            if tr is None:
                out[ns][nv] = None
            else:
                w, d, nxt = tr
                out[ns][nv] = (yp[w], -d if mirror else d,
                               None if nxt < 0 else sp[nxt])
    return out


def _enc(tr):
    """Comparable encoding of one transition; None (halt) sorts first."""
    if tr is None:
        return (0, 0, 0)
    w, d, nxt = tr
    return (w + 1, d + 1, nxt + 2)


def key_of(trans, n, m):
    return tuple(tuple(_enc(tr) for tr in row) for row in trans)


def canonical(tm: bb.TM):
    """Canonical form preserving the standard input: blank 0 and start A fixed.

    A full state/symbol permutation maps a machine to an isomorphic table, but
    it need not preserve the *initial configuration* (all-0 tape, state A).
    For holdout deduplication the symmetry must send A->A and 0->0; mirroring
    is still allowed because the all-blank tape is mirror-symmetric.
    """
    best = None
    best_sym = None
    for sp in itertools.permutations(range(1, tm.n)):
        sp = (0,) + sp
        for yp in itertools.permutations(range(1, tm.m)):
            yp = (0,) + yp
            for mirror in (False, True):
                k = key_of(transform_trans(tm, sp, yp, mirror), tm.n, tm.m)
                if best is None or k < best:
                    best = k
                    best_sym = (sp, yp, mirror)
    return best, best_sym


def load_machines(path, strip_id=False):
    out = []
    with open(path, encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.split("#")[0].strip()
            if not line:
                continue
            if strip_id and " " in line:
                parts = line.split()
                # '<id> <spec>' files; tolerate plain-spec files too
                line = parts[-1]
            if "_" not in line or " " in line:
                continue
            out.append(line)
    return out


def report(name, specs):
    groups = {}
    for i, s in enumerate(specs):
        tm = bb.TM.parse(s)
        k, sym = canonical(tm)
        groups.setdefault(k, []).append((i, s, sym))
    dup = {k: v for k, v in groups.items() if len(v) > 1}
    print(f"{name}: {len(specs)} machines, {len(groups)} symmetry classes, "
          f"{len(dup)} duplicate classes")
    for v in dup.values():
        print("  DUP:", [x[1] for x in v])
    return groups


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    out = {}
    if which in ("all", "37"):
        specs = load_machines("Bb2x5_informalLast37.txt")
        out["37"] = report("BB(2,5) informal 37", specs)
    if which in ("all", "60"):
        specs = load_machines("BB2x5_Rocq_holdouts_60.txt", strip_id=True)
        out["60"] = report("BB(2,5) formal 60", specs)
    if which in ("all", "608"):
        specs = load_machines("BB6_holdouts_608.txt", strip_id=True)
        out["608"] = report("BB(6) 608", specs)
    if which in ("all", "3x3"):
        specs = load_machines("3x3_holdout_6.txt")
        out["3x3"] = report("BB(3,3) 6", specs)

    # Cross-list: are the 37 classes contained in the 60 classes?
    if "37" in out and "60" in out:
        k37 = set(out["37"])
        k60 = set(out["60"])
        print(f"\n37-classes inside 60-classes: {len(k37 & k60)}/{len(k37)}")
        print(f"37 classes NOT in 60: {len(k37 - k60)}")
        for k in (k37 - k60):
            print("   not-in-60 example:", out["37"][k][0][1])

    # Does any BB(2,5) holdout coincide with the champion (a proven halter)?
    if "37" in out:
        champ = bb.TM.parse("1RB3LA4RB0RB2LA_1LB2LA3LA1RA1RZ")
        ck, _ = canonical(champ)
        print("\nchampion in 37 classes:", ck in out["37"])
        if "60" in out:
            print("champion in 60 classes:", ck in out["60"])


if __name__ == "__main__":
    main()
