"""Test whether two standard-format machines are isomorphic under the usual
symmetries: state permutation, symbol permutation, and tape mirroring.

If a symmetry maps one machine's table exactly onto the other's, the two
machines agree on every configuration, so any initial-configuration
equivalence is immediate (same machine, renamed).
"""

import itertools

import bb


def transform(tm, state_perm, sym_perm, mirror):
    n, m = tm.n, tm.m
    out = [[None] * m for _ in range(n)]
    for s in range(n):
        for v in range(m):
            tr = tm.trans[s][v]
            ns = state_perm[s]
            nv = sym_perm[v]
            if tr is None:
                out[ns][nv] = None
            else:
                w, d, nxt = tr
                out[ns][nv] = (sym_perm[w], -d if mirror else d,
                               None if nxt < 0 else state_perm[nxt])
    return out


def isomorphic(a: bb.TM, b: bb.TM):
    if (a.n, a.m) != (b.n, b.m):
        return None
    for sp in itertools.permutations(range(a.n)):
        for yp in itertools.permutations(range(a.m)):
            for mirror in (False, True):
                if transform(a, sp, yp, mirror) == b.trans:
                    return sp, yp, mirror
    return None


def main():
    pairs = [
        ("153", "1RB0LB0RC_2LC2LA1RA_1RA1LC---", "758", "1RB2LC1RC_2LC---2RB_2LA0LB0RA"),
        ("531", "1RB2LA1LA_2LA0RA2RC_---0LC2RA", "532", "1RB2LA1LA_2LA0RA2RC_---1RB2RA"),
        ("397", "1RB1LB2LC_1LA2RB1RB_---0LA2LA", "531", "1RB2LA1LA_2LA0RA2RC_---0LC2RA"),
        ("Bigfoot", "1RB2RA1LC_2LC1RB2RB_---2LA1LA", "397", "1RB1LB2LC_1LA2RB1RB_---0LA2LA"),
    ]
    for name_a, sa, name_b, sb in pairs:
        a, b = bb.TM.parse(sa), bb.TM.parse(sb)
        res = isomorphic(a, b)
        print(f"{name_a:8s} vs {name_b:8s}: isomorphic={bool(res)}"
              + (f"  state_perm={res[0]} sym_perm={res[1]} mirror={res[2]}" if res else ""))


if __name__ == "__main__":
    main()
