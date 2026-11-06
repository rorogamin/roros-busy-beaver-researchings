"""Reachable (state, symbol) pairs for the six BB(3,3) holdouts.

A pair that is never read cannot influence the run.  This explains why two
machines that differ only in one unreachable cell have identical behaviour,
and it is the first thing to check before attempting a merge proof.
"""

import bb

MACHINES = {
    "Bigfoot": "1RB2RA1LC_2LC1RB2RB_---2LA1LA",
    "153": "1RB0LB0RC_2LC2LA1RA_1RA1LC---",
    "758": "1RB2LC1RC_2LC---2RB_2LA0LB0RA",
    "531": "1RB2LA1LA_2LA0RA2RC_---0LC2RA",
    "532": "1RB2LA1LA_2LA0RA2RC_---1RB2RA",
    "397": "1RB1LB2LC_1LA2RB1RB_---0LA2LA",
}

CAP = 1_000_000


def visited_pairs(tm: bb.TM, cap: int):
    tape = {}
    head = 0
    state = 0
    seen = set()
    for _ in range(cap):
        v = tape.get(head, 0)
        seen.add((state, v))
        tr = tm.trans[state][v]
        if tr is None:
            return seen, True, state, v
        w, d, nxt = tr
        if w:
            tape[head] = w
        else:
            tape.pop(head, None)
        head += d
        state = nxt
    return seen, False, state, None


def main():
    for name, spec in MACHINES.items():
        tm = bb.TM.parse(spec)
        seen, halted, state, sym = visited_pairs(tm, CAP)
        full = tm.n * tm.m
        missing = [(s, v) for s in range(tm.n) for v in range(tm.m)
                   if (s, v) not in seen]
        print(f"{name:8s} visited {len(seen)}/{full} pairs; halted={halted}"
              + (f" at ({state},{sym})" if halted else "")
              + (f"; never read: {missing}" if missing else "; all pairs read"))


if __name__ == "__main__":
    main()
