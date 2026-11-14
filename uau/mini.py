"""State-minimisation probe for the uubin machine.

Two states are equivalent when, for both symbols, they write the same bit, move
the same way, and go to equivalent states.  Merging equivalent states leaves the
behaviour on every tape unchanged, so any class count below 325 is free states.

Usage:  python mini.py [halt_on]
"""

import sys
from collections import defaultdict

sys.path.insert(0, ".")
import uubin as U  # noqa: E402


def signature(tm, q, cls, extras):
    out = []
    for b in (0, 1):
        w, mv, nx = tm.tr[(q, b)]
        if nx is None:
            tag = -1
        elif nx in cls:
            tag = cls[nx]
        else:
            tag = extras[nx]  # sink target such as TRAP, never a source
        out.append((w, mv, tag))
    return tuple(out)


def minimise(states, tm):
    cls = {q: 0 for q in states}
    extras = {
        nx: -(i + 2)
        for i, nx in enumerate(sorted({tm.tr[(q, b)][2] for q in states for b in (0, 1)} - set(states)))
    }
    ncls = 1
    while True:
        sigs = {}
        for q in states:
            sigs.setdefault(signature(tm, q, cls, extras), []).append(q)
        new = {}
        for i, group in enumerate(sigs.values()):
            for q in group:
                new[q] = i
        if len(sigs) == ncls:
            return new, len(sigs), sigs
        cls, ncls = new, len(sigs)


def main():
    halt_on = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    tm, start = U.build(halt_on)
    states = sorted({q for q, b in tm.tr})
    cls, n, groups = minimise(states, tm)
    print("states %d -> classes %d (mergeable %d)" % (len(states), n, len(states) - n))
    for sig, group in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        if len(group) > 1:
            print("  class of %d: %s" % (len(group), " ".join(sorted(group))))


if __name__ == "__main__":
    main()
