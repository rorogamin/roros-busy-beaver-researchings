"""Held-out validation for the shrunken BVE cursor/predecessor quotients.

This does not use the training corpus from `bve_searchmin.py`.  It generates
fresh shallow/deep terms and raw predecessor outputs, runs the reference
46/44 table and the requested quotient, and requires identical output tapes.

Usage: python tools/bve_holdout.py [module]
Default module: bve_compose38

Scope: cursor + predecessor only.  No general FS.
"""

import importlib
import random
import sys
sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import V, ZERO, ONE, phi, add
import bve_compose
import bve_compose44


def run(TABLE, tape, head, max_steps=200_000):
    tape = dict(tape)
    state = 0
    for _ in range(max_steps):
        row = TABLE.get((state, tape.get(head, 0)))
        if row is None:
            return True, tape, head
        w, d, nxt = row
        tape[head] = w
        head += 1 if d == 'R' else -1
        if nxt is None:
            return True, tape, head
        state = nxt
    return False, tape, head


def gen(seed=991, n=800):
    rng = random.Random(seed)

    def term(d):
        if d <= 0:
            return rng.choice((ZERO, ONE))
        k = rng.randrange(4)
        if k == 0:
            return phi(0, term(d - 1))
        if k == 1:
            return phi(1, term(d - 1))
        if k == 2:
            return add(term(d - 1), term(d - 1))
        return add(phi(0, term(d - 1)), term(d - 1))

    terms = [B.epsilon0(), B.epsilon1(), B.epsilon0_plus_one(),
             phi(0, ONE), add(phi(0, ONE), ONE)]
    for _ in range(n):
        terms.append(term(4))
    out = []
    seen = set()
    for v in terms:
        if v.is_zero():
            continue
        try:
            s = bve_compose.term_tape(v)
        except Exception:
            continue
        if s in seen:
            continue
        seen.add(s)
        out.append(({i: int(c) for i, c in enumerate(s)},
                    bve_compose.h_end_of(v)))
    # One raw predecessor pass, then use the output as a fresh input.
    raw = []
    for tape, head in out[:250]:
        ok, t2, h2 = run(bve_compose44.TABLE, tape, head)
        if not ok:
            continue
        s = bve_compose.tape_string(t2)
        try:
            v = bve_compose.T.from_tape(s)
        except Exception:
            continue
        if v.is_zero() or s in seen:
            continue
        seen.add(s)
        raw.append(({i: int(c) for i, c in enumerate(s)},
                    bve_compose.h_end_of(v)))
    out.extend(raw)
    return out


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'bve_compose38'
    mod = importlib.import_module(name)
    data = gen()
    bad = 0
    for idx, (tape, head) in enumerate(data):
        ok1, t1, h1 = run(bve_compose44.TABLE, tape, head)
        ok2, t2, h2 = run(mod.TABLE, tape, head)
        if (ok1, bve_compose.tape_string(t1), h1) != \
           (ok2, bve_compose.tape_string(t2), h2):
            bad += 1
            if bad <= 8:
                print(f'  MISMATCH {idx}: ok {ok1}/{ok2}')
                print(f'    ref {bve_compose.tape_string(t1)}')
                print(f'    got {bve_compose.tape_string(t2)}')
    print(f'{name}: {len(data)} held-out tapes; '
          + ('all equal to reference' if bad == 0 else f'{bad} mismatches'))
    return 0 if bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
