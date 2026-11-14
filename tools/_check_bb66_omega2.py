"""Check the 6x6 BB(6,6) champion against the omega*2 chain spec.

The spec (tools/omega2_chain.py) decodes a tape to (a, b) = w*a + b and moves
    pred: (a, b) -> (a, b-1)   (b > 0), n += 1
    fs:   (a, 0) -> (a-1, n)

The champion's clean early pass decodes as (a, b) = (#3, #2).  This checker
segments the pass at new tape extremes (one carry step each), compares the
observed transition with the spec, and reports the level-marker (4) boundaries
where the machine's macro moves would have to live.

Exit 0 only if the observed moves match the spec.  A mismatch is the result,
not a crash.
"""

import sys

sys.path.insert(0, 'tools')

from bbmulti import parse
import omega2_chain as S

SPEC = ('4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_'
        '3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB')


def counts(tape, nsym):
    c = [0] * nsym
    for v in tape.values():
        c[v] += 1
    return c


def main():
    table, nst, nsym = parse(SPEC)
    tape = {}
    head = 0
    state = 'A'
    steps = 0
    lo = hi = 0
    events = []
    bounds = []
    prev4 = None
    while steps < 300_000:
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print(f'halt at {steps}')
            break
        w, d, nxt = a
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt
        if head < lo or head > hi:
            lo = min(lo, head)
            hi = max(hi, head)
            if steps > 1400:
                events.append((steps, state, head, counts(tape, nsym), lo, hi))
        p4 = [p for p, v in tape.items() if v == 4]
        if p4 != prev4 and steps > 4000:
            bounds.append((steps, state, head, counts(tape, nsym), p4))
        prev4 = p4

    print('first extreme events after the boot (a=#3, b=#2, n=#1)')
    for st, s, h, c, l, r in events[:10]:
        print(f'  step {st:>6} {s} head {h:>4}: a={c[3]:>3} b={c[2]:>3} '
              f'n={c[1]:>3} 4s={c[4]} 5s={c[5]}')

    # The C states are the macro homes; the interleaved B states are the
    # one-step write of the next 3 at the frontier (a -> a+1).
    homes = [e for e in events if e[1] == 'C']
    if len(homes) >= 2:
        e0, e1 = homes[0], homes[1]
        st0 = (e0[3][3], e0[3][2])
        n0 = e0[3][1]
        try:
            want, n2, kind = S.step(st0, n0)
        except S.Halt:
            want, kind = None, 'halt'
        got = (e1[3][3], e1[3][2])
        print(f'\nspec move 1 from {st0} at n={n0}: {kind} -> {want}')
        print(f'observed next C home: {got}')
        match = want == got
        print('  ' + ('MATCH' if match else 'MISMATCH'))
    else:
        match = False

    first = [e for e in events if e[1] == 'C' and e[3][5] == 1]
    ok1 = 0
    for i in range(1, len(first)):
        a0, b0 = first[i - 1][3][3], first[i - 1][3][2]
        a1, b1 = first[i][3][3], first[i][3][2]
        if (a1, b1) == (a0 - 1, b0 + 3):
            ok1 += 1
    print(f'\nfirst pass (5 present, C homes): {len(first)} homes, '
          f'carry {ok1}/{max(0, len(first) - 1)}')
    if first:
        a, b = first[-1][3][3], first[-1][3][2]
        print(f'  last first-pass home: a={a} b={b}, 3a+b={3 * a + b}')
    ok_all = 0
    for i in range(1, len(homes)):
        a0, b0 = homes[i - 1][3][3], homes[i - 1][3][2]
        a1, b1 = homes[i][3][3], homes[i][3][2]
        if (a1, b1) == (a0 - 1, b0 + 3):
            ok_all += 1
    print(f'  full window: carry {ok_all}/{max(0, len(homes) - 1)} '
          '(breaks after the level boundary)')
    vals = [3 * e[3][3] + e[3][2] for e in first[:10]]
    print('3a+b at the first C homes: ' + ', '.join(str(v) for v in vals))

    def spec_matches(seq):
        ok = tot = 0
        for i in range(1, len(seq)):
            st0 = (seq[i - 1][3][3], seq[i - 1][3][2])
            n0 = seq[i - 1][3][1]
            got = (seq[i][3][3], seq[i][3][2])
            try:
                want, _, _ = S.step(st0, n0)
            except S.Halt:
                continue
            tot += 1
            ok += (want == got)
        return ok, tot

    okf, totf = spec_matches(first)
    oka, tota = spec_matches(homes)
    print(f'  spec move-for-move: first pass {okf}/{totf}, '
          f'full window {oka}/{tota}')

    print('\nlevel-marker (4) boundaries')
    for st, s, h, c, p4 in bounds:
        print(f'  step {st:>6} {s} head {h:>5} 4@{p4} '
              f'counts 1:{c[1]} 2:{c[2]} 3:{c[3]} 4:{c[4]} 5:{c[5]}')

    print('\nVERDICT: ' + ('the champion follows the w*2 descent'
                           if match else
                           'NEGATIVE - the champion does not follow the w*2 descent'))
    return 0 if match else 1


if __name__ == '__main__':
    sys.exit(main())
