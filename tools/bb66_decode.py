"""Decode the BB(6,6) champion's base-3 notation and check conformance.

The decode, read off the run (not off the claim):

  L2  the 5-marker layer.  Tape `5 3^a 2^b`, value V = 3a + b.
      The carry (a, b) -> (a-1, b+3) preserves V.
  --  the 5 is erased and the 4-marker layer starts with fuel = out = V.
  L1  the 4-marker layer.  Tape `4 1^fuel 3^out`.
      sweep: the head reaches a new left minimum, fuel += 1.
      chunk: a 32-cell group of fuel is copied to output, 1^32 -> 3^32,
             i.e. fuel -= 32, out += 32 (the count is preserved).

The champion is the machine; this file is its spec.  The checker segments the
run at new head extremes, verifies the L2 carry, the level transition, the
sweep and the 32-chunk copy, and reports the final decode.  A mismatch is a
result, not a crash.

Run: python tools/bb66_decode.py [cap]
"""

import sys

sys.path.insert(0, 'tools')

from bbmulti import parse

SPEC = ('4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_'
        '3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB')


def counts(tape, nsym):
    c = [0] * nsym
    for v in tape.values():
        c[v] += 1
    return c


def decode(tape, nsym):
    c = counts(tape, nsym)
    if c[5]:
        return ('L2', c[3], c[2], 3 * c[3] + c[2], c)
    if c[4]:
        return ('L1', c[1], c[3], c[1], c)
    return ('L0', c[1], c[3], c[1], c)


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 50_000_000
    table, nst, nsym = parse(SPEC)
    tape = {}
    head = 0
    state = 'A'
    steps = 0
    lo = hi = 0
    events = []
    while steps < cap:
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print(f'HALT at {steps}')
            break
        w, d, nxt = a
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt
        if head < lo or head > hi:
            lo = min(lo, head)
            hi = max(hi, head)
            events.append((steps, state, head, counts(tape, nsym)))

    print(f'cap={cap:,} steps={steps:,} events={len(events):,} '
          f'span={hi - lo + 1:,}')

    # 1. L2 carry: C homes with the 5 present.
    first = [e for e in events if e[3][5] == 1 and e[1] == 'C']
    ok = 0
    for i in range(1, len(first)):
        a0, b0 = first[i - 1][3][3], first[i - 1][3][2]
        a1, b1 = first[i][3][3], first[i][3][2]
        ok += ((a1, b1) == (a0 - 1, b0 + 3))
    vals = sorted({3 * e[3][3] + e[3][2] for e in first})
    print(f'\nL2 carry (5 present, C homes): {len(first)} homes, '
          f'carry {ok}/{max(0, len(first) - 1)}')
    print(f'  3a+b values: {vals}')
    l2_ok = len(first) > 1 and ok == len(first) - 1 and vals == [91]

    # 2. Level transition: 5 gone, 4 present, fuel = out = 91 (out = 3-block
    #    minus the 2-cell carry, hence the observed 3-block 93).
    erase = [i for i in range(1, len(events))
             if events[i][3][5] == 0 and events[i - 1][3][5] == 1
             and events[i][0] > 4_000]
    if erase:
        e = events[erase[0]]
        print(f'\n5-marker erase (L2 -> L1): step {e[0]:,} {e[1]} h={e[2]}: '
              f'1:{e[3][1]} 2:{e[3][2]} 3:{e[3][3]} 4:{e[3][4]} 5:{e[3][5]}')
    else:
        print('\n5-marker erase: not found')
    lvl = [e for e in events if e[3][4] == 1 and e[3][5] == 0]
    fuel_home = [e for e in lvl if e[3][1] == 91]
    if fuel_home:
        e = fuel_home[0]
        print(f'L1 value home (fuel 91, first 4 marker): step {e[0]:,} '
              f'{e[1]} h={e[2]}: '
              f'1:{e[3][1]} 2:{e[3][2]} 3:{e[3][3]} 4:{e[3][4]} 5:{e[3][5]}')
        lvl_ok = bool(erase)
    else:
        print(f'L1 value home: no fuel-91 home in {len(lvl)} events')
        lvl_ok = False

    # 3. The 32-chunk copy: fuel -32, out +32, carry unchanged.
    chunks = []
    for i in range(1, len(events)):
        b, a = events[i - 1][3], events[i][3]
        if a[1] - b[1] == -32 and a[3] - b[3] == 32 and a[2] == b[2] \
                and a[4] - b[4] in (0, 1):
            chunks.append((events[i][0], events[i][1], events[i][2], b, a))
    print(f'\nL1 chunk copies 1^32 -> 3^32: {len(chunks)}')
    for s, st, h, b, a in chunks[:6]:
        print(f'  step {s:,} {st} h={h}: fuel {b[1]}->{a[1]} '
              f'out {b[3]}->{a[3]} carry {b[2]} 4 {b[4]}->{a[4]}')
    chunk_ok = len(chunks) >= 1

    # 4. The sweep: new minimum, fuel +1, everything else fixed.
    sweeps = []
    for i in range(1, len(events)):
        b, a = events[i - 1][3], events[i][3]
        if events[i][0] > 23_000 and a[1] - b[1] == 1 and a[2] == b[2] \
                and a[3] == b[3] and a[4] == b[4]:
            sweeps.append(i)
    print(f'\nL1 sweeps (+1 fuel, other fields fixed): {len(sweeps)} '
          f'of {len(events) - 1} post-23k events')

    # 5. Final decode.
    level, a, b, value, c = decode(tape, nsym)
    print(f'\nfinal decode: {level} a={a} b={b} value={value}')
    print(f'  counts 1:{c[1]} 2:{c[2]} 3:{c[3]} 4:{c[4]} 5:{c[5]}')

    ok_all = l2_ok and lvl_ok and chunk_ok
    print('\nVERDICT: ' + (
        'the champion conforms to the decoded chunked base-3 notation '
        f'({ok}/{max(0, len(first) - 1)} L2 carries, {len(chunks)} chunks, '
        f'{len(sweeps)} sweeps).  The decoded L1 dynamics are a fuel-driven '
        'unary/base-3 conversion (score ~ sqrt(steps), i.e. quadratic time), so '
        'f_{w*2} is not established by this decode.'
        if ok_all else
        'the decoded notation does not match the run'))
    return 0 if ok_all else 1


if __name__ == '__main__':
    sys.exit(main())
