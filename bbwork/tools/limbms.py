"""Run the BB(150) machine in `limbms.txt` and check its documented modules.

The file is a 5-tuple listing with `_` for blank, `*` for "no move", `!` for a
breakpoint and `;` comments. The machine is 150 states: a 6-state loader, a
doubling module, the S module (cloner), the T module, then the RFPMS core.

Nothing here can run the full machine: the loader writes 10^^15 marks. What can
be run is every module downstream of the loader on small inputs, which is what
this checks:

  1. the doubling module, entered as `d0` with a run of marks,
  2. the S module on `S(a, b) = 1^a 0 1^b`,
  3. the documented RFPMS example, `11_11__111_111_...`, which the comments give
     an expected expansion sequence and a HALT for.
"""

import re
import sys

RAW = 'limbms.txt'


def parse(path=RAW):
    """5-tuples -> {(state, sym): (write, dir, next)}; halt states map to None."""
    rows = {}
    for line in open(path, encoding='utf-8'):
        line = line.split(';')[0].replace('!', '').strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 5:
            continue
        st, sym, w, d, nx = parts
        if sym == '*':
            for s in (0, 1):
                rows[(st, s)] = _row(w, d, nx, s)
        else:
            rows[(st, '_' if sym == '_' else sym)] = _row(w, d, nx, sym)
    out = {}
    for (st, sym), (w, d, nx) in rows.items():
        s = 0 if sym == '_' else int(sym)
        w = None if w == '*' else (0 if w == '_' else int(w))
        out[(st, s)] = (w, d, None if nx.startswith('halt') else nx)
    return out


def _row(w, d, nx, sym):
    return (w, d, nx)


def parse_tape(text):
    """`11_11__111` -> {cell: symbol} with cell 0 the leftmost character."""
    tape = {}
    for i, ch in enumerate(text):
        if ch == '1':
            tape[i] = 1
    return tape


def render(tape):
    """Runs of marks separated by blanks: the S(a, b, c, ...) form."""
    if not tape:
        return 'S()'
    lo, hi = min(tape), max(tape)
    groups, run = [], 0
    for i in range(lo, hi + 2):
        if tape.get(i, 0) == 1:
            run += 1
        else:
            if run:
                groups.append(run)
            run = 0
    return 'S(' + ','.join(map(str, groups)) + ')'


def run(rows, start, tape, head=0, max_steps=200000, watch=None):
    """Step the machine; `watch` records the tape each time that state is entered."""
    seen = []
    t = dict(tape)
    st, h = start, head
    for step in range(1, max_steps + 1):
        if watch is not None and st == watch:
            seen.append(dict(t))
        sym = t.get(h, 0)
        row = rows.get((st, sym))
        if row is None:
            return dict(steps=step - 1, tape=t, head=h, state=st, halted=True,
                        trapped=False, seen=seen)
        w, d, nx = row
        if w is not None and w != sym:
            t[h] = w
        elif w is None:
            pass
        if d == 'r':
            h += 1
        elif d == 'l':
            h -= 1
        if nx is None:
            return dict(steps=step, tape=t, head=h, state=None, halted=True,
                        trapped=False, seen=seen)
        st = nx
    return dict(steps=max_steps, tape=t, head=h, state=st, halted=False,
                trapped=True, seen=seen)


def _go(rows, text, start, cap):
    """Run from a text tape; report steps, halt, states used and the final tape."""
    tape = parse_tape(text)
    t, h, st, seen = dict(tape), 0, start, set()
    for n in range(1, cap + 1):
        seen.add(st)
        r = rows.get((st, t.get(h, 0)))
        if r is None:
            return n - 1, True, st, seen, t
        w, d, nx = r
        if w is not None:
            t[h] = w
        if d == 'r':
            h += 1
        elif d == 'l':
            h -= 1
        if nx is None:
            return n, True, None, seen, t
        st = nx
    return cap, False, st, seen, t


def backend_check(rows):
    """The backend end to end: doubling -> S -> T -> the core, starting at d0.

    d0 is where the 6-state loader hands over, so this is the whole machine minus
    its loader, run from a small input.
    """
    ok = True
    print()
    print('backend from d0 (doubling -> e1..e6 -> S1..S13 -> T1..T3 -> A1 core)')
    steps, halted, stop, seen, t = _go(rows, '11_11', 'd0', 200000)
    allst = {s for s, _ in rows}
    good = halted and steps == 30841 and len(seen) == 144
    ok = ok and good
    print(f'  S(2,2): steps={steps} halted={halted} states_used={len(seen)} '
          f'of {len(allst)} {"PASS" if good else "FAIL"}')
    loader_only = sorted(allst - seen)
    print(f'  untouched states: {loader_only} (the loader, as expected)')
    # the production input shape, with the setup's own m > n^2
    print()
    print('production input 1 0 1^n 0 (0 1^n)^m')
    cases = [((2, 5), 2176, True), ((2, 6), 198785, True), ((2, 7), 200028, True),
             ((3, 5), 9162, True), ((3, 7), 9444, True)]
    for (n_, m_), want, whalt in cases:
        text = '1' + '_' + '1' * n_ + '_' + ('_' + '1' * n_) * m_
        steps, halted, stop, seen, t = _go(rows, text, 'A1', 300000)
        good = steps == want and halted == whalt and len(seen) == 119
        ok = ok and good
        print(f'  n={n_} m={m_}: steps={steps} halted={halted} '
              f'states_used={len(seen)} want {want} {"PASS" if good else "FAIL"}')
    # a growing instance: the same shape one step wider does not halt
    text = '1' + '_' + '1' * 2 + '_' + ('_' + '1' * 2) * 8
    steps, halted, stop, seen, t = _go(rows, text, 'A1', 2000000)
    good = (not halted) and steps == 2000000
    ok = ok and good
    print(f'  n=2 m=8: steps={steps} halted={halted} stop={stop} (growing) '
          f'{"PASS" if good else "FAIL"}')
    return ok


def check():
    rows = parse()
    states = sorted({s for s, _ in rows})
    print(f'parsed {len(rows)} rows over {len(states)} states')
    ok = True

    # 1. the documented RFPMS example: start at A1, expect the listed expansions
    #    and a halt (the comments give the sequence and say it halts).
    tape = parse_tape('11_11__111_111_111_111_111_111_111_111')
    r = run(rows, 'A1', tape, head=0, max_steps=200000, watch='A1')
    print(f'\nRFPMS example: {len(r["seen"])} cycles, halted={r["halted"]}, '
          f'steps={r["steps"]}')
    for i, t in enumerate(r['seen'][:8]):
        print(f'  cycle {i}: {render(t)}')
    if not r['halted']:
        print('  (did not halt)')
        ok = False

    # 2. the S module on S(a, b): should clone b about a times
    for a, b in ((2, 2), (3, 2)):
        t0 = {i: 1 for i in range(a)}
        t0[a + b + 1] = 0
        tape = {i: 0 for i in range(a)}
        for i in range(a):
            tape[i] = 1
        base = a + 1
        for i in range(b):
            tape[base + i] = 1
        r = run(rows, 'S1', tape, head=0, max_steps=200000)
        print(f'\nS({a},{b}) -> halted={r["halted"]} steps={r["steps"]} '
              f'{render(r["tape"])}')

    return ok


if __name__ == '__main__':
    print('BB(150) module checks')
    ok = check()
    ok = backend_check(parse()) and ok
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
