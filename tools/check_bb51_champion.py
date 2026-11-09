"""Check machines/bb51_eps0_champion.txt: parse, verify the transcription's
shape, and run it to a step cap.

The recorded claim (wiki Talk:Champions, Racheline, Sept 2024, original text
in the corpus) is that the machine's ones-count beats (f_e0)^8 of a big
tower and so surpasses f_{e0+1}(8).  That is far beyond any simulation; the
checks here are the ones a transcript CAN support:

  * the parse is exact: 51 states, 2 symbols, 101 rows (the halt pair is
    state 50 read 1, which this repo encodes as a missing pair);
  * a run from the recorded start (state 30, blank tape, head on cell 0)
    reaches the 10^7-step cap without halting — or, if it halts earlier,
    halts ONLY on the recorded pair (50, 1): an undefined pair anywhere
    else is a transcription bug and fails the check;
  * the run's census (steps, distinct states used, tape span, ones at cap)
    as a stable observational signature for future comparisons.

No level claim is made; the recorded claim stays the wiki's.

Run: python tools/check_bb51_champion.py    (expect ALL OK)
"""

import sys

sys.path.insert(0, 'tools')

from morphet import step as mstep


def parse(path='machines/bb51_eps0_champion.txt'):
    rows = {}
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split()
            fis, rd, wr, dirn, nxt = parts
            s, r, w, n = int(fis), int(rd), int(wr), int(nxt)
            assert dirn in ('L', 'R'), dirn
            assert 0 <= s <= 50 and 0 <= n <= 50, f'unexpected id: {line}'
            assert (s, r) not in rows, f'duplicate {line}'
            rows[(s, r)] = (w, dirn, n)
    return rows


def run(rows, head=0, state=30, cap=10_000_000):
    """Returns (halt_or_none, steps, lo, hi, states_used, tape).
    halt_or_none is None on cap exhaustion, else the (state, read) row read
    when no row existed."""
    tape = {}
    cur = 0
    minc = maxc = head
    states_used = {state}
    while cur < cap:
        k = (state, tape.get(head, 0))
        if k not in rows:
            return k, cur, minc, maxc, states_used, tape
        w, d, nxt = rows[k]
        tape[head] = w
        if d == 'R':
            head += 1
            maxc = max(maxc, head)
        else:
            head -= 1
            minc = min(minc, head)
        state = nxt
        states_used.add(state)
        cur += 1
    return None, cur, minc, maxc, states_used, tape


def main():
    rows = parse()
    n_states = len({s for s, _ in rows} | {n for _, _, n in rows.values()})
    print(f'parsed: {n_states} states, {len(rows)} rows, 2 symbols')
    ok = n_states == 51 and len(rows) == 101
    if not ok:
        print('FAIL: expected 51 states / 101 rows')
    halt, steps, lo, hi, used, tape = run(rows)
    ones = sum(1 for v in tape.values() if v == 1)
    print('run to cap 10^7 from state 30 on blank tape:')
    if halt is None:
        print(f'  cap reached with no halt: steps {steps}, '
              f'span {hi - lo + 1} cells ({lo}..{hi}), ones {ones}, '
              f'distinct states used {len(used)}')
        ok = ok and steps >= 10_000_000 - 10_000
    else:
        print(f'  halted at step {steps} on row {halt}, '
              f'span {hi - lo + 1} cells ({lo}..{hi}), ones {ones}')
        ok = ok and halt == (50, 1) and steps > 10_000
    sus = sorted(used)
    print(f'  used states: {sus}')
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
