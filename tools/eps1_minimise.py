"""Minimise a table: Moore partition refinement, then rebuild and recheck.

A 2-symbol machine is a map (state, symbol) -> (write, move, next). Two states
are equivalent when, for both symbols, they write the same thing, move the same
way and go to equivalent states, so refinement never changes the run -- it only
renames states. Whatever it saves is free.
"""

import sys

sys.path.insert(0, 'tools')

HALT = -1


def blocks_of(rows):
    """Refine the partition of states until it stops changing."""
    states = sorted({s for s, _ in rows})
    block = {s: 0 for s in states}
    while True:
        sig = {}
        for s in states:
            key = []
            for sym in (0, 1):
                row = rows.get((s, sym))
                if row is None:
                    key.append(None)
                else:
                    w, d, t = row
                    key.append((w, d, HALT if t is None else block[t]))
            sig[s] = tuple(key)
        order = {}
        new = {}
        for s in states:
            k = sig[s]
            if k not in order:
                order[k] = len(order)
            new[s] = order[k]
        if len(order) == len({block[s] for s in states}):
            block = new
            break
        block = new
    return block, len({block[s] for s in states})


def rebuild(rows, start):
    block, n = blocks_of(rows)
    out = {}
    for (s, sym), (w, d, t) in rows.items():
        out[(block[s], sym)] = (w, d, None if t is None else block[t])
    return out, block[start], n


def main():
    import tm
    import eps1_loader as L

    m, rows = L.machine()
    states = len({s for s, _ in rows})
    mini, start, n = rebuild(rows, 6)   # the carve's entry, fed a short run
    print(f'composed: {states} states, {len(rows)} rows')
    print(f'refined : {n} states, {len(mini)} rows')
    ok = True
    for run, want in ((9, 3), (10, 255)):
        tape = {i: 1 for i in range(run)}
        steps, t, h, s, halted = tm.TM(n, mini).run(
            head=0, state=start, tape=tape, max_steps=3_000_000)
        got = L.m1.value(t, L.BUDGET + 1)
        good = halted and got == want
        ok = ok and good
        print(f'  refined machine on 1^{run}: steps={steps} value={got} want={want} '
              f'{"PASS" if good else "FAIL"}')
    print('ALL OK' if ok else 'FAILURES')
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
