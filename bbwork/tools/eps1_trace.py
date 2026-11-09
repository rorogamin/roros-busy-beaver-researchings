"""eps1_trace.py — one-shot tracer: run the sn=1 machine on sample tapes,
log every move (state, pos, read) and print the landed tape positions."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import eps1_odi as O


def run_trace(cells, head, T, cap=2000, label=''):
    pos = head
    st = 'IN'
    log = []
    # tape snapshotter
    lo = min(list(cells.keys()) + [pos]) - 4
    hi = max(list(cells.keys()) + [pos]) + 6
    print(f'--- {label}: tape {lo}..{hi}')
    print('   start:', ' '.join(f'{i}:{cells.get(i,0)}' for i in range(lo, hi + 1)))
    for step in range(cap):
        row = T.get(st)
        if row is None:
            log.append((step, st, pos, 'HALT'))
            print(f'  {step}: {st}@{pos} HALT')
            break
        r = cells.get(pos, 0)
        if r not in row:            # hmm: rows keyed by read symbol
            log.append((step, st, pos, 'NOROW'))
            print(f'  {step}: {st}@{pos} read={r} NO ROW (death)')
            break
        w, d, nxt = row[r]
        log.append((step, st, pos, r, w, d, nxt))
        if step < 60 or st.startswith(('D', 'IN', 'M', 'PK', 'WAS', 'ABS', 'WR', 'WB', 'FSP', 'RAW')):
            print(f'  {step}: {st}@{pos} read={r} write={w} {d} -> {nxt}')
        if w != r:
            cells[pos] = w
        pos += 1 if d == 'R' else -1
        st = nxt
    return cells, pos, st, log


def main():
    T, meta = O.build_table(1)
    print('states:', len(T))
    # p=1, chain=[3] -> top L = 5: dispatch D-walk, route E walk (WAE),
    # the look, the fs spend (FSL/FSP) and the fs walk back.
    cells, head = O.mk_tape(1, [3])
    c2, p2, halt, log = run_trace(dict(cells), head, T, 200,
                                  'p=1 chain=[3] (top L=5) FULL')
    print('landed:', O.decode_tape(c2) if halt else 'death', 'head', p2)


def tmp():
    pass


if __name__ == '__main__':
    main()
