"""Check machines/eps1_s40_drain.txt: parse, run, compare decode-exactly.

The artifact is the SAME device the checked tool build_drain() implements; this
checker re-verifies the emitted separator on the same 213 starts (13 fixed
edges + 200 random), directly from the txt, through the frame/decode of the
150-state table.

Run: python tools/check_eps1_s40_drain.py    (expect ALL OK)
"""

import sys
import random

sys.path.insert(0, 'tools')

from morphet import step as mstep
import eps1_table as T
from eps1_table import frame as tf_frame, decode as tf_decode
from eps1_chain import NUM, ATOM, ATOM1


def parse(path='machines/eps1_s40_drain.txt'):
    rows = {}
    names = {}
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split()
            if not parts:
                continue
            fs, rd, wr, dirn, nxt = parts
            s, r, w, n = int(fs), int(rd), int(wr), int(nxt)
            assert dirn in ('L', 'R'), dirn
            assert (s, r) not in rows, f'duplicate {line}'
            rows[(s, r)] = (w, dirn, n)
            names.setdefault(s, f's{s}')
            names.setdefault(n, f's{n}')
    return rows, names


def run(rows, tape, head, state, limit=400000):
    cur = 0
    while cur < limit:
        out = mstep(rows, tape, head, state)
        cur += 1
        if out is None:
            return cur, head
        head, state = out
    raise TimeoutError('no halt in %d steps' % limit)


# the model cases: (p, chain, n) — the identical sweep to tools/eps1_s40.py
CASES = [
    (0, [ATOM], 1),
    (0, [ATOM], 2),
    (0, [ATOM, NUM(2)], 1),
    (1, [NUM(3)], 2),
    (2, [ATOM1, NUM(2), NUM(3)], 1),
    (0, [NUM(3), NUM(7)], 2),
    (2, [ATOM, NUM(5), NUM(3)], 2),
    (1, [NUM(1), NUM(2), NUM(3)], 1),
    (0, [ATOM, NUM(2)], 2),
    (3, [ATOM1], 1),
    (0, [NUM(9)], 2),
    (2, [ATOM, NUM(2), NUM(3), NUM(4)], 2),
    (1, [ATOM, NUM(2), NUM(3), NUM(4)], 2),
]


def main():
    rows, names = parse()
    n_states = len(names)
    print(f'parsed machines/eps1_s40_drain.txt: {n_states} states, '
          f'{len(rows)} rows')
    assert n_states == 21 and len(rows) == 31, \
        f'artifact shape changed: {n_states} states, {len(rows)} rows'
    bad = 0
    ok = 0
    for p, chain, n in CASES:
        tape, E, home = tf_frame(p, list(chain), n)
        work = dict(tape)
        try:
            steps, head = run(rows, work, E, 0)
        except TimeoutError as exc:
            bad += 1
            print(f'  TIMEOUT p={p} chain={chain} n={n}: {exc}')
            continue
        try:
            got = tf_decode(work, head)
        except Exception as exc:                             # noqa: BLE001
            bad += 1
            print(f'  DECODE FAILED p={p} chain={chain} n={n}: {exc}')
            continue
        pp, ch, nn = got
        want = (p + n, list(chain), n)
        if (pp, ch, nn) != want:
            bad += 1
            print(f'  MISMATCH p={p} chain={chain} n={n}: got {(pp, ch, nn)}, '
                  f'want {want}')
        else:
            ok += 1
    rng = random.Random(5)
    for _ in range(200):
        p = rng.randint(0, 2)
        n = rng.randint(1, 5)
        chain = [rng.choice([NUM(1), NUM(2), NUM(3), NUM(5), ATOM, ATOM1])] \
            + [rng.choice([NUM(2), NUM(3), ATOM])
               for _ in range(rng.randint(0, 2))]
        tape, E, home = tf_frame(p, list(chain), n)
        work = dict(tape)
        try:
            steps, head = run(rows, work, E, 0)
        except TimeoutError as exc:
            bad += 1
            print(f'  TIMEOUT p={p} chain={list(chain)} n={n}: {exc}')
            continue
        try:
            got = tf_decode(work, head)
        except Exception as exc:                             # noqa: BLE001
            bad += 1
            print(f'  DECODE FAILED p={p} chain={list(chain)} n={n}: {exc}')
            continue
        pp, ch, nn = got
        want = (p + n, list(chain), n)
        if (pp, ch, nn) != want:
            bad += 1
            print(f'  MISMATCH p={p} chain={list(chain)} n={n}: '
                  f'got {(pp, ch, nn)}, want {want}')
        else:
            ok += 1
    print(f'  {ok}/{ok + bad} starts ended decode-exactly '
          f'(canonical layout, {len(rows)} rows)')
    print()
    print('ALL OK' if bad == 0 else f'{bad} FAILURES')
    return 0 if bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
