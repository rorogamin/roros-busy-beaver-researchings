"""Search for observed-context merges below the 40-state BVE quotient.

The greedy pass in `bve_contextmin.py` found 44 -> 40.  A different merge
order may unlock a fifth state.  This script uses a wider corpus (deep random
terms plus raw predecessor outputs) and a beam search over candidate merges
that are sound on every context actually fired by that corpus.  Each candidate
is checked against the 44-state reference outputs on the corpus; whenever a
shorter table is found, the full 409-term BVE check is run before accepting it.

Scope: cursor + predecessor only.  No general FS.

Run: python tools/bve_searchmin.py
"""

import os
import random
import sys
sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import V, ZERO, ONE, phi, add
import bve_compose
import bve_compose44
import bve_contextmin


def term_tape(v):
    return bve_compose.term_tape(v)


def h_end(v):
    return bve_compose.h_end_of(v)


def run(TABLE, tape, head, max_steps=200_000):
    tape = dict(tape)
    state = 0
    fired = {}
    for _ in range(max_steps):
        sym = tape.get(head, 0)
        fired.setdefault(state, set()).add(sym)
        row = TABLE.get((state, sym))
        if row is None:
            return True, tape, head, fired
        w, d, nxt = row
        tape[head] = w
        head += 1 if d == 'R' else -1
        if nxt is None:
            return True, tape, head, fired
        state = nxt
    return False, tape, head, fired


def _term_gen(seed, n1, n2):
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

    fixed = [ONE, B.epsilon0(), B.epsilon1(), B.epsilon0_plus_one(),
             phi(0, ONE), phi(0, phi(0, ONE)),
             add(phi(0, ONE), ONE), add(ONE, ONE),
             add(phi(0, ONE), phi(0, ONE)),
             add(phi(0, ONE), phi(1, ZERO)),
             add(phi(1, ONE), phi(1, ONE))]
    terms = list(fixed)
    for _ in range(n1):
        terms.append(term(3))
    for _ in range(n2):
        terms.append(term(4))
    return terms


def make_corpus():
    terms = _term_gen(101, 500, 250)
    data = []
    seen = set()
    for v in terms:
        if v.is_zero():
            continue
        try:
            s = term_tape(v)
        except Exception:
            continue
        key = s
        if key in seen:
            continue
        seen.add(key)
        data.append(({i: int(c) for i, c in enumerate(s)}, h_end(v)))
    # Raw predecessor outputs are valid inputs for the next predecessor pass.
    raw = []
    for tape, head in data[:300]:
        ok, out, _h, _f = run(bve_compose44.TABLE, tape, head)
        if not ok:
            continue
        s = bve_compose.tape_string(out)
        try:
            v = bve_compose.T.from_tape(s)
        except Exception:
            continue
        if v.is_zero():
            continue
        if s in seen:
            continue
        seen.add(s)
        raw.append(({i: int(c) for i, c in enumerate(s)}, h_end(v)))
    data.extend(raw)
    return data


def fingerprint(TABLE, data):
    out = []
    for tape, head in data:
        ok, t2, h2, _f = run(TABLE, tape, head)
        if not ok:
            return None
        out.append((ok, bve_compose.tape_string(t2), h2))
    return tuple(out)


def exact_quotient(TABLE):
    live = bve_compose44._reachable(TABLE, 0)
    part = bve_compose44._partition(TABLE, live)
    return bve_compose44._quotient(TABLE, part)


def contexts(TABLE, data):
    fired = {}
    for tape, head in data:
        ok, _t, _h, f = run(TABLE, tape, head)
        if not ok:
            continue
        for s, syms in f.items():
            fired.setdefault(s, set()).update(syms)
    return fired


def candidates(TABLE, data):
    fired = contexts(TABLE, data)
    states = sorted({s for (s, _sym) in TABLE})
    out = []
    for y in states:
        if not fired.get(y):
            continue
        for x in states:
            if x == y:
                continue
            if all(TABLE.get((y, sym)) == TABLE.get((x, sym))
                   for sym in fired[y]):
                out.append((y, x))
    return out


def merge(TABLE, y, x):
    trial = {}
    for (s, sym), row in TABLE.items():
        if s == y:
            continue
        w, d, nxt = row
        trial[(s, sym)] = (w, d, x if nxt == y else nxt)
    return trial


def accepts_std(TABLE, n):
    old_table, old_n = bve_compose44.TABLE, bve_compose44.N_STATES
    bve_compose44.TABLE, bve_compose44.N_STATES = TABLE, n
    try:
        return bve_compose44.check()
    finally:
        bve_compose44.TABLE, bve_compose44.N_STATES = old_table, old_n


def table_key(TABLE):
    return tuple(sorted((s, sym, w, d, nxt)
                        for (s, sym), (w, d, nxt) in TABLE.items()))


def emit_module(table, n, path=None):
    if path is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            'bve_compose%d.py' % n)
    rows = []
    for (s, sym) in sorted(table):
        w, d, nxt = table[(s, sym)]
        rows.append(f'    ({s}, {sym}): ({w}, {d!r}, {nxt!r}),')
    text = '''"""The %d-state observed-context BVE cursor/predecessor table.

Generated by tools/bve_searchmin.py.  Cursor + predecessor only: no general
FS, no index, no boot.

Run: python tools/bve_compose%d.py
"""

import sys
sys.path.insert(0, 'tools')

import bve_compose

N_STATES = %d
TABLE = {
%s
}


def check():
    old_table, old_n = bve_compose.TABLE, bve_compose.N_STATES
    bve_compose.TABLE, bve_compose.N_STATES = TABLE, N_STATES
    try:
        ok = bve_compose.check()
        ok = bve_compose.check_raw_chain() and ok
    finally:
        bve_compose.TABLE, bve_compose.N_STATES = old_table, old_n
    return ok


def main():
    print(f'BVE search quotient: {N_STATES} states, {len(TABLE)} rows')
    ok = check()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
''' % (n, n, n, '\n'.join(rows))
    with open(path, 'w', encoding='ascii') as f:
        f.write(text)
    return path


def main():
    data = make_corpus()
    base = dict(bve_compose44.TABLE)
    fn = fingerprint(base, data)
    assert fn is not None
    print(f'corpus={len(data)}; reference 44 states')
    starts = [(44, base, ())]
    seen = {table_key(base)}
    best = (44, base, ())
    beam = 32
    for depth in range(1, 8):
        nxt = []
        for n, table, path in starts:
            for y, x in candidates(table, data):
                trial = merge(table, y, x)
                t2, n2, _ = exact_quotient(trial)
                if n2 >= n:
                    continue
                key = table_key(t2)
                if key in seen:
                    continue
                seen.add(key)
                fp = fingerprint(t2, data)
                if fp != fn:
                    continue
                if n2 < best[0]:
                    best = (n2, t2, path + ((y, x),))
                    print(f'  depth {depth}: {n2} states, path {best[2]}')
                if n2 < 40:
                    if not accepts_std(t2, n2):
                        print(f'    full check rejected {n2}')
                        continue
                    emit_module(t2, n2)
                    print(f'FOUND {n2} states; wrote tools/bve_compose{n2}.py')
                    return 0
                nxt.append((n2, t2, path + ((y, x),)))
        if not nxt:
            break
        nxt.sort(key=lambda z: (z[0], table_key(z[1])))
        starts = nxt[:beam]
        print(f'  depth {depth}: frontier {len(nxt)}, best {starts[0][0]}')
    print(f'no sub-40 table; best {best[0]} states')
    print('This search is sound only on the recorded corpus + full 409 check; '
          'it does not build the general FS arm.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
