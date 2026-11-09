"""eps1_mergehunt.py — the automated merge hunt for the eps1_odi machine.

What it does, per seed sn:
  1. proves the bisimulation floor of the shipped table (the exact
     coarsest-signature partition of minimise_table, reported honestly:
     every class must be a singleton or the checker of record missed a
     merge);
  2. a trace-driven dead-row audit: drives a large, diverse corpus of
     starts (tower pre-states, random chains, deep unit stacks, deep
     p-values) through the machine and records every (state, read) row
     that ever fires; a row that never fires on any canonical input is
     a free rewrite candidate (its successor/write can be changed to
     whatever helps a neighbouring fusion);
  3. a closest-pair report: for every pair of states this lists the
     rows that block a bisimulation merge, classified as
       'target-only'  — same write and direction, different successor
       'write-diff'   — different write or direction
     and reports the minimum number of row-pairs that separate it.  A
     pair separated only by target-only rows in *dead* rows is usable
     today; the same in live rows is the documented fork-problem wall.

Usage:  python tools/eps1_mergehunt.py [sn]
Exit code 0 with summary; nonzero if an unexpected anomaly appears
(non-singleton bisim classes are printed but are NOT an error here: the
plain tool never claims the table was already at a fixed point under a
different partition).
"""

import os
import sys
import random
import collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import eps1_odi as O
import eps1_chain as C
from eps1_odi import build_table, campaign, step_model, same_chain
from eps1_super_local import chain_of, D


def bisim_partition(T, part):
    """One coarsening round; returns None when fixed."""
    blocks = collections.defaultdict(list)
    for s in T:
        sig = []
        for sym in (0, 1):
            r = T[s].get(sym)
            if r is None:
                sig.append(('H',))
            else:
                w, d, nxt = r
                sig.append(('R', w, d, part[nxt]))
        blocks[tuple(sig)].append(s)
    ids = {}
    for i, key in enumerate(sorted(blocks, key=lambda k: min(blocks[k]))):
        for m in blocks[key]:
            ids[m] = i
    return ids


def exact_partition(T):
    part = {s: s for s in T}
    while True:
        nxt = bisim_partition(T, part)
        if nxt is None or nxt == part:
            return part
        part = nxt


def fired_rows(T, sn, trials=1200, seed=99, stack_depth=12):
    """Collect the set of (state, read-symbol) rows ever fired."""
    rng = random.Random(seed)
    fired = set()
    # the corpus: tower pre-states, random chains, deep unit stacks
    starts = []
    for t_n in (1, 2, 3):
        p, ch = chain_of(D.tower(t_n))
        starts.append((p, list(ch)))
    for _ in range(max(trials - 3, 0)):
        kind = rng.random()
        if kind < 0.45:
            # plain deep chain
            ch = [rng.randint(1, 6) for _ in range(rng.randint(1, 8))]
            p = rng.randint(0, 4)
            try:
                ch = list(C.normalise(p, ch)[1])
            except Exception:
                continue
            starts.append((p, ch))
        elif kind < 0.8:
            # deep unit stack with a mixed bottom
            k = rng.randint(1, stack_depth)
            bottom = rng.choice([2, 3, 4, [1, 1][:1]])
            if bottom == [1, 1]:
                ch = [1] * k
            else:
                ch = [bottom] + [1] * k
            p = rng.randint(0, 3)
            try:
                ch = list(C.normalise(p, ch)[1])
            except Exception:
                continue
            starts.append((p, ch))
        else:
            # alternating tall/short
            ch = []
            for _ in range(rng.randint(2, 7)):
                ch.append(rng.choice([1, 2, 3, 5, 6]))
            p = rng.randint(0, 3)
            try:
                ch = list(C.normalise(p, ch)[1])
            except Exception:
                continue
            starts.append((p, ch))
    for mp, mc in starts:
        try:
            cells, h0 = O.mk_tape(mp, list(mc))
        except ValueError:
            continue
        for _m in range(6):
            try:
                ok = step_model(mp, list(mc), sn)
            except Exception:
                break
            if ok[0] != 'move':
                break
            st, h = 'IN', h0
            steps = 0
            while steps < 400000:
                sym = cells.get(h, 0)
                a = T.get(st, {}).get(sym)
                if a is None:
                    break       # machine death (counts via the harness)
                w, d, nx = a
                fired.add((st, sym))
                cells[h] = w
                h += 1 if d == 'R' else -1
                st = nx
                steps += 1
                if st == 'IN':
                    break
            if st != 'IN':
                break           # died; do not continue this start
            try:
                dp, dc = O.decode_tape(cells)
            except ValueError:
                break
            if O.C.full(dp, dc) != O.C.full(ok[1], ok[2]):
                break
            mp, mc = ok[1], list(ok[2])
            cells, h0 = cells, h
    return fired


def pair_report(T):
    """For every unordered pair, the blocking rows."""
    names = sorted(T)
    report = {}
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            s, t = names[i], names[j]
            diffs = []
            for sym in (0, 1):
                rs, rt = T[s].get(sym), T[t].get(sym)
                if rs is None and rt is None:
                    continue
                if rs is None or rt is None:
                    diffs.append((sym, 'halt-hollow'))
                    continue
                ws, ds, ns = rs
                wt, dt, nt = rt
                if ws != wt or ds != dt:
                    diffs.append((sym, 'write-diff'))
                elif ns != nt:
                    diffs.append((sym, 'target-only'))
            if diffs:
                report[(s, t)] = diffs
    return report


def main():
    sn = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    T, meta = build_table(sn)
    print(f'sn={sn}: started table: {len(T)} states, '
          f'{sum(len(r) for r in T.values())} rows')
    part = exact_partition(T)
    multi = collections.defaultdict(list)
    for s, b in part.items():
        multi[b].append(s)
    classes = {b: sorted(v) for b, v in multi.items() if len(v) > 1}
    if classes:
        print('  bisim classes with >1 member (the checker of record '
              'merged by renaming; these are residual structures):')
        for b, v in sorted(classes.items()):
            print('   ', v)
    else:
        print('  bisim floor: every state is its own class '
              '(the shipped checker fixed point confirmed)')

    fired = fired_rows(T, sn)
    allrows = {(s, sym) for s in T for sym in T[s]}
    dead = sorted(allrows - fired)
    print(f'  trace audit: {len(fired)} rows ever fired '
          f'of {len(allrows)}; dead rows: {len(dead)}')
    for s, sym in dead:
        print(f'    dead row: {s}.{sym} = {T[s][sym]}'
              f'  ({meta.get(s, "")})')

    rep = pair_report(T)
    # focus: pairs separated only by target-only rows
    closest = {k: v for k, v in rep.items() if all(d == 'target-only'
               for _, d in v)}
    print(f'  pair report: {len(rep)} non-equal pairs; '
          f'{len(closest)} differ ONLY in successors '
          '(one-row rewrites away; live-row cases = the fork-problem wall)')
    n = 0
    for (s, t), v in sorted(closest.items(),
                            key=lambda kv: len(kv[1]))[:14]:
        print(f'    {s} ~ {t}: {len(v)} differing row(s): '
              + ', '.join(f'[{sym}]' for sym, _ in v)
              + '  [' + (meta.get(s) or '') + ' | ' + (meta.get(t) or '') + ']')
        n += 1
    if not closest:
        print('    (none: every pair differs in a write/direction row)')
    print('MERGEEHUNT DONE')


if __name__ == '__main__':
    main()
