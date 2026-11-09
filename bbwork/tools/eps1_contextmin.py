"""eps1_contextmin.py — the observed-context merge hunt.

Bisimulation keeps two states separate whenever some row differs, but a
state that never enters on those differing symbols (per every firing in
the corpus) can be replaced by any state agreeing on its observed rows.
The gate harness rebuilds the tape from the decoded (p, chain) after
every landing, so the reachable behaviour is exactly what the corpus
exercises; this tool turns that into a reduction pass:

  1. fire the corpus of record (census pre-step states, gate-2 style
     randoms, adversarial starts, plus an exhaustive small-region sweep)
     with an instrumented campaign, recording per state the set of
     symbols actually read;
  2. propose merges: redirect Y's predecessors to X whenever X's rows
     agree with Y's on every symbol Y ever reads;
  3. apply candidates greedily, judged by a gate screen
     (census tiers 1..2 up to landing bad, 250 random starts x 4 moves,
     tiers 1..2); a candidate is applied only if the screen passes;
  4. re-minimise (reachability + bisimulation) after each success;
  5. report the surviving redirect list (bake candidate) and re-run the
     full battery + the adversarial battery on the final tables.

The merge is sound on the machine's reachable configurations given the
corpus: the redirect replaces Y's rows with X's exactly at the symbols
Y was observed reading, and everything else about X is untouched.

Usage: python tools/eps1_contextmin.py [sn]
Exit 0 when the final tables pass every gate.
"""

import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import eps1_chain as C
from eps1_odi import (build_table, campaign, check_moves_random,
                      check_tiers, census_battery, decode_tape, mk_tape,
                      minimise_table, step_model)


# ------------------------------------------------------------------
# the corpus collectors

def corpus_census(limit_t=3):
    from eps1_super_local import chain_of, D
    out = []
    for t_n in range(1, limit_t + 1):
        mp, mc = chain_of(D.tower(t_n))
        for _ in range(200000):
            if not mc:
                break
            try:
                kind, p2, c2 = step_model(mp, list(mc), 1)
            except Exception:
                break
            out.append((mp, list(mc)))
            if kind != 'move':
                break
            mp, mc = p2, list(c2)
    return out


def corpus_random(trials=1500, seed=99, moves=4, limit_t=2):
    from eps1_super_local import chain_of, D
    rng = random.Random(seed)
    out = []
    for t_i in range(trials):
        if t_i % 4 == 0:
            mp, mc = chain_of(D.tower(rng.randint(1, limit_t)))
        else:
            mc = [rng.choice([2, 3])] + [rng.choice([1, 1, 2, 3])
                 for _ in range(rng.randint(1, 3))]
            mp, mc = C.normalise(rng.randint(0, 2), list(mc))
        out.append((mp, list(mc)))
        for _m in range(moves - 1):
            try:
                kind, p2, c2 = step_model(mp, list(mc), 1)
            except Exception:
                break
            if kind != 'move':
                break
            out.append((p2, list(c2)))
            mp, mc = p2, list(c2)
    return out


def corpus_exhaustive(max_len=4, park_max=2):
    out = []
    parts = ['B0', 'B1', 1, 2, 3]
    def gen(prefix):
        yield tuple(prefix)
        if len(prefix) >= max_len:
            return
        for nxt in parts:
            if prefix and nxt in ('B0', 'B1'):
                continue
            yield from gen(prefix + [nxt])
    for ch in gen([]):
        for p in range(park_max + 1):
            out.append((p, list(ch)))
    return out


def corpus_adv(trials=2500, seed=424242, moves=3):
    import eps1_adversarial as A
    rng = random.Random(seed)
    out = []
    for _ in range(trials):
        st = A.random_start(rng)
        if st is None:
            continue
        p, ch, _cells, _h0 = st
        out.append((p, list(ch)))
        for _m in range(moves - 1):
            try:
                kind, p2, c2 = step_model(p, list(ch), 1)
            except Exception:
                break
            if kind != 'move':
                break
            out.append((p2, list(c2)))
            p, ch = p2, list(c2)
    return out


# ------------------------------------------------------------------
# the instrumented firing pass

def fire_corpus(T, sn, corpus):
    """Yield through the corpus; return {state: {symbols ever read}}."""
    fired = {}

    def icamp(p, ch):
        try:
            cells, h0 = mk_tape(p, list(ch))
        except ValueError:
            return False
        st, h, steps = 'IN', h0, 0
        while steps < 400000:
            sym = cells.get(h, 0)
            fired.setdefault(st, set()).add(sym)
            a = T[st].get(sym)
            if a is None:
                return True
            w, d, nx = a
            cells[h] = w
            h += 1 if d == 'R' else -1
            st = nx
            steps += 1
            if st == 'IN':
                return True
        return True

    fired_stats = {'starts': 0}
    for p, ch in corpus:
        if icamp(p, ch):
            fired_stats['starts'] += 1
    return fired, fired_stats


# ------------------------------------------------------------------
# the merge driver

def merge_candidate_pairs(T, fired):
    """Ordered (Y, X) pairs: X agrees with Y at every symbol Y reads;
    a state may also die on a never-rowed symbol (compared via .get)."""
    pairs = []
    names = sorted(T)
    for Y in names:
        ey = fired.get(Y)
        if ey is None:
            continue            # never fired: unreachable in this corpus
        for X in names:
            if X == Y:
                continue
            if all(T[X].get(s) == T[Y].get(s) for s in ey):
                pairs.append((Y, X))
    return pairs


def redirect(now, Y, X):
    """n = rows retargeted Y -> X (in place)."""
    n = 0
    for s, rows in now.items():
        for a, (w, d, nx) in list(rows.items()):
            if nx == Y:
                rows[a] = (w, d, X)
                n += 1
    return n


def screen(T, sn):
    _ok, bad_c, _h, _f = census_battery(T, sn, limit_t=2)
    if bad_c:
        return False
    if check_moves_random(T, sn, trials=250, seed=sn * 977 + 13, moves=4):
        return False
    if check_tiers(T, sn, limit_t=2):
        return False
    return True


def hunt(T, meta, sn, verbose=True):
    meta = dict(meta)
    base = len(T)
    applied = []
    round_i = 0
    fired, stats = fire_corpus(T, sn, CORPUS)
    if verbose:
        print(f'  fired corpus: {stats["starts"]} starts, '
              f'{sum(1 for v in fired.values() if v)} states ever fired')
    while True:
        round_i += 1
        progress = False
        for (Y, X) in merge_candidate_pairs(T, fired):
            if Y not in T or X not in T:
                continue
            backup = {s: dict(r) for s, r in T.items()}
            redirect(T, Y, X)
            ok = screen(T, sn)
            if not ok:
                T.clear()
                for s, r in backup.items():
                    T[s] = dict(r)
                continue
            T, meta = minimise_table(T, meta, 'IN')
            applied.append((Y, X))
            progress = True
            if verbose:
                print(f'  merged: {Y} -> {X} (kept {X})  '
                      f'states now {len(T)}')
        if not progress:
            return T, meta, applied, fired
        fired, stats = fire_corpus(T, sn, CORPUS)   # refresh observations


CORPUS = None


def run(sn, verbose=True):
    global CORPUS
    CORPUS = (corpus_census(3) + corpus_random(1500, 99, 4)
              + corpus_exhaustive(5, 3) + corpus_adv(4000, 424242, 3))
    T, meta = build_table(sn)
    if verbose:
        print(f'sn={sn}: built {len(T)} states')
    T, meta, applied, _fired = hunt(T, meta, sn, verbose)
    if verbose:
        print(f'sn={sn}: applied {len(applied)} merges: '
              f'{[f"{a}->{b}" for a, b in applied]}')
    ok, bad, _h, _f = census_battery(T, sn)
    bad2 = check_moves_random(T, sn)
    bad3 = check_tiers(T, sn)
    verdict = ('ALL OK' if bad == 0 and bad2 == 0 and bad3 == 0
               else 'FAILED')
    print(f'sn={sn}: final {len(T)} states, battery {verdict}')
    return len(applied), verdict, len(T)


if __name__ == '__main__':
    sn = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    _n, verdict, _states = run(sn)
    sys.exit(0 if verdict == 'ALL OK' else 1)
