"""eps1 index-fit: which arithmetic candidate reproduces the Hardy index
from the (p, chain) alone, on the injected bumping runs?

The probe (eps1_index_probe.py) measured that (p, chain) is index-free
injective in the tested windows: an expression exists.  This module fits
concrete candidates on the collected samples:

    A  n == p + 1 + (number of non-bottom entries)   (the spawn-chain idea)
    B  n == the top entry's value + p - 1
    C  n == (sum of plain entry values) + p - 1
    D  n == the bottom (first) entry's value - 1
    E  n == (the plain entry count) + p - 1
    F  n == p * 2 - ... no; (top entry value) alone
    G  n == (the second entry's value, if any) ...
plus a learned check: index == f for ALL samples of one run.

Run: python tools/eps1_fit.py     (prints the per-candidate fit)
"""

import sys

sys.path.insert(0, 'tools')

import eps1_descent as D
import eps1_chain as C
from eps1_chain import full, chain_of

from eps1_index_probe import norm_key, bumping_run


def samples(k, seed, moves=400):
    out = []
    for (p, c, n, _k) in bumping_run(k, seed, cap_moves=moves):
        out.append((p, list(c), n))
    return out


def feats(p, c):
    chain = list(c)
    pl = [b for b in chain if isinstance(b, int)]
    top = chain[-1] if chain else None
    bottom = chain[0] if chain else None

    def numval(b):
        if isinstance(b, int):
            return b
        if b.is_atom():
            return None
        e, cf = b.terms[-1] if len(b.terms) else (None, 0)
        if e is not None and e.is_zero():
            return cf
        return None
    tv = numval(top)
    bv = numval(bottom)
    sv = sum(b for b in pl)
    second = chain[1] if len(chain) > 1 else None
    secv = numval(second) if second is not None else 0
    return dict(p=p, npn=len(chain), tv=tv, bv=bv, sv=sv,
                top1=(1 if tv == 1 else 0), secv=secv,
                np=len(pl))


def fit(k, seed):
    rows = samples(k, seed)
    cands = {
        'A p+1+entries': lambda f: (f['p'] + 1 + (f['npn'] - 1)),
        'B tv+p-1':      lambda f: ((f['tv'] if f['tv'] is not None else 0) + f['p'] - 1),
        'C sv+p-1':      lambda f: (f['sv'] + f['p'] - 1),
        'D bv-1':        lambda f: ((f['bv'] if f['bv'] is not None else 0) - 1),
        'E np+p-1':      lambda f: (f['np'] + f['p'] - 1),
        'F tv':          lambda f: (f['tv'] if f['tv'] is not None else 0),
        'G secv+p':      lambda f: (f['secv'] + f['p']),
        'H tv-1+p':      lambda f: ((f['tv'] if f['tv'] is not None else 0) - 1 + f['p']),
        'I tv-2+p':      lambda f: ((f['tv'] if f['tv'] is not None else 0) - 2 + f['p']),
        'J bv+p-2':      lambda f: ((f['bv'] if f['bv'] is not None else 0) + f['p'] - 2),
        'K tv+sv':       lambda f: ((f['tv'] if f['tv'] is not None else 0) + f['sv']),
    }
    res = {}
    for name, fn in cands.items():
        bad = 0
        for (p, c, n) in rows:
            f = feats(p, c)
            try:
                if fn(f) != n:
                    bad += 1
            except Exception:
                bad += 1
        res[name] = bad
    return len(rows), res


def run():
    print('index-fit: candidates for n == f(p, chain) on bumping-run samples')
    allbad = {}
    counts = {}
    for k in (1, 2, 3):
        for seed in (1, 2, 3):
            total, res = fit(k, seed)
            counts[k, seed] = total
            for name, bad in res.items():
                allbad.setdefault(name, [0, 0])
                allbad[name][0] += bad
                allbad[name][1] += total
    total_rows = sum(counts.values())
    for name, (bad, tot) in sorted(allbad.items(), key=lambda x: x[1][0]):
        print(f'  {name}: {bad}/{tot} mismatches' + ('   FULL FIT' if bad == 0 else ''))
    print(f'  samples per run-window: {total_rows} rows across '
          f'{len(counts)} runs (eps_1[1..3] x seeds 1..3)')
    fits = [name for name, (bad, _) in allbad.items() if bad == 0]
    if fits:
        print('FIT FOUND:', fits)
        return True
    print('NO FIT among the listed candidates: the reading rule stays open')
    return False


if __name__ == '__main__':
    run()
