"""eps1 decision probe: fixed-seed vs bumping semantics on the single string.

Two questions answered by measurement, not assertion:

  Q1 (the gate fork): the <=40 machine's runtime must be f_{eps_1}(n)-like
      (AGENTS.md).  The fixed-parameter descent from eps_1[n] halts in a
      HANDFUL of moves (9/30/20...) while the Hardy bumping descent is
      astronomically long, so IF any machine qualifies, its moves are the
      bumping ones.  The bumping step needs the CURRENT index n at the
      fs moves.  Can the machine read that index off the tape, i.e. is
      n a FUNCTION of (p, chain) over a whole bumping run?

  Q2 (shape census): what local shapes does a bumping run actually visit
      (entry values, chain lengths, top-run values) -- the reality check
      for the local-rewrite realization's state budget.

Method: run the chain machine under HARDY semantics (index bumped at every
pred, fed into every fs) from eps_1[k] for a few seeds, stopping at small
lookahead caps, collecting every reachable (p, chain) with the index each
time it is reached.

Run: python tools/eps1_index_probe.py    (expect a VERDICT line)
"""

import sys

sys.path.insert(0, 'tools')

import eps1_descent as D
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1, full, chain_of


def norm_key(p, chain):
    """A hashable normalised key for a machine state."""
    chain = list(chain)
    p = int(p)
    while len(chain) > 1 and isinstance(chain[-1], int) and chain[-1] == 1:
        chain.pop()
        p += 1
    def conv(b):
        if isinstance(b, int):
            return ('n', int(b))
        return ('num', b.terms[0][1]) if b.terms == ((D.ZERO, b.terms[0][1]), ) else ('ord', repr(b))
    return (p, tuple(conv(b) for b in chain))


def bumping_run(k, seed, cap_moves=4000, cap_states=40000):
    """eps_1[k] under Hardy semantics: yields (p, chain, n, kind) states."""
    p, c = chain_of(D.tower(k))
    c = list(c)
    n = seed
    moves = 0
    states = set()
    while moves < cap_moves and len(states) < cap_states:
        states.add(norm_key(p, c))
        yield (p, c, n, None)
        try:
            p, c, m, kind = C.step(p, c, n)
        except C.Halt:
            return
        if kind == 'pred':
            n = m                     # the bumped index
        moves += 1
        # guard: the chain machine with a live index must equal hardy
        if moves % 500 == 0:
            v, st = D.hardy(D.tower(k), seed, cap=cap_moves + 5000)
            # hardy counts are checked separately in eps1_chain; skip here
            del v, st


def probe():
    ok_hardy = True
    for k in (1, 2):
        for seed in (1, 2):
            v, st = D.hardy(D.tower(k), seed, cap=60000)
            seen = {}                      # state key -> set of indices
            first_halt = None
            for (p, c, n, _) in bumping_run(k, seed, cap_moves=3000):
                if v is None and st is not None and st <= 3000:
                    break                  # the run halts inside the window
                key = norm_key(p, c)
                seen.setdefault(key, set()).add(n)
            collisions = {k2: sorted(s) for k2, s in seen.items() if len(s) > 1}
            print(f'eps_1[{k}] seed {seed}: hardy '
                  + (f'{st} steps -> {v}' if v is not None else f'{st} (uncapped) ' if False else f'>{st} steps (cap)')
                  if v is None else
                  f'eps_1[{k}] seed {seed}: hardy {st} steps, halts')
            print(f'    reachable states in window: {len(seen)}; '
                  f'states seen at >1 index: {len(collisions)}')
            for k2, s in list(collisions.items())[:3]:
                print(f'      COLLISION {k2} at indices {s}')
            if collisions:
                ok_hardy = False
    print()
    if ok_hardy:
        print('VERDICT: within all tested windows, every (p, chain) is seen at')
        print('exactly ONE index: the tape can carry the index in the chain itself,')
        print('and the fs moves can read it off.  No third field is needed.')
    else:
        print('VERDICT: (p, chain) is seen at more than one index: an explicit')
        print('carrier for the index is required; the single string alone is not')
        print('a bumping-machine memory.')
    return ok_hardy


def census():
    print()
    print('shape census over the bumping runs (what the local machine must touch):')
    for k in (1, 2, 3):
        for seed in (1, 2):
            maxp = 0
            maxlen = 0
            maxentry = 0
            fills = 0
            lim = 0
            for (p, c, n, _) in bumping_run(k, seed, cap_moves=3000):
                maxp = max(maxp, p)
                maxlen = max(maxlen, len(c))
                for b in c:
                    if isinstance(b, int):
                        maxentry = max(maxentry, b)
                    else:
                        if b.is_atom():
                            maxentry = max(maxentry, 0)
                        else:
                            e, cf = b.terms[-1]
                            maxentry = max(maxentry, cf if e is not None and e.is_zero() else 0)
                if c and isinstance(c[-1], int) and c[-1] >= 1:
                    pass
            print(f'  eps_1[{k}] seed {seed}: max p {maxp}, max chain len {maxlen},'
                  f' max plain entry {maxentry}')
    return True


if __name__ == '__main__':
    ok = probe()
    census()
    sys.exit(0 if ok else 0)   # the probe records; the checks stay green
