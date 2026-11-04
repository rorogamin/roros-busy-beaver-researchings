"""PrSS / Address Notation, checked against the eps_1 chain machinery.

This is the model check for EPS1_67_PLAN.md §10's index-free descent
candidate.  The corpus (Yeyito777/bbchallenge-corpus, snapshot 2026-10-29)
records that the community's 51-state eps_0 champion simulates Address
Notation — a Primitive Sequence System variant — and that Racheline gave
the expansion rule verbatim (wiki Talk:Champions, original text):

    Given a sequence S of natural numbers, to compute its expansion,
    start by letting c be the last element of S.  If c = 0, then S is a
    successor and its predecessor is S without the last element.
    Otherwise, find the last element r of S which is less than c.
    Decrease c by 1, and let B be everything in this new sequence after
    r.  Append infinitely many copies of B.

No corpus page pins the list-to-ordinal map's orientation, so this module
does the check the plan prescribes: implement the expansion verbatim, and
mechanically test the small family of candidate bridges (orientation,
sentinel placement, copies convention) against eps1_chain's own chain_fs
and pred_chain, value-by-value via full().  So the atoms stay out of the
bridge battery: NUM-bottom chains only, with the entry-code translation
NUM(c) -> c+2 (the same convention the 150-state table's code() uses), and
atom-bottom cases are recorded as not-expressible rather than asserted.

The recorded result of record (do not "improve" it by hand): on the
covered class NO candidate bridge produced a single value match — 0 for
every bridge.  reversed+trailing shows 85 value MISMATCHES (the
successor-class cases, where the trailing-0 construction makes the rule
fire the pred branch, which can never equal pred_chain's value) and 215
non-expressions; the per-class breakdown below prints the empirical
distribution, and the examples it records are what the next decoding
candidate has to explain.

Run: python tools/eps1_prss.py
"""

import sys
import random

sys.path.insert(0, 'tools')

import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1, full, chain_fs, pred_chain, normalise


def to_ints(chain):
    """Chain -> plain-int list: the NUM bottom c becomes c+2, tails as-is."""
    b = chain[0]
    code = b.terms[0][1] + 2 if isinstance(b, C.Ord) else b + 2
    return [code] + list(chain[1:])


def to_chain(body):
    """Int list back: first entry v -> NUM(v-2) (v >= 3), the rest as-is."""
    return [NUM(body[0] - 2)] + list(body[1:])


def prss_expand(S, copies):
    """One Address-Notation expansion pass, verbatim (see the docstring).

    S: list of naturals.  The rule needs an element < c to exist before the
    last, which a canonical list always provides (its leading 0 sentinel);
    a list violating that is rejected.  `copies` is the fundamental-
    sequence parameter: the machine iterates the append finitely per pass.
    """
    if not S:
        raise ValueError('empty list')
    c = S[-1]
    if c == 0:
        return S[:-1], 'pred'          # successor: predecessor, no appends
    r = None
    for j in range(len(S) - 2, -1, -1):
        if S[j] < c:
            r = j
            break
    if r is None:
        raise ValueError(f'no element < {c}: {S!r} is not canonical')
    new = S[:-1] + [c - 1]
    B = new[r + 1:]
    return new + B * copies, 'fs'


# ------------------------------------------------------------- the bridges
# Each bridge: (chain -> PrSS list).  Inputs are already int lists.

def bridge_identity(chain):
    """PrSS list = [0] + int-coded chain as-is."""
    return [0] + list(chain)


def bridge_identity_rev(chain):
    """PrSS list = reversed int-coded chain with a trailing sentinel 0."""
    return list(reversed(chain)) + [0]


def bridge_bare(chain):
    """PrSS list = the int-coded chain itself, no sentinel."""
    return list(chain)


BRIDGES = {'identity+sentinel': bridge_identity,
           'reversed+trailing': bridge_identity_rev,
           'bare': bridge_bare}


def val_of(body):
    """full(0, chain(body)); None when the shape is not a valid chain."""
    if not body or body[0] < 3:
        return None
    if any(x == 0 for x in body[1:]):
        return None
    try:
        return full(0, to_chain(body))
    except Exception:                                    # noqa: BLE001
        return None


def check_bridges(trials=300, seed=13, samples=3):
    """Expansion of the bridged chain vs chain_fs / pred_chain, by value.

    Reports the per-class empirical distribution (kind x outcome) per
    bridge, and records up to `samples` example shapes per outcome class.
    """
    print('the expansion rule against eps1_chain, per candidate bridge')
    print('  (NUM-bottom chains only; atom bottoms are not-expressible in')
    print('   the int bridges and are counted as skips, never asserted)')
    rng = random.Random(seed)
    results = {nm: {} for nm in BRIDGES}
    for _ in range(trials):
        bottom = rng.choice([NUM(2), NUM(3), NUM(5)])
        tail = [rng.choice([1, 1, 2, 3]) for _ in range(rng.randint(1, 3))]
        chain = [bottom] + tail
        kind = 'limit' if tail[-1] == 1 else 'succ'
        rng_n = rng.randint(1, 3)
        ints = to_ints(chain)
        for nm, fn in BRIDGES.items():
            S = fn(ints)
            outcome = None
            if kind == 'limit':
                wb, cb = normalise(0, list(chain_fs(chain, rng_n)))
                want = full(wb, cb)
                try:
                    got_list, kind_got = prss_expand(list(S), rng_n)
                except ValueError as exc:
                    outcome = ('skip', exc)
                else:
                    v = val_of(got_list)
                    if v is None:
                        outcome = ('skip', 'not-expressible-value')
                    elif v == want:
                        outcome = ('ok', None)
                    else:
                        outcome = ('bad', None)
            else:
                wb, cb = normalise(0, list(pred_chain(chain)))
                want = full(wb, cb)
                if S[-1] != 0:
                    outcome = ('skip', 'no-successor-reading')
                else:
                    got_list, kind_got = prss_expand(list(S), 1)
                    if kind_got != 'pred':
                        outcome = ('bad', 'kind')
                    else:
                        v = val_of(got_list)
                        if v is None:
                            outcome = ('skip', 'not-expressible-value')
                        elif v == want:
                            outcome = ('ok', None)
                        else:
                            outcome = ('bad', None)
            if outcome is None:                      # defensive: unreachable
                continue
            res, why = outcome
            slot = results[nm].setdefault((kind, res), {'n': 0, 'ex': []})
            slot['n'] += 1
            if len(slot['ex']) < samples:
                slot['ex'].append((chain, rng_n, why))
    for nm in BRIDGES:
        r = results[nm]
        ok = sum(v['n'] for (kind, res), v in r.items() if res == 'ok')
        bad = sum(v['n'] for (kind, res), v in r.items() if res == 'bad')
        skip = sum(v['n'] for (kind, res), v in r.items() if res == 'skip')
        print(f'  {nm}: ok {ok}, value mismatches {bad}, '
              f'not-expressible {skip}')
        for (kind, res), v in sorted(r.items()):
            if res == 'ok' or not v['ex']:
                continue
            ex = '; '.join(f'(chain {ch!r}, k {k}' + (f' - {w}' if w else '') + ')'
                               for ch, k, w in v['ex'])
            print(f'      {kind}/{res} n={v["n"]} e.g. {ex}')
    return results


def check_expansion_rule():
    """Structural unit tests of the verbatim rule itself."""
    print('the verbatim rule: structural checks')
    bad = 0
    S, kind = prss_expand([0, 2, 0], 5)
    if S != [0, 2] or kind != 'pred':
        bad += 1
        print(f'  FAIL successor: {S} {kind}')
    S, kind = prss_expand([0, 3], 2)
    # c=3, r=0 (the sentinel), new=[0,2], B=[2], copies 2 -> [0,2,2,2]
    if S != [0, 2, 2, 2] or kind != 'fs':
        bad += 1
        print(f'  FAIL limit: {S} {kind}')
    S, kind = prss_expand([0, 1, 3], 1)
    # c=3, r = index 1 (value 1), new=[0,1,2], B=[2] -> [0,1,2,2]
    if S != [0, 1, 2, 2] or kind != 'fs':
        bad += 1
        print(f'  FAIL segment: {S} {kind}')
    print('  ' + ('OK' if bad == 0 else 'FAILURES'))
    return bad == 0


def main():
    print('PrSS / Address Notation, checked against the eps_1 chains')
    print()
    ok = check_expansion_rule()
    print()
    check_bridges()
    print()
    print('reading: the verbatim rule is implemented and unit-tested; the')
    print('bridge table is the mechanical orientation search the plan')
    print('prescribes. The recorded result is NEGATIVE on the covered class')
    print('(0 matches for every bridge): the Address-Notation decoding')
    print('needs Racheline\'s own correspondence, which the corpus does not')
    print('carry (a member asked for it in Nov 2024 and the request is')
    print('recorded as unanswered).  The example shapes printed above are')
    print('what the next decoding candidate must explain.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
