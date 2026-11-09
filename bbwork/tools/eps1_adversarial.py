"""eps1_adversarial.py — stress the eps1_odi machine beyond the gates.

Generates adversarial but canonical (p, chain) starts well beyond the
tier set and the gate-2 generator, drives them through the machine one
campaign at a time and compares every landing (value level, C.full)
against eps1_chain.step:

  * deep unit stacks [NUM(1), NUM(1), ..., NUM(1)] of depth 1..12 — the
    pop-cascade loops longest here (the cascade pops every unit entry
    above the first non-unit, writing a park mark per pop);
  * mixed deep chains: tall reservoirs under garbage tops, alternating
    tall/short, all-3-runs, pockets of 2s and 6s;
  * park values 0..5, seeds 1..2 (all supported builds) and 3.

Whatever normalise cannot canonicalise or the model's assert corners
reject is skipped (the same policy as gate 2), but every accepted start
runs up to `moves` sequential campaigns with a strict landing compare,
which the machine must satisfy step for step.

Usage: python tools/eps1_adversarial.py [sn] [trials] [seed] [moves]
Exit 0 on ALL OK, 1 on any failure.
"""

import os
import sys
import random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import eps1_odi as O
import eps1_chain as C
from eps1_odi import build_table, step_model, C


def random_start(rng):
    """An adversarial canonical start; returns None if not canonical."""
    kind = rng.random()
    if kind < 0.40:
        # deep unit stack with a varied base entry
        k = rng.randint(1, 12)
        base = rng.choice([2, 3, 4, None])
        ch = [] if base is None else [base]
        ch += [1] * k
        if base is None:
            ch = [1] * k
    elif kind < 0.75:
        # long mixed chain
        ch = [rng.choice([1, 1, 2, 3, 3, 4, 6])
              for _ in range(rng.randint(1, 9))]
    else:
        # alternating tall / shallow entries
        ch = []
        for _ in range(rng.randint(2, 6)):
            ch.append(rng.choice([2, 5, 6, 3, 1]))
        for _ in range(rng.randint(1, 4)):
            ch.append(1)
    p = rng.randint(0, 5)
    try:
        ch = list(C.normalise(p, ch)[1])
    except Exception:
        return None
    try:
        cells, h0 = O.mk_tape(p, ch)
    except ValueError:
        return None
    return p, ch, cells, h0


def run(sn, trials, seed, moves):
    rng = random.Random(seed)
    bad = 0
    checked = skipped = 0
    for t_i in range(trials):
        st = random_start(rng)
        if st is None:
            skipped += 1
            continue
        p, ch, cells, h0 = st
        checked += 1
        for _m in range(moves):
            try:
                out = step_model(p, list(ch), sn)
            except Exception:
                break                       # the model's assert corners
            if out[0] != 'move':
                break
            cells, h0 = O.mk_tape(p, list(ch))
            k2, steps, cells2, h2 = O.campaign(cells, h0, T)
            if k2 != 'rest':
                bad += 1
                print(f'  FAIL campaign-{k2} steps={steps} at ({p}, {ch})')
                break
            try:
                dp, dc = O.decode_tape(cells2)
            except ValueError as e:
                bad += 1
                print(f'  FAIL decode ({p}, {ch}): {e}')
                break
            if C.full(dp, dc) != C.full(out[1], out[2]):
                bad += 1
                print(f'  FAIL unfaithful ({p}, {ch}): machine '
                      f'({dp}, {list(dc)}) vs model ({out[1]}, {list(out[2])})')
                break
            p, ch = out[1], list(out[2])
    print(f'sn={sn}: {checked} starts checked ({skipped} skipped), '
          + ('ALL OK' if bad == 0 else f'{bad} FAILURES'))
    return bad


if __name__ == '__main__':
    sn = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 2026
    moves = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    T, meta = build_table(sn)
    sys.exit(0 if run(sn, trials, seed, moves) == 0 else 1)
