"""Measure the phase ledger of the retargeted residual.

The ledger charge of a phase starting at (a0, c0) is

    lLen a0 c0 = the largest n with 2*c0*3^n <= 2^n*(a0 + 2*c0)      (L region)
    jLen a0 c0 = the largest m with 3^m*(a0+1) <= a0 + 2*c0 + 4*m     (J region)

i.e. the sharp per-phase length bound read off the phase's own start (the Lean/Rocq
definitions lLen/jLen).  The ledger of a run is the sum of those charges over the run's
phases, and PhaseLedger asserts it is <= 10000 for every post-j family state.
"""
import sys

from _cyc import step


def lLen(a0, c0):
    """Largest admissible L length at (a0, c0)."""
    q = a0 + 2 * c0
    n = 0
    while 2 * c0 * 3 ** (n + 1) <= 2 ** (n + 1) * q:
        n += 1
        if n > 4000:
            break
    return n


def jLen(a0, c0):
    """Largest admissible j length at (a0, c0), at least 1."""
    m = 1
    while 3 ** (m + 1) * (a0 + 1) <= a0 + 2 * c0 + 4 * (m + 1):
        m += 1
        if m > 4000:
            break
    return m


def ledger(a, c, cap=40000):
    """Return (steps, ledger_sum, phase_records, why)."""
    c0 = c
    t = 0
    total = 0
    phases = []
    cur = None
    while t < cap:
        reg = 'J' if a <= c else 'L'
        if reg != cur:
            cur = reg
            q = lLen(a, c) if reg == 'L' else jLen(a, c)
            total += q
            phases.append((reg, a, c, q))
        nx = step(a, c)
        if nx is None:
            return t + 1, total, phases, 'halt'
        a, c = nx
        t += 1
        if a == 1:
            return t, total, phases, 'a1'
        if 2 * c <= c0:
            return t, total, phases, 'c-halved'
    return t, total, phases, 'cap'


def main():
    worst = None
    count = 0
    # exhaustive over the family for k <= 8
    for k in range(0, 9):
        m = 2 * 3 ** k - 1
        for c in range(1, 2 * 3 ** k):
            t, tot, ph, why = ledger(m, c)
            count += 1
            if worst is None or tot > worst[0]:
                worst = (tot, k, c, t, why, ph)
    print('exhaustive k<=8: %d runs, max ledger %d at k=%d c=%d (T=%d, %s, %d phases)'
          % (count, worst[0], worst[1], worst[2], worst[3], worst[4], len(worst[5])))

    # the certified extremal trace and other large-k samples
    samples = [(289, 2047), (292, 471656), (292, 3583), (292, 65535),
               (280, 8191), (240, 2047), (200, 2047), (160, 2047), (120, 2047)]
    import random
    random.seed(12345)
    for k in [10, 40, 80, 120, 160, 200, 240, 280, 292]:
        for _ in range(30):
            samples.append((k, random.randrange(1, 2 * 3 ** k)))
    for k, c in samples:
        if not (1 <= c < 2 * 3 ** k):
            continue
        t, tot, ph, why = ledger(2 * 3 ** k - 1, c)
        count += 1
        if worst is None or tot > worst[0]:
            worst = (tot, k, c, t, why, ph)
    print('with large-k samples: %d runs, max ledger %d at k=%d c=%d (T=%d, %s, %d phases)'
          % (count, worst[0], worst[1], worst[2], worst[3], worst[4], len(worst[5])))

    t, tot, ph, why = ledger(2 * 3 ** 289 - 1, 2047)
    print('record trace k=289 c=2047: T=%d ledger=%d phases=%d (%s)' % (t, tot, len(ph), why))
    print('  per-phase charges:', [p[3] for p in ph])
    t, tot, ph, why = ledger(2 * 3 ** 7 - 1, 24)
    print('witness k=7 c=24: T=%d ledger=%d phases=%d (%s)' % (t, tot, len(ph), why))
    print('  per-phase charges:', [p[3] for p in ph])


if __name__ == '__main__':
    main()
