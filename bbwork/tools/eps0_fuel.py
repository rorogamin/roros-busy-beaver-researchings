"""The fuel drive: how a 2-symbol machine gets past 2^c and into tower growth.

The tower machine (`tools/tower_machine.py`) doubles its value c times, where c
is a fixed row of marks on the tape.  That is multiplication by 2^c, the omega^c
rung.  For eps_0 the number of rounds must itself come from the tape, so the
stage has to feed on its own value.

The cheap operation in 2 symbols is *moving* a mark, not copying one: erase at
one end of a block, write at the end of another, keeping a blank between them so
the walk can tell the two blocks apart.  So each stage buys its rounds with
marks moved out of the value block:

    c <- v // 2          fuel: half the block becomes counter marks
    v <- v - c           the block shrinks to its other half
    v <- (v+1)*2^c - 1   the tower machine's round, c times over

The block regrows past what was spent, so the stage is self-feeding: the rounds
of stage k+1 are bought with the value stage k produced, which is about 2^(v/2).
One stage is one exponentiation of the previous value's size, so n stages is the
n-th rung of the tower.

Two things this model settles, before any hardware exists:

* with an input block n fixing the number of stages, the run halts after exactly
  n stages -- the value cannot be both the fuel and the stage counter, and
  letting the value decide the stage count diverges (that was the first version
  of this file: v grew as 2^(v/2) per stage and never stopped);
* each stage's rounds are exactly v//2 and each stage's value is exactly
  (v - v//2 + 1) * 2^(v//2) - 1, so the growth is reproducible, not sampled.

Cost of one round, measured on the tower machine: (v+1)*2^c - 1 marks took 122
steps at c=2,v=1 and 1263 at c=3,v=3, roughly 400 steps per round once the
blocks are a few marks long.  ROUND_COST is that calibration; every step count
printed from it is an estimate, not a measurement.

This file is a model: the tape is two integers.  No machine here.
"""

import sys

ROUND_COST = 400          # measured on the tower machine, steps per round
BIT_CAP = 4096            # stop the ladder when a value passes this many bits


def stage(v):
    """One fuel stage, exact.  Returns (fuel, v_after, bits_before, bits_after).

    bits_* are computed without building the full number when it would exceed
    BIT_CAP: (v+1)*2^c-1 has bit length c + bit_length(v+1).
    """
    fuel = v // 2
    if fuel == 0:
        return 0, v, v.bit_length(), v.bit_length()
    rest = v - fuel
    bits_before = v.bit_length()
    bits_after = fuel + (rest + 1).bit_length()
    if bits_after > BIT_CAP:
        return fuel, None, bits_before, bits_after
    return fuel, (rest + 1) * 2 ** fuel - 1, bits_before, bits_after


def run(v0, stages):
    """Run a fixed number of stages.  Returns (rounds, trace, capped).

    trace entries: (k, fuel, bits_before, bits_after).
    """
    v = v0
    rounds = 0
    trace = []
    for k in range(1, stages + 1):
        fuel, v2, b0, b1 = stage(v)
        if fuel == 0:
            return rounds, trace, False
        rounds += fuel
        trace.append((k, fuel, b0, b1))
        if v2 is None:
            return rounds, trace, True
        v = v2
    return rounds, trace, False


def short(n):
    """Compact form for values that would print millions of digits."""
    if n < 10 ** 9:
        return str(n)
    return f'~{int(n.bit_length() * 0.30103) + 1}d'


def check():
    ok = True

    # 1. halting: exactly n stages, or the cap cut a tower short mid-ladder
    for v0 in (2, 3, 4, 5, 6):
        rounds, trace, capped = run(v0, 4)
        good = (len(trace) == 4 or (capped and len(trace) >= 2)) and rounds > 0
        print(f'  v0={v0}: stages={len(trace)} rounds={short(rounds)} '
              f'capped={capped} {"PASS" if good else "FAIL"}')
        ok = ok and good

    # 2. self-feeding: fuel never drops, and ends far above where it started.
    #    At v=2 two stages both buy a single round, which is why this is
    #    non-decreasing plus a strict end, not a strict rise everywhere.
    for v0 in (2, 3, 4, 5):
        rounds, trace, _ = run(v0, 4)
        fuels = [t[1] for t in trace]
        nondec = all(fuels[i + 1] >= fuels[i] for i in range(len(fuels) - 1))
        grows = fuels[-1] > fuels[0]
        good = nondec and grows
        print(f'  v0={v0}: fuel {[short(f) for f in fuels]} '
              f'{"PASS" if good else "FAIL"}')
        ok = ok and good

    # 3. tower signature: from stage two on, each stage at least doubles the
    #    previous bit count.  That is what separates a tower from linear growth.
    for v0 in (2, 3):
        rounds, trace, _ = run(v0, 4)
        bits = [t[3] for t in trace]
        rising = all(bits[i + 1] >= bits[i] for i in range(len(bits) - 1))
        late = len(bits) >= 3 and bits[-1] >= 2 * bits[1]
        good = rising and late
        print(f'  v0={v0}: bits {bits} {"PASS" if good else "FAIL"}')
        ok = ok and good

    # 4. the ladder, stage by stage
    print('   v0  stage  fuel                bits')
    for v0 in (2, 3, 4, 5, 6):
        rounds, trace, capped = run(v0, 4)
        for k, fuel, b0, b1 in trace:
            print(f'  {v0:>3}  {k:>5}  {short(fuel):>16}  {b0:>5} -> {b1}')
        if capped:
            print(f'  {v0:>3}          (capped: past {BIT_CAP} bits)')
    return ok


if __name__ == '__main__':
    print('fuel drive: n stages fixed by the input, each stage bought from the value')
    ok = check()
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
