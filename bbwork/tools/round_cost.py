"""Round-by-round accounting for the eps_0 drive, checked against closed forms.

One *round* of the drive is one stage's worth of work: it erases one counter
mark, runs module K once (which maps a value of [v] marks to [2v+1]), and
walks back to the same decision state.

This script

  * cuts the machine's trace into rounds (from one [R1] on a mark to the next),
  * measures, at each round entry, the two parameters of the shape

        R1, on, on :: zeros m ++ ones v ++ bl :: on :: []

    namely the hole run [m] and the value length [v],
  * and checks the measured round cost against

        2*m + 7*v + 14 + k_pre v 0 0

    where [k_pre] is the Fixpoint proved in rocq/ModuleK.v, transcribed below.

It is a check of the *statement* the Coq proof must establish, not a proof.

Run: python tools/round_cost.py
"""

import sys

sys.path.insert(0, 'tools')
import tm  # noqa: F401  (kept for parity with the other probes)
from eps0_machine import TABLE, NAMES, start, R1, R2, R4, R5, R6, A5, A6, A7
from eps0_machine import A8, A9, AA, K1, K2, K3, K4, K5, K6, K7

LOOP_STATES = {R1, R2, R4, R5, R6, A5, A6, A7, A8, A9, AA,
               K1, K2, K3, K4, K5, K6, K7}


# ---- k_pre, transcribed from rocq/ModuleK.v -------------------------------

def last_pre(G, d):
    if G == 0:
        return ((1 + (d + 2)) + (d + 1 + 2)) + 2
    Gp = G - 1
    return ((G + 1 + (d + 2)) + (d + 1 + 2)) + (1 + (Gp + 2))


def k_pre(x, G=0, d=0):
    if x == 0:
        return 0
    if x == 1:
        return last_pre(G, d)
    return (2 * G + 2 * d + 9) + k_pre(x - 1, G + 1, d + 2)


# ---- tape helpers ---------------------------------------------------------

def cells(tape, lo, hi):
    return [tape.get(i, 0) for i in range(lo, hi + 1)]


def rle(xs):
    if not xs:
        return '-'
    out, run, prev = [], 0, None
    for x in xs:
        if x == prev:
            run += 1
        else:
            if prev is not None:
                out.append(f'{prev}^{run}')
            prev, run = x, 1
    out.append(f'{prev}^{run}')
    return ' '.join(out)


def shape(tape, head):
    """Read the round-entry shape off the tape: (m, v) or None."""
    right = cells(tape, head + 1, head + 400)
    # the first cell right of the head must be the counter's last mark
    if right[0] != 1:
        return None
    i = 1
    m = 0
    while i < len(right) and right[i] == 0:
        m += 1
        i += 1
    v = 0
    while i < len(right) and right[i] == 1:
        v += 1
        i += 1
    tail = right[i:i + 2]
    if v == 0 or tail != [0, 1]:
        return None
    return m, v


# ---- trace and rounds -----------------------------------------------------

def trace(n, v, limit=60000):
    tape, head, state = start(n, v)
    tape = dict(tape)
    seen = []
    for _ in range(limit):
        seen.append((head, state, dict(tape)))
        k = (state, tape.get(head, 0))
        if k not in TABLE:
            return seen, True
        w, d, nxt = TABLE[k]
        tape[head] = w
        head += 1 if d == 'R' else -1
        state = nxt
    return seen, False


def rounds(n, v, limit=60000):
    seen, halted = trace(n, v, limit)
    marks = []
    for i, (head, state, tape) in enumerate(seen):
        if state == R1 and tape.get(head, 0) == 1:
            s = shape(tape, head)
            if s is not None:
                marks.append((i, head, s, tape))
    out = []
    for j in range(len(marks) - 1):
        i0, h0, s0, t0 = marks[j]
        i1, h1, s1, t1 = marks[j + 1]
        # a *pure* round never touches the stage branch or the fuel phase
        pure = all(st in LOOP_STATES for _, st, _ in seen[i0:i1])
        out.append((s0, i1 - i0, (i0, i1), pure))
    return out, halted, marks


def main():
    print('epss_0 drive: round costs vs 2*m + 7*v + 14 + k_pre v 0 0')
    print()
    bad = 0
    checked = 0
    skipped = 0
    for n in range(1, 5):
        for v0 in range(1, 3):
            rs, halted, marks = rounds(n, v0)
            for (m, v), cost, span, pure in rs:
                pred = 2 * m + 7 * v + 14 + k_pre(v)
                if not pure:
                    skipped += 1
                    continue
                checked += 1
                ok = pred == cost
                if not ok:
                    bad += 1
                print(f'  n={n} v0={v0} round@({span[0]},{span[1]}) '
                      f'm={m} v={v} cost={cost} pred={pred} '
                      f'{"ok " if ok else "BAD"}')
    print()
    print(f'pure rounds checked: {checked}, mismatches: {bad}, '
          f'rounds spanning a stage/fuel transition (not loop rounds): {skipped}')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
