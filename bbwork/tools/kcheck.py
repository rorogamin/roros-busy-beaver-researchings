"""Numerical check of rocq/ModuleK.v against the same table as eps_machine.py.

Two claims are checked, both with the *Coq* step convention: `run` does not
count the failing step that ends a halting run, so k steps means k successful
transitions and then a lookup that must fail.

  1. the round: from  ki (S s) g d  at cost 2g + 2d + 7 the configuration is
     ki s (S g) (S (S d)), where ki s g d = (K2, 1^s, blank, 0^g 1^d);
  2. the whole module: from the K1 start on 1^x 0 1, at cost 3*x*(x+2) the
     machine has halted on 0^x 0 1^(2x+1).

Nothing here is a proof; it is the independent check the proof file refers to.
"""

import sys

sys.path.insert(0, 'tools')
import tm
from eps_machine import machine

K1, K2, K3, K4, K5, K6, K7 = range(7)
NAMES = {K1: 'K1', K2: 'K2', K3: 'K3', K4: 'K4', K5: 'K5', K6: 'K6', K7: 'K7'}


def tape_of_conf(state, left, cur, right):
    """Zipper -> tape dict, head at 0.  left/right are nearest-first."""
    tape = {-(i + 1): v for i, v in enumerate(left)}
    tape[0] = cur
    tape.update({i + 1: v for i, v in enumerate(right)})
    return tape


def conf_of_tape(tape, head, state, left_width, right_width):
    left = [tape.get(head - 1 - i, 0) for i in range(left_width)]
    right = [tape.get(head + 1 + i, 0) for i in range(right_width)]
    return state, left, tape.get(head, 0), right


def ki(s, g, d):
    return (K2, [1] * s, 0, [0] * g + [1] * d)


def step_k(m, tape, head, state, k):
    """k successful steps; returns (tape, head, state, halted_on_last)."""
    for _ in range(k):
        r = m.step(tape, head, state)
        if r is None:
            return tape, head, state, True
        head, state = r
    return tape, head, state, False


def check_rounds():
    m = machine()
    ok = True
    for g in range(0, 4):
        for d in range(1, 5):
            for s in range(1, 4):
                state, left, cur, right = ki(s + 1, g, d)
                tape = tape_of_conf(state, left, cur, right)
                k = 2 * g + 2 * d + 7
                tape, head, st, halted = step_k(m, tape, 0, state, k)
                want = ki(s, g + 1, d + 2)
                wide = max(len(want[1]), len(want[3])) + 1
                got = conf_of_tape(tape, head, st, wide, wide)
                good = (not halted) and got[0] == want[0] and got[2] == want[2] \
                    and got[1][:len(want[1])] == want[1] and got[3][:len(want[3])] == want[3]
                if not good:
                    ok = False
                    print(f'  round g={g} d={d} s={s}: FAIL')
                    print(f'    got  {NAMES[got[0]]} L={got[1]} cur={got[2]} R={got[3]}')
                    print(f'    want {NAMES[want[0]]} L={want[1]} cur={want[2]} R={want[3]}')
    print(f'rounds: {"PASS" if ok else "FAIL"}  (2g+2d+7, ki(S s,g,d) -> ki(s,S g,S(S d)))')
    return ok


def check_totals():
    m = machine()
    ok = True
    for x in range(1, 8):
        state, left, cur, right = K1, [1] * (x - 1), 1, [0] + [1]
        tape = tape_of_conf(state, left, cur, right)
        k = 3 * x * (x + 2)
        tape, head, st, halted = step_k(m, tape, 0, state, k)
        if halted:
            ok = False
            print(f'  x={x}: halted early (before {k} steps)')
            continue
        nxt = m.step(tape, head, st)
        marks = sorted(i for i, v in tape.items() if v == 1)
        want = list(range(2, 2 * x + 3))  # seed at +1, destination ends at 2x+2
        good = nxt is None and marks == want and tape.get(head, 0) == 0
        ok = ok and good
        if not good:
            print(f'  x={x}: steps={k} next={nxt} marks={marks} want={want}')
    print(f'totals: {"PASS" if ok else "FAIL"}  (3x(x+2) steps, then a failing lookup)')
    return ok


if __name__ == '__main__':
    a = check_rounds()
    b = check_totals()
    print('ALL OK' if a and b else 'FAILURES')
    sys.exit(0 if a and b else 1)
