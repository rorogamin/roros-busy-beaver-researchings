"""Design harness for the 'core' doubling machine.

Tape layout for the core:
        0^inf  [C]  0  [U]  0  [W]  0^inf
with the head starting on the leftmost cell of C.

One 'pass' consumes one cell of C and consumes all of U while appending two
cells to W (seeding W with two cells when it is empty).  Passes repeat until C
is exhausted; the final tape is 0^inf [W] 0^inf, so the score is |W|.

Invariants relied upon:
  * the U-W gap is exactly one zero;
  * C is consumed from its left end (so the C-U gap may grow);
  * U is consumed from its left end;  W grows at its right end.
"""

A, T = 0, 1            # erase leftmost of U ; then test the next cell
F0, F1, F2 = 2, 3, 4   # cross zeros ; cross U's ones ; cross W's ones
G1, G2 = 5, 6          # write two cells at W's right end
R1, R2 = 7, 8          # walk back over W, step over the 1-zero gap, test
R3 = 9                 # walk left over U's ones
R4, R5 = 10, 11        # (pass end) walk left over zeros, then over C's ones
A2, T2 = 12, 13        # erase leftmost of C ; test (halt when C empty)
N0, N1 = 14, 15        # walk right over C's ones, then over zeros up to U

TBL = {}

TBL[(A, 1)] = (0, 'R', T)
TBL[(T, 1)] = (1, 'R', F1)
TBL[(T, 0)] = (0, 'R', F0)
TBL[(F0, 0)] = (0, 'R', F0)
TBL[(F0, 1)] = (1, 'R', F2)
TBL[(F1, 1)] = (1, 'R', F1)
TBL[(F1, 0)] = (0, 'R', F2)
TBL[(F2, 1)] = (1, 'R', F2)
TBL[(F2, 0)] = (1, 'R', G1)
TBL[(G1, 0)] = (1, 'L', R1)
TBL[(R1, 1)] = (1, 'L', R1)
TBL[(R1, 0)] = (0, 'L', R2)
TBL[(R2, 1)] = (1, 'L', R3)
TBL[(R2, 0)] = (0, 'L', R4)
TBL[(R3, 1)] = (1, 'L', R3)
TBL[(R3, 0)] = (0, 'R', A)
TBL[(R4, 0)] = (0, 'L', R4)
TBL[(R4, 1)] = (1, 'L', R5)
TBL[(R5, 1)] = (1, 'L', R5)
TBL[(R5, 0)] = (0, 'R', A2)
TBL[(A2, 1)] = (0, 'R', T2)
TBL[(T2, 1)] = (1, 'R', N0)
# (T2, 0) undefined -> halt
TBL[(N0, 1)] = (1, 'R', N0)
TBL[(N0, 0)] = (0, 'R', N1)
TBL[(N1, 0)] = (0, 'R', N1)
TBL[(N1, 1)] = (0, 'R', T)


def wire():
    t = {}
    for k, v in TBL.items():
        t[k] = v
    return t


if __name__ == '__main__':
    import tm
    m = tm.TM(N1 + 1, wire())
    ok = True
    for c in (1, 2, 3, 4, 5):
        for u in (2, 3, 4, 7):
            for w in (1, 2, 5):
                # layout: C at 0..c-1, gap at c, U at c+1..c+u, gap, W
                tape = {}
                for i in range(c):
                    tape[i] = 1
                for i in range(u):
                    tape[c + 1 + i] = 1
                wstart = c + 1 + u + 1
                for i in range(w):
                    tape[wstart + i] = 1
                steps, tp, head, st, halted = m.run(head=0, state=A, tape=tape)
                score = m.score(tp)
                pred = 2 ** (c - 1) * (2 * u + w + 2) - 2
                status = 'OK' if (halted and score == pred) else 'FAIL'
                if status == 'FAIL':
                    ok = False
                print(f'c={c} u={u} w={w} -> halted={halted} score={score} pred={pred} steps={steps} {status}')
    print('ALL OK' if ok else 'SOME FAILED')
