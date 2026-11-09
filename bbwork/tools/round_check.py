"""Numerical check of the copy-loop round lemma stated in rocq/StackPass.v.

The round statement (what the Coq proof still owes):

    run tbl (2*s + 2*d + 9) (loop_inv (S s) d (bl :: L) R)
      = Some (loop_inv s (S d) L (on :: R))          for s >= 1

Reading: one iteration takes one mark from the source (s -> s-1), appends one
mark to the destination (d -> d+1), eats one blank from the left context
(bl :: L -> L) and pushes one mark onto the right tail (R -> on :: R).

This script does not prove the lemma; it checks the literal statement against
the real 250-state table of machines/machine_5_stack.txt over a grid of
(s, d) and several contexts L, R, so that the Coq proof has the right goal.

Run: python tools/round_check.py
"""
import sys
sys.path.insert(0, 'tools')
import tm

BL, ON = 0, 1
m = tm.load('machines/machine_5_stack.txt')


def loop_inv(s, d, L, R):
    """rocq/StackPass.v: loop_inv s d L R"""
    return (202, [ON] * s + [BL, BL] + [ON] * d + list(L), ON, [BL] + list(R))


def cells(st, l, cur, r):
    t = {}
    for i, x in enumerate(l):
        t[-1 - i] = x
    t[0] = cur
    for i, x in enumerate(r):
        t[1 + i] = x
    return t


def run(st, l, cur, r, k):
    tape = cells(st, l, cur, r)
    head = 0
    for _ in range(k):
        res = m.step(tape, head, st)
        if res is None:
            return None
        head, st = res
    out = {i - head: v for i, v in tape.items() if v}
    return st, out


def normalise(st, l, cur, r):
    d = cells(st, l, cur, r)
    return st, {i: v for i, v in d.items() if v}


CONTEXTS = [([0, 0, 0, 0], []),
            ([0, 0, 0, 1, 0], [1]),
            ([0, 1, 0, 0], [1, 1, 0]),
            ([0, 0, 0, 0, 1, 1, 0], [1, 0, 1])]


def main():
    ok = bad = 0
    for s in range(1, 7):
        for d in range(0, 6):
            for L, R in CONTEXTS:
                st, l, cur, r = loop_inv(s + 1, d, [BL] + L, R)
                k = 2 * (s + 1) + 2 * d + 9
                got = run(st, l, cur, r, k)
                want = normalise(*loop_inv(s, d + 1, L, [ON] + R))
                if got == want:
                    ok += 1
                else:
                    bad += 1
                    if bad <= 3:
                        print(f'  MISMATCH s={s} d={d} L={L} R={R}: got={got} want={want}')
    print(f'round lemma (s >= 1, 0 <= d <= 5, 4 contexts): {ok} pass, {bad} fail')

    # composition: c rounds from loop_inv (c+s) d, total c*(2*(s+d)+9) steps
    print('composition check (per-round cost is constant in s+d):')
    for c in range(1, 6):
        s, d = c, 0
        st, l, cur, r = loop_inv(s, d, [BL] * c, [])
        total = 0
        good = True
        for i in range(c):
            step_cost = 2 * (s - i) + 2 * (d + i) + 9
            total += step_cost
            st, l, cur, r = loop_inv(s - i - 1, d + i + 1, [BL] * (c - i - 1), [ON] * (i + 1))
        after = run(*loop_inv(s, d, [BL] * c, []), total)
        want = normalise(st, l, cur, r)
        print(f'  c={c}: total {total} == c*(2c+9)={c*(2*c+9)}: {total == c*(2*c+9)}, '
              f'reaches s=0,d={d+c}: {after == want}')
        good = good and after == want
    print('exit check: from loop_inv 0 d L R the head reaches state 208 on a blank (exit), '
          'not another loop head')
    st, l, cur, r = loop_inv(0, 2, [BL, BL, BL], [])
    tape = cells(st, l, cur, r)
    head, state = 0, 202
    for n in range(1, 60):
        res = m.step(tape, head, state)
        if res is None:
            print(f'  halted after {n} steps')
            break
        head, state = res
        if state == 208 and tape.get(head, BL) == BL:
            print(f'  exit reached after {n} steps, state 208 on a blank -- PASS')
            break
    else:
        print('  no exit found -- CHECK')


if __name__ == '__main__':
    main()


def exit_checks():
    """After the last round the source is empty and state 208 (E7) sits on a
    blank: 208 bl -> 209 (E8), 209 bl -> 210 (E9), 210 walks RIGHT over marks,
    210 bl -> 211 (E10), 211 bl -> 220 (D0), and 220 bl -> bl,R,220 walks right
    over blanks until it meets the stack.  So the exit is not a closed loop: it
    is conditioned by what is to the right."""
    # end-of-pass invariant produced by pass_run: R = ones c ++ bl :: rest
    c, k = 2, 3
    R = [ON] * c + [BL] + []
    st, l, cur, r = loop_inv(0, c, [BL] * k, R)
    tape = cells(st, l, cur, r)
    head, state, n = 0, st, 0
    e9_marks = None
    while n < 200:
        res = m.step(tape, head, state)
        if res is None:
            print('  unexpected halt')
            return
        head, state = res
        n += 1
        if state == 210:          # E9: count how many marks it crosses
            e9_marks = (e9_marks or 0) + (1 if tape.get(head, BL) == ON else 0)
        if state == 220:
            break
    print(f'  reached D0 (220) after {n} steps; E9 swept {e9_marks} marks '
          f'(sweep length depends on the whole layout, so there is no one-line '
          f'formula in c)')

    # D0 with no stack: walks right over blanks without end
    start_head = head
    for _ in range(200):
        res = m.step(tape, head, state)
        if res is None:
            print('  D0 halted unexpectedly')
            return
        head, state = res
    print(f'  no stack: after 200 more steps still state {state}, head +{head - start_head} '
          f'-- {"PASS (diverges over blank tape)" if state == 220 and head - start_head == 200 else "CHECK"}')

    # D0 with a stack after a gap of g blanks: it stops at the stack's first mark
    for g in (1, 3, 6):
        R = [ON] * c + [BL] * (1 + g) + [ON] * 3 + [BL] * 2
        st, l, cur, r = loop_inv(0, c, [BL] * k, R)
        tape = cells(st, l, cur, r)
        head, state, n = 0, st, 0
        while n < 400:
            res = m.step(tape, head, state)
            if res is None:
                break
            head, state = res
            n += 1
            if state >= 221:
                break
        print(f'  gap g={g}: D0 hands over to {state} after {n} steps '
              f'({"PASS" if state == 221 else "CHECK"})')


def exit_cost_checks():
    """From loop_inv 0 d (source exhausted) with a blank left context the exit
    costs 4d + 26 steps: the machine runs a CARRY loop (202/203/204 lengthen the
    left mark run, 205..208 test it) before E8 lands on a blank and E9 sweeps."""
    ok = True
    for d in range(5):
        st, l, cur, r = loop_inv(0, d, [BL] * 2, [BL])
        tape = cells(st, l, cur, r)
        head, state, n = 0, st, 0
        while n < 400 and state != 220:
            res = m.step(tape, head, state)
            if res is None:
                break
            head, state = res
            n += 1
        good = state == 220 and n == 4 * d + 26
        ok = ok and good
        print(f'  exit from loop_inv 0 {d}: {n} steps to D0 '
              f'(4d+26={4 * d + 26}) -- {"PASS" if good else "FAIL"}')
    return ok


if __name__ == '__main__':
    exit_checks()
    exit_cost_checks()


def _tape_of(L, c, R):
    tape = {}
    for i, v in enumerate(L):
        tape[-1 - i] = v
    tape[0] = c
    for i, v in enumerate(R):
        tape[1 + i] = v
    return tape


def _enc(tape, head, span=24):
    f = lambda i: '1' if tape.get(i, BL) == ON else '0'
    return (''.join(f(head - 1 - i) for i in range(span)),
            f(head), ''.join(f(head + 1 + i) for i in range(span)))


def _enc_conf(L, c, R, span=24):
    f = lambda xs: ''.join('1' if v == ON else '0' for v in xs) + '0' * span
    return (f(L)[:span], '1' if c == ON else '0', f(R)[:span])


def sweep_checks():
    """walk_E9 and exit_sweep, checked with the same table Coq uses."""
    ok = True
    for n in range(5):
        for L in ([], [BL, BL], [ON, ON, BL]):
            for R in ([BL, BL, BL], [ON, BL, ON, BL]):
                st = 210
                start = _tape_of(L, ON, [ON] * n + [BL, BL] + R)
                tape, head = dict(start), 0
                # walk_E9: S n steps
                for _ in range(n + 1):
                    head, st = m.step(tape, head, st)
                got = _enc(tape, head)
                # start right = ones n ++ bl :: (bl :: R), so the sweep ends
                # with right = bl :: R (the first blank is the block's terminator)
                want = _enc_conf([ON] * (n + 1) + L, BL, [BL] + R)
                good = st == 210 and got == want
                # exit_sweep: S n + 2 steps in total
                tape, head, st = dict(start), 0, 210
                for _ in range(n + 3):
                    head, st = m.step(tape, head, st)
                got2 = _enc(tape, head)
                want2 = _enc_conf([BL, BL] + [ON] * (n + 1) + L,
                                  R[0] if R else BL, R[1:])
                good2 = st == 220 and got2 == want2
                ok = ok and good and good2
                if not (good and good2):
                    print(f'  n={n} L={L} R={R}: walk_E9 {good}, exit_sweep {good2}')
                    print('    got ', got, got2)
                    print('    want', want, want2)
    print(f'  walk_E9 / exit_sweep over n<=4 and 6 contexts: '
          f'{"PASS" if ok else "FAIL"}')
    return ok


if __name__ == '__main__':
    exit_checks()
    exit_cost_checks()
    sweep_checks()


def carry_front_checks():
    """carry_front: E1 on a blank with m+1 settled marks -> E4 with m+2 marks,
    in 2m+5 steps.  (The loop variable is [k]; [m] is the machine.)"""
    ok = True
    for k in range(4):
        for Z0 in ([], [BL, BL], [ON, BL]):
            for R in ([BL, BL, BL], [ON, ON, BL]):
                L = [BL] + [ON] * (k + 1) + [BL] + Z0
                tape = _tape_of(L, BL, R)
                head, st = 0, 202
                for _ in range(2 * k + 5):
                    head, st = m.step(tape, head, st)
                got = _enc(tape, head)
                want = _enc_conf([ON] * (k + 2) + Z0, BL, [BL] + R)
                good = st == 205 and got == want
                ok = ok and good
                if not good:
                    print(f'  k={k} Z0={Z0} R={R}:')
                    print('    got ', st, got)
                    print('    want 205', want)
    print(f'  carry_front over k<=3 and 6 contexts: {"PASS" if ok else "FAIL"}')
    return ok


if __name__ == '__main__':
    carry_front_checks()


def carry_exit_checks():
    """carry_exit: loop head -> E9 on the grown block, in 2m+10 steps."""
    ok = True
    for k in range(4):
        for Z0 in ([], [BL, BL], [ON, BL]):
            for R1 in ([BL, BL, BL], [ON, ON, BL]):
                L = [BL] + [ON] * (k + 1) + [BL] + Z0
                tape = _tape_of(L, BL, [BL, BL] + R1)
                head, st = 0, 202
                for _ in range(2 * k + 10):
                    head, st = m.step(tape, head, st)
                got = _enc(tape, head)
                want = _enc_conf([ON] * (k + 1) + Z0, ON, [ON, ON, ON, BL] + R1)
                good = st == 210 and got == want
                ok = ok and good
                if not good:
                    print(f'  k={k} Z0={Z0} R1={R1}:')
                    print('    got ', st, got)
                    print('    want 210', want)
    print(f'  carry_exit over k<=3 and 6 contexts: {"PASS" if ok else "FAIL"}')
    return ok


if __name__ == '__main__':
    carry_exit_checks()


def exit_run_checks():
    """exit_run: loop head -> D0 in 2m+16 steps."""
    ok = True
    for k in range(4):
        for Z0 in ([], [BL, BL], [ON, BL]):
            for R in ([BL, BL, BL], [ON, BL, ON]):
                L = [BL] + [ON] * (k + 1) + [BL] + Z0
                tape = _tape_of(L, BL, [BL, BL, BL] + R)
                head, st = 0, 202
                for _ in range(2 * k + 16):
                    head, st = m.step(tape, head, st)
                got = _enc(tape, head)
                want = _enc_conf([BL, BL] + [ON] * 4 + [ON] * k + [ON] + Z0,
                                 R[0] if R else BL, R[1:])
                good = st == 220 and got == want
                ok = ok and good
                if not good:
                    print(f'  k={k} Z0={Z0} R={R}:')
                    print('    got ', st, got)
                    print('    want 220', want)
    print(f'  exit_run over k<=3 and 6 contexts: {"PASS" if ok else "FAIL"}')
    return ok


if __name__ == '__main__':
    exit_run_checks()
