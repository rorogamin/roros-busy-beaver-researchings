#!/usr/bin/env python3
"""Three-left/three-right abstract reachability for machine 14's 2025 block model.

The abstraction is an over-approximation: when a rule needs a token beyond the
stored window, every possible token is enumerated and the corresponding "more"
flag is kept.  If the forward reachable set is closed and contains no `> R`,
that is a block-level nonhalting certificate (not yet a raw-machine proof).
"""
from collections import deque
import machine14_block_rules as blocks

LTOK = ['L', 'U', 'W', 'F', 'Y', 'Q']
RTOK = ['R', 'X', 'V', 'C', 'C1', 'C2', 'P']


def norm_left(L, more):
    L = list(L)
    return tuple(L[:4]), more or len(L) > 3


def norm_right(R, more):
    R = list(R)
    return tuple(R[:4]), more or len(R) > 3


def succ(a):
    head, L, Lm, R, Rm = a
    L = list(L)
    R = list(R)
    out = set()

    def emit(nh, nL, nLm, nR, nRm):
        nL, nLm = norm_left(nL, nLm)
        nR, nRm = norm_right(nR, nRm)
        out.add((nh, nL, nLm, nR, nRm))

    if head == '<':
        if not L:
            return out
        x = L[0]

        def tail():
            if len(L) > 1:
                return L[1:], Lm
            if Lm:
                return None, True
            return [], False

        t, tm = tail()
        if x == 'W':
            if t is None:
                for y in LTOK:
                    emit('<', [y], True, ['V'] + R, Rm)
            else:
                emit('<', t, tm, ['V'] + R, Rm)
        elif x == 'U':
            if t is None:
                for y in LTOK:
                    emit('>', ['W', y], True, R, Rm)
            else:
                emit('>', ['W'] + t, tm, R, Rm)
        elif x == 'L':
            emit('w>', L, Lm, R, Rm)
        elif x == 'Y':
            if t is None:
                for y in LTOK:
                    emit('<', [y], True, ['X'] + R, Rm)
            else:
                emit('<', t, tm, ['X'] + R, Rm)
        elif x == 'F':
            if t is None:
                for y in LTOK:
                    emit('<', [y], True, ['C'] + R, Rm)
            else:
                emit('<', t, tm, ['C'] + R, Rm)
        elif x == 'Q':
            if t is None:
                for y in LTOK:
                    emit('<', [y], True, ['P'] + R, Rm)
            else:
                emit('<', t, tm, ['P'] + R, Rm)
        return out

    if not R:
        return out
    x = R[0]

    def rtail():
        if len(R) > 1:
            return R[1:], Rm
        if Rm:
            return None, True
        return [], False

    t, rm = rtail()
    if head == '>':
        if x == 'V':
            if t is None:
                for y in RTOK:
                    emit('>', ['U'] + L, Lm, [y], True)
            else:
                emit('>', ['U'] + L, Lm, t, rm)
        elif x == 'X':
            emit('<', L, Lm, ['C1', 'P'] + (t if t is not None else []),
                 rm if t is not None else True)
            if t is None:
                for y in RTOK:
                    emit('<', L, Lm, ['C1', 'P', y], True)
        elif x == 'C':
            if t is None:
                for y in RTOK:
                    emit('<', L, Lm, ['C1', y], True)
            else:
                emit('<', L, Lm, ['C1'] + t, rm)
        elif x == 'C1':
            if t is None:
                for y in RTOK:
                    emit('<', L, Lm, ['C2', y], True)
            else:
                emit('<', L, Lm, ['C2'] + t, rm)
        elif x == 'C2':
            if t is None:
                for y in RTOK:
                    emit('>', ['F'] + L, Lm, [y], True)
            else:
                emit('>', ['F'] + L, Lm, t, rm)
        elif x == 'P':
            if t is None:
                for y in RTOK:
                    emit('w>', L, Lm, [y], True)
            else:
                emit('w>', L, Lm, t, rm)
        return out

    if head == 'w>':
        if x == 'V':
            if t is None:
                for y in RTOK:
                    emit('w>', ['U'] + L, Lm, [y], True)
            else:
                emit('w>', ['U'] + L, Lm, t, rm)
        elif x == 'X':
            if t is None:
                for y in RTOK:
                    emit('w>', ['Y'] + L, Lm, [y], True)
            else:
                emit('w>', ['Y'] + L, Lm, t, rm)
        elif x == 'R':
            if t is None:
                emit('<', L, Lm, ['X', 'R'], False)
            else:
                emit('<', L, Lm, ['X', 'R'] + t, rm)
        elif x == 'C':
            if t is None:
                for y in RTOK:
                    emit('>', ['Q', 'F'] + L, Lm, [y], True)
            else:
                emit('>', ['Q', 'F'] + L, Lm, t, rm)
        elif x == 'C1':
            if t is None:
                for y in RTOK:
                    emit('>', ['Q', 'U'] + L, Lm, [y], True)
            else:
                emit('>', ['Q', 'U'] + L, Lm, t, rm)
        elif x == 'C2':
            if t is None:
                for y in RTOK:
                    emit('w>', ['W'] + L, Lm, [y], True)
            else:
                emit('w>', ['W'] + L, Lm, t, rm)
        elif x == 'P':
            if t is None:
                for y in RTOK:
                    emit('>', ['U'] + L, Lm, [y], True)
            else:
                emit('>', ['U'] + L, Lm, t, rm)
        return out
    return out


def abstract(tokens, h, head):
    L = tokens[:h][::-1] if head == '<' else tokens[:h][::-1]
    R = tokens[h:]
    return (head, *norm_left(L, False), *norm_right(R, False))


def main():
    init = ('<', ('Q', 'U', 'L'), False, ('R',), False)
    seen = {init}
    q = deque([init])
    bad = []
    while q:
        a = q.popleft()
        head, L, Lm, R, Rm = a
        if head == '>' and R and R[0] == 'R':
            bad.append(a)
            break
        for b in succ(a):
            if b not in seen:
                seen.add(b)
                q.append(b)
    print('abstract states', len(seen), 'bad', len(bad))
    for a in sorted(seen, key=str):
        print(a)

    # Check the abstraction against the concrete 1e6-step block run.
    tokens = ['L', 'U', 'Q', 'R']
    h, head = 3, '<'
    actual_bad = 0
    missing = 0
    for i in range(1_000_000):
        a = abstract(tokens, h, head)
        if a not in seen:
            missing += 1
            if missing <= 5:
                print('MISSING', i, a, tokens[:h], tokens[h:])
        if head == '>' and h < len(tokens) and tokens[h] == 'R':
            actual_bad += 1
        r = blocks.step(tokens, h, head)
        if r is None:
            print('CONCRETE STUCK', i, head, tokens[:h], '|', tokens[h:])
            break
        tokens, h, head = r
    print('actual_bad', actual_bad, 'missing', missing)


if __name__ == '__main__':
    main()
