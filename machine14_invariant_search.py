#!/usr/bin/env python3
"""Search finite right-context invariants for machine 14's block model.

The abstraction keeps the head, the left-head token (or ?), and the first two
right tokens plus a `more` flag.  It is an over-approximation: transitions from
an unknown left-head branch over all left tokens.  A state is bad when the head
is `>` and the first right token is `R`.  We compute the backward-reachable bad
set; any state outside it is a candidate inductive invariant.
"""
from __future__ import annotations

from collections import deque

HEADS = ["<", ">", "w>"]
LTOK = ["L", "U", "W", "F", "Y", "Q"]
RTOK = ["R", "X", "V", "C", "C1", "C2", "P"]
LH = [None] + LTOK


def abstract(tokens, h, head):
    left = tokens[h - 1] if head == "<" and h > 0 else None
    right = tokens[h:] if head != "<" else tokens[h:]
    r0 = right[0] if len(right) > 0 else None
    r1 = right[1] if len(right) > 1 else None
    more = len(right) > 2
    return (head, left, r0, r1, more)


def concretize(a):
    head, lh, r0, r1, more = a
    left = [lh] if lh is not None else []
    right = []
    if r0 is not None:
        right.append(r0)
    if r1 is not None:
        right.append(r1)
    if more:
        right.append("R")
    return left, right


# Manual abstract transition relation.  It mirrors the 19 block rules and
# branches on every possible left token when the left head is unknown.
def succ(a):
    head, lh, r0, r1, more = a
    out = set()

    def emit(nh, nlh, right):
        nr0 = right[0] if len(right) > 0 else None
        nr1 = right[1] if len(right) > 1 else None
        nmore = len(right) > 2
        out.add((nh, nlh, nr0, nr1, nmore))

    lefts = [lh] if lh is not None else LTOK
    if head == "<":
        for x in lefts:
            if x == "W":
                emit("<", None, [("V")] + ([r0] if r0 else []) + ([r1] if r1 else []) + (["R"] if more else []))
            elif x == "U":
                emit(">", "W", [r0] if r0 else [])
            elif x == "L":
                emit("w>", "L", [r0] if r0 else [])
            elif x == "Y":
                emit("<", None, ["X"] + ([r0] if r0 else []) + ([r1] if r1 else []) + (["R"] if more else []))
            elif x == "F":
                emit("<", None, ["C"] + ([r0] if r0 else []) + ([r1] if r1 else []) + (["R"] if more else []))
            elif x == "Q":
                emit("<", None, ["P"] + ([r0] if r0 else []) + ([r1] if r1 else []) + (["R"] if more else []))
        return out

    right = []
    if r0 is not None:
        right.append(r0)
    if r1 is not None:
        right.append(r1)
    if more:
        right.append("R")
    if not right:
        return out
    x = right[0]
    rest = right[1:]
    if head == ">":
        if x == "V":
            emit(">", "U", rest)
        elif x == "X":
            emit("<", lh, ["C1", "P"] + rest)
        elif x == "C":
            emit("<", lh, ["C1"] + rest)
        elif x == "C1":
            emit("<", lh, ["C2"] + rest)
        elif x == "C2":
            emit(">", "F", rest)
        elif x == "P":
            emit("w>", lh, rest)
    else:  # w>
        if x == "V":
            emit("w>", "U", rest)
        elif x == "X":
            emit("w>", "Y", rest)
        elif x == "R":
            emit("<", lh, ["X", "R"] + rest)
        elif x == "C":
            emit(">", "Q", rest)
        elif x == "C1":
            emit(">", "Q", rest)
        elif x == "C2":
            emit("w>", "W", rest)
        elif x == "P":
            emit(">", "U", rest)
    return out


def all_states():
    states = []
    for head in HEADS:
        for lh in LH:
            if head == "<" and lh is None:
                continue
            for r0 in [None] + RTOK:
                for r1 in ([None] + RTOK) if r0 is not None else [None]:
                    for more in [False, True] if r1 is not None else [False]:
                        states.append((head, lh, r0, r1, more))
    return states


def is_bad(a):
    return a[0] == ">" and a[2] == "R"


def main():
    states = all_states()
    pred = {a: [] for a in states}
    for a in states:
        for b in succ(a):
            if b in pred:
                pred[b].append(a)
    bad = [a for a in states if is_bad(a)]
    seen = set(bad)
    q = deque(bad)
    while q:
        b = q.popleft()
        for a in pred[b]:
            if a not in seen:
                seen.add(a)
                q.append(a)
    safe = [a for a in states if a not in seen]
    print(f"states={len(states)} bad_seed={len(bad)} backward_bad={len(seen)} safe={len(safe)}")
    print("bad states by head:")
    for head in HEADS:
        xs = [a for a in seen if a[0] == head]
        print(f"  {head}: {len(xs)}")
    print("sample bad:")
    for a in sorted(seen, key=str)[:30]:
        print(" ", a)
    print("sample safe:")
    for a in sorted(safe, key=str)[:15]:
        print(" ", a)
    # Check the actual 1e6 run never leaves safe.
    import machine14_block_rules as b
    tokens = ["L", "U", "Q", "R"]
    h, head = 3, "<"
    bad_actual = 0
    for i in range(1_000_000):
        a = abstract(tokens, h, head)
        if a in seen:
            bad_actual += 1
            if bad_actual <= 5:
                print("ACTUAL_BAD", i, head, tokens[:h], "|", tokens[h:])
        r = b.step(tokens, h, head)
        if r is None:
            print("block stuck", i)
            break
        tokens, h, head = r
    print("actual_bad", bad_actual)


if __name__ == "__main__":
    main()
