#!/usr/bin/env python3
"""Independent literal checks for the new formulas; deterministic seed."""
from itertools import product
import json
from pathlib import Path
import random
from overflow import (TABLE, PAIR_DIGIT, TERNARY_ENCODE, return_plan,
                      drain_plan, ternary_digits, counter_cost)

TOKENS = ((2,), (4, 0), (4, 2), (4, 4), (4, 3))


def literal(a, p, q):
    tr = TABLE[q][a[p]]
    if tr is None:
        raise AssertionError(('unexpected halt', p, a[p]))
    w, d, q = tr
    a[p] = w
    return p + d, q


def check_drain(tokens, n=1, width=1):
    word = [x for tok in tokens for x in tok]
    root = 80
    cut = root + len(word)
    a = [0] * 256
    # Deliberately hostile suffix. It must never be scanned before our endpoint.
    a[cut:cut + 5] = [1, 3, 1, 4, 2]
    a[root:cut] = word
    oldds = ternary_digits(n, width)
    for j, d in enumerate(oldds):
        a[root - 1 - j] = TERNARY_ENCODE[d]
    a[root - width - 1] = 1
    original = a.copy()
    plan = drain_plan(a, root, end=cut)
    expected = original.copy()
    for pos, s in plan.edits:
        expected[pos] = s
    newds = ternary_digits(n + plan.capacity, width)
    for j, d in enumerate(newds):
        expected[root - 1 - j] = TERNARY_ENCODE[d]
    expected[root - len(newds) - 1] = 1
    expected_time = plan.cost + counter_cost(n, plan.capacity, width)
    p, q, t = root, 0, 0
    while p != cut:
        p, q = literal(a, p, q)
        t += 1
        assert t <= expected_time, ('late first entry', tokens, n, width)
    assert (q, t, a) == (0, expected_time, expected), (tokens, n, width, t, expected_time)
    assert original[root:cut] == word  # Planning itself did not mutate input.
    return expected_time


def check_returns(tokens, calls, rng):
    word = [x for tok in tokens for x in tok]
    root, cut = 32, 32 + len(word)
    a = [rng.randrange(5) for _ in range(128)]
    a[root:cut] = word
    a[cut] = 1
    before = a.copy()
    cap = drain_plan(a, root, end=cut).capacity
    plan = return_plan(a, root, calls)
    assert (plan is not None) == (calls <= cap), (tokens, calls, cap)
    if plan is None:
        return
    expected = a.copy()
    for p, s in plan.edits:
        expected[p] = s
    t = 0
    for _ in range(calls):
        p, q = root, 0
        while p >= root:
            assert p < cut
            p, q = literal(a, p, q)
            t += 1
            assert t <= plan.cost
        assert (p, q) == (root - 1, 1)
    assert t == plan.cost and a == expected
    assert drain_plan(a, root, end=cut).capacity == cap - calls


def check_word_rule(before, after, steps, state, rng):
    root = 32
    a = [rng.randrange(5) for _ in range(128)]
    a[root:root + len(before)] = before
    expected = a.copy()
    expected[root:root + len(after)] = after
    p, q = root, 0
    for i in range(steps):
        assert p >= root, ('early left exit', before, i)
        p, q = literal(a, p, q)
    assert (p, q, a) == (root - 1, state, expected), (before, after, steps)


def main():
    rng = random.Random(20260924)
    stats = dict(exhaustive_drains=0, random_drains=0, return_batches=0,
                 terminal_context_checks=0, literal_transitions_in_drains=0)
    # Every token word up to length five; several different counter widths.
    for length in range(6):
        for tokens in product(TOKENS, repeat=length):
            for n, width in ((0, 0), (1, 1), (2, 1), (26, 3)):
                stats['literal_transitions_in_drains'] += check_drain(tokens, n, width)
                stats['exhaustive_drains'] += 1
            cap = drain_plan([x for tok in tokens for x in tok], 0,
                             end=sum(map(len, tokens))).capacity
            for k in set((0, 1, cap, cap + 1, cap // 2)):
                check_returns(tokens, k, rng)
                stats['return_batches'] += 1
    for _ in range(1000):
        tokens = [rng.choice(TOKENS) for _ in range(rng.randrange(1, 10))]
        width = rng.randrange(0, 6)
        n = rng.randrange(3 ** width)
        stats['literal_transitions_in_drains'] += check_drain(tokens, n, width)
        stats['random_drains'] += 1
    for m in range(31):
        for _ in range(10):
            check_word_rule([4, 4] * m + [3, 2], [2, 2] + [4, 2] * m,
                            8 * m + 1, 0, rng)
            check_word_rule([4, 4] * (m + 1) + [0, 0, 0, 0],
                            [2, 2] + [4, 2] * m + [4, 4, 3, 2], 8 * m + 19, 0, rng)
            check_word_rule([4, 3, 2, 0, 0], [4, 4, 4, 3, 2], 11, 1, rng)
            stats['terminal_context_checks'] += 3
    print(json.dumps({'status': 'PASS', **stats}, indent=2))

if __name__ == '__main__':
    main()
