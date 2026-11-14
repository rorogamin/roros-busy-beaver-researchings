#!/usr/bin/env python3
"""Test the constructive productive-family induction against literal TM runs."""
import json
import random
from overflow import TABLE
D = -99
WORDS = {D: [2], -1: [4, 0], 0: [4, 2], 1: [4, 4], 3: [4, 3]}


def word(prefix):
    return [s for token in prefix for s in WORDS[token]] + [4, 3, 2]


def productive_step(prefix):
    """Return (new prefix, exact step count), with an implicit final 4320^inf.

    Termination: lexicographic induction on (number of D/43 tokens, length).
    A return never increases the first component. See RESULTS.md.
    """
    if not prefix:
        return (1,), 11
    token, tail = prefix[0], prefix[1:]
    if token == -1:
        return (0,) + tail, 3
    if token == 0:
        return (1,) + tail, 3
    if token == 1:
        new, cost = productive_step(tail)
        return (0,) + new, cost + 4
    if token in (D, 3):
        cost = 4 if token == D else 5
        for _ in range(3 if token == D else 2):
            tail, child_cost = productive_step(tail)
            cost += child_cost
        return ((D,) if token == D else (0,)) + tail, cost
    raise ValueError('invalid token')


def main():
    rng = random.Random(20260924)
    count = steps_total = 0
    for _ in range(200):
        prefix = tuple(rng.choice(tuple(WORDS)) for _ in range(rng.randrange(0, 6)))
        a, root = [0] * 256, 64
        a[:root] = [rng.randrange(5) for _ in range(root)]
        a[root:root + len(word(prefix))] = word(prefix)
        for _ in range(5):
            out, n = productive_step(prefix)
            assert sum(t in (D, 3) for t in out) <= sum(t in (D, 3) for t in prefix)
            expected = a.copy()
            expected[root:root + len(word(out))] = word(out)
            p, q = root, 0
            for step in range(n):
                assert p >= root, ('early exit', prefix, step, n)
                tr = TABLE[q][a[p]]
                assert tr is not None
                symbol, delta, q = tr
                a[p] = symbol
                p += delta
            assert (p, q, a) == (root - 1, 1, expected)
            count += 1
            steps_total += n
            prefix = out
    # Show why arbitrary left counters + arbitrary binary-looking words are
    # not themselves a nonhalting invariant.
    counterexamples = []
    for suffix in ([4, 2], [2, 4], [4, 2, 2]):
        a = [0] * 128
        p, q, t = 64, 0, 0
        a[p-2:p] = [1, 4]
        a[p:p+len(suffix)] = suffix
        while TABLE[q][a[p]] is not None and t < 10000:
            symbol, delta, q = TABLE[q][a[p]]
            a[p] = symbol
            p += delta
            t += 1
        assert (q, a[p]) == (0, 1)
        counterexamples.append(dict(initial_counter=1, initial_suffix=suffix,
                                    reaches_A1_after_defined_transitions=t))
    print(json.dumps(dict(status='PASS', productive_returns=count,
                         literal_transitions=steps_total,
                         counterexamples=counterexamples), indent=2))

if __name__ == '__main__':
    main()
