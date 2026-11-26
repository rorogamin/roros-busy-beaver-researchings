"""Find the harp: the variant of the seed machine whose turns keep lengthening
1,2,3,4,... instead of resetting."""

USER = """0 _ 1 r 0
0 1 _ l 0
0 2 2 l 1
1 1 1 l 1
1 _ 1 r 2
2 1 1 r 2
2 2 2 r 2
2 _ _ r 3
3 _ 1 l 3
3 1 _ r 3
3 2 2 r 4
4 1 1 r 4
4 _ 1 l 5
5 2 2 l 5
5 1 1 l 5
5 _ _ r 0
"""
SYMS = ('_', '1', '2')


def parse(text):
    out = []
    for line in text.strip().splitlines():
        out.append(line.split())
    return out


def intervals(rules, steps=200000, init=(0, '_', 1, '2')):
    head, s, left, right = init
    tape = {0: '_', 1: '2'}
    q, d = '0', 'r'
    turns = []
    for step in range(steps):
        sym = tape.get(head, '_')
        w, nd, nq = rules.get((q, sym), (None, None, None))
        if w is None:
            break
        tape[head] = w
        if nd != d:
            turns.append(step)
            d = nd
        head += 1 if nd == 'r' else -1
        q = nq
    return [turns[i + 1] - turns[i] for i in range(len(turns) - 1)]


def longest_ramp(seq):
    best = 1 if seq else 0
    run = 1
    for i in range(1, len(seq)):
        if seq[i] == seq[i - 1] + 1:
            run += 1
            best = max(best, run)
        else:
            run = 1
    return best


def window(seq, n=26):
    # the ramp that starts the longest run, for display
    best_i, best_len, run, start = 0, 1, 1, 0
    for i in range(1, len(seq)):
        if seq[i] == seq[i - 1] + 1:
            run += 1
            if run > best_len:
                best_len, best_i = run, start
        else:
            run, start = 1, i
    return seq[best_i:best_i + n]
