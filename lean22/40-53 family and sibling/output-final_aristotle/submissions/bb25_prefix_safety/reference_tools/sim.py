"""Reference simulator for the BB(2,5) family 1RB2LA0RB1LB---_1LA3RA1RA4LB---.

Directed-head configuration:  (l, q, d, r)
  l : list of symbols left of the marker, nearest first
  r : list of symbols right of the marker, nearest first
  d : 'L' (head reads l[0]) or 'R' (head reads r[0])
Cells outside the lists are 0.
"""

A, B = 'A', 'B'

famA = {0: (1, 'R', B), 1: (2, 'L', A), 2: (0, 'R', B), 3: (1, 'L', B), 4: None}


def machine(b4):
    famB = {0: (1, 'L', A), 1: (3, 'R', A), 2: (1, 'R', A), 3: (4, 'L', B), 4: b4}
    return {A: famA, B: famB}


def hd(xs):
    return xs[0] if xs else 0


def tl(xs):
    return xs[1:] if xs else []


def step(m, c):
    l, q, d, r = c
    a = hd(l) if d == 'L' else hd(r)
    t = m[q][a]
    if t is None:
        return None
    w, mv, q2 = t
    if d == 'L':
        if mv == 'L':
            return (tl(l), q2, 'L', [w] + r)
        return ([w] + tl(l), q2, 'R', r)
    else:
        if mv == 'L':
            return (l, q2, 'L', [w] + tl(r))
        return ([w] + l, q2, 'R', tl(r))


def show(c):
    if c is None:
        return 'HALT'
    l, q, d, r = c
    ls = ''.join(map(str, reversed(l)))
    rs = ''.join(map(str, r))
    mark = f'<{q}' if d == 'L' else f'{q}>'
    return f'{ls} {mark} {rs}'


def run(c, n, m):
    out = [(0, c)]
    for i in range(1, n + 1):
        c = step(m, c)
        out.append((i, c))
        if c is None:
            break
    return out


if __name__ == '__main__':
    m = machine(None)
    for i, c in run(([], A, 'R', []), 12, m):
        print(i, show(c))
