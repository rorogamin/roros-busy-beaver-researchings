"""Structure of phases: maximal same-region runs, lengths, starts, rule usage."""
from fractions import Fraction
from t758_probe import step

def trace(k, c0v, cap=20000):
    a, c = 2*3**k - 1, c0v
    seq = []
    while len(seq) < cap:
        a2, c2, h, r = step(a, c)
        seq.append((a, c, a2, c2, h, r))
        if h or a2 == 1 or 2*c2 <= c0v: break
        a, c = a2, c2
    return seq

def phases(seq):
    """maximal runs of consecutive steps with the same region of the *current* state"""
    out = []
    i = 0
    while i < len(seq):
        a, c = seq[i][0], seq[i][1]
        reg = 'J' if a <= c else 'L'
        j = i
        while j < len(seq) and (('J' if seq[j][0] <= seq[j][1] else 'L') == reg):
            j += 1
        out.append((a, c, reg, j - i, i))
        i = j
    return out

rules = {}
maxJ = (0, None); maxL = (0, None)
maxJ_shallow = (0, None)
lens = {}
witness_h = []
for k in list(range(1, 26)) + [50, 100, 150, 200, 250, 280, 288, 289, 290, 291, 292]:
    top = 2*3**k
    cls = list(range(1, min(top, 200))) + [top//2, top//3, top//7, top-1, top-2, 2047, 2052]
    for c0v in cls:
        if not (1 <= c0v < top): continue
        seq = trace(k, c0v)
        for (a, c, a2, c2, h, r) in seq:
            rules[r] = rules.get(r, 0) + 1
            if r == 'h' and c > 1000:
                witness_h.append((k, c0v, a, c, a2, c2))
        for (a, c, reg, ln, i) in phases(seq):
            lens[ln] = lens.get(ln, 0) + 1
            if reg == 'J':
                if ln > maxJ[0]: maxJ = (ln, (k, c0v, a, c))
                if a <= 2*c and ln > maxJ_shallow[0]: maxJ_shallow = (ln, (k, c0v, a, c))
            else:
                if ln > maxL[0]: maxL = (ln, (k, c0v, a, c))
print("rule counts:", rules)
print("max J phase:", maxJ)
print("max J phase with start a<=2c:", maxJ_shallow)
print("max L phase:", maxL)
print("phase length histogram (len: count):", dict(sorted(lens.items())))
print("h steps with c>1000:", witness_h[:10])
