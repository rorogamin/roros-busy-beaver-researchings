"""Find short translated local cycles in CET(4) holdouts.

The certificate is a repeated extended key: both states, head distance, and the
radius-R tape around each head, together with a common nonzero displacement.
R is chosen larger than the largest period plus the one-cell read radius, so the
whole cycle stays inside the checked window.  A virgin homogeneous frontier is
also required in the direction of motion.
"""
import sys

R = 12
MAXP = 9
CAP = 3000


def parse(line):
    a1, a2 = line.strip().split('|')

    def ag(s):
        rows = []
        for row in s.split('_'):
            trs = []
            for i in range(0, 6, 3):
                trs.append((int(row[i]), 1 if row[i + 1] == 'R' else -1,
                            ord(row[i + 2]) - 65))
            rows.append(trs)
        return rows
    return ag(a1), ag(a2)


def scan(line):
    a1, a2 = parse(line)
    t, p1, p2, s1, s2 = {}, 0, 2, 0, 0
    seen = {}
    for k in range(CAP):
        key = (s1, s2, p2 - p1,
               tuple(t.get(p1 + z, 0) for z in range(-R, R + 1)),
               tuple(t.get(p2 + z, 0) for z in range(-R, R + 1)))
        old = seen.get(key)
        if old is not None:
            k0, q1, q2 = old
            P = k - k0
            d1, d2 = p1 - q1, p2 - q2
            if P <= MAXP and d1 == d2 and d1:
                lo, hi = min(p1, p2), max(p1, p2)
                if d1 > 0:
                    ok = all(t.get(x, 0) == 0
                             for x in range(hi + R + 1, hi + R + 101))
                else:
                    ok = all(t.get(x, 0) == 0
                             for x in range(lo - R - 100, lo - R))
                if ok:
                    return k0, P, d1, p1, p2
        else:
            seen[key] = (k, p1, p2)
        x, y = a1[s1][t.get(p1, 0)], a2[s2][t.get(p2, 0)]
        t[p1], t[p2] = x[0], y[0]
        p1 += x[1]; s1 = x[2]
        p2 += y[1]; s2 = y[2]
        if p1 == p2:
            return None
    return None


def main():
    lines = open('all_holdouts_cet4.txt').read().splitlines()
    out = []
    for i, line in enumerate(lines[:int(sys.argv[1]) if len(sys.argv) > 1 else 500]):
        r = scan(line)
        if r:
            out.append((i, line, r))
    for i, line, r in out:
        print(i, r, line)
    print('small-period cycles:', len(out))


if __name__ == '__main__':
    main()
