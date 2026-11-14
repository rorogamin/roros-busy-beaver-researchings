"""Greedy matcher: cut a computation into the macro pieces the Lean development provides.

Every piece of `RequestProject/*.lean` is listed here as a window rule
`(state in, head offset in, word in, state out, head offset out, word out, steps)`; the
matcher looks for the piece that consumes the most steps at the current configuration,
verifies it by simulation, applies it, and repeats.  The output is the stage list of a
candidate macro rule, in the form in which the Lean proofs are written.

Exploratory only; nothing here is machine-checked.
"""

T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}


def U(a, b): return [0] + [4] * a + [2] * b
def V(c):    return [4, 3] + [2] * c
u = U(1, 1)


def run(q, k, l, n):
    l = list(l)
    for _ in range(n):
        if not (0 <= k < len(l)): return None
        t = T[(q, l[k])]
        if t is None: return None
        w, d, s = t
        l[k] = w; k += d; q = s
    if not (0 <= k < len(l)): return None
    return q, k, l


def rep(x, n): return x * n


def pieces(N=14):
    """The library.  `N` bounds the parameter of the parametric pieces."""
    P = []

    def add(name, qi, ki, wi, qo, ko, wo, n):
        P.append((name, qi, ki, wi, qo, ko, wo, n))

    # fixed pieces
    add('carry_open', 'B', 3, [0,0,0,0,4,4,2,2,4,3,2,0], 'A', 11,
        [0,1,3,1,0,1,1,0,1,0,3,0], 22)
    add('carry_reflect', 'A', 3, [0,1,0,3,2], 'B', 4, [1,3,1,0,2], 7)
    add('carry_B2', 'B', 0, [2,2], 'A', 1, [3,2], 1)
    add('p3_final', 'A', 11, [0,1,3,1,0,1,1,1,3,1,0,3], 'B', 0,
        [0,4,4,2,0,4,4,4,4,2,0,4], 11)
    add('p1g_open', 'B', 3, [0,0,0,0,4,4,2,0,4,4,4,4,2,0], 'A', 13,
        [0,1,3,1,0,0,3,1,0,0,0,0,3,0], 16)
    add('p1g_reflect', 'A', 3, [0,0,0,3], 'B', 3, [1,3,1,4], 8)
    add('p1g_B4', 'B', 0, [4,2], 'B', 1, [0,2], 1)
    add('p1g_back', 'A', 5, [0,1,3,1,0,3], 'B', 0, [0,4,4,2,0,4], 5)
    add('p1g_close', 'B', 8, [0,1,3,1,0,0,3,1,0], 'B', 0, [0,4,4,2,2,0,4,2,0], 10)
    add('p1v_back', 'A', 5, [0,3,1,0,1,3], 'B', 0, [0,4,2,0,4,4], 5)
    add('p1v_close', 'B', 5, [0,1,3,1,0,0], 'B', 0, [0,4,4,2,2,0], 7)
    add('u21_turn', 'B', 3, [3,1,0,2,2,0], 'A', 0, [3,2,2,2,2,0], 15)
    add('u2b_restart', 'B', 2, [0,0,3,2,2], 'A', 4, [0,1,0,3,2], 4)
    add('u2b_exit', 'A', 2, [0,3,2,2,0], 'A', 4, [1,1,0,3,0], 8)
    add('u2b_vturn', 'A', 0, [0,2,2], 'A', 0, [1,4,3], 4)
    add('turn_U2_second', 'B', 1, [0,2,2,4,3], 'B', 4, [1,1,0,0,3], 9)
    add('vcross_step', 'A', 2, [0,3,2,4,3,2,2], 'A', 6, [1,1,0,1,0,3,2], 12)
    add('vcross_end', 'A', 2, [0,3,2,4,3,2,0], 'A', 6, [1,1,0,1,0,3,0], 12)
    # sweeps (a sweep is a window rule on the word plus the cell it stops on)
    add('sweepR_042', 'A', 0, [0,4,2,-1], 'A', 3, [1,0,3,-1], 3)
    add('sweepR_02', 'A', 0, [0,2,-1], 'A', 2, [1,3,-1], 2)
    add('sweepR_204', 'B', 0, [2,0,4,-1], 'B', 3, [3,1,0,-1], 3)
    add('blockR2', 'A', 0, [0,4,4,2,-1], 'A', 4, [1,0,0,3,-1], 4)
    add('sweepL_103', 'A', 3, [-1,1,0,3], 'A', 0, [-1,2,0,4], 3)
    add('blockL_1003', 'A', 4, [-1,1,0,0,3], 'A', 0, [-1,2,2,0,4], 6)
    add('retU2', 'A', 4, [-1,1,1,3,2], 'A', 0, [-1,2,2,4,3], 4)
    add('retV', 'A', 2, [-1,0,3], 'A', 0, [-1,0,4], 2)
    add('retL_1103', 'A', 4, [-1,1,1,0,3], 'A', 0, [-1,2,2,0,4], 4)
    add('sweepL_A3', 'A', 1, [-1,3], 'B', 0, [-1,4], 1)
    add('sweepL_B3', 'B', 1, [-1,3], 'A', 0, [-1,4], 1)
    add('sweepL_A1', 'A', 1, [-1,1], 'A', 0, [-1,2], 1)
    add('sweepL_B1', 'B', 1, [-1,1], 'B', 0, [-1,4], 1)
    add('sweepL_B0', 'B', 1, [-1,0], 'A', 0, [-1,0], 1)
    add('sweepL_310', 'B', 2, [-1,3,1,0], 'B', 0, [-1,4,2,0], 3)
    add('sweepL_031', 'A', 2, [-1,0,3,1], 'A', 0, [-1,0,4,2], 3)
    add('sweepR_420', 'B', 0, [4,2,0,-1], 'B', 3, [0,3,1,-1], 3)
    add('sweepR_B4', 'B', 0, [4,-1], 'B', 1, [0,-1], 1)
    add('sweepR_B2', 'B', 0, [2,-1], 'A', 1, [3,-1], 1)
    add('sweepR_A0', 'A', 0, [0,-1], 'B', 1, [1,-1], 1)
    # parametric pieces
    for n in range(1, N):
        add('run_ones_B %d' % n, 'B', n, [-1] + [1] * n, 'B', 0, [-1] + [4] * n, n)
        add('run_fours %d' % n, 'B', 0, [4] * n + [-1], 'B', n, [0] * n + [-1], n)
        add('sweepL_310^%d' % n, 'B', 3 * n, [-1] + rep([3,1,0], n), 'B', 0,
            [-1] + rep([4,2,0], n), 3 * n)
        add('run_ones_A %d' % n, 'A', n, [-1] + [1] * n, 'A', 0, [-1] + [2] * n, n)
        add('sweepL_bulk %d' % n, 'A', 3 * n, [-1] + rep([1,0,3], n), 'A', 0,
            [-1] + rep([2,0,4], n), 3 * n)
        add('sweepR_042^%d' % n, 'A', 0, rep([0,4,2], n) + [-1], 'A', 3 * n,
            rep([1,0,3], n) + [-1], 3 * n)
        add('sweepR_204^%d' % n, 'B', 0, rep([2,0,4], n) + [-1], 'B', 3 * n,
            rep([3,1,0], n) + [-1], 3 * n)
        add('pingpong_chain0 %d' % n, 'A', 2, [0,3] + [2] * (2 * n + 1), 'A', 2 * n + 2,
            [1] * (2 * n) + [0,3,2], 8 * n)
        add('cross_back %d' % n, 'A', 4, [3,1,0,3] + [2] * (2 * n + 1) + [0], 'A', 0,
            [3] + [2] * (2 * n + 4) + [0], 10 * n + 14)
        add('turn_U2 %d' % n, 'A', 4, [1,0,0,3] + [2] * (2 * n + 1) + [0], 'A', 3,
            [1,1,3] + [2] * (2 * n + 2) + [0], 10 * n + 15)
    for n in [0]:
        add('cross_back 0', 'A', 4, [3,1,0,3] + [2] + [0], 'A', 0, [3] + [2] * 4 + [0], 14)
        add('turn_U2 0', 'A', 4, [1,0,0,3,2,0], 'A', 3, [1,1,3,2,2,0], 15)
    return P


LIB = pieces()


def wmatch(seg, w):
    """`-1` in `w` is a wildcard: the cell is neither read nor written by the piece."""
    if len(seg) != len(w): return False
    return all(x == y or y == -1 for x, y in zip(seg, w))


def match(q, k, l):
    """Find the piece that consumes the most steps at this configuration."""
    best = None
    for (name, qi, ki, wi, qo, ko, wo, n) in LIB:
        if q != qi or n == 0: continue
        b = k - ki
        if b < 0 or b + len(wi) > len(l): continue
        if not wmatch(l[b:b + len(wi)], wi): continue
        res = run(q, k, l, n)
        if res is None: continue
        q2, k2, l2 = res
        if q2 != qo or k2 != b + ko: continue
        if not wmatch(l2[b:b + len(wo)], wo): continue
        if l2[:b] != l[:b] or l2[b + len(wo):] != l[b + len(wo):]: continue
        if best is None or n > best[1]:
            best = (name, n)
    return best


def decompose(q, k, l, total, verbose=True):
    """Cut `total` steps into pieces; returns the list of (name, steps, state, head)."""
    out = []
    t = 0
    while t < total:
        mm = match(q, k, l)
        if mm is None:
            if verbose:
                print('  NO MATCH at t=%d %s @%d  %s' % (t, q, k, ''.join(map(str, l))))
            return out, (t, q, k, l)
        name, n = mm
        if t + n > total:
            if verbose:
                print('  overshoot at t=%d with %s (%d steps)' % (t, name, n))
            return out, (t, q, k, l)
        q, k, l = run(q, k, l, n)
        t += n
        out.append((name, n, q, k))
        if verbose:
            print('  %-22s t=%4d  %s @%d' % (name, t, q, k))
    return out, None
