#!/usr/bin/env python3
"""Search for a translation-invariant GF(2) invariant of machine 14.

Invariant form:
    I(tape, state) = sum_i f(tape[i .. i+W-1]) + h[state]   (mod 2)

with f(0^W) = 0.  We solve, for all states, head symbols and contexts, the
linear equations saying that one raw step preserves I.  Then we check whether
the halt condition B/3 has a context-independent value different from the
start.

This is an exact invariant search, not a simulation.
"""
from __future__ import annotations

import itertools
import sys

# raw machine: (state, symbol) -> (write, direction, next state)
TR = {
    (0, 0): (1, +1, 1),
    (0, 1): (2, -1, 0),
    (0, 2): (0, +1, 1),
    (0, 3): (4, -1, 1),
    (0, 4): (1, +1, 0),
    (1, 0): (1, -1, 0),
    (1, 1): (3, +1, 0),
    (1, 2): (1, +1, 0),
    (1, 3): None,
    (1, 4): (0, -1, 0),
}
SYMS = range(5)


def words(W):
    return list(itertools.product(SYMS, repeat=W))


def solve(W: int, verbose: bool = True):
    ws = words(W)
    idx = {w: i for i, w in enumerate(ws)}
    nf = len(ws)
    hA, hB = nf, nf + 1
    nv = nf + 2

    rows = []

    def add_row(coeffs):
        mask = 0
        for v in coeffs:
            mask ^= 1 << v
        if mask:
            rows.append(mask)

    lefts = list(itertools.product(SYMS, repeat=W - 1))
    rights = list(itertools.product(SYMS, repeat=W - 1))
    for (st, a), tr in TR.items():
        if tr is None:
            continue
        w, d, st2 = tr
        for L in lefts:
            for R in rights:
                old = tuple(L) + (a,) + tuple(R)
                new = tuple(L) + (w,) + tuple(R)
                # windows starting at -W+1 .. 0
                coeff = []
                for start in range(-(W - 1), 1):
                    oi = start + (W - 1)  # index into old
                    ow = old[oi:oi + W]
                    nw = new[oi:oi + W]
                    coeff.append(idx[ow])
                    coeff.append(idx[nw])
                coeff.append(hA if st == 0 else hB)
                coeff.append(hA if st2 == 0 else hB)
                add_row(coeff)

    # Gaussian elimination; track pivot rows.
    piv = {}
    for row in rows:
        r = row
        while r:
            p = r.bit_length() - 1
            if p in piv:
                r ^= piv[p]
            else:
                piv[p] = r
                break
    rank = len(piv)
    nullity = nv - rank
    if verbose:
        print(f"W={W} vars={nv} equations={len(rows)} rank={rank} nullity={nullity}")

    # Find a basis of the nullspace by back-substitution.  Pivot variables are
    # expressed in terms of free variables.  We only need one nonzero solution.
    # Build a row echelon matrix on pivot variables.
    piv_list = sorted(piv, reverse=True)
    # For each free variable, set it to 1 and solve.
    free = [v for v in range(nv) if v not in piv]
    sols = []
    for fv in free:
        x = [0] * nv
        x[fv] = 1
        # Process pivots from low to high?  Row piv[p] has highest bit p; it
        # may contain lower pivot bits.  Eliminate using piv rows in increasing
        # pivot order.
        for p in sorted(piv):
            row = piv[p]
            val = 0
            rr = row & ~(1 << p)
            while rr:
                b = rr.bit_length() - 1
                val ^= x[b]
                rr &= rr - 1
            x[p] = val
        sols.append(x)
    if not sols:
        return None

    # Check the start and whether B/3 is context-independent.
    # start after 14 raw steps: 110111, head at offset 4, state A.
    start_tape = [1, 1, 0, 1, 1, 1]
    start_head = 4

    def value(x, tape, head, state):
        # finite tape with blanks outside; sum all W-windows that meet tape.
        lo = -W + 1
        hi = len(tape)
        s = 0
        full = [0] * (len(tape) + 2 * W)
        for i, v in enumerate(tape):
            full[i + W] = v
        for start in range(lo, hi + W):
            win = tuple(full[start + W:start + 2 * W])
            if len(win) < W:
                continue
            s ^= x[idx[win]]
        s ^= x[hA if state == 0 else hB]
        return s

    print("start values:", [value(x, start_tape, start_head, 0) for x in sols[:8]])
    # Halt B/3: head symbol 3, state B, all contexts.  Compute local value
    # (sum of windows touching the head cell) and check constancy.
    halt_vals = set()
    for L in lefts:
        for R in rights:
            tape = list(L) + [3] + list(R)
            head = W - 1
            # value on just this local tape; windows outside are zero.
            s = 0
            full = [0] * (len(tape) + 2 * W)
            for i, v in enumerate(tape):
                full[i + W] = v
            for start in range(-W + 1, len(tape)):
                win = tuple(full[start + W:start + 2 * W])
                if len(win) < W:
                    continue
                s ^= x[idx[win]]
            s ^= x[hB]
            halt_vals.add(s)
    print("halt B/3 value set size:", len(halt_vals), "sample:", sorted(halt_vals)[:4])

    # Return the first solution and diagnostics.
    return sols[0], (nf, hA, hB, idx, W)


def main():
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    out = solve(W)
    if out is None:
        print("no nonzero invariant")
        return
    x, meta = out
    nf, hA, hB, idx, W = meta
    ws = words(W)
    nz = [(ws[i], i) for i in range(nf) if x[i]]
    print("nonzero f windows:", len(nz))
    for w, i in nz[:40]:
        print(" ", "".join(map(str, w)))
    print("hA", x[hA], "hB", x[hB])


if __name__ == "__main__":
    main()
