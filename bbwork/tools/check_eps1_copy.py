"""Check rocq/Eps1Copy.v's phase statements against the Python machine.

A tape-level proof is only worth what its tape is worth: a lemma can be true
about a frame no run ever reaches.  So for every phase lemma in the file this
script builds the lemma's *start* frame as a tape, runs the lemma's step count
on `tools/eps1_machine.py`'s machine, and compares the result with the lemma's
end frame -- state, cells left of the head, the cell under it, and the cells to
the right, all as the Coq statements write them (left list head-most first).

    python tools/check_eps1_copy.py

Exits non-zero on the first mismatch.
"""

import sys

sys.path.insert(0, 'tools')
import eps1_machine as em
import eps1_copy as cp

OFF = em.OFF
WALK = em.WALK
C1 = cp.C1 + OFF
CL = cp.CL + OFF
CG = cp.CG + OFF
B1 = cp.B1 + OFF
B2 = cp.B2 + OFF
P1 = cp.P1 + OFF
P2 = cp.P2 + OFF
P3 = cp.P3 + OFF
P4 = cp.P4 + OFF
P5 = cp.P5 + OFF
BQ = cp.BQ + OFF
BW = cp.BW + OFF
R1 = cp.R1 + OFF
R2 = cp.R2 + OFF
R3 = cp.R3 + OFF

WIN = 40          # cells compared on each side


def ones(n):
    return [1] * n


def zeros(n):
    return [0] * n


def tape_of(clft, ccur, crgt):
    """A tape dict from the three Coq fields; the head sits at cell 0."""
    t = {0: ccur}
    for i, x in enumerate(clft):
        t[-1 - i] = x
    for i, x in enumerate(crgt):
        t[1 + i] = x
    return t


def frame_of(tape, head):
    """The three Coq fields back out of a tape, trimmed of trailing blanks."""
    left = [tape.get(head - 1 - i, 0) for i in range(WIN)]
    right = [tape.get(head + 1 + i, 0) for i in range(WIN)]
    while left and left[-1] == 0:
        left.pop()
    while right and right[-1] == 0:
        right.pop()
    return left, tape.get(head, 0), right


def run(state, clft, ccur, crgt, steps):
    tape = tape_of(clft, ccur, crgt)
    m = em.machine()
    head, st = 0, state
    for _ in range(steps):
        r = m.step(tape, head, st)
        if r is None:
            return st, None
        head, st = r
    return st, frame_of(tape, head)


def drop(xs, k):
    """tl applied k times, as Coq reduces it."""
    return list(xs[k:])


def at(xs, k):
    """The cell k cells into a list, with Coq's [hd bl] default for a miss."""
    return xs[k] if k < len(xs) else 0


def trim(xs):
    xs = list(xs)
    while xs and xs[-1] == 0:
        xs.pop()
    return xs


fails = []
checked = 0


def check(name, state, clft, ccur, crgt, steps, want_state, wclft, wccur, wcrgt):
    global checked
    checked += 1
    st, got = run(state, clft, ccur, crgt, steps)
    if got is None:
        fails.append('%s: halted after %d steps' % (name, steps))
        return
    want = (want_state, trim(wclft), wccur, trim(wcrgt))
    have = (st, got[0], got[1], got[2])
    if have != want:
        fails.append('%s:\n   want %s\n   got  %s' % (name, want, have))


# --- the rows of the frame, as the Coq statements build them ----------------
for A in ([0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0], [0, 1]):
    for c in (0, 1):
        for Y in ([0, 0], [1, 0], [0, 1, 0, 0]):
            # steps_C1 : forall A c Y
            check('steps_C1 %s %d %s' % (A, c, Y), C1, [0] + A, c, Y, 3,
                  CL, drop(A, 2), at(A, 1), [1, 0, c] + Y)

for m in (0, 1, 2, 5):
    for L in ([], [0], [1, 0, 0]):
        for Y in ([1, 0], [0, 1, 0, 0]):
            # walk_WALK : forall m L Y  (m + 2 steps)
            check('walk_WALK %d %s %s' % (m, L, Y), WALK, L, 0, zeros(m) + [1] + Y,
                  m + 2, C1, [0] + zeros(m + 1) + L, at(Y, 0), drop(Y, 1))

for m in (0, 1, 3):
    for Z in ([0, 1, 0, 0], [0, 1, 1, 0]):
        for Y in ([0], [1, 0]):
            # walk_CL_marks : forall m Z Y  (S (S m) steps)
            check('walk_CL_marks %d %s %s' % (m, Z, Y), CL, ones(m) + [0] + Z, 1, Y,
                  m + 2, CG, drop(Z, 1), at(Z, 0), [0] + ones(m + 1) + Y)

for Z in ([0, 1, 0, 0], [0, 1, 1], [0, 1]):
    for Y in ([0], [1, 0]):
        # walk_CL_blank : forall Z Y  (1 step)
        check('walk_CL_blank %s %s' % (Z, Y), CL, Z, 0, Y, 1,
              CG, drop(Z, 1), at(Z, 0), [0] + Y)

for q in (0, 1, 2, 4):
    for W in ([0, 1, 0], [0, 1, 1, 0, 0]):
        for Y in ([0], [1, 0, 0]):
            # walk_CG : forall q W Y  (S q steps); the head is on the first of
            # zeros q ++ on :: W
            L = zeros(q) + [1] + W
            check('walk_CG %d %s %s' % (q, W, Y), CG, L[1:], L[0], Y, q + 1,
                  B1, drop(W, 1), at(W, 0), [1] + zeros(q) + Y)

for L in ([], [0], [1, 0]):
    for c in (0, 1):
        for Y in ([0], [1, 0]):
            # step_B1 : forall L c Y  (1 step)
            check('step_B1 %s %d %s' % (L, c, Y), B1, L, c, Y, 1,
                  B2, drop(L, 1), at(L, 0), [c] + Y)

for m in (0, 1, 2, 4):
    for Z in ([0, 0, 1, 0], [0, 1]):
        for Y in ([0], [1, 0, 0]):
            # walk_B2 : forall m Z Y  (S (S m) steps)
            check('walk_B2 %d %s %s' % (m, Z, Y), B2, ones(m) + [0] + Z, 1, Y,
                  m + 2, P1, drop(Z, 1), at(Z, 0), ones(m + 2) + Y)

for q in (0, 1, 3):
    for V in ([1, 1, 0], [0, 1], [1, 0]):
        for Y in ([0], [1, 0]):
            # walk_P1 : forall q V Y  (S q steps)
            L = zeros(q) + [1] + V
            check('walk_P1 %d %s %s' % (q, V, Y), P1, L[1:], L[0], Y, q + 1,
                  P2, drop(V, 1), at(V, 0), [0] + zeros(q) + Y)

# --- the return half's remaining runs ---------------------------------------
for q in (0, 1, 3):
    for Lt in ([], [0], [1, 0]):
        for Z in ([1, 1, 0], [0, 1, 0], [1, 0]):
            # walk_P4 : forall q L Z  (q + 2 steps)
            check('walk_P4 %d %s %s' % (q, Lt, Z), P4, Lt, 0, zeros(q) + [1] + Z,
                  q + 2, P5, [1] + zeros(q + 1) + Lt, at(Z, 0), drop(Z, 1))

for m in (0, 1, 3):
    for Lt in ([], [0], [1, 0]):
        for Z in ([1, 1, 0], [0, 1, 1], [1]):
            # walk_P5 : forall m L Z  (m + 2 steps)
            check('walk_P5 %d %s %s' % (m, Lt, Z), P5, Lt, 1,
                  ones(m) + [0] + Z, m + 2, BQ, [0] + ones(m) + [1] + Lt,
                  at(Z, 0), drop(Z, 1))

for Lt in ([], [0]):
    for c in (0, 1):
        for Z in ([1, 1, 0], [0]):
            # st_BQ_any / st_BW_any : one step each, either symbol
            check('st_BQ_any %s %d %s' % (Lt, c, Z), BQ, Lt, c, Z, 1,
                  BW, [c] + Lt, at(Z, 0), drop(Z, 1))
            check('st_BW_any %s %d %s' % (Lt, c, Z), BW, Lt, c, Z, 1,
                  R1, [c] + Lt, at(Z, 0), drop(Z, 1))

for Lt in ([], [0]):
    for Z in ([1, 1, 0], [0, 1, 0]):
        # st_R1_on : one step
        check('st_R1_on %s %s' % (Lt, Z), R1, Lt, 1, Z, 1,
              R2, [1] + Lt, at(Z, 0), drop(Z, 1))

for r in (0, 1, 2, 4):
    for Lt in ([], [0], [1, 0]):
        for Z in ([1, 1, 0], [0, 1, 1]):
            # walk_R2 : forall r L Z  (r + 2 steps)
            check('walk_R2 %d %s %s' % (r, Lt, Z), R2, Lt, 1,
                  ones(r) + [0] + Z, r + 2, R3, [0] + ones(r) + [1] + Lt,
                  at(Z, 0), drop(Z, 1))

# --- the return half, composed, and the whole trip --------------------------
for n in (0, 1, 2):
    for m in (0, 1, 2):
        for e in (1, 2):
            for c in (0, 1):
                for Y in ([0], [1, 1, 0]):
                    Lt = zeros(6)
                    # trip_back : forall n m e c Y L  (2n + 2m + S e + 12)
                    check('trip_back n=%d m=%d e=%d c=%d' % (n, m, e, c), P2,
                          ones(n) + [0] + Lt, 1,
                          [0] + zeros(e + 1) + ones(m + 2) + [0, 1, 0]
                          + ones(m + 1) + [1, 0, c] + Y,
                          2 * n + 2 * m + (e + 1) + 12, R3,
                          [0] + ones(m + 2) + [0, 1, 0] + ones(m + 2)
                          + zeros(e + 1) + [0] + ones(n + 2) + Lt, c, Y)

for n in (0, 1):
    for m in (0, 1, 2):
        for e in (1, 2):
            for c in (0, 1):
                for Y in ([0], [1, 1, 0]):
                    A = zeros(m + 1) + [0] + zeros(6)
                    # trip : j = S m at the start, S (S m) at the end
                    check('trip n=%d m=%d e=%d c=%d' % (n, m, e, c), R3,
                          [0] + ones(m + 1) + [0, 1, 0] + ones(m + 1) + [0]
                          + zeros(e + 1) + ones(n + 2) + A[m + 1:],
                          1, [c] + Y,
                          4 * m + 2 * (e + 1) + 2 * (n + 1) + 21, R3,
                          [0] + ones(m + 2) + [0, 1, 0] + ones(m + 2) + [0]
                          + zeros(e + 1) + ones(n + 2) + A[m + 2:],
                          c, Y)

# --- the first trip, j = 0 ---------------------------------------------------
# `trip` is stated for j = S m, so it does not cover the trip that runs from an
# empty block and an empty copy; `trip0` does.  From `trip_frame 0 D kk A` --
# two blanks, the wall, two blanks, the gap, the budget -- it reaches
# `trip_frame 1 D kk A` in 2D + 2kk + 17 steps, with the head on the source's
# next cell.  (In the proof the gap is written S d, so D >= 1 here.)
for n in (0, 1, 2):
    for D in (1, 2, 3):
        for c in (0, 1):
            for Y in ([0], [1, 1, 0]):
                for far in (4, 7):
                    A = zeros(far)
                    kk = n + 1
                    check('first trip n=%d D=%d c=%d far=%d' % (n, D, c, far),
                          R3, [0] + [0, 1, 0] + [0] + zeros(D)
                          + ones(kk + 1) + A, 1, [c] + Y,
                          2 * D + 2 * kk + 17, R3,
                          [0] + ones(1) + [0, 1, 0] + ones(1) + [0]
                          + zeros(D) + ones(kk + 1) + A[1:], c, Y)

# --- the sweep: v trips composed, from the frame to v frames later ------------
# `sweep` in rocq/Eps1Copy.v is an induction, so the only way to know its
# statement is true of the machine is to run the whole composed count.  The
# closed form of `sweep_steps` is what the Coq statement carries:
#
#     sweep_steps v j d n = v * (4j + 2(S d) + 2(S n) + 15) + 2vv
#
# and the frame bookkeeping is trip_frame j -> trip_frame (j + v), head on the
# blank after the source, rung budget j cells further left.


def trip_frame(j, D, kk, A):
    """trip_frame, as the Coq definition writes it (left list head-most first)."""
    return ([0] + ones(j) + [0, 1] + [0] + ones(j) + [0] + zeros(D)
            + ones(kk + 1) + list(A)[j:])


def sweep_steps(v, j, d, n):
    return v * (4 * j + 2 * (d + 1) + 2 * (n + 1) + 15) + 2 * v * v


for w in (0, 1, 2, 3):
    for j in (0, 1, 2):
        for d in (1, 2):
            for n in (0, 1):
                for Z in ([0], [1, 1, 0]):
                    v = w + 1
                    N = j + v + 1
                    A = zeros(N + 1)
                    start = trip_frame(j, d + 1, n + 1, A)
                    end = trip_frame(j + v, d + 1, n + 1, A)
                    check('sweep w=%d j=%d d=%d n=%d' % (w, j, d, n),
                          R3, start, 1, ones(w) + [0] + Z,
                          sweep_steps(v, j, d, n), R3, end, 0, Z)

# --- the return half's first two runs ---------------------------------------
for n in (0, 1, 2, 3):
    for L in ([], [0], [0, 0]):
        for Y in ([0], [1, 0, 1]):
            # walk_P2 : forall n L Y  (n + 2 steps)
            check('walk_P2 %d %s %s' % (n, L, Y), P2, ones(n) + [0] + L, 1, Y,
                  n + 2, P3, [1] + L, 1, ones(n) + Y)
            # walk_P3 : forall n L Y  (S (S n) steps)
            check('walk_P3 %d %s %s' % (n, L, Y), P3, [1] + L, 1,
                  ones(n) + [0] + Y, n + 2, P4,
                  [0] + ones(n + 1) + [1] + L, at(Y, 0), drop(Y, 1))

# --- the trip out, composed: rocq/Eps1Copy.v's trip_out ---------------------
for m in (0, 1, 2, 3):
    for D in (1, 2, 3):
        for kk in (0, 1, 2):
            for c in (0, 1):
                for tail in ([], [0], [1, 0]):
                    for Y in ([0, 0], [1, 0, 0]):
                        A = ones(2) + [0, 1, 0] + tail
                        frame = ([0] + ones(m + 1) + [0, 1, 0] + ones(m + 1)
                                 + [0] + zeros(D) + ones(kk + 1) + A[m + 1:])
                        # trip_frame (S m): the cells left of the head, head-most
                        # first; the head itself is the 'on' this frame points at
                        V = ones(kk) + A[m + 1:]
                        check('trip_out m=%d D=%d kk=%d c=%d A=%s Y=%s'
                              % (m, D, kk, c, A, Y),
                              R3, frame, 1, [c] + Y,
                              2 * m + D + 11, P2,
                              drop(V, 1), at(V, 0),
                              [0] + zeros(D) + ones(m + 2) + [0, 1, 0] + ones(m + 1)
                              + [1, 0, c] + Y)

print('phase frames checked against tools/eps1_machine.py: %d' % checked)
if fails:
    for f in fails:
        print('  FAIL', f)
    print('%d FAILURES' % len(fails))
    sys.exit(1)
print('ALL OK')
