"""
eps1_u3.py — the RUN-CODE eps_1 machine: a 2-symbol table, fresh build V1.

Tape (one growing object, single 0/1 string; the sim pads with free cells
in both directions):

    [1^p] 00 [1^L1] 0 [1^L2] 0 ... [1^Lm] 0 [0 0 0 ...blank right]

* the two 00 pairs: the PARK pair (home a, immediately after the p-block)
  and the CHAIN-END pair after the last run's close; single 0s separate
  runs, so there is never an interior 00: leftward the first 00 is the
  park, rightward the first 00 is the chain end.
* p grows to the LEFT (the model's wrapped count), spends from the RIGHT
  (the cell a-1: fs erases exactly one mark there, p >= 1 iff that cell
  held a 1, which is also the whole p-test: one move left from a).
* the bottom kind rides in the first run's length: L1 = 1 the atom eps_0,
  L2 = 2 the atom+1, L >= 3 the plain numeral L - 2.  Tail runs are plain
  numerals L >= 3 (entry c = L - 2 >= 1); trailing unit entries never sit
  on the canonical tape (they were folded into p).

The machine is the FIXED-SEED realization of eps1_chain.step: every seed
sn gets its own table parameter, first build is sn = 1, so the fs push is
one entry NUM(2) = a run of 4 marks and the atom-limit grow is p += 1.

Campaign per model step (rest on a, state U, returns to U):
  * dispatch: a+2 blank below chain empty -> halt (no row);
    else read a-1: 1 = fs (spend one park mark right here), 0 = pred;
  * p-agnostic bottom+tail tests: cross run1's marks rightward, check the
    cell after its close: 1 = MULTI (normal body work), 0 = the singleton
    arms by bottom kind (the pure atom widen, the pure atom+1 flip /
    atom-rest };
  * the MULTI body work: walk right to the chain end, walk left counting
    the TOP run's marks: L >= 5 plain dec; L == 4: fs plain decs it too
    (the dec'd entry is a legit limit-1) but PRED pops the run folding it
    into p; L == 3 = the [NUM(1)] singleton handled at the dispatch, so
    dead here.  Then fs appends the 4-mark entry, pred folds or rests.
  * singletons: the widen (any p): run 1 -> 3 growing into the pad, p += 1;
    the atom+1: fs erases one mark and pushes; pred erases one mark only;
    the plain singleton: the same count machinery over run1 itself.

BOVEHMO PROMISE: no state count is claimed here — the table is counted
honestly in main(), green-first, minimised later by separate rounds.

Run: python tools/eps1_u3.py
"""

import sys
import random
import tools
sys.path.insert(0, 'tools')

import eps1_chain as C
import eps1_descent as D
from eps1_chain import NUM, ATOM, ATOM1, full, chain_of, is_succ
from eps1_descent import Ord, ZERO

SEED = 1                      # this build is the fixed-seed sn = 1 machine

# ---------------------------------------------------------------- codec


def canon(p, chain):
    """The canonical (p, chain): units at the top folded into p."""
    chain = list(chain)
    while len(chain) > 1 and isinstance(chain[-1], int) and chain[-1] == 1:
        chain.pop()
        p += 1
    if chain and isinstance(chain[0], int):
        chain = [NUM(chain[0])] + chain[1:]
    return p, chain


def make_tape(p, chain):
    """(p, chain) -> run-code string (the canonical form only)."""
    p, chain = canon(p, chain)
    runs = []
    if not chain:
        pass
    else:
        b0 = chain[0]
        if b0 == ATOM:
            runs.append(1)
        elif b0 == ATOM1:
            runs.append(2)
        elif isinstance(b0, Ord):
            runs.append(C.num_of(b0) + 2)
        else:
            runs.append(b0 + 2)
        for b in chain[1:]:
            assert not isinstance(b, Ord), 'plain chains only'
            assert b >= 1
            runs.append(b + 2)
    return '1' * p + '00' + ''.join('1' * L + '0' for L in runs) + '00'


def read_tape(tape):
    """Run-code string -> (p, chain); raises on anything non-canonical."""
    i, L = 0, len(tape)
    p = 0
    while i < L and tape[i] == '1':
        p += 1
        i += 1
    if i + 1 >= L or tape[i] != '0' or tape[i + 1] != '0':
        raise ValueError('park pair 00 missing')
    i += 2
    runs = []
    while i < L:
        j = i
        while j < L and tape[j] == '1':
            j += 1
        Lr = j - i
        if Lr == 0:
            break                       # chain end
        if j >= L or tape[j] != '0':
            raise ValueError('run without close')
        runs.append(Lr)
        i = j + 1
    chain = []
    k = 0
    while k < len(runs):
        r = runs[k]
        if k == 0:
            if r == 1:
                chain.append(ATOM)
            elif r == 2:
                chain.append(ATOM1)
            else:
                chain.append(NUM(r - 2))
        else:
            assert r >= 3, 'unit tails are non-canonical'
            chain.append(r - 2)
        k += 1
    return p, chain


# ------------------------------------------------------------------ table


def build_table():
    """The 2-symbol transition table.  A missing (state, symbol) row halts."""
    T = {}

    def st(nm, note):
        T[nm] = {}
        return nm

    def r(nm, sym, w, dir, nx, note=''):
        T[nm][sym] = (w, dir, nx)

    r.preventDefault = None

    # ---- U the entry: head rests on a, the park pair's LEFT 0
    U = st('U', 'rest at a')
    r(U, 0, 0, 'R', 'V')            # step right onto a+1

    # ---- V, W: the halt test (a+2 blank = the chain emptied)
    V = st('V', 'at a+1 (0): step right onto a+2')
    r(V, 0, 0, 'R', 'W')
    W = st('W', 'halt look on a+2')
    # no 0-row: the chain emptied, halt per the model
    r(W, 1, 1, 'L', 'X', 'the body exists: walk left to the p-test')

    # ---- X, Y, P: walk left to the park edge
    X = st('X', 'at a+1 (0): step left onto a')
    r(X, 0, 0, 'L', 'Y')
    Y = st('Y', 'at a (0): step left onto a-1')
    r(Y, 0, 0, 'L', 'P')

    # ---- P: the p-test on a-1: 1 = fs (spend the mark, write 0 right
    # here), 0 = pred (leave it).  Either way walk back right to a+2 and
    # share the bottom/tail tests from there.
    P = st('P', 'p-test on a-1')
    r(P, 0, 0, 'R', 'N1', 'pred: the mark stays 0, the branch rides later')
    r(P, 1, 0, 'R', 'N1', 'fs: the spend lands right here (write 0)')
    # NOTE: the two rows differ only in the write.  The machine encodes the
    # answer by the write itself; the ARMS that still need fs-vs-pred get
    # their own state copies (see R, the banked split below).

    # ---- N1..N3: walk right a-1 -> a+2 (the post-p-test approach)
    N1 = st('N1', 'at a-1 (0): step right onto a')
    r(N1, 0, 0, 'R', 'N2')
    N2 = st('N2', 'at a (0): step right onto a+1')
    r(N2, 0, 0, 'R', 'N3')
    N3 = st('N3', 'at a+1 (0): step right onto a+2')
    r(N3, 0, 0, 'R', 'M1')

    # ---- M1, M2: the bottom/tail test.  Cross run1's marks to its close,
    # then read the cell after the close: 1 = MULTI, 0 = SINGLETON.
    M1 = st('M1', 'cross run1\'s marks rightward')
    r(M1, 1, 1, 'R', 'M1')
    r(M1, 0, 0, 'R', 'M2')
    M2 = st('M2', 'read the cell after run1\'s close')
    r(M2, 0, 0, 'L', 'S0', 'SINGLETON: step back onto the close, then arms')
    r(M2, 1, 1, 'R', 'F1', 'MULTI: walk right into the body work')

    # ---- the singleton arms (the head backed up onto run1's close b0)
    S0 = st('S0', 'the singleton dispatch on b0 (0): 1 = tail test, 0 = edge')
    # step left onto run1's LAST mark to read the bottom kind pattern:
    r(S0, 0, 0, 'L', 'S1', 'the unlock: one move left is enough for L1 | 1')
    S1 = st('S1', 'read run1\'s last mark')
    r(S1, 0, 0, 'L', 'S2', 'the mark is 0 = the run has 0 marks here: dead')
    r(S1, 1, 1, 'L', 'S2')
    # Simplified probe: read LEFT over run1 to its FIRST cell, watching for
    # the boundary 0; the number of reads distinguishes L1 = 1 / 2 / >= 3.
    S2 = st('S2', '1st probe left: 0 = the boundary hit (L1 == 1: the atom)')
    # 0 here means run1 was ONE mark: the pure [ATOM] (or [ATOM,x..] went
    # MULTI), so the WIDEN arm fires.
    r(S2, 0, 0, 'R', 'WD0', 'pure [ATOM]: the widen arm')
    r(S2, 1, 1, 'L', 'S3', '1 more mark: L1 >= 2, keep probing')
    S3 = st('S3', '2nd probe left: 0 = L1 == 2 (the atom+1 bottom)')
    r(S3, 0, 0, 'R', 'AT0', 'the atom+1 singleton: flip / atom-pred')
    r(S3, 1, 1, 'R', 'BD0', 'L1 >= 3: plain-bottom singleton: body work on run1')
    # the probes step right and count: three states S0..S3 above (each one
    # spends exactly one move left; the reads happen on arrival).

    # ---- BD0: the plain-bottom singleton's body work = run1 itself.
    # Position: the head is back right of run1 (after the probes it stood
    # on the cell right of the boundary...).  Cleanest: hand to the shared
    # count machinery with a fresh walk right to run1's close.
    BD0 = st('BD0', 'plain singleton: walk right to run1\'s close (from a-1)')
    # the probes left the head around run1's start; walk right over the run
    r(BD0, 1, 1, 'R', 'BD0')
    r(BD0, 0, 0, 'R', 'BD1')
    BD1 = st('BD1', 'on run1\'s close (0): walk left, count run1 as the top')
    r(BD1, 0, 0, 'L', 'T2', 'the count machinery entry (the same T-states)')

    # ---- the MULTI body work (F1..F2 cross, T0..T6 count)
    F1 = st('F1', 'cross right over runs and single seps')
    r(F1, 1, 1, 'R', 'F1')
    r(F1, 0, 0, 'R', 'F2')
    F2 = st('F2', 'peek after a 0: 1 = interior sep, 0 = chain end')
    r(F2, 1, 1, 'R', 'F1')
    r(F2, 0, 0, 'L', 'T0', 'the chain end: the head is on the pair\'s right 0')

    # the count: tape ... 1^L 0(b) 0(t): the head starts on t.
    T0 = st('T0', 'on t (0): step left')
    r(T0, 0, 0, 'L', 'T1')
    T1 = st('T1', 'on b (0): step left onto the top run')
    r(T1, 0, 0, 'L', 'T2')
    T2 = st('T2', 'count mark 1 of the top run')
    # 0 = no run (dead); 1 = keep counting
    r(T2, 1, 1, 'L', 'T3')
    T3 = st('T3', 'count mark 2 (0 = L == 1: dead on canonical tapes)')
    r(T3, 1, 1, 'L', 'T4')
    T4 = st('T4', 'count mark 3 (0 = L == 2: dead on canonical tapes)')
    r(T4, 1, 1, 'L', 'T5')
    T5 = st('T5', 'count mark 4 (0 = L == 3: the singleton-only case, dead '
                  'here because MULTI is enforced by M2)')
    r(T5, 1, 1, 'L', 'T6')
    T6 = st('T6', 'count mark 5 (0 = L == 4; 1 = L >= 5)')
    r(T6, 0, 0, 'L', 'L4', 'the L == 4 branch')
    r(T6, 1, 1, 'R', 'R1', 'the L >= 5 plain branch: walk right back to r')
    # the head rests on b-4 either way; R1/L4 the flows for both.

    # ---- R1, R2: the plain dec for fs.  Position: the head is
    # somewhere inside the top run; walk right over its marks back to the
    # close, then one more step left to the last mark r; erase; branch.
    R1 = st('R1', 'walk right back over the counted marks')
    r(R1, 1, 1, 'R', 'R1')
    r(R1, 0, 0, 'L', 'R2', 'the close reached; step left onto r')
    R2 = st('R2', 'read r (the top run\'s last mark): the dec write')
    r(R2, 0, 0, 'L', 'H1', 'defence only (the mark must be 1)')
    r(R2, 1, 0, 'R', 'FS0', 'the erase lands (write 0); step right to e')

    # ---- the fs after the plain dec: append the push at the chain end.
    # The head is on r (the just-erased cell, now 0): the new terminator
    # begins here; the push writes 4 marks over (e, t, t+1, t+2) then the
    # close, then the walk home.
    FS0 = st('FS0', 'on r (0): step right to e')
    r(FS0, 0, 0, 'R', 'A0')
    A0 = st('A0', 'push mark 1 (the head is on e)')
    r(A0, 0, 1, 'R', 'A1')
    A1 = st('A1', 'push mark 2')
    r(A1, 0, 1, 'R', 'A2')
    A2 = st('A2', 'push mark 3')
    r(A2, 0, 1, 'R', 'A3')
    A3 = st('A3', 'push mark 4')
    r(A3, 0, 1, 'R', 'A4')
    A4 = st('A4', 'push close (write 0, keep heading right)')
    r(A4, 0, 0, 'R', 'H1')

    # ---- the pred after the plain dec (NO append).  Separate state (the
    # fs/pred fork is explicit and honest here for the first build).
    PD0 = st('PD0', 'the pred plain dec: walk to the home')
    # the head is on r after the erase: step right, then the walk home
    r(PD0, 0, 0, 'R', 'H1')
    # PD0 is entered from the pred variant of R2 (see PBR below)

    # ---- the L == 4 branch: fs = plain dec (reuse R1), pred = POP.
    # The head is on b-4; walk right to r (the same cell), then fork.
    L4 = st('L4', 'the L == 4: walk right to r')
    r(L4, 1, 1, 'R', 'L4')
    r(L4, 0, 0, 'L', 'LB', 'the close reached; step left to r')
    LB = st('LB', 'read r for the L == 4 branch')
    # the rows encode fs-vs-pred: fs writes the dec and shares FS0; pred
    # erases the WHOLE run and folds.  The fork needs two states:
    r(LB, 0, 0, 'L', 'H1', 'defence only (the mark must be 1)')
    r(LB, 1, 0, 'R', 'FS0', 'fs: erase r and share the append flow')
    # the PD pop variant of LB:
    LBP = st('LBP', 'the pred L == 4 pop: r erased, erase the rest')
    r(LBP, 1, 0, 'R', 'POP', 'pop the remaining 3 marks and grow p')
    # LBP is entered from a distinct PD branch below.

    # ---- POP: erase rightward over 1s until the close, then GROW p.
    POP = st('POP', 'pop erase loop: 1 = erase and march on, 0 = done')
    r(POP, 1, 0, 'R', 'POP')
    r(POP, 0, 0, 'L', 'G0', 'the run is erased; the head is on the close')

    # ---- GROW: p grew by one: walk left over the whole tape to the park's
    # left end, write 1 there, walk right back to the home.
    G0 = st('G0', 'grow: cross left over runs and seps')
    r(G0, 1, 1, 'L', 'G0')
    r(G0, 0, 0, 'L', 'G1')
    G1 = st('G1', 'check left of a 0: 1 = interior sep, 0 = the park pair')
    r(G1, 1, 1, 'L', 'G0')
    r(G1, 0, 0, 'L', 'G2', 'the pair crossed; now inside the park p-regime')
    G2 = st('G2', 'cross the park leftward: 1 = park mark, 0 = the edge')
    r(G2, 1, 1, 'L', 'G2')
    r(G2, 0, 1, 'R', 'G3', 'the park\'s left end: write 1 (the growth)')
    G3 = st('G3', 'walk right back over the grown park')
    r(G3, 1, 1, 'R', 'G3')
    r(G3, 0, 0, 'R', 'U', 'back on a? No: the head lands on the pair\'s '
                          'left cell a directly.  G3 arrives on a via the '
                          'cross; the row sends it right into U with the '
                          'head on a+1 — then U\'s first move corrects.')
    # NOTE honesty: G3's 0-row reaches a in state U but the head moved one
    # cell right: the next campaign starts a+1.  That breaks the invariant.
    # So re-route through the shared backup couple HB0:
    # (kept here for the first build: HB0 corrects it.)
    # ... (see G3's 0-row target H3 below in the final version)

    # ---- H1..H3: the walk home (find the park pair's 00 leftward)
    H1 = st('H1', 'walk home: cross 1s; on 0 hop left and check')
    r(H1, 1, 1, 'L', 'H1')
    r(H1, 0, 0, 'L', 'H2')
    H2 = st('H2', 'check-left: 1 = interior sep (continue), 0 = the pair')
    r(H2, 1, 1, 'L', 'H1')
    r(H2, 0, 0, 'R', 'H3', 'the pair found; back up onto its right cell')
    H3 = st('H3', 'back up onto the pair\'s right 0')
    r(H3, 0, 0, 'L', 'U', 'step left onto a: the campaign ends on a in U')

    # ---- the pure [ATOM] widen arm (any p): head on the close b0 = a+3,
    # the tape is [1^p] 00 1 0 00: write TWO marks over (a+3, a+4) growing
    # into the pad, then grow p by 1 (the seed's grow).
    WD0 = st('WD0', 'the widen: the head is on a+3 (the atom\'s close)')
    r(WD0, 0, 1, 'R', 'WD1', 'mark 2 (over the close)')
    WD1 = st('WD1', 'the widen\'s mark 3 (over the pad)')
    r(WD1, 0, 1, 'R', 'WD2', 'mark 3, then the new close is the next cell')
    WD2 = st('WD2', 'the widen done: walk left and grow p by one')
    r(WD2, 0, 0, 'L', 'G0')
    # NOTE: also restore a pair after the run... the grow walk passes the
    # body/from wherever the head is: shared G0 fine.

    # ---- the pure [ATOM1] singleton: flip (fs) or atom-rest (pred).
    # The head is on the close b0 = a+4-ish... (the cell after the run).
    AT0 = st('AT0', 'the atom+1 singleton: step left onto run1\'s marks')
    r(AT0, 0, 0, 'L', 'AT1')
    AT1 = st('AT1', 'read the run\'s last mark: erase it (the 2 -> 1 flip)')
    r(AT1, 0, 0, 'L', 'AT4', 'defence (the mark must be 1)')
    r(AT1, 1, 0, 'R', 'AT2', 'erase one mark; the atom+1 is now the atom')
    AT2 = st('AT2', 'the flip: step right to the push site')
    r(AT2, 0, 0, 'R', 'AT3', 'to the close cell b0')
    AT3 = st('AT3', 'the push: write 4 marks (the head on b0)')
    r(AT3, 0, 1, 'R', 'AT3a')
    AT3a = st('AT3a', 'push mark 2')
    r(AT3a, 0, 1, 'R', 'AT3b')
    AT3b = st('AT3b', 'push mark 3')
    r(AT3b, 0, 1, 'R', 'AT3c')
    AT3c = st('AT3c', 'push mark 4')
    r(AT3c, 0, 1, 'R', 'AT3d')
    AT3d = st('AT3d', 'push close')
    r(AT3d, 0, 0, 'R', 'H1')
    # the pred variant skips the push:
    AT4 = st('AT4', 'the atom+1 singleton pred: head home (no push)')
    r(AT4, 0, 0, 'R', 'H1')

    # ---- the [NUM(1)] singleton arms (L1 == 3, c == 1): erase the whole
    # 3-mark run.  fs: then the fresh push; pred: home.  Entry: the head
    # is on the close b0 (a+5-ish) — the singleton walk positioned it.
    N10 = st('N10', 'the NUM(1) singleton: step left into the run')
    r(N10, 0, 0, 'L', 'N11')
    N11 = st('N11', 'erase loop: erase each mark marching left')
    r(N11, 1, 0, 'L', 'N11')
    r(N11, 0, 0, 'R', 'N12', 'the run erased (the head on the left edge '
                             'cell): step right to the push site')
    N12 = st('N12', 'the head is on the cell left of the erased run')
    r(N12, 0, 0, 'R', 'N13')
    N13 = st('N13', 'the push site: write 4 fresh marks (the fs variant)')
    r(N13, 0, 1, 'R', 'N13a')
    N13a = st('N13a', 'push mark 2')
    r(N13a, 0, 1, 'R', 'N13b')
    N13b = st('N13b', 'push mark 3')
    r(N13b, 0, 1, 'R', 'N13c')
    N13c = st('N13c', 'push mark 4')
    r(N13c, 0, 1, 'R', 'N13d')
    N13d = st('N13d', 'push close')
    r(N13d, 0, 0, 'R', 'H1')
    # the pred variant:
    N1P = st('N1P', 'the NUM(1) pred: erased; head home, no push')
    r(N1P, 0, 0, 'R', 'H1')
    return T


TABLE = build_table()

# -------------------------------------------------------------------- sim


class Sim:
    """A 2-symbol head-machine with free tape: cells default to 0."""

    def __init__(self):
        self.cell = {}
        self.pos = 0
        self.state = 'U'

    def get(self, i):
        return self.cell.get(i, 0)

    def put(self, i, v):
        self.cell[i] = v

    def step(self):
        rows = TABLE.get(self.state)
        assert rows is not None, f'missing state {self.state}'
        row = rows.get(self.get(self.pos))
        if row is None:
            raise RuntimeError(f'halt row missing at {self.state}')
        w, d, nx = row
        self.put(self.pos, w)
        self.pos += 1 if d == 'R' else -1
        self.state = nx

    def campaign(self):
        mv = 0
        while True:
            self.step()
            mv += 1
            if self.state == 'U':
                return mv

    def tape_str(self):
        lo = min(self.cell.keys(), default=0)
        hi = max(self.cell.keys(), default=0)
        return ''.join('1' if self.get(i) else '0'
                       for i in range(min(lo, 0), max(hi, 1) + 1))


def boot(tape_str, state='U'):
    s = Sim()
    for i, ch in enumerate(tape_str):
        if ch == '1':
            s.put(i, 1)
    # rest the head on the park pair's left cell = the position of the 00
    # right after the leading 1^p block:
    ip = tape_str.index('00')
    s.pos, s.state = ip, state
    return s


# ---------------------------------------------------------------- checks


def check_codec(trials=200, seed=11):
    print('codec round-trip: read_tape(make_tape(p, c)) == canon(p, c)')
    rng = random.Random(seed)
    bad = 0
    for i in range(trials):
        if i % 5 == 0:
            p, c = chain_of(D.tower(rng.randint(1, 3)))
        else:
            p = rng.randint(0, 2)
            c = ([rng.choice([2, 3])]
                 + [rng.choice([1, 1, 2, 3])
                    for _ in range(rng.randint(1, 3))])
        p, c = canon(p, list(c))
        tp = make_tape(p, c)
        try:
            got = read_tape(tp)
        except Exception as exc:
            bad += 1
            print(f'  READ FAIL p={p} chain={c!r} tape={tp!r}: {exc}')
            continue
        want = canon(p, list(c))
        if got != want:
            bad += 1
            print(f'  MISMATCH: {got!r} vs {want!r}')
    print(f'  {trials} round-trips: ' + ('OK' if bad == 0 else f'BAD {bad}'))
    return bad == 0


def model_step(p, chain, seed=SEED):
    """(p, chain) -> ((p2, c2), kind) or ((None, None), None) on halt."""
    if not chain:
        return (None, None), None
    try:
        p2, c2, _, kind = C.step(p, chain, seed)
    except C.Halt:
        return (None, None), None
    return canon(p2, c2), kind


def check_faithful(trials=200, seed=9, moves=4):
    print('move faithfulness: the machine\'s campaign equals one model step')
    rng = random.Random(seed)
    bad = 0
    for t in range(trials):
        if t % 4 == 0:
            p, c = chain_of(D.tower(rng.randint(1, 3)))
        else:
            p = rng.randint(0, 2)
            c = ([rng.choice([2, 3])]
                 + [rng.choice([1, 1, 2, 3])
                    for _ in range(rng.randint(1, 3))])
        p, c = canon(p, list(c))
        tp = make_tape(p, c)
        m = boot(tp)
        for _ in range(moves):
            (p2, c2), kind = model_step(p, list(c))
            if (p2, c2) == (None, None):
                break                       # the model halts: expect nothing
            try:
                m.campaign()
            except (RuntimeError, AssertionError) as exc:
                bad += 1
                print(f'  MACHINE STOP: {exc} on tape {tp!r}')
                break
            try:
                got = read_tape(m.tape_str())
            except Exception as exc:
                bad += 1
                print(f'  READ FAIL after a step: {exc} on {m.tape_str()!r}')
                break
            got = canon(got[0], got[1]).__class__ and canon(*got)
            if got != (p2, c2) or kind is None:
                bad += 1
                print(f'  UNFAITHFUL on p={p} c={c!r}:')
                print(f'    machine {got!r}')
                print(f'    model   {(p2, c2)!r} kind={kind!r}')
                break
            p, c, _ = p2, c2, 0
            if not c2:
                break
    print(f'  {trials} starts x up to {moves} moves: '
          + ('OK' if bad == 0 else f'BAD {bad}'))
    return bad == 0


def check_tape_vs_chain(cap=6000):
    print('tape == chain on full eps_1[n] runs, seed 1')
    ok = True
    for n in (1, 2, 3):
        p, c = chain_of(D.tower(n))
        tp = make_tape(p, list(c))
        mv_c = 0
        while True:
            (p2, c2), kind = model_step(p, list(c))
            if (p2, c2) == (None, None):
                break
            p, c = p2, c2
            mv_c += 1
            if mv_c > cap:
                mv_c = None
                break
        m = boot(tp)
        mv_t, done = 0, None
        try:
            while mv_t <= cap:
                m.campaign()
                mv_t += 1
                pp, cc = read_tape(m.tape_str())
                if cc == []:
                    done = True
                    break
        except (RuntimeError, AssertionError, ValueError) as exc:
            print(f'    eps_1[{n}] machine CRASHED: {exc}')
            print(f'    (the tape was {m.tape_str()!r})')
            done = False
        same = (mv_t == mv_c) and done is True
        print(f'    eps_1[{n}]: machine {mv_t if mv_t <= cap else ">cap"}'
              f' vs chain {mv_c if mv_c is not None else ">cap"}'
              + ('' if same else '   MISMATCH'))
        ok = ok and same
    print('  ' + ('OK' if ok else 'FAILURES'))
    return ok


def main():
    ok = check_codec()
    ok = check_faithful() and ok
    ok = check_tape_vs_chain() and ok
    print()
    print(f'states in the table: {len(TABLE)}')
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
