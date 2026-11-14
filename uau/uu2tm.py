#!/usr/bin/env python3
"""
uu2tm.py -- compile a 2-symbol Turing machine that runs the greedy 0-indexed
U.a.U-avoiding sequence over the integers and halts iff it places the symbol 5.

Because nobody knows whether a 5 is ever placed, the generated machine is a
cryptid: its halting behaviour is equivalent to an open problem.

--------------------------------------------------------------------------
Tape (2 symbols: 0 = blank, 1)
--------------------------------------------------------------------------
The machine is written as a "virtual" machine over an 8-letter alphabet
{0,U,A,B,S,C,E,x} and compiled down to two symbols by spending 3 tape cells
per virtual cell:

    virtual cell v  ==  physical cells (MSB first)  b2 b1 b0   of v

so virtual 0 is physical "000" == blank, i.e. blank is 0 and the tape outside
the used region reads as a run of virtual 0 (= 0) cells.

The virtual tape holds one region, bounded on the left by the wall S and on the
right by the end marker E.  Between them the sequence is stored in unary with
one delimiter cell per symbol:

    S  D0  U^(1+v0)  D1  U^(1+v1)  D2  ...  D(n-1)  U^(1+v(n-1))  Dn  E

with every D_j a virtual-0 cell.  A symbol of value v is a block of v+1 ones,
so blocks are never empty, a delimiter is always exactly one cell, and the
delimiter of a symbol doubles as the position marker of that symbol.  Internal
delimiters carry markers while the checker runs:

    A, B   anchors: the two block starts of the candidate factor U a U
    C, X   the same two positions, walking right during one comparison

Appending c to a word w of length N is legal iff there is no m >= 1 with

    w'[N-2m-1+t] == w'[N-m+t]   for t = 0 .. m-1     (w' = w + c)

because such an m makes w' end in U a U with U = w'[N-2m-1 : N-m-1].
Mismatches pull A two symbols left and B one symbol left, which is exactly
m -> m+1, so no counter is needed anywhere in the machine.

Deliverable 1 of the request is this encoding; deliverable 2 is this script,
which prints the complete 5-tuple set (deliverable 3 is the self-test below).

Run:   python uu2tm.py            # self-test + writes uu.tm
--------------------------------------------------------------------------
"""

import sys

# ---------------------------------------------------------------------------
# virtual alphabet
# ---------------------------------------------------------------------------
Z, U, A, B, S, C, E, X = range(8)          # 0 = blank / delimiter
VNAME = "0UAB SCE"                          # only for pretty printing
VCH = {Z: "0", U: "u", A: "A", B: "B", S: "S", C: "c", E: "E", X: "x"}


# ---------------------------------------------------------------------------
# 1. the sequence, straight from the definition (reference implementation)
# ---------------------------------------------------------------------------
def creates_uuaw(w, c):
    """True iff appending c to w creates a factor U a U (|U|>=1, |a|=1)."""
    v = list(w) + [c]
    n = len(v)
    for m in range(1, (n - 1) // 2 + 1):
        # U a U ends at the last cell: first U = v[n-2m-1:n-m-1],
        # a = v[n-m-1], last U = v[n-m:n]
        if v[n - 2 * m - 1:n - m - 1] == v[n - m:n]:
            return True
    return False


def creates_uuaw_sym(w, c):
    """Same predicate, in the symmetric form the machine implements.

    U a U ending at the last cell means: there is a centre p with
    v[p-i] == v[p+i] for i = 1..(n-1-p)  and  p-(n-1-p) >= 0.
    """
    v = list(w) + [c]
    n = len(v)
    for p in range(0, n - 1):
        m = n - 1 - p
        if p - m < 0:
            continue
        if all(v[p - i] == v[p + i] for i in range(1, m + 1)):
            return True
    return False


def reference(nsym):
    """First nsym symbols of the greedy sequence (smallest non-negative
    integer c in {0..5} whose appending creates no U a U)."""
    s = [0]
    while len(s) < nsym:
        for c in range(6):
            if not creates_uuaw(s, c):
                s.append(c)
                break
        else:                       # pragma: no cover - never happens
            raise RuntimeError("all candidates rejected at index %d" % len(s))
    return s


# ---------------------------------------------------------------------------
# 2. the virtual machine (8 symbols, one tape, markers)
# ---------------------------------------------------------------------------
class VTM:
    def __init__(self):
        self.tr = {}                                  # (state, sym) -> (wr, mv, nxt)

    def set(self, st, sy, wr, mv, nx):
        self.tr[(st, sy)] = (wr, mv, nx)

    def go(self, st, mv, nx):
        """unconditional: keep the symbol, move, change state"""
        for s in range(8):
            self.set(st, s, s, mv, nx)

    def wr(self, st, sy, mv, nx):
        """unconditional: write sy, move, change state"""
        for s in range(8):
            self.set(st, s, sy, mv, nx)

    def scan(self, st, mv, stops):
        """move while the symbol is not in stops; on a stop symbol dispatch
        without moving"""
        for s in range(8):
            if s in stops:
                self.set(st, s, s, "N", stops[s])
            else:
                self.set(st, s, s, mv, st)

    def rest(self, st, nx):
        """all still-undefined symbols: no move, go to nx"""
        for s in range(8):
            if (st, s) not in self.tr:
                self.set(st, s, s, "N", nx)

    def uskip(self, st, mv):
        """inside a unary block: walk over the 1-cells; stop on the first
        non-U cell and go to st+'!' without moving"""
        for s in range(8):
            if s == U:
                self.set(st, s, s, mv, st)
            else:
                self.set(st, s, s, "N", st + "!")

    def at_delim(self, st, onS, nx):
        """sitting on a delimiter: S means 'ran off the left end'"""
        for s in range(8):
            if s == S:
                self.set(st, s, s, "N", onS)
            else:
                self.set(st, s, s, "N", nx)


def build(halt_on):
    """Virtual machine.

    Layout invariant:      S  (D_j U^(1+v_j))*  D_n  E
    The machine keeps looping:
        append candidate 0, test, if forbidden roll it back and try 1, ... 5
        if a candidate survives it stays on the tape; on 5 the machine halts
        (for the shipped machine halt_on == 5).
    'halt_on' is a parameter so the same code can be proved to halt at the
    first occurrence of 1, 2, 3 ... during self-testing.
    """
    m = VTM()

    # ---------------- main loop: append candidate c -----------------------
    m.scan("TOP", "R", {E: "APP0"})                 # walk to the end marker
    for c in range(6):
        m.set("APP%d" % c, E, U, "R", "APP%d#%d" % (c, 1))   # 1st one of block
        m.rest("APP%d" % c, "TRAP")           # only reachable on the end marker
        for k in range(1, c + 1):                            # c more ones
            m.wr("APP%d#%d" % (c, k), U, "R", "APP%d#%d" % (c, k + 1))
        m.wr("APP%d#%d" % (c, c + 1), Z, "R", "APP%dZ" % c)  # new delimiter
        m.wr("APP%dZ" % c, E, "N", "CHK1")                   # new end marker

    # ---------------- locate the m = 1 anchors ----------------------------
    #  condition(m):  w'[N-2m-1+t] == w'[N-m+t]   for t = 0..m-1
    #  A marks D_(N-2m-1) (left end of the first U), B marks D_(N-m)
    #  (left end of the last U).  C and X are the walking copies of A and B.
    m.go("CHK1", "L", "CHK2")            # E -> D_N
    m.go("CHK2", "L", "H1s")
    m.uskip("H1s", "L")                  # -> D_(N-1)
    m.at_delim("H1s!", "NOPE", "RB")
    m.wr("RB", B, "N", "H2")
    m.go("H2", "L", "H2s")
    m.uskip("H2s", "L")                  # -> D_(N-2)
    m.at_delim("H2s!", "NOPE", "H3")
    m.go("H3", "L", "H3s")
    m.uskip("H3s", "L")                  # -> D_(N-3)
    m.at_delim("H3s!", "NOPE", "RA")
    m.wr("RA", A, "N", "STAGE0")

    # ---------------- t = 0 : compare the two anchors ---------------------
    m.scan("STAGE0", "L", {A: "SA0"})
    m.go("SA0", "R", "AL0")
    m.set("AL0", U, U, "R", "AL1")       # a block always starts with a one
    m.rest("AL0", "TRAP")
    for k in range(1, 7):
        st = "AL%d" % k
        if k < 6:
            m.set(st, U, U, "R", "AL%d" % (k + 1))
        else:
            m.set(st, U, U, "N", "TRAP")          # seven ones cannot happen
        m.rest(st, "TOB%d" % k)
    for k in range(1, 7):
        m.scan("TOB%d" % k, "R", {B: "BL%d0" % k})
        m.go("BL%d0" % k, "R", "BL%dw" % k)        # step onto the first one
        m.set("BL%dw" % k, U, U, "R", "BL%d1" % k)
        m.rest("BL%dw" % k, "TRAP")
        for j in range(1, 7):
            st = "BL%d%d" % (k, j)
            if j < 6:
                m.set(st, U, U, "R", "BL%d%d" % (k, j + 1))
            else:
                m.set(st, U, U, "N", "TRAP")
            m.rest(st, "Q0_%d_%d" % (k, j))
        for j in range(1, 7):
            m.go("Q0_%d_%d" % (k, j), "N", "LAST0" if j == k else "FAILST")

    m.go("LAST0", "R", "PZ0")
    m.set("PZ0", E, E, "N", "FOUND")     # B was the last symbol -> U a U !
    m.rest("PZ0", "NEWW")

    # ---------------- t >= 1 : walk both pointers to the right ------------
    m.scan("NEWW", "L", {A: "NW1"})
    m.go("NW1", "R", "NW1s")
    m.uskip("NW1s", "R")                 # -> D_(L0+1)
    m.wr("NW1s!", C, "N", "NW2")
    m.scan("NW2", "R", {B: "NW3"})
    m.go("NW3", "R", "NW3s")
    m.uskip("NW3s", "R")                 # -> D_(R0+1)
    m.wr("NW3s!", X, "N", "STAGE1")

    m.scan("STAGE1", "L", {C: "CL0"})
    m.go("CL0", "R", "CL00")
    m.set("CL00", U, U, "R", "CL1")
    m.rest("CL00", "TRAP")
    for k in range(1, 7):
        st = "CL%d" % k
        if k < 6:
            m.set(st, U, U, "R", "CL%d" % (k + 1))
        else:
            m.set(st, U, U, "N", "TRAP")
        m.rest(st, "TOX%d" % k)
    for k in range(1, 7):
        m.scan("TOX%d" % k, "R", {X: "XL%d0" % k})
        m.go("XL%d0" % k, "R", "XL%dw" % k)
        m.set("XL%dw" % k, U, U, "R", "XL%d1" % k)
        m.rest("XL%dw" % k, "TRAP")
        for j in range(1, 7):
            st = "XL%d%d" % (k, j)
            if j < 6:
                m.set(st, U, U, "R", "XL%d%d" % (k, j + 1))
            else:
                m.set(st, U, U, "N", "TRAP")
            m.rest(st, "Q1_%d_%d" % (k, j))
        for j in range(1, 7):
            m.go("Q1_%d_%d" % (k, j), "N", "LAST1" if j == k else "FAILST")

    m.go("LAST1", "R", "PZ1")
    m.set("PZ1", E, E, "N", "FOUND")
    m.rest("PZ1", "STEPW")

    # ---------------- advance the walking pointers ------------------------
    m.scan("STEPW", "L", {C: "SW1"})
    m.wr("SW1", Z, "R", "SW1s")          # erase C, step into its block
    m.uskip("SW1s", "R")                 # -> D_(C+1)
    m.wr("SW1s!", C, "N", "SW2")
    m.scan("SW2", "R", {X: "SW3"})
    m.wr("SW3", Z, "R", "SW3s")          # erase X, step into its block
    m.uskip("SW3s", "R")                 # -> D_(X+1)
    m.wr("SW3s!", X, "N", "STAGE1")

    # ---------------- m failed: pull the anchors one step left ------------
    #   A moves two symbols left, B one symbol left.  Running into S means
    #   the blocks no longer fit, so no larger m can be a witness.
    m.scan("FAILST", "L", {S: "FS1"})
    m.set("FS1", C, Z, "R", "FS1")       # erase the walking pointers
    m.set("FS1", X, Z, "R", "FS1")
    m.set("FS1", E, E, "N", "FS2")
    m.set("FS1", Z, Z, "R", "FS1")
    m.set("FS1", U, U, "R", "FS1")
    m.set("FS1", A, A, "R", "FS1")
    m.set("FS1", B, B, "R", "FS1")
    m.set("FS1", S, S, "R", "FS1")
    m.scan("FS2", "L", {A: "FS3"})
    m.wr("FS3", Z, "L", "FS3s")          # erase A, step into previous block
    m.uskip("FS3s", "L")                 # -> D_(L0-1)
    m.at_delim("FS3s!", "NOPE", "FS4")
    m.go("FS4", "L", "FS4s")
    m.uskip("FS4s", "L")                 # -> D_(L0-2)
    m.at_delim("FS4s!", "NOPE", "FS5")
    m.wr("FS5", A, "N", "FS6")
    m.scan("FS6", "R", {B: "FS7"})
    m.wr("FS7", Z, "L", "FS7s")          # erase B, step into previous block
    m.uskip("FS7s", "L")                 # -> D_(R0-1)
    m.at_delim("FS7s!", "NOPE", "FS8")
    m.wr("FS8", B, "N", "STAGE0")

    # ---------------- verdicts -------------------------------------------
    for name, res in (("NOPE", "RES_OK"), ("FOUND", "RES_BAD")):
        m.scan(name, "L", {S: name + "1"})
        for s in (A, B, C, X):
            m.set(name + "1", s, Z, "R", name + "1")
        m.set(name + "1", E, E, "N", res)
        for s in (Z, U, S):
            m.set(name + "1", s, s, "R", name + "1")

    # ---------------- read back the candidate we appended -----------------
    for name, kind in (("RES_OK", "ok"), ("RES_BAD", "bad")):
        m.scan(name, "R", {E: name + "1"})
        m.go(name + "1", "L", name + "2")        # E -> D_N
        m.go(name + "2", "L", name + "3")        # -> inside last block
        m.uskip(name + "3", "L")                 # -> D_(N-1)
        m.go(name + "3!", "R", name + "4")       # -> first one of the block
        m.set(name + "4", U, U, "R", name + "5_1")
        m.rest(name + "4", "TRAP")
        for j in range(1, 7):                    # block length j -> value j-1
            st = "%s5_%d" % (name, j)
            if j < 6:
                m.set(st, U, U, "R", "%s5_%d" % (name, j + 1))
            else:
                m.set(st, U, U, "N", "TRAP")
            if kind == "ok":
                m.rest(st, "HALT" if (j - 1) == halt_on else "TOP")
            else:
                m.rest(st, ("UN%d" % (j - 1)) if (j - 1) < 5 else "STUCK")

    # ---------------- roll the rejected candidate back --------------------
    for c in range(6):
        m.scan("UN%d" % c, "R", {E: "UN%d_1" % c})
        m.go("UN%d_1" % c, "L", "UN%d_2" % c)    # E -> D_N
        m.go("UN%d_2" % c, "L", "UN%d_3" % c)    # -> inside last block
        m.uskip("UN%d_3" % c, "L")               # -> D_(N-1)
        m.go("UN%d_3!" % c, "R", "UN%d_4" % c)   # -> first one of the block
        m.wr("UN%d_4" % c, E, "R", "UN%d_e1" % c)  # put E back here
        for t in range(1, c + 3):                  # scrub c+2 leftover cells
            nxt = ("UN%d_e%d" % (c, t + 1)) if t < c + 2 else ("UN%d_bk" % c)
            m.wr("UN%d_e%d" % (c, t), Z, "R", nxt)
        m.scan("UN%d_bk" % c, "L", {E: "APP%d" % (c + 1)})   # back onto E

    # HALT, TRAP and STUCK get no transitions: the machine stops there.
    return m


# ---------------------------------------------------------------------------
# 3. compiler: virtual 8-symbol tape -> 2-symbol tape (3 cells per symbol)
# ---------------------------------------------------------------------------
def compile_phys(vtm):
    tr = {}                                   # (state, bit) -> (bit, 'L'/'R', state)

    def add(q, rd, wr, mv, nx):
        tr[(q, rd)] = (wr, mv, nx)

    for (q, s), (s2, mv, q2) in vtm.tr.items():
        b = [(s >> 2) & 1, (s >> 1) & 1, s & 1]
        w = [(s2 >> 2) & 1, (s2 >> 1) & 1, s2 & 1]
        # read the three cells of the code, moving right (cells 3k, 3k+1, 3k+2)
        add(q, b[0], b[0], "R", "%s|p1|%d" % (q, b[0]))
        add("%s|p1|%d" % (q, b[0]), b[1], b[1], "R",
            "%s|p2|%d%d" % (q, b[0], b[1]))
        add("%s|p2|%d%d" % (q, b[0], b[1]), b[2], b[2], "R", "%s|tb|%d" % (q, s))
        # head now on cell 3k+3, whose contents belong to the next symbol:
        # traverse it blindly, then write the new code walking back
        add("%s|tb|%d" % (q, s), 0, 0, "L", "%s|w1|%d" % (q, s))
        add("%s|tb|%d" % (q, s), 1, 1, "L", "%s|w1|%d" % (q, s))
        add("%s|w1|%d" % (q, s), b[2], w[2], "L", "%s|w2|%d" % (q, s))
        add("%s|w2|%d" % (q, s), b[1], w[1], "L", "%s|mv|%d" % (q, s))
        # carry out the virtual head move, ending on a code boundary
        st = "%s|mv|%d" % (q, s)                  # on cell 3k, reads old b[0]
        if mv == "N":                          # stay: step right, step back
            add(st, b[0], w[0], "R", "%s|nz|%d" % (q, s))
            add("%s|nz|%d" % (q, s), w[1], w[1], "L", q2)
        elif mv == "R":
            add(st, b[0], w[0], "R", "%s|r1|%d" % (q, s))
            add("%s|r1|%d" % (q, s), w[1], w[1], "R", "%s|r2|%d" % (q, s))
            add("%s|r2|%d" % (q, s), w[2], w[2], "R", q2)
        else:                                  # left: cells of the neighbour
            add(st, b[0], w[0], "L", "%s|l1|%d" % (q, s))
            for bit in (0, 1):
                add("%s|l1|%d" % (q, s), bit, bit, "L", "%s|l2|%d" % (q, s))
                add("%s|l2|%d" % (q, s), bit, bit, "L", q2)
    return tr


def start_tape():
    """virtual tape  S 0 E  ->  physical bits"""
    bits = []
    for v in (S, Z, E):
        bits += [(v >> 2) & 1, (v >> 1) & 1, v & 1]
    return bits


# ---------------------------------------------------------------------------
# 4. physical simulator + decoder
# ---------------------------------------------------------------------------
def decode(tape):
    hi = max(tape) if tape else 0
    bits = [tape.get(i, 0) for i in range(hi + 1)]
    out = []
    for k in range(0, len(bits) - 2, 3):
        out.append((bits[k] << 2) | (bits[k + 1] << 1) | bits[k + 2])
    return out


def parse_seq(virt):
    i = virt.index(S) + 1
    seq = []
    while True:
        if virt[i] != Z:
            raise ValueError("delimiter expected at virtual cell %d, got %d"
                             % (i, virt[i]))
        if i + 1 < len(virt) and virt[i + 1] == E:
            break
        j, n = i + 1, 0
        while j < len(virt) and virt[j] == U:
            n += 1
            j += 1
        seq.append(n - 1)
        i = j
    return seq


def run(tr, start, steps, probe_states=("TOP",)):
    tape = dict(enumerate(start_tape()))
    pos, st, n = 0, start, 0
    seen = []
    while n < steps:
        b = tape.get(pos, 0)
        if (st, b) not in tr:
            return "halt", st, n, tape, pos, seen
        w, mv, nxt = tr[(st, b)]
        tape[pos] = w
        pos += 1 if mv == "R" else -1
        st = nxt
        n += 1
        if st in probe_states:
            seen.append((n, parse_seq(decode(tape))))
    return "limit", st, n, tape, pos, seen


# ---------------------------------------------------------------------------
# 5. Morphett export
# ---------------------------------------------------------------------------
def export_morphett(tr, start, path):
    """Morphett format:  <state> <read> <write> <l|r> <next>, ';' starts a
    comment, '_' is blank, and the machine halts on a state named halt*."""
    halt_label = {"HALT": "halt", "TRAP": "halt-trap", "STUCK": "halt-stuck"}
    ids, order = {}, []

    def sid(q):
        if q not in ids:
            ids[q] = halt_label.get(q, str(len(order)))
            order.append(q)
        return ids[q]

    sid(start)                       # the start state must be called 0
    for (q, b) in sorted(tr):
        sid(q)
        sid(tr[(q, b)][2])

    head = ["; greedy U.a.U-avoiding sequence, 2 symbols {1, _}, blank = _",
            "; start state 0, tape below, 'halt' <=> a 5 was placed",
            "; virtual symbols S,0,u,A,B,c,E,x are 3 tape cells each",
            "; (comments after a semicolon are ignored by the simulator)",
            ";",
            "; initial tape: " + bits_to_string(start_tape())]
    for q in order:
        if "|" not in q:             # only the virtual (boundary) states
            head.append("; state %s = %s" % (ids[q], q))
    head.append("")
    for (q, b) in sorted(tr):
        w, mv, nx = tr[(q, b)]
        head.append("%s %s %s %s %s" % (ids[q], "1" if b else "_",
                                        "1" if w else "_", mv.lower(),
                                        ids[nx]))
    with open(path, "w") as f:
        f.write("\n".join(head))
        f.write("\n")
    return len(order), len(tr), ids[start]


def bits_to_string(bits):
    return "".join("1" if b else "_" for b in bits)


# ---------------------------------------------------------------------------
# 6. self-test
# ---------------------------------------------------------------------------
def main():
    ref = reference(80)
    print("reference prefix (literal definition):", ref[:12])
    print("example prefix from the request      : [0, 0, 1, 0, 0, 1, 2]")
    bad = [w for w in ([0, 0, 1, 0],) if creates_uuaw(w[:-1], w[-1])]
    print("  -> 0,0,1,0 already contains U a U (U=0, a=1, U=0);")
    print("     so that example is inconsistent with the stated rule.")
    print("     cross-check symmetric form:",
          all(creates_uuaw(ref[:i], ref[i]) == creates_uuaw_sym(ref[:i], ref[i])
              for i in range(1, 9)))
    print()

    # every virtual state must be total (except the three halting ones)
    m0 = build(5)
    states = {q for (q, s) in m0.tr}
    holes = [(q, s) for q in states for s in range(8) if (q, s) not in m0.tr]
    bad = [q for q in states if q not in ("HALT", "TRAP", "STUCK")
           and any((q, s) not in m0.tr for s in range(8))]
    print("virtual machine: %d states, %d tuples, undefined entries: %d"
          % (len(states), len(m0.tr), len(holes)))
    print("non-halting states with a missing transition:", bad)
    ok = (not bad and not holes)

    for halt_on in (0, 1, 2, 3):
        want = ref[:ref.index(halt_on) + 1]
        tr = compile_phys(build(halt_on))
        res, st, n, tape, pos, seen = run(tr, "TOP", 40_000_000)
        got = parse_seq(decode(tape))
        good = (res == "halt" and got == want)
        ok &= good
        print("machine halting on %d : %-5s steps=%d  tape=%s"
              % (halt_on, res, n, parse_seq(decode(tape))))
        print("    expected sequence %s\n    machine sequence  %s   %s"
              % (want, got, "OK" if good else "MISMATCH"))

    # the shipped machine halts on 5.  Whether a 5 ever appears is open, so
    # the expected behaviour is: keep writing the true prefix, never halt.
    tr5 = compile_phys(build(5))
    budget = 4_000_000
    res, st, n, tape, pos, seen = run(tr5, "TOP", budget)
    got = seen[-1][1] if seen else []
    print("")
    print("machine halting on 5 : %-6s after %d of %d steps"
          % (res, n, budget))
    print("    symbols emitted   : %s" % (got,))
    print("    true prefix       : %s  ->  %s"
          % (ref[:len(got)], "OK" if got == ref[:len(got)] else "MISMATCH"))
    print("    halting state reached:", res == "halt")
    ok &= got == ref[:len(got)] and res != "halt"

    ns, nt, sid = export_morphett(tr5, "TOP", "uu.tm")
    print("\nwrote uu.tm : %d states, %d transition tuples" % (ns, nt))
    print("initial tape: %s" % bits_to_string(start_tape()))
    print("start state id:", sid)
    print("\nALL CHECKS PASSED" if ok else "\nSOMETHING FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
