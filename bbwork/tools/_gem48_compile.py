"""REJECTED 2026-11-04 round 13: this tag-on-departure family is INVALID.

The construction tries to store M's state as a per-cell tag written on
departure; but a TM step writes the cell it LEAVES, not the one it lands on,
so any revisited cell reads a stale tag (bisim failed at step 1 for every
grouping; the (1,96) extreme is impossible for the same reason: a 1-state
machine can only keep state in the symbol it just wrote, one cell behind
the head, and revisits outrun it). Kept as the record of a refuted idea.



Construction ("tag-on-arrival"):
  Compound cell = one M-cell; symbol = (bit, tag), tag in 0..g-1.
  Compound state = a group of g M-states (ceil(n/g) groups).
  Invariant: the tag at the head's cell always names the exact M-state to
  execute (written there by the previous step when it landed; the blank
  (0,0) decodes to S01 for the first step). Every step rewrites the landing
  cell with (M's write bit, tag of M's next state in its own group) -- both
  are fully determined by the executed row, so a stale tag is impossible.
  Result: 1 compound step per M step; halting time and head trajectory are
  IDENTICAL to the original; the tape bits are IDENTICAL (tags = scratch).

Verify: lockstep bisimulation against the original over 100,000 steps
(member, head, tape bits, halt step), plus the 2,000,000-step endpoint.

Run:  py -3.14 tools/_gem48_compile.py
"""
import re
import sys

V_PATH = 'rocq/gemini_epsilon1_tm_48s_v2_fix.v'

# ---------------------------------------------------------------- parse .v
src = open(V_PATH, encoding='utf-8').read()
rows = re.findall(
    r'\| (S\d{2}), B([01]) => \(B([01]), ([LR]), (?:St (S\d{2})|Halt)\)', src)
assert len(rows) == 96, len(rows)
TAB = {}
for q, br, w, d, nq in rows:
    q = str(int(q[1:]) - 1)              # S01 -> '0' ... S48 -> '47'
    TAB[(q, int(br))] = (int(w), d, 'halt' if nq == '' else str(int(nq[1:]) - 1))
STATES = sorted({int(q) for q, _ in TAB})
assert STATES == list(range(48))

# ---------------------------------------------------------------- symbols
POOL = ("123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        "abcdefghijklmnopqrstuvwxyz!#$%&()+-.:=<>?@[]^{}")
def symchar(b, t):
    if b == 0 and t == 0:
        return '_'                        # blank decodes to (bit0, tag0)
    return POOL[2 * t + b - 1]

def dechar(ch):
    if ch == '_':
        return (0, 0)
    i = POOL.index(ch)
    return ((i + 1) % 2, (i + 1) // 2)

# ---------------------------------------------------------------- compile
def partition(g):
    return [[str(i) for i in range(a, min(a + g, 48))]
            for a in range(0, 48, g)]

def compile_g(g):
    groups = partition(g)
    gid = {s: (gi, si) for gi, gr in enumerate(groups) for si, s in enumerate(gr)}
    n_groups = len(groups)
    hdr = ['; gem48 compiled: %d states, %d symbols (tag-on-arrival, 0 slowdown)'
           % (n_groups, 2 * g),
           '; groups: ' + ' | '.join(','.join(gr) for gr in groups),
           '; symbols: ' + ' '.join('%s=bit%d,tag%d' % (symchar(b, t), b, t)
                                    for b in (0, 1) for t in range(g)),
           '; start state 0 (morphett default), blank tape, head 0;'
           ' head-cell tag == exact gem48 S-state to execute']
    cans = []
    for gi, gr in enumerate(groups):
        for b in (0, 1):
            for t in range(len(gr)):
                m = gr[t]
                w, d, nx = TAB[(m, b)]
                if nx == 'halt':
                    nxt, wt = 'halt', 0    # landing tag never read again
                else:
                    gj, tj = gid[nx]
                    nxt, wt = str(gj), tj  # tag of next state in ITS group
                cans.append('%s %s %s %s %s'
                            % (gi, symchar(b, t), symchar(w, wt), d.lower(), nxt))
    for gi, gr in enumerate(groups):       # inert rows for tags beyond group size
        for b in (0, 1):
            for t in range(len(gr), g):
                cans.append('%s %s %s r %s' % (gi, symchar(b, t),
                                               symchar(b, t), gi))
    name = 'gem48_c%dx%dsym.txt' % (n_groups, 2 * g)
    with open(name, 'w', encoding='utf-8', newline='\n') as f:
        for h in hdr:
            f.write(h + '\n')
        for line in cans:
            f.write(line + '\n')
    return name, groups

# ---------------------------------------------------------------- sims
def parse_morphett(path):
    tab = {}
    for raw in open(path, encoding='utf-8'):
        line = raw.split(';')[0].strip()
        if not line:
            continue
        p = line.split()
        assert len(p) == 5, line
        q, rd, wr, d, nq = p
        nx = 'Halt' if nq.lower().startswith('halt') else nq
        assert (q, rd) not in tab, (q, rd)
        tab[(q, rd)] = (wr, d.upper(), nx)
    return tab

class Orig:
    """the original 2-symbol machine (same table TAB, names '0'..'47')."""
    def __init__(self):
        self.state, self.head = '0', 0
        self.bits = {}                      # pos -> 1 (else 0)
        self.steps = 0
        self.halted = None
    def step(self):
        b = self.bits.get(self.head, 0)
        w, d, nx = TAB[(self.state, b)]
        if w: self.bits[self.head] = 1
        else: self.bits.pop(self.head, None)
        self.head += 1 if d == 'R' else -1
        self.steps += 1
        if nx == 'halt':
            self.halted = self.steps
            self.state = 'halt'
        else:
            self.state = nx
    def run(self, n):
        while self.halted is None and self.steps < n:
            self.step()
        return self

class Compound:
    def __init__(self, tab):
        self.tab = tab
        self.state, self.head = '0', 0
        self.cells = {}                     # pos -> symbol string
        self.steps = 0
        self.halted = None
    def read(self):
        return self.cells.get(self.head, '_')
    def step(self):
        w, d, nx = self.tab[(self.state, self.read())]
        self.cells[self.head] = w
        self.head += 1 if d == 'R' else -1
        self.steps += 1
        if nx == 'Halt':
            self.halted = self.steps
            self.state = 'Halt'
        else:
            self.state = nx
    def run(self, n):
        while self.halted is None and self.steps < n:
            self.step()
        return self

# ---------------------------------------------------------------- verify
def bisim(name, groups, N):
    tab = parse_morphett(name)
    gid = {s: (gi, si) for gi, gr in enumerate(groups) for si, s in enumerate(gr)}
    mv, cs = Orig(), Compound(tab)
    while mv.halted is None and mv.steps < N:
        b, t = dechar(cs.read())            # what the compound is about to use
        gi, _ = gid[cs.state]
        m = groups[gi][t]                   # member the invariant claims
        if mv.state != m:
            print('  FAIL %s step %d: member %s but M-state %s'
                  % (name, mv.steps, m, mv.state))
            return False
        w, d, nx = TAB[(m, b)]              # M's actual row
        cw, cd, cnx = tab[(cs.state, cs.read())]
        wexp = symchar(w, 0 if nx == 'halt' else gid[nx][1])
        nexp = 'Halt' if nx == 'halt' else str(gid[nx][0])
        if (cw, cd, cnx) != (wexp, d.upper(), nexp):
            print('  FAIL %s step %d: compound row %s != expected (%s,%s,%s)'
                  % (name, mv.steps, (cw, cd, cnx), (wexp, d, nexp)))
            return False
        mv.step()
        cs.step()
        if mv.head != cs.head or mv.halted != cs.halted:
            print('  FAIL %s step %d: head/halt divergence' % (name, mv.steps))
            return False
    # tape bits: every written compound cell's bit must match M's bit
    bad = [c for c, ch in cs.cells.items()
           if dechar(ch)[0] != mv.bits.get(c, 0)]
    if bad:
        print('  FAIL %s: tape bit mismatch at %d cells e.g. %s'
              % (name, len(bad), bad[:3]))
        return False
    print('  bisim OK  %-28s %d steps, member/head/tape/halt identical'
          % (name, mv.steps))
    return True

def endpoint(name, N):
    cs = Compound(parse_morphett(name))
    cs.run(N)
    ones = {c for c, ch in cs.cells.items() if dechar(ch)[0] == 1}
    return cs.halted, len(ones), cs.head

# ---------------------------------------------------------------- main
def main():
    print('gem48 compilation family (tag-on-arrival, zero slowdown):')
    all_ok = True
    results = []
    for g in (2, 3, 4, 6, 8, 12, 24, 48):
        name, groups = compile_g(g)
        ok = bisim(name, groups, 100_000)
        all_ok &= ok
        results.append((name, len(groups), 2 * g, ok))
    print()
    hlt, ones, head = endpoint('gem48_c24x4sym.txt', 2_000_000)
    if hlt is None and ones == 1242 and head == 418:
        print('g=2 compound 2M endpoint: no halt, 1242 bit-cells, head 418 '
              '-- matches the record  OK')
    else:
        print('g=2 compound 2M endpoint MISMATCH: halt=%s ones=%d head=%d'
              % (hlt, ones, head))
        all_ok = False
    print()
    for name, ns, ks, ok in results:
        print('  %-28s  (%2d states, %2d symbols)  %s'
              % (name, ns, ks, 'OK' if ok else 'FAIL'))
    print('ALL OK' if all_ok else 'FAILURES PRESENT')
    sys.exit(0 if all_ok else 1)

main()
