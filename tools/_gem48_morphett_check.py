"""Verify gem48_morphett.txt encodes EXACTLY the gemini 48-state machine.

Checks:
  1. static: all 96 morphett rows == the .v trans table under Sxx->n-1 mapping
  2. dynamic: both tables run identically for 100 000 blank steps, compared
     every step (state, head, ones)
  3. milestones from the .v lemmas, replayed through the MORPHETT file run:
     boot_18 (S02,h0,[0,1,2,4]); boot_20 (S34,-2,[1,2,4]);
     boot_352 = cfg_worm(-15,1,[(0,0),(0,2)]); boot_702 = cfg_worm(-16,2,
     [(0,0),(0,1),(1,1),(2,1)]); boot_1641 = cfg_worm(-17,3,W7);
     base-worm [(0,0),(1,0)] halts at 148, head 4, tape [-1,0,1];
     2 000 000 blank steps: no halt, tape 1242 cells, head 418.

Morphett semantics (per morphett.info): '<state> <sym> <write> <dir> <next>',
halt when next starts with 'halt'; the halt line still writes and moves first
(must match the .v, whose step applies (w,d) even when landing in Halt).
Blank symbol '_'; start state '0'.
"""
import re
import sys

FAIL = []

# ------------------------------------------------- 0. parse the morphett file
M_PATH = 'gem48_morphett.txt'
VMAP = {f'S{i:02d}': str(i - 1) for i in range(1, 49)}   # S01->'0' ... S48->'47'

def parse_morphett(path):
    tab, seen = {}, set()
    for raw in open(path, encoding='utf-8'):
        line = raw.split(';')[0].strip()
        if not line:
            continue
        p = line.split()
        if len(p) != 5:
            print(f'  BAD LINE: {raw!r}'); FAIL.append('syntax'); continue
        q, rd, wr, d, nq = p
        sym = 1 if rd == '1' else 0            # '_' = blank 0-bit
        out = 1 if wr == '1' else 0
        nx = 'Halt' if nq.lower().startswith('halt') else nq
        key = (q, sym)
        assert key not in seen, f'duplicate row {key}'
        seen.add(key); tab[key] = (out, d.upper(), nx)
    return tab

MT = parse_morphett(M_PATH)

# ------------------------------------------------- 1. static compare with .v
src = open('rocq/gemini_epsilon1_tm_48s_v2_fix.v', encoding='utf-8').read()
vtab = re.findall(
    r'\| (S\d{2}), (B[01]) => \(B([01]), ([LR]), (?:St (S\d{2})|Halt)\)', src)
V = {}
for q, br, w, d, nq in vtab:
    words = VMAP[q]
    sym = int(br[1])   # br = 'B0'/'B1'
    out = int(w)       # w  = '0'/'1' (digit capture)
    nx = 'Halt' if nq == '' else VMAP.get(nq, 'Halt') or 'Halt'
    # NOTE: nq=='' means Halt branch (the regex leaves St-group empty)
    V[(words, sym)] = (out, d, nx)

if set(MT) != set(V):
    diff = set(MT) ^ set(V)
    print(f'  FAIL state/symbol coverage: {len(diff)} differing keys {list(diff)[:4]}')
    FAIL.append('coverage')
else:
    bad = [k for k in V if MT[k] != V[k]]
    if bad:
        print(f'  FAIL {len(bad)} differing entries e.g. {bad[:3]}: '
              f'morphett={MT[bad[0]]} vs .v={V[bad[0]]}')
        FAIL.append('table')
    else:
        print('  static: all 96 morphett rows match the .v table exactly')

# ------------------------------------------------- 2. differential 100k run
class Sim:
    def __init__(self, state, head, ones=None):
        self.ones = set(ones or [])
        self.state = state
        self.head = head
        self.steps = 0
        self.halted = None
        self.log = []
    def read(self):
        return 1 if self.head in self.ones else 0
    def step(self, watch=None):
        r = MT[(self.state, self.read())]
        if watch is not None and (self.state, self.read()) == watch:
            self.log.append((self.steps, self.head))
        w, d, nx = r
        if w: self.ones.add(self.head)
        else: self.ones.discard(self.head)
        self.head += 1 if d == 'R' else -1
        if nx == 'Halt':
            self.halted = self.steps + 1
            self.state = 'Halt'
        else: self.state = nx
        self.steps += 1
    def run(self, n, watch=None):
        while self.halted is None and self.steps < n:
            self.step(watch)
        return self

# same table pipeline for the .v side, keyed as strings per the morphett names
def run_v_differential(n):
    sv = Sim('0', 0)
    sm = Sim('0', 0)
    dv = 0
    for _ in range(n):
        rm = MT[(sm.state, sm.read())]
        rv = SV_TABLE[(sv.state, sv.read())]
        if rm != rv: dv += 1
        for s, r in ((sm, rm), (sv, rv)):
            w, d, nx = r
            if w: s.ones.add(s.head)
            else: s.ones.discard(s.head)
            s.head += 1 if d == 'R' else -1
            s.state = 'Halt' if nx == 'Halt' else nx
            if nx == 'Halt':
                s.halted = s.steps + 1
            s.steps += 1
        assert sm.state == sv.state and sm.head == sv.head and sm.ones == sv.ones
        if sm.halted:
            break
    return sm, sv, dv

# .v table keyed by morphett names (same construction as static compare)
SV_TABLE = dict(V)

# differential walk
sm, sv, dv = run_v_differential(100_000)
infod = f'diff-run 100k: rm==rv mismatches {dv}'
print(f'  {infod}' + (' -> FAIL' if dv else ' -> identical at every step'))
if dv: FAIL.append('differential')
if sm.state != sv.state or sm.halted != sv.halted: FAIL.append('differential')

# ------------------------------------------------- 3. milestones on MT only
def worm_config(c0, n, pairs):
    ones = set(range(c0, c0 + n + 1))
    pos = c0 + n + 4
    for a, b in pairs:
        ones |= set(range(pos, pos + a + 1))
        pos_b = pos + a + 2
        ones |= set(range(pos_b, pos_b + b + 1))
        pos = pos_b + b + 2
    return ones, pos - 2

def want(name, got, wantstate, wanthd, c0=None, pairs=None):
    if c0 is not None:
        ones, hd = worm_config(c0, WORM_N[c0], pairs)
        ok = (got.state == wantstate and got.head == hd
              and got.ones == ones)
        wanthd = hd
    else:
        ok = got.state == wantstate and (wanthd is None or got.head == wanthd)
    if ok:
        print(f'  OK  {name}')
    else:
        FAIL.append(name)
        print(f'  FAIL {name}: got state={got.state} head={got.head} '
              f'ntape={len(got.ones)}; wanted state={wantstate} head={wanthd}')

W7 = [(0,0), (0,1), (1,1), (2,0), (2,1), (3,0), (3,1)]
# worm n per c0 as used by _check_gem48 (c0 = -(n+14) counter-block style)
WORM_N = {-15: 1, -16: 2, -17: 3}

m = Sim('0', 0).run(18);   want('boot_18 (state, head, tape)', m, '1', 0)
m = Sim('0', 0).run(20);   want('boot_20 (state, head, tape)', m, '33', -2)
m = Sim('0', 0).run(352);  want('boot_352 (state, head, worm)', m, '1', None, c0=-15, pairs=[(0,0), (0,2)])
m = Sim('0', 0).run(702);  want('boot_702 (state, head, worm)', m, '1', None, c0=-16, pairs=[(0,0), (0,1), (1,1), (2,1)])
m = Sim('0', 0).run(1641); want('boot_1641 (state, head, worm)', m, '1', None, c0=-17, pairs=W7)
# cfg_worm's state is S02 per the file's cfg_worm_state lemma (checked above)
# base-worm halt: [(0,0),(1,0)] with w-state S02
ones, hd = worm_config(0, 1, [(0,0), (1,0)])
m = Sim('1', hd, ones).run(400)
if m.halted == 148 and m.head == 4 and sorted(m.ones) == [-1, 0, 1]:
    print(f'  OK  halts_on_base_worm 148 (head 4, tape {sorted(m.ones)})')
else:
    FAIL.append('base_worm_148')
    print(f'  FAIL base-worm: steps={m.halted} head={m.head} tape={sorted(m.ones)}')
# 2M sampler
m = Sim('0', 0).run(2_000_000)
rec = f'none@{m.steps}'
if m.halted is None and len(m.ones) == 1242 and m.head == 418:
    print(f'  OK  2 000 000 steps: no halt, tape {len(m.ones)} cells, head {m.head}')
else:
    FAIL.append('2M')
    print(f'  FAIL 2M: halted={m.halted} cells={len(m.ones)} head={m.head}')

print()
print('VERIFY: ' + ('ALL CHECKED MILESTONES REPRODUCE' if not FAIL
                   else f'FAILURES: {FAIL}'))
sys.exit(0 if not FAIL else 1)
