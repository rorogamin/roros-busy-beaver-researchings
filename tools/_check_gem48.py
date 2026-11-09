"""Independent check of the gemini 48-state 2-symbol claim (epsilon1_tm.v).

Parses the trans table DIRECTLY from the .v source (not from any chat
rendering), simulates blank-tape and seeded runs, and checks every
vm_compute milestone the file states:

  boot_18, boot_20, boot_352, boot_702, boot_1641 (state, head, body)
  campaign_halt (5 steps -> Halt)
  campaign_pop_and_cantor (139), campaign_rule2_cantor (135),
  campaign_rule3_eps0 (284), campaign_rule3_eps1_seed (350)
  halts_on_base_worm (152 -> Halt)

The worm configs are decoded structurally: (n, pairs) per the file's
cfg_worm / encode_pairs layout (counter 1^{n+1}, 000 sep, then each pair
as 1^{a+1} 0 1^{b+1}, head on the last 1).

Run: python tools/_check_gem48.py
"""
import re
import sys
from pathlib import Path

DEFAULT_V = Path(__file__).resolve().parent.parent / 'rocq' / 'gemini_epsilon1_tm_48s_v2_fix.v'
V_PATH = sys.argv[1] if len(sys.argv) > 1 else str(DEFAULT_V)

# ---------------------------------------------------------------- parsing
src = open(V_PATH, encoding='utf-8').read()
defn = re.search(r'Definition trans.*?end\.', src, re.S).group(0)
rows = re.findall(r'\| (S\d\d), (B0|B1) => \(B(\d), (L|R), (St (S\d\d)|Halt)\)',
                  defn)
assert len(rows) == 96, f'expected 96 table rows, got {len(rows)}'
TABLE = {}
for st, b, w, d, _st_raw, nx in rows:
    nx = nx if nx else 'Halt'   # non-participating group parses as ''
    TABLE[(st, 0 if b == 'B0' else 1)] = (int(w), d, nx)
STATES = sorted({st for st, _ in TABLE})
print(f'table parsed from the .v: {len(STATES)} states, {len(TABLE)} rows')


class Sim:
    def __init__(self, state, head, ones):
        self.ones = set(ones)
        self.state = state
        self.head = head
        self.steps = 0
        self.halted = None
        self.log = []            # (step, event) for selector-branch watching

    def read(self):
        return 1 if self.head in self.ones else 0

    def step(self, watch=None):
        r = TABLE[(self.state, self.read())]
        if watch is not None and (self.state, self.read()) == watch:
            self.log.append((self.steps, self.head))
        w, d, nx = r
        if w:
            self.ones.add(self.head)
        else:
            self.ones.discard(self.head)
        self.head += 1 if d == 'R' else -1
        if nx == 'Halt':
            self.halted = self.steps + 1
            self.state = 'Halt'
        else:
            self.state = nx
        self.steps += 1

    def run(self, n, watch=None):
        while self.halted is None and self.steps < n:
            self.step(watch)
        return self

    # -------------------------------------------------- cfg_worm decoding
    def decode_worm(self):
        """Structural decode of the cfg_worm layout; None on mismatch."""
        ones = sorted(self.ones)
        lo = ones[0]
        # the counter block: consecutive 1s from the leftmost 1
        c0 = lo
        k = lo
        while k in self.ones:
            k += 1
        n = (k - lo) - 1
        # the 000 separator: the next 3 cells must be 0
        gap = [c for c in range(k, k + 3) if c in self.ones]
        if gap:
            return None
        i = k + 3
        pairs = []
        while True:
            if i not in self.ones:
                break
            j = i
            while j in self.ones:
                j += 1
            a = (j - i) - 1
            if j in self.ones:          # the separating gap must be a 0
                return None
            i = j + 1
            if i not in self.ones:
                return None
            j = i
            while j in self.ones:
                j += 1
            b = (j - i) - 1
            pairs.append((a, b))
            i = j + 1
        hd = i - 2 if pairs else i - 2
        return c0, n, pairs, hd


def worm_config(c0, n, pairs):
    """Build the ones-set and head per cfg_worm / encode_pairs."""
    ones = set(range(c0, c0 + n + 1))
    pos = c0 + n + 4
    for a, b in pairs:
        ones |= set(range(pos, pos + a + 1))
        pos_b = pos + a + 2
        ones |= set(range(pos_b, pos_b + b + 1))
        pos = pos_b + b + 2
    hd = pos - 2
    return ones, hd


FAIL = []


def want(name, m, state, head, cfg=None):
    ok = (m.state == state and (head is None or m.head == head))
    if cfg is not None and ok:
        c0, n, pairs = cfg
        ones, hd = worm_config(c0, n, pairs)
        ok = (m.ones == set(ones)) and (m.head == hd)
    tag = 'OK ' if ok else 'FAIL'
    if not ok:
        FAIL.append(name)
        print(f'  {tag} {name}: got state={m.state} head={m.head} '
              f'ntape={len(m.ones)}; wanted state={state} head={head}'
              + (f' cfg={cfg}' if cfg else ''))
    else:
        print(f'  {tag} {name}'
              + (f' (ntape={len(m.ones)})' if cfg is not None else ''))


MILLIS = [
    ('boot_18', 18, ('S02', 0)),
    ('boot_20', 20, ('S34', -2)),
    ('boot_352', 352, ('S02', -15, (-15, 1, [(0, 0), (0, 2)]))),
    ('boot_702', 702, ('S02', -16, (-16, 2,
        [(0, 0), (0, 1), (1, 1), (2, 1)]))),
    ('boot_1641', 1641, ('S02', -17, (-17, 3,
        [(0, 0), (0, 1), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)]))),
]

print('bootstrap milestones (state + head + decoded worm content):')
for name, t, spec in MILLIS:
    m = Sim('S01', 0, []).run(t)
    if len(spec) == 2:
        want(name, m, spec[0], spec[1])
    else:
        state = spec[0]
        c0, n, pairs = spec[2]
        ones, hd = worm_config(c0, n, pairs)
        ok = (m.state == state) and (m.head == hd) and m.ones == set(ones)
        dec = m.decode_worm()
        ok = ok and dec is not None and dec[0] == c0 and dec[1] == n \
            and dec[2] == pairs
        if not ok:
            FAIL.append(name)
            print(f'  FAIL {name}: got state={m.state} head={m.head} '
                  f'dec={dec} n1s={len(m.ones)}; wanted c0={c0} n={n} '
                  f'pairs={pairs} head={hd}')
        else:
            print(f'  OK  {name} (worm decoded: c0={dec[0]} n={dec[1]} '
                  f'{len(dec[2])} pairs, head={m.head})')

print('boot selector watch (S48 on 0, to 20k steps):')
m = Sim('S01', 0, []).run(20000, watch=('S48', 0))
print(f'  S48[0] fired {len(m.log)} time(s): {m.log[:5]}'
      f'{"..." if len(m.log) > 5 else ""}')
if len(m.log) != 1 or m.log[0][0] != 248:
    print('  NOTE: the writeup claims exactly once, at step 248')

print('campaign faithfulness lemmas:')
W = {
    'campaign_halt': (0, 1, [(0, 0)], 5, ('Halt', None)),
    'campaign_pop_and_cantor': (0, 1, [(0, 0), (1, 0), (0, 0)], 139,
                                ('S02', (-1, 2,
                                    [(0, 0), (0, 0), (0, 0)]))),
    'campaign_rule2_cantor': (0, 1, [(0, 0), (1, 0)], 135,
                              ('S02', (-1, 2,
                                  [(0, 0), (0, 0), (0, 0)]))),
    'campaign_rule3_eps0': (0, 1, [(0, 0), (0, 1)], 284,
                            ('S02', (-1, 2,
                                [(0, 0), (0, 0), (1, 0), (2, 0)]))),
    'campaign_rule3_eps1_seed': (-15, 1, [(0, 0), (0, 2)], 350,
                                 ('S02', (-16, 2,
                                     [(0, 0), (0, 1), (1, 1), (2, 1)]))),
}
for name, (c0, n, pairs, T, (state, cfg)) in W.items():
    ones, hd = worm_config(c0, n, pairs)
    m = Sim('S02', hd, ones).run(T)
    if state == 'Halt':
        ok = (m.state == 'Halt') and (m.halted == T) and m.head == 4 \
            and sorted(m.ones) == [0, 1]
        if not ok:
            FAIL.append(name)
            print(f'  FAIL {name}: state={m.state} halted={m.halted} '
                  f'head={m.head} ones={sorted(m.ones)}')
        else:
            print(f'  OK  {name}')
        continue
    ones_w, hd_w = worm_config(cfg[0], cfg[1], cfg[2])
    ok = (m.state == state) and (m.head == hd_w) and m.ones == set(ones_w)
    dec = m.decode_worm()
    ok = ok and dec is not None and dec[0] == cfg[0] and dec[1] == cfg[1] \
        and dec[2] == cfg[2]
    if not ok:
        FAIL.append(name)
        print(f'  FAIL {name}: got state={m.state} head={m.head} dec={dec};'
              f' wanted {state} c0={cfg[0]} n={cfg[1]} {cfg[2]} head={hd_w}')
    else:
        print(f'  OK  {name}')

print('halts_on_base_worm (the lemma computes with the UNMODIFIED table; '
      'the S48 comment is a gloss):')
ones, hd = worm_config(0, 1, [(0, 0), (1, 0)])
m = Sim('S02', hd, ones).run(400)
# the halting claim is now parsed from the file's own lemma:
#   exists 148%nat, 4, [-1; 0; 1].
_mc = re.search(r'exists (\d+)%nat, (\-?\d+), \[([^\]]*)\]', src)
if not _mc:
    print('  could not parse the halting claim from the file')
    FAIL.append('halts_on_base_worm')
else:
    claim_step = int(_mc.group(1))
    claim_head = int(_mc.group(2))
    claim_tape = [int(x) for x in _mc.group(3).replace(';', ',').split(',') if x.strip()]
    print(f'  file-claim: exists {claim_step}, head {claim_head}, tape {claim_tape}')
    print(f'  halted at step {m.halted}, head {m.head}, tape {sorted(m.ones)}')
    ok = (m.halted == claim_step and m.head == claim_head
          and sorted(m.ones) == sorted(claim_tape))
    print('  OK' if ok else '  MISMATCH')
    if not ok:
        FAIL.append('halts_on_base_worm')
# for the record: the S48[0]->S35 variant of the comment, as a side note
TABLE[('S48', 0)] = (0, 'R', 'S35')
m2 = Sim('S02', hd, ones).run(400)
print(f'  side note: the S48[0]->S35 variant halts at {m2.halted} instead')
for k, v in {('S48', 0): (0, 'L', 'S30')}.items():
    TABLE[k] = v

print('blank-tape survival beyond the milestones (2,000,000 steps):')
m = Sim('S01', 0, []).run(2_000_000)
print(f'  halted={m.halted} steps={m.steps:,} tape={len(m.ones)} cells '
      f'over head={m.head}')

print()
print('VERIFY: ' + ('ALL CHECKED MILESTONES REPRODUCE'
                  if not FAIL else f'FAILURES: {FAIL}'))
sys.exit(0 if not FAIL else 1)
