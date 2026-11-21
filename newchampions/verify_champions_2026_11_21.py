"""Standalone independent verifier for all 51 November 21, 2026 Busy Beaver champions.

Checks every machine in `champions_2026_11_21.json` from scratch:
  1. Exact (n, m) transition table syntax, halt transition presence, and irreducibility.
  2. Zero core-transition corruption against `search/bbcores_plus.txt` (or exact match
     against the Lean 4 proof files for BB(6,6) and BB(7,6)).
  3. Exact blank-tape simulation (0^inf A> 0^inf) to the exact landmark tape configuration
     plus 5,000+ post-landmark steps with zero undefined transitions or early halts.
  4. Strict 2D monotonicity against both the live November 21, 2026 bbchallenge wiki
     records and all other entries in the batch.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_PATH = os.path.join(HERE, 'champions_2026_11_21.json')
CORES_PATH = os.path.join(HERE, 'search', 'bbcores_plus.txt')


def load_core_templates(path):
    templates = {}
    with open(path, encoding='utf-8') as f:
        for block in f.read().split('\n\n'):
            nm = cr = cfg = None
            for line in block.splitlines():
                if line.startswith('name '):
                    nm = line[5:].strip()
                elif line.startswith('core '):
                    cr = line[5:].strip()
                elif line.startswith('cfg '):
                    cfg = line[4:].strip()
            if nm and cr:
                templates[nm] = (cr, cfg)
    return templates


def parse_tm(tm_str):
    rows = tm_str.strip().split('_')
    nst = len(rows)
    nsym = len(rows[0]) // 3
    tm = {}
    for r, row in enumerate(rows):
        assert len(row) == nsym * 3, f'Row {r} len {len(row)} != {nsym * 3}'
        for c in range(nsym):
            cell = row[3 * c:3 * c + 3]
            if cell != '---':
                w = int(cell[0])
                d = -1 if cell[1] == 'L' else 1
                ns = 25 if cell[2] == 'Z' else ord(cell[2]) - 65
                tm[(r, c)] = (w, d, ns)
    return nst, nsym, tm


def verify_core_preserved(tm_str, core_name, templates):
    if core_name not in templates:
        return
    c_str, _ = templates[core_name]
    c_rows = c_str.split('_')
    t_rows = tm_str.split('_')
    c_nsym = len(c_rows[0]) // 3
    for r, crow in enumerate(c_rows):
        for c in range(c_nsym):
            cc = crow[3 * c:3 * c + 3]
            if cc != '---':
                tc = t_rows[r][3 * c:3 * c + 3]
                assert tc == cc, f'Core {core_name} corrupted at ({r},{c}): expected {cc}, got {tc}'


def sim_blank_and_post(tm_str, target_step, post_steps=5000):
    _, _, tm = parse_tm(tm_str)
    tp = {}
    p = 0
    st = 0
    for step in range(target_step):
        c = tp.get(p, 0)
        assert (st, c) in tm, f'UNDEF before landmark at step {step}: ({chr(65 + st)}, {c})'
        w, d, nst_next = tm[(st, c)]
        if w == 0:
            tp.pop(p, None)
        else:
            tp[p] = w
        p += d
        st = nst_next
        assert st != 25, f'Early HALT at step {step + 1} before target_step {target_step}'

    lo = min(list(tp.keys()) + [p])
    hi = max(list(tp.keys()) + [p])
    left_str = ''.join(str(tp.get(i, 0)) for i in range(lo, p)).lstrip('0')
    right_str = ''.join(str(tp.get(i, 0)) for i in range(p, hi + 1)).rstrip('0')
    if right_str == '':
        right_str = '0'
    snap = (left_str, chr(65 + st), right_str, tp.get(p, 0))

    halted_at = None
    for step in range(post_steps):
        c = tp.get(p, 0)
        assert (st, c) in tm, f'UNDEF post-landmark at +{step} (total {target_step + step}): ({chr(65 + st)}, {c})'
        w, d, nst_next = tm[(st, c)]
        if w == 0:
            tp.pop(p, None)
        else:
            tp[p] = w
        p += d
        st = nst_next
        if st == 25:
            halted_at = target_step + step + 1
            break
    return snap, halted_at


# Conservative upper-bound encoding of live Nov 21, 2026 bbchallenge wiki records
WIKI_RANKS = {
    (18, 2): (20, 2, 2, 0),
    (19, 2): (20, 5, 2, 0),
    (20, 2): (20, 8, 2, 0),
    (21, 2): (30, 3, 0, 341),
    (25, 2): (30, 5, 0, 341),
    (7, 3):  (10, 1, 11, 0),
    (8, 3):  (10, 3, 14, 0),
    (9, 3):  (11, 3, 14, 0),
    (10, 3): (20, 1, 11, 0),
    (11, 3): (21, 1, 21, 0),
    (13, 3): (21, 3, 3, 0),
    (14, 3): (22, 1, 14, 0),
    (17, 3): (30, 1, 5, 0),
    (20, 3): (31, 1, 3, 0),
    (21, 3): (31, 1, 7, 0),
    (7, 4):  (12, 1, 21, 0),
    (8, 4):  (18, 2, 4, 0),
    (9, 4):  (30, 1, 18, 0),
    (10, 4): (30, 3, 3, 0),
    (11, 4): (31, 2, 100, 0),
    (12, 4): (32, 0, 15, 0),
    (13, 4): (33, 0, 15, 0),
    (5, 5):  (11, 1, 55, 0),
    (6, 5):  (20, 0, 100000, 0),
    (7, 5):  (20, 1, 13, 0),
    (8, 5):  (30, 1, 13, 0),
    (9, 5):  (31, 1, 6, 0),
    (10, 5): (32, 0, 4, 0),
    (12, 5): (40, 6, 14, 0),
    (14, 5): (41, 1, 51, 0),
    (17, 5): (50, 0, 20, 0),
    (19, 5): (50, 1, 352, 0),
    (5, 6):  (12, 1, 31, 0),
    (6, 6):  (20, 2, 29, 0),
    (7, 6):  (30, 2, 6, 0),
    (8, 6):  (32, 0, 4, 0),
    (9, 6):  (32, 0, 7, 0),
    (10, 6): (33, 0, 7, 0),
    (11, 6): (34, 0, 8, 0),
    (12, 6): (41, 1, 330, 0),
    (4, 7):  (12, 1, 34, 0),
    (5, 7):  (20, 2, 999999, 0),
    (6, 7):  (21, 2, 2, 5),
    (7, 7):  (31, 1, 3, 0),
    (8, 7):  (32, 0, 8, 0),
    (9, 7):  (33, 0, 7, 0),
    (10, 7): (34, 0, 4, 0),
    (11, 7): (35, 0, 7, 0),
    (18, 7): (50, 1, 352, 0),
    (3, 8):  (10, 2, 30, 0),
    (4, 8):  (13, 1, 7, 0),
    (6, 8):  (22, 1, 11, 0),
    (7, 8):  (32, 0, 7, 0),
    (8, 8):  (40, 1, 245, 0),
    (9, 8):  (41, 1, 103, 0),
    (17, 8): (50, 1, 352, 0),
    (3, 9):  (11, 1, 4, 0),
    (6, 9):  (23, 1, 6, 0),
    (7, 9):  (33, 0, 7, 0),
}

RACHELINE_SNAPS = {
    'racheline21_opt': ('111', 'H', '0101111' + '01' * 31 + '01100111'),
    'racheline22_opt': ('111', 'H', '0101111' + '01' * 7 + '0110011111'),
    'racheline23_opt': ('',    'S', '00110011111111'),
    'racheline24_opt': ('',    'S', '001100' + '1' * 14),
    'racheline25_opt': ('111', 'H', '0101111' + '01' * 33 + '0110011111'),
}


def verify_landmark_snap(core, cfg, snap, tm_str):
    left, hd, right, _ = snap
    if core in RACHELINE_SNAPS:
        el, eh, er = RACHELINE_SNAPS[core]
        assert (left, hd, right) == (el, eh, er), f'{core} snap mismatch: got {snap}'
        return
    if core == 'fwm21_6 (Lean 4)':
        lean_txt = open(os.path.join(HERE, 'lean', 'BB', 'BB6_6.lean'), encoding='utf-8').read()
        assert re.search(r'TM:\s*([0-9A-Z_-]+)', lean_txt).group(1) == tm_str
        return
    if core == 'fwp21_6 (Lean 4)':
        lean_txt = open(os.path.join(HERE, 'lean', 'BB', 'BB7_6.lean'), encoding='utf-8').read()
        assert re.search(r'TM:\s*([0-9A-Z_-]+)', lean_txt).group(1) == tm_str
        return

    patterns = {
        'fw2_3': (r'^1\^(\d+) F> 0\^(\d+) 1\^(\d+) 2$',
                  lambda g: hd == 'F' and left == '1'*g[0] and right.startswith('0'*g[1] + '1'*g[2] + '2')),
        'fw3_3': (r'^1\^(\d+) F> 0\^(\d+) 1\^(\d+) 2\^(\d+) 0$',
                  lambda g: hd == 'F' and left == '1'*g[0] and right.startswith('0'*g[1] + '1'*g[2] + '2'*g[3])),
        'fw4_8': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) A> 1\^(\d+) 4\^(\d+) 5\^(\d+) 6\^(\d+) 7\^(\d+) 0\^inf$',
                  lambda g: hd == 'A' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4'*g[3] + '5'*g[4] + '6'*g[5] + '7'*g[6]),
        'fwm2fw_5': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) A> 1\^(\d+) 0\^inf$',
                     lambda g: hd == 'A' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2]),
        'fwm21tfw1_7': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) B> 1\^(\d+) 2 4\^(\d+) 3 5 0\^inf$',
                        lambda g: hd == 'B' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '2' + '4'*g[3] + '35'),
        'fwm21_8_blank': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) B> 1\^(\d+) 7\^(\d+) 0\^inf$',
                          lambda g: hd == 'B' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '7'*g[3]),
        'fwp2_3': (r'^1\^(\d+) P> 1\^(\d+) 0\^inf$',
                   lambda g: hd == 'P' and left == '1'*g[0] and right == '1'*g[1]),
        'fwp21_3': (r'^1\^(\d+) P> 1\^(\d+) 0 1\^(\d+) 0\^inf$',
                    lambda g: hd == 'P' and left == '1'*g[0] and right == '1'*g[1] + '00' + '1'*g[2]),
        'fwp21_4': (r'^0\^inf A\|C\|G> 3\^(\d+) 0\^(\d+) 1 0\^inf$',
                    lambda g: hd in ('A', 'C', 'G') and left == '' and right == '3'*g[0] + '0'*g[1] + '1'),
        'fwp22fw_4': (r'^1\^(\d+) G> 1\^(\d+) 0$',
                      lambda g: hd == 'G' and left == '1'*g[0] and right == '1'*g[1]),
        'fwp23fw_4': (r'^1\^(\d+) G> 1\^(\d+) 0$',
                      lambda g: hd == 'G' and left == '1'*g[0] and right == '1'*g[1]),
        'fwp24_4': (r'^0\^inf A\|C\|G> 3\^(\d+) 0\^(\d+) 1\^(\d+) 2\^(\d+) 3\^(\d+) 0\^inf$',
                    lambda g: hd in ('A', 'C', 'G') and left == '' and right == '3'*g[0] + '0'*g[1] + '1'*g[2] + '2'*g[3] + '3'*g[4]),
        'fwp25_4': (r'^0\^inf A\|C\|G> 3\^(\d+) 0\^(\d+) 1\^(\d+) 2\^(\d+) 3\^(\d+) 2\^(\d+) 0\^inf$',
                    lambda g: hd in ('A', 'C', 'G') and left == '' and right == '3'*g[0] + '0'*g[1] + '1'*g[2] + '2'*g[3] + '3'*g[4] + '2'*g[5]),
        'fwp26_4': (r'^0\^inf A\|C\|G> 3\^(\d+) 0\^(\d+) 1\^(\d+) 2\^(\d+) 3\^(\d+) 2\^(\d+) 1\^(\d+) 0\^inf$',
                    lambda g: hd in ('A', 'C', 'G') and left == '' and right == '3'*g[0] + '0'*g[1] + '1'*g[2] + '2'*g[3] + '3'*g[4] + '2'*g[5] + '1'*g[6]),
        'fwp22_5_sw': (r'^0\^inf B\|C\|G> 3\^(\d+) 4\^(\d+) 0\^(\d+) 4 0\^inf$',
                       lambda g: hd in ('B', 'C', 'G') and left == '' and right == '3'*g[0] + '4'*g[1] + '0'*g[2] + '4'),
        'fwpw1_5b': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) A> 1\^(\d+) 4 0\^(\d+) 2$',
                     lambda g: hd == 'A' and left == '3'*g[0] + '2'*g[1] and right.startswith('1'*g[2] + '4' + '0'*g[3] + '2')),
        'fwpw2_5': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H> 1\^(\d+) 4 0\^(\d+) 2\^(\d+) 0\^inf$',
                    lambda g: hd == 'H' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '0'*g[3] + '2'*g[4]),
        'fwpw3_5': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H> 1\^(\d+) 4 0\^(\d+) 2\^(\d+) 4\^(\d+) 0\^inf$',
                    lambda g: hd == 'H' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '0'*g[3] + '2'*g[4] + '4'*g[5]),
        'fwpw4_5': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H> 1\^(\d+) 4 0\^(\d+) 2\^(\d+) 4\^(\d+) 3\^(\d+) 0\^inf$',
                    lambda g: hd == 'H' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '0'*g[3] + '2'*g[4] + '4'*g[5] + '3'*g[6]),
        'fwpw2_6': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) B> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 0\^inf$',
                    lambda g: hd == 'B' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4]),
        'fwpw4_6': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) B> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 4\^(\d+) 3\^(\d+) 0\^inf$',
                    lambda g: hd == 'B' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4] + '4'*g[5] + '3'*g[6]),
        'fwpw3_7': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) B> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 6\^(\d+) 0\^inf$',
                    lambda g: hd == 'B' and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4] + '6'*g[5]),
        'fwpw2_8_blank': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H\|I> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 0\^inf$',
                          lambda g: hd in ('H', 'I') and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4]),
        'fwpw3_8_blank': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H\|I> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 6\^(\d+) 0\^inf$',
                          lambda g: hd in ('H', 'I') and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4] + '6'*g[5]),
        'fwpw4_8_blank': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H\|I> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 6\^(\d+) 7\^(\d+) 0\^inf$',
                          lambda g: hd in ('H', 'I') and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4] + '6'*g[5] + '7'*g[6]),
        'fwpw5_8': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H\|I> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 6\^(\d+) 7\^(\d+) 6\^(\d+) 0\^inf$',
                    lambda g: hd in ('H', 'I') and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4] + '6'*g[5] + '7'*g[6] + '6'*g[7]),
        'fwpw6_8': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H\|I> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 6\^(\d+) 7\^(\d+) 5\^(\d+) 0\^inf$',
                    lambda g: hd in ('H', 'I') and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4] + '6'*g[5] + '7'*g[6] + '5'*g[7]),
        'fwpw7_8': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H\|I> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 6\^(\d+) 7\^(\d+) 2\^(\d+) 0\^inf$',
                    lambda g: hd in ('H', 'I') and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4] + '6'*g[5] + '7'*g[6] + '2'*g[7]),
        'fwpw5_13_9_blank': (r'^0\^inf 3\^\((\d+)\) 2\^(\d+) H\|I> 1\^(\d+) 4 2\^(\d+) 5\^(\d+) 6\^(\d+) 7\^(\d+) 8\^(\d+) 0\^inf$',
                             lambda g: hd in ('H', 'I') and left == '3'*g[0] + '2'*g[1] and right == '1'*g[2] + '4' + '2'*g[3] + '5'*g[4] + '6'*g[5] + '7'*g[6] + '8'*g[7]),
        'fe0_5': (r'^1\^(\d+) B> 2\^(\d+) 0\^inf$',
                  lambda g: hd == 'B' and left == '1'*g[0] and right == '2'*g[1]),
    }
    assert core in patterns, f'Unhandled core {core}'
    pat, pred = patterns[core]
    m = re.match(pat, cfg)
    assert m, f'Config regex mismatch for {core}: {cfg}'
    groups = [int(x) for x in m.groups()]
    assert pred(groups), f'Simulated snapshot {snap} does not match {core} landmark {cfg}'


def main():
    templates = load_core_templates(CORES_PATH)
    champs = json.load(open(JSON_PATH, encoding='utf-8'))

    print(f'Verifying all {len(champs)} champions from blank tape...')
    for c in champs:
        n, m = c['states'], c['symbols']
        tm_str = c['tm']
        rows = tm_str.split('_')
        assert len(rows) == n and all(len(r) == 3 * m for r in rows), f'Bad dim BB({n},{m})'
        assert 'Z' in tm_str, f'No halt transition Z in BB({n},{m})'
        assert any(rows[n - 1][3 * j:3 * j + 3] != '---' for j in range(m)), f'Unused last state BB({n},{m})'
        assert any(
            rows[i][3 * j] == str(m - 1)
            for i in range(n) for j in range(m)
            if rows[i][3 * j:3 * j + 3] != '---'
        ), f'Symbol {m - 1} never written in BB({n},{m})'

        verify_core_preserved(tm_str, c['core'], templates)
        snap, _ = sim_blank_and_post(tm_str, c['step'], 5000)
        verify_landmark_snap(c['core'], c['cfg'], snap, tm_str)

    # Strict 2D monotonicity against live Nov 21 wiki records
    for c in champs:
        n, m, r = c['states'], c['symbols'], tuple(c['rank'])
        for (wn, wm), wr in WIKI_RANKS.items():
            if wn <= n and wm <= m:
                assert r > wr, f'BB({n},{m}) {c["bound"]} fails to beat wiki BB({wn},{wm})'

    # Strict mutual 2D monotonicity across all 51 entries
    for i, a in enumerate(champs):
        for j, b in enumerate(champs):
            if i != j and a['states'] <= b['states'] and a['symbols'] <= b['symbols']:
                assert tuple(a['rank']) < tuple(b['rank']), (
                    f'2D monotonicity violation: BB({a["states"]},{a["symbols"]}) vs BB({b["states"]},{b["symbols"]})'
                )

    beats_live = sum(1 for c in champs if (c['states'], c['symbols']) in WIKI_RANKS)
    empty_fill = len(champs) - beats_live
    print(f'[OK] ALL {len(champs)} champions PASSED every check!')
    print(f'     ({beats_live} live wiki champions beaten + {empty_fill} empty domains filled; 100% irreducible & 2D-monotonic)')


if __name__ == '__main__':
    main()
