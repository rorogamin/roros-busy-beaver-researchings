"""Harvest verified cursor-5 bootstraps for all 12 new 9..11-state cores."""
import json
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor
from search.test_9to11_cores import CORES
from search.sim import parse_tm, run, fmt_cfg

SPECS = [
    ('BB9_6',  1, 8, '12',    '1',   1),
    ('BB10_6', 1, 8, '12',    '41',  1),
    ('BB11_6', 1, 8, '12',    '412', 2),
    ('BB9_7',  1, 8, '126',   '1',   1),
    ('BB10_7', 1, 8, '126',   '14',  4),
    ('BB11_7', 1, 8, '126',   '146', 6),
    ('BB9_8',  2, 8, '1267',  '1',   1),
    ('BB10_8', 2, 8, '1267',  '16',  6),
    ('BB11_8', 2, 8, '1267',  '167', 7),
    ('BB9_9',  2, 8, '12678', '1',   1),
    ('BB10_9', 2, 8, '12678', '16',  6),
    ('BB11_9', 2, 8, '12678', '167', 7),
]

def run_one(spec):
    name, min_r, max_r, allow_low, allow_high, top_sym = spec
    core = CORES[name]
    best = None
    # Try up to 3 seeds if needed to get topCnt >= 6 and clean extra
    for seed in [101, 202, 303]:
        cmd = [
            'search/find_boot_cursor.exe', core,
            str(min_r), str(max_r), allow_low, allow_high, str(top_sym),
            '280', '80000000', '8', str(seed)
        ]
        res = subprocess.run(cmd, capture_output=True, text=True, check=True)
        cur_desc = None
        cur_tm = None
        for line in res.stdout.splitlines():
            if line.startswith('NEW BEST: '):
                cur_desc = line[len('NEW BEST: '):]
            elif line.startswith('  TM: '):
                cur_tm = line[len('  TM: '):]
        if cur_desc and cur_tm:
            m = re.search(r'5\^(\d+) 3\^(\d+) 2 A> ([0-9]*) 5 ([0-9]+) 0\^inf \[top=(\d+) extra=(\d+) step=(\d+)\]', cur_desc)
            assert m, f"Parse fail: {cur_desc}"
            r, n3, wlow, whigh, topc, extra, step = (
                int(m.group(1)), int(m.group(2)), m.group(3), m.group(4),
                int(m.group(5)), int(m.group(6)), int(m.group(7))
            )
            cand = {
                'name': name, 'r': r, 'm': (n3 - 1) // 2, 'n3': n3,
                'wlow': wlow, 'whigh': whigh, 'top': topc, 'extra': extra,
                'step': step, 'tm': cur_tm.replace('---', '1RZ'), 'desc': cur_desc,
                'top_sym': top_sym,
            }
            if best is None or (min(cand['top'], 8), -cand['extra'], -cand['step']) > (min(best['top'], 8), -best['extra'], -best['step']):
                best = cand
            if best['top'] >= 8 and best['extra'] <= 2 and best['step'] <= 220:
                break
    # Independently verify in search/sim.py!
    assert best is not None, f"No bootstrap found for {name}!"
    ns, ms, tab = parse_tm(best['tm'])
    t, tp, p, s = run(tab, {}, 0, 0, best['step'])
    assert t == best['step'] and s == 0, f"{name}: sim mismatch t={t} s={s}"
    expected_L = '5' * best['r'] + '3' * best['n3'] + '2'
    expected_R = best['wlow'] + '5' + best['whigh']
    actual = fmt_cfg(tp, p, s)
    expected = f"{expected_L} A> {expected_R}"
    assert actual == expected, f"{name}: expected `{expected}`, got `{actual}`"
    print(f"OK {name:6s}: step={best['step']:3d}  {expected}  (top={best['top']} extra={best['extra']})", flush=True)
    return best

if __name__ == '__main__':
    with ThreadPoolExecutor(max_workers=6) as ex:
        results = list(ex.map(run_one, SPECS))
    out = {r['name']: r for r in results}
    with open('search/boots_9to11.json', 'w') as f:
        json.dump(out, f, indent=2)
    print(f"\nALL {len(results)} BOOTSTRAPS VERIFIED AND SAVED TO search/boots_9to11.json!")
