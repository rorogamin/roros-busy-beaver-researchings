"""Fetch live https://wiki.bbchallenge.org/wiki/Champions?action=raw and compute 2D floors."""
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fgh_order as F

OUT_JSON = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'wiki_live_2026_11_24.json')
RAW_TXT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'wiki_live_2026_11_24.raw.txt')


def main():
    raw = subprocess.check_output(
        ['curl.exe', '-s', '--max-time', '25', '-A', 'Mozilla/5.0',
         'https://wiki.bbchallenge.org/wiki/Champions?action=raw']
    ).decode('utf-8', errors='replace')
    assert len(raw) > 20000 and '== 2-Symbol TMs ==' in raw, f'Bad wiki fetch len={len(raw)}'
    open(RAW_TXT, 'w', encoding='utf-8').write(raw)

    grid = {}
    sec = None
    cur = []

    def flush(cur_rows, cur_sec):
        if not cur_rows or not cur_sec:
            return
        dom_raw = cur_rows[0].lstrip('|').strip()
        rt_raw = cur_rows[1].lstrip('|').strip() if len(cur_rows) > 1 else ''
        tm_raw = cur_rows[2].lstrip('|').strip() if len(cur_rows) > 2 else ''
        disc_raw = cur_rows[3].lstrip('|').strip() if len(cur_rows) > 3 else ''
        m1 = re.search(r'BB\((\d+),(\d+)\)', dom_raw)
        m2 = re.search(r'BB\((\d+)\)', dom_raw)
        if m1:
            n, m = int(m1.group(1)), int(m1.group(2))
        elif m2 and '2-Symbol' in cur_sec:
            n, m = int(m2.group(1)), 2
        else:
            return
        rt_clean = re.sub(r'</?math>', '', rt_raw).strip()
        tm_match = re.search(r'\{\{TM\|([^|}]+)', tm_raw)
        tm_str = tm_match.group(1).strip() if tm_match else ''
        parsed = F.parse_wiki_latex(rt_clean)
        grid[(n, m)] = {
            'n': n,
            'm': m,
            'runtime_latex': rt_clean,
            'parsed_str': F.fmt_expr(parsed),
            'tm': tm_str,
            'discovered_by': disc_raw,
        }

    for line in raw.splitlines():
        m = re.match(r'^==\s*(.+?)\s*==$', line)
        if m:
            flush(cur, sec)
            cur = []
            sec = m.group(1)
            continue
        if not sec or 'Symbol' not in sec:
            continue
        if line.startswith('|-') or line.startswith('|}'):
            flush(cur, sec)
            cur = []
        elif line.startswith('|') and not line.startswith('|+'):
            cur.append(line)
    flush(cur, sec)

    # Compute 2D-monotone floor for 2..40 x 2..9
    parsed_map = {k: F.parse_wiki_latex(v['runtime_latex']) for k, v in grid.items()}
    floor = {}
    for n in range(2, 41):
        for m in range(2, 10):
            cand = parsed_map.get((n, m))
            best = cand
            for nb in ((n - 1, m), (n, m - 1)):
                nf = floor.get(nb)
                if nf is None:
                    continue
                if best is None:
                    best = nf
                elif F.cmp_conservative(nf, best) == 1:
                    best = nf
                elif F.cmp_conservative(nf, best) is None:
                    # Take conservative max by ordinal/approx
                    best = nf if F.min_base_value(nf) > F.min_base_value(best) else best
            floor[(n, m)] = best

    out = {
        'cells': {f'{n}x{m}': v for (n, m), v in sorted(grid.items())},
        'floors': {
            f'{n}x{m}': F.fmt_expr(floor[(n, m)])
            for n in range(2, 41) for m in range(2, 10)
        },
    }
    json.dump(out, open(OUT_JSON, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
    print(f'Fetched {len(grid)} wiki cells. Saved {OUT_JSON}')
    for m in range(2, 10):
        cnt = sum(1 for (nn, mm), v in grid.items() if mm == m and nn <= 25 and v['runtime_latex'])
        print(f'  m={m}: {cnt} filled cells in n<=25')


if __name__ == '__main__':
    main()
