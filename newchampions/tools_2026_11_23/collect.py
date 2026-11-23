"""Parse work/raw/*.txt bbsearch logs into work/hits.jsonl."""
import json, os, re, sys

ROOT = r'C:\Users\Rowan\Documents\findthatmachine'
RAW = os.path.join(ROOT, 'work', 'raw')
OUT = os.path.join(ROOT, 'work', 'hits.jsonl')


def parse(path):
    core, n, m = os.path.basename(path)[:-4].rsplit('_', 2)
    n, m = int(n), int(m)
    rec = {'core': core, 'n': n, 'm': m, 'hit': False}
    try:
        text = open(path, encoding='utf-8', errors='replace').read()
    except OSError:
        return rec
    lines = text.splitlines()
    idx = [i for i, l in enumerate(lines) if l.startswith('best ')]
    if not idx:
        rec['none'] = True
        return rec
    i = idx[-1]
    rec['landmark'] = lines[i][5:].strip()
    for l in lines[i:i + 12]:
        m1 = re.search(r'\bstep=(\d+)', l)
        m2 = re.search(r'states_used=(\d+)', l)
        if m1:
            rec['step'] = int(m1.group(1))
        if m2:
            rec['states_used'] = int(m2.group(1))
    want = n * 3 * m + (n - 1)
    for l in lines[i:i + 12]:
        s = l.strip()
        if s and re.fullmatch(r'[0-9A-Z_]+', s) and len(s) == want:
            rec['tnf'] = s
            break
    rec['hit'] = 'tnf' in rec
    return rec


def main():
    recs = []
    for fn in sorted(os.listdir(RAW)):
        if fn.endswith('.txt'):
            recs.append(parse(os.path.join(RAW, fn)))
    with open(OUT, 'w', encoding='utf-8') as f:
        for r in recs:
            f.write(json.dumps(r) + '\n')
    hs = [r for r in recs if r['hit']]
    print(f'jobs parsed: {len(recs)}, hits: {len(hs)}')
    cells = {}
    for r in hs:
        cells.setdefault((r['n'], r['m']), []).append(r)
    print(f'cells with a hit: {len(cells)}')
    for k in sorted(cells):
        best = max(cells[k], key=lambda r: r['step'])
        print(f'  BB({k[0]:>2},{k[1]}) {len(cells[k])} hit(s) e.g. {best["core"]} step={best["step"]}')


if __name__ == '__main__':
    main()
