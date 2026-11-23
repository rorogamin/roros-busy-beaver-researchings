"""Parallel BB champion sweep: every core, every reachable (states,symbols) cell.

Writes one JSON line per (core, n, m) attempt to work/hits.jsonl.
"""
import json, os, re, subprocess, sys, time
from concurrent.futures import ProcessPoolExecutor, as_completed

ROOT = r'C:\Users\Rowan\Documents\findthatmachine'
NC = os.path.join(ROOT, 'repos', 'roros-busy-beaver-researchings', 'newchampions')
EXE = os.path.join(NC, 'search', 'bbsearch_mc.exe')
CORES = os.path.join(NC, 'search', 'bbcores_plus.txt')
OUT = os.path.join(ROOT, 'work', 'hits.jsonl')
BUDGET = int(os.environ.get('SWEEP_BUDGET', '300000000'))
MAXN = int(os.environ.get('SWEEP_MAXN', '21'))
MINN = int(os.environ.get('SWEEP_MINN', '4'))
MINM = int(os.environ.get('SWEEP_MINM', '3'))
MAXM = int(os.environ.get('SWEEP_MAXM', '9'))

# proof-theoretic strength ranking of core families (higher = stronger bound)
def rank(name):
    if name.startswith('fe1'):   return (6, 0, name)
    if name.startswith('fe0'):   return (5, 0, name)
    nums = re.findall(r'\d+', name)
    tail = int(nums[-1]) if nums else 0
    if name.startswith('fwpw'):  # omega^omega + k
        return (4, tail, name)
    if name.startswith('fwp'):   # omega^2 + k
        return (3, tail, name)
    if name.startswith('fwm2'):  # omega*2 + k
        return (2, tail, name)
    if name.startswith('fw'):    # omega + k
        return (1, tail, name)
    return (0, 0, name)


def list_cores():
    r = subprocess.run([EXE, '--cores-file', CORES, '--cores'],
                       capture_output=True, text=True, errors='replace')
    cores = []
    for line in r.stdout.splitlines():
        p = line.split()
        if len(p) >= 3 and p[1].isdigit() and p[2].isdigit():
            cores.append((p[0], int(p[1]), int(p[2])))
    return cores


def run_one(job):
    core, n, m = job
    t0 = time.time()
    rec = {'core': core, 'n': n, 'm': m, 'hit': False}
    try:
        r = subprocess.run(
            [EXE, '--core', core, '--cores-file', CORES, '--states', str(n),
             '--symbols', str(m), '--cap', '20000', '--budget', str(BUDGET)],
            capture_output=True, text=True, errors='replace', timeout=900)
        out = r.stdout
    except Exception as e:
        rec['err'] = repr(e); rec['wall'] = round(time.time() - t0, 1)
        return rec
    rec['wall'] = round(time.time() - t0, 1)
    lines = out.splitlines()
    idx = [i for i, l in enumerate(lines) if l.startswith('best ')]
    if not idx:
        rec['none'] = True
        return rec
    i = idx[-1]
    rec['landmark'] = lines[i][5:].strip()
    for l in lines[i:i + 10]:
        s = l.strip()
        if s.startswith('step='):
            rec['step'] = int(s[5:])
        elif s.startswith('states_used='):
            rec['states_used'] = int(s[12:])
    want = n * 3 * m + (n - 1)
    for l in lines[i:i + 10]:
        s = l.strip()
        if s and re.fullmatch(r'[0-9A-Z_]+', s) and len(s) == want:
            rec['tnf'] = s
            break
    rec['hit'] = 'tnf' in rec
    return rec


def build_jobs(cores):
    jobs, seen = [], set()
    ranked = sorted(cores, key=lambda c: rank(c[0]), reverse=True)
    # for every cell, take the strongest MAXK cores that fit
    MAXK = int(os.environ.get('SWEEP_TOPK', '4'))
    for m in range(MINM, MAXM + 1):
        for n in range(MINN, MAXN + 1):
            fit = [c for c in ranked if c[1] <= n and c[2] <= m]
            for c, n0, m0 in fit[:MAXK]:
                # hit this exact cell, plus one slack state if there is room
                for nn in (n,):
                    key = (c, nn, m)
                    if key not in seen:
                        seen.add(key); jobs.append(key)
    return jobs


def main():
    cores = list_cores()
    print(f'cores parsed: {len(cores)}', flush=True)
    for c in cores:
        print('  %-18s %2d x %d  rank=%s' % (c[0], c[1], c[2], rank(c[0])), flush=True)
    jobs = build_jobs(cores)
    print(f'jobs: {len(jobs)}  budget={BUDGET}', flush=True)
    done = 0
    t0 = time.time()
    with open(OUT, 'a', encoding='utf-8') as f, \
         ProcessPoolExecutor(max_workers=12) as ex:
        futs = {ex.submit(run_one, j): j for j in jobs}
        for fut in as_completed(futs):
            rec = fut.result()
            f.write(json.dumps(rec) + '\n'); f.flush()
            done += 1
            if done % 20 == 0:
                el = time.time() - t0
                print(f'  {done}/{len(jobs)}  {el:.0f}s  eta={el/done*(len(jobs)-done):.0f}s', flush=True)
    print('SWEEP DONE', flush=True)


if __name__ == '__main__':
    main()
