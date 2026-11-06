"""Scan consecutive c = LOW-k below the known 758 wall for reachability of H."""
import os
import sys
import time
import multiprocessing as mp

import wall

H = wall.H
LOW = H - 8_000_000


def task(k):
    c = LOW - k
    for i in range(200000):
        if c == H:
            return (k, 'H', i)
        if c > H:
            return (k, 'over', i)
        r = wall.chain(c)
        if r[0] == 'halt':
            return (k, 'halt', i)
        c = r[2]
    return (k, 'limit', 200000)


if __name__ == '__main__':
    start = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else max(1, (os.cpu_count() or 4))
    print(f"scanning k={start}..{start+count-1} with {workers} workers", flush=True)
    t0 = time.time()
    done = 0
    failures = []
    with mp.Pool(workers) as pool:
        for k, kind, chains in pool.imap_unordered(task, range(start, start + count)):
            done += 1
            if kind != 'H':
                failures.append((k, kind, chains))
                print(f"FAIL k={k}: {kind} after {chains} chains", flush=True)
            elif done % 10 == 0 or done == count:
                print(f"  {done}/{count} done, all H so far, {time.time()-t0:.1f}s", flush=True)
    print(f"finished {done} in {time.time()-t0:.1f}s; failures={failures}", flush=True)
    if not failures:
        print(f"wall extends contiguously to H-{8_000_000 + start + count - 1}", flush=True)
