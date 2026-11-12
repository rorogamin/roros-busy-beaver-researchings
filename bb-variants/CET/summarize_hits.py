import os, re
from collections import defaultdict

BASE = r"c:\Users\Rowan\Documents\st\bbwork\bb-variants\CET"

def summarize(fname, label):
    path = os.path.join(BASE, fname)
    engs = set()
    gls = set()
    by_M = defaultdict(list)
    total = 0
    with open(path) as f:
        for line in f:
            total += 1
            parts = line.strip().split("\t")
            pair = parts[0]
            e, g = pair.split("|")
            meta = parts[1] if len(parts) > 1 else ""
            mP = re.search(r"P=(\d+)\s+D=(\d+)\s+M=(\d+)\s+nH=(\d+)\s+nB=(\d+)", meta)
            if not mP:
                continue
            P, D, M, nH, nB = map(int, mP.groups())
            engs.add(e)
            gls.add((g, P, D, M))
            # Check transitions summary signature
            sig = (meta.split("spanL=")[1] if "spanL=" in meta else meta)
            by_M[(M, P, D)].append((e, g, nH, nB, meta))
    print(f"=== {label}: {total} hits | {len(engs)} engines | {len(gls)} gliders ===")
    for k in sorted(by_M.keys(), key=lambda x: (-x[0], -x[1]))[:20]:
        lst = by_M[k]
        # sample distinct engines
        ex_e = lst[0][0]
        ex_g = lst[0][1]
        print(f"  M={k[0]:2d} (P={k[1]:2d}, D={k[2]:2d}): {len(lst):5d} pairs | ex: {ex_e}|{ex_g} | nH={lst[0][2]} nB={lst[0][3]}")

summarize("hits_cet3_P4.txt", "CET(3)")
summarize("hits_cet23_t1_P4.txt", "CET(2,3) tsym=1")
summarize("hits_cet23_t2_P4.txt", "CET(2,3) tsym=2")
