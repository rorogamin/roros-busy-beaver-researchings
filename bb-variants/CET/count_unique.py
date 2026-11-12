import os

BASE = r"c:\Users\Rowan\Documents\st\bbwork\bb-variants\CET"

def parse(spec):
    states = spec.split("_")
    nsym = len(states[0]) // 3
    tbl = []
    for st in states:
        row = []
        for i in range(nsym):
            s = st[3*i:3*i+3]
            row.append((int(s[0]), 1 if s[1]=='R' else -1, ord(s[2])-65))
        tbl.append(row)
    return tbl, nsym

def dedup_and_trace(fname, label):
    path = os.path.join(BASE, fname)
    # Collapse pairs by core (E, G) keeping track of which transitions are actually visited during t=0..5000 + local gaps
    seen = {}
    lines = []
    with open(path) as f:
        for line in f:
            lines.append(line.strip())
    # Group first by exact string? Let's trace 5000 steps per line? Wait 77k in Python is slow; check how many distinct Ggliders and Eengines!
    engs = {}
    gls = {}
    for line in lines:
        pair, meta = line.split("\t", 1)
        e, g = pair.split("|")
        engs.setdefault(e, []).append((g, meta))
        gls.setdefault(g, []).append((e, meta))
    print(f"{label}: {len(lines)} lines, {len(engs)} engines, {len(gls)} gliders")

dedup_and_trace("hits_cet3_P4.txt", "CET(3)")
dedup_and_trace("hits_cet23_t1_P4.txt", "CET(2,3) t1")
dedup_and_trace("hits_cet23_t2_P4.txt", "CET(2,3) t2")
