def canon_bcd(spec):
    # Parse 4 states x 2 symbols
    blocks = spec.split("_")
    # Check all4 present
    tbl = []
    for b in blocks:
        for i in (0, 3):
            if b[i] == "-":
                tbl.append(None)
            else:
                tbl.append((int(b[i]), b[i+1], ord(b[i+2]) - 65))
    # Canonicalize {1,2,3} (B,C,D) by BFS from 0 (A) on syms (0,1),
    # trying minimal order if disconnected (all reachable in active machines).
    order = [0]
    seen = {0}
    q = [0]
    while q:
        s = q.pop(0)
        for sym in (0, 1):
            tr = tbl[s*2 + sym]
            if tr is not None:
                ns = tr[2]
                if ns not in seen:
                    seen.add(ns)
                    order.append(ns)
                    q.append(ns)
    if len(order) < 4:
        for s in range(4):
            if s not in seen:
                order.append(s)
    inv = [0]*4
    for new_i, old_i in enumerate(order):
        inv[old_i] = new_i
    out_blocks = []
    for new_s in range(4):
        old_s = order[new_s]
        s_str = ""
        for sym in (0, 1):
            tr = tbl[old_s*2 + sym]
            if tr is None:
                s_str += "---"
            else:
                s_str += f"{tr[0]}{tr[1]}{chr(65 + inv[tr[2]])}"
        out_blocks.append(s_str)
    return "_".join(out_blocks), order, inv

def parse_tbl(spec):
    tbl = []
    for b in spec.split("_"):
        for i in (0, 3):
            if b[i] == "-": tbl.append(None)
            else: tbl.append((int(b[i]), -1 if b[i+1]=="L" else 1, ord(b[i+2])-65))
    return tbl

def test_engine_counter(spec, sr):
    tbl = parse_tbl(spec)
    # Check L=7..12 to verify all 4 states actually execute inside counter & get exact exponential ratio
    ts = []
    used_states = set()
    for L in range(7, 13):
        tape = [0]*400; OFF = 150
        for i in range(L, 180): tape[OFF+i] = 1
        pos = OFF - 1; st = sr; t = 0
        while t < 150000:
            tr = tbl[st*2 + tape[pos]]
            if tr is None: return None
            w, d, ns = tr
            if L >= 9: used_states.add(st)
            tape[pos] = w; pos += d; st = ns; t += 1
            if pos >= OFF + L:
                ts.append(t); break
        else:
            return None
        if pos < OFF - 40: return None
    # Check exponential growth ts[5] > 4 * ts[2] and all 4 states visited in counter
    if len(used_states) < 4: return None
    if ts[5] < 4 * ts[2]: return None
    return ts

# Process engines
e_seen = {}
for line in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/engines_4x2_tnf.txt"):
    p = line.strip().split("\t")
    spec = p[0]
    if not all(c in spec for c in "ABCD"): continue
    kv = dict(x.split("=") for x in p[1:] if "=" in x)
    cspec, order, inv = canon_bcd(spec)
    if cspec in e_seen: continue
    sr_new = inv[ord(kv["sr"]) - 65]
    ts = test_engine_counter(cspec, sr_new)
    if ts is not None:
        e_seen[cspec] = (cspec, chr(65+sr_new), ts)

with open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/engines_4x2_clean.txt", "w") as f:
    for cspec, sr_ch, ts in e_seen.values():
        f.write(f"{cspec}\tsr={sr_ch}\tL12={ts[5]}\trat={ts[5]/ts[2]:.2f}\n")

# Process gliders (keep all4, canon, prioritize diverse M >= 8)
g_seen = {}
for line in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/gliders_4x2_tnf.txt"):
    p = line.strip().split("\t")
    spec = p[0]
    if not all(c in spec for c in "ABCD"): continue
    kv = dict(x.split("=") for x in p[1:] if "=" in x)
    P, D = int(kv["P"]), int(kv["D"])
    M = P - D
    if P < 4 or M < 8: continue
    cspec, _, _ = canon_bcd(spec)
    if cspec in g_seen: continue
    # Verify glider actually visits all 4 states during boot+cycle up to 1000 steps
    tbl = parse_tbl(cspec)
    tape = {}; pos = 2; st = 0; used = set()
    ok = True
    for _ in range(1000):
        tr = tbl[st*2 + tape.get(pos, 0)]
        if tr is None: ok = False; break
        used.add(st); tape[pos] = tr[0]; pos += tr[1]; st = tr[2]
    if not ok or len(used) < 4: continue
    g_seen[cspec] = (M, P, D, cspec)

# Sort gliders nicely: M in 10..28 first (sweet spot for multi-round bouncing!), then rest
g_list = sorted(g_seen.values(), key=lambda x: (0 if 10 <= x[0] <= 26 else 1, -x[0], x[1]))
with open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/gliders_4x2_clean.txt", "w") as f:
    for M, P, D, cspec in g_list:
        f.write(f"{cspec}\tP={P}\tD={D}\tM={M}\n")

print(f"Clean all-4-state canonical engines: {len(e_seen)}")
print(f"Clean all-4-state canonical gliders (M>=8): {len(g_list)}")
