lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/engines_4x2_tnf.txt").read().splitlines()
recs = []
for l in lines:
    p = l.split()
    kv = dict(x.split("=") for x in p[1:] if "=" in x)
    recs.append((float(kv["ratio"]), p[0], kv))
recs.sort(reverse=True)

def sim_eng(spec):
    tbl = []
    for b in spec.split("_"):
        for i in (0, 3):
            if b[i] == "-": tbl.append((-1, 0, 0))
            else: tbl.append((int(b[i]), -1 if b[i+1] == "L" else 1, ord(b[i+2]) - 65))
    return tbl

shown = set()
for rat, spec, kv in recs:
    if len(shown) >= 30: break
    sr_str = kv["sr"]
    sr = ord(sr_str) - 65
    tbl = sim_eng(spec)
    ts = []; used = set()
    for L in range(6, 15):
        tape = [0] * 400; OFF = 200
        for i in range(L, 200):
            if OFF + i < 400: tape[OFF + i] = 1
        pos = OFF - 1; st = sr; t = 0
        while t < 80000:
            sym = tape[pos]; w, d, ns = tbl[st * 2 + sym]
            if w < 0: break
            used.add((st, sym)); tape[pos] = w; pos += d; st = ns; t += 1
            if pos >= OFF + L:
                ts.append(t); break
        else:
            ts.append(-1); break
    if -1 in ts: continue
    key = tuple(ts[:6])
    if key in shown: continue
    shown.add(key)
    ratios = [round(ts[i+1]/ts[i], 3) if ts[i] > 0 and ts[i+1] > 0 else 0 for i in range(len(ts)-1)]
    st_list = "".join(sorted(set(chr(65+s) for s, _ in used)))
    print(f"{spec} sr={sr_str} st={st_list} ts={ts} rat={ratios}")
