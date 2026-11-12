lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

def parse_pair(pair_str, nS, nSym):
    a, b = pair_str.split("|")
    return [[[(int(blk[i*3]), -1 if blk[i*3+1]=="L" else 1, ord(blk[i*3+2])-65) if blk[i*3]!='-' else None for i in range(nSym)] for blk in side.split("_")] for side in (a,b)]

# 1. Inspect top BIG_R1 items at t=1..50k (what is Ag1 doing? Did Ag1 exit yet, or is tape growing inside a counter?)
print("=== PART 1: INSPECT TOP BIG_R1 AT t=20k & t=200k ===")
for name, fn, nS, nSym in [
    ("CET3", "r1_exact_cet3.txt", 3, 2),
    ("CET23_t1", "r1_exact_cet23_t1.txt", 2, 3),
    ("CET23_t2", "r1_exact_cet23_t2.txt", 2, 3),
]:
    cands = []
    seen = set()
    for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn):
        if not l.startswith("BIG_R1"): continue
        pre, mech_full = l.split("\t||")
        mr = int(mech_full.split("\t")[0].split("=")[1])
        m = parse_mech_line(mech_full.split("\t", 1)[1])
        z = [x for x in pre.split("\t") if x.startswith("z_clean=")]
        zc = int(z[0].split("=")[1]) if z else -1
        k = (mr, m["bt"], zc, m["e_spec"])
        if k not in seen:
            seen.add(k)
            cands.append((mr, zc, m))
    cands.sort(key=lambda x: (-x[0], -x[1]))
    print(f"\n--- {name}: {len(cands)} unique (MAXR, zc, eng) BIG_R1 ---")
    for mr, zc, m in cands[:8]:
        tbl1, tbl2 = parse_pair(m["pair"], nS, nSym)
        tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
        min1, max1 = 0, 0
        snap = {}
        for t in range(1, 200001):
            t1 = tbl1[s1][tape.get(p1,0)]; t2 = tbl2[s2][tape.get(p2,0)]
            if t1 is None or t2 is None:
                snap['halt'] = t; break
            tape[p2] = t2[0]; tape[p1] = t1[0]
            p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
            if p1 < min1: min1 = p1
            if p1 > max1: max1 = p1
            if t in (5000, 20000, 100000, 200000):
                snap[t] = (p1, chr(65+s1), min1, max1, p2)
        tstr = " ".join(f"{x}:{tape.get(x,0)}" for x in range(min1, min(max1+5, min1+38)))
        print(f"  MAXR={mr} bt={m['bt']} zc={zc} P={m['P']} D={m['D']} | {m['pair']}")
        print(f"    snaps={snap}")
        print(f"    tape[{min1}..]: {''.join(str(tape.get(x,0)) for x in range(min1, max1+20))}")

# 2. Check ALL lines in mechs_3x2.txt!
print("\n=== PART 2: ALL mechs_3x2.txt WITH ALREADY R1=COL1 OR POTENTIAL R>=5 ===")
m3 = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/mechs_3x2.txt").read().splitlines()
col1_wins = []
pot5_count = 0
pot5_groups = {}
for l in m3:
    m = parse_mech_line(l)
    if not m: continue
    if m["r1"].startswith("R1=COL1:"):
        rkv = dict(x.split("=") for x in m["r1"][8:].split(":") if "=" in x)
        G1 = int(rkv["gap"])
        if G1 in m["events"] and m["events"][G1][0] == "B":
            L2 = int(rkv["x1"]) - int(rkv["r2min"]) + m["events"][G1][1]["mna"]
            res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=20)
            if res and res[0] == "HALT" and len(res[1]) >= 4:
                col1_wins.append((len(res[1]), m["bt"], G1, L2, res[1], m["pair"]))
# Done part 2 quick COL1 check across ALL 10966!
col1_wins.sort(reverse=True)
print(f"Total mechs_3x2={len(m3)}, direct COL1 R>=4 count={len(col1_wins)}")
for w in col1_wins[:15]:
    print("  COL1 WIN:", w)
