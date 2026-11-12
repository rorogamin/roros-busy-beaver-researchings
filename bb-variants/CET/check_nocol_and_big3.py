# Check 1: those 15 NOCOL1_AT_501 in CET(2,3) t1!
# Check 2: summarize unique (pair, max1) in pinned_cet3_exh BIG_R1!
lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

def parse(s, nSym=3):
    a, b = s.split("|")
    return [[[(int(blk[i*3]), -1 if blk[i*3+1]=="L" else 1, ord(blk[i*3+2])-65) if blk[i*3]!='-' else None for i in range(nSym)] for blk in side.split("_")] for side in (a,b)]

print("=== Checking NOCOL1_AT_501 in pinned_cet23_t1.txt ===")
for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/pinned_cet23_t1.txt"):
    if not l.startswith("NOCOL1_AT_501"): continue
    rest = l.split("\t||", 1)[1]
    mech_full = rest.split("\t||", 1)[1]
    m = parse_mech_line(mech_full.split("\t", 1)[1])
    T1, T2 = parse(m["pair"], 3)
    tp = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    hits = []
    for t in range(1, 1500):
        x = T1[s1][tp.get(p1,0)]; y = T2[s2][tp.get(p2,0)]
        if x is None or y is None: break
        tp[p2]=y[0]; tp[p1]=x[0]; p1+=x[1]; s1=x[2]; p2+=y[1]; s2=y[2]
        if p1 == p2: hits.append(("H", t, p2-p1)); break
        if t > 50 and p2 - p1 >= m["mg"] and p2 - p1 < m["mg"] + m["M"] and p2 - p1 in m["events"]:
            ev = m["events"][p2-p1]
            if ev[0] == "B":
                # test exact R
                res = exact_tower_rounds(m, p2-p1, max(10, p1 + ev[1]["mna"] + 2), round_start=2, max_depth=15)
                if res and res[0] == "HALT" and len(res[1]) >= 6:
                    hits.append((t, p2-p1, chr(65+s1), chr(65+s2), len(res[1]), res[1]))
    print(" ", m["pair"], "->", hits[:3])

print("\n=== Checking BIG_R1 unique engines in pinned_cet3_exh.txt ===")
big_u = {}
for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/pinned_cet3_exh.txt"):
    if not l.startswith("BIG_R1:"): continue
    col, rest = l.split("\t||", 1)
    mx = int(col.split("=")[1])
    mr = int(rest.split("\t")[0].split("=")[1])
    pair = rest.split("\t")[1]
    big_u.setdefault((mx, pair.split("|")[0]), []).append((mr, pair))
print(f"Unique (max1_20k, eng) among 1116 BIG_R1: {len(big_u)}")
for k, v in sorted(big_u.items(), reverse=True)[:15]:
    print(f"  max1_20k={k[0]} eng={k[1]} count={len(v)} sample_maxR={max(x[0] for x in v)} sample_pair={v[0][1]}")
