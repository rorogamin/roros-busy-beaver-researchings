lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

# Part 1: Inspect ALL unique MAXR=5..7 BIG_R1 pairs up to 500k steps to see if ANY actually grow!
for name, fn, nS, nSym in [
    ("CET3", "r1_exact_cet3.txt", 3, 2),
    ("CET23_t1", "r1_exact_cet23_t1.txt", 2, 3),
    ("CET23_t2", "r1_exact_cet23_t2.txt", 2, 3),
]:
    big_growing = []
    seen_e = set()
    for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn):
        if not l.startswith("BIG_R1"): continue
        pre, mech_full = l.split("\t||")
        pkv = dict(x.split("=") for x in pre.split("\t")[1:] if "=" in x)
        mr = int(mech_full.split("\t")[0].split("=")[1])
        m = parse_mech_line(mech_full.split("\t", 1)[1])
        z = int(pkv.get("z_clean", -1))
        m1 = int(pkv.get("max1_20k", 0))
        if m["e_spec"] in seen_e: continue
        seen_e.add(m["e_spec"])
        # Quick check up to 300k steps in Python
        a, b = m["pair"].split("|")
        tbl1 = [[(int(blk[i*3]), -1 if blk[i*3+1]=="L" else 1, ord(blk[i*3+2])-65) if blk[i*3]!='-' else None for i in range(nSym)] for blk in a.split("_")]
        tape = {}
        p1, s1 = 0, 0
        # Wait Ag2 only affects >=2 if Ag1 reaches >=2, we should simulate BOTH for true R1 or just read max1 at 20k vs 200k!
        tbl2 = [[(int(blk[i*3]), -1 if blk[i*3+1]=="L" else 1, ord(blk[i*3+2])-65) if blk[i*3]!='-' else None for i in range(nSym)] for blk in b.split("_")]
        p2, s2 = 2, 0
        mx20 = mx200 = 0
        halted = 0
        for t in range(1, 200001):
            t1 = tbl1[s1][tape.get(p1,0)]; t2 = tbl2[s2][tape.get(p2,0)]
            if t1 is None or t2 is None: halted = t; break
            tape[p2] = t2[0]; tape[p1] = t1[0]
            p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
            if p1 == p2: halted = t; break
            if t <= 20000 and p1 > mx20: mx20 = p1
            if p1 > mx200: mx200 = p1
        if mx200 > mx20 or halted:
            big_growing.append((mr, z, mx20, mx200, halted, m["pair"]))
    print(f"=== {name} BIG_R1 growing/halting among {len(seen_e)} unique engines: {len(big_growing)} ===")
    for item in big_growing[:15]:
        print(" ", item)

# Part 2: Scan ALL lines of mechs_cet3.txt, mechs_cet23_t1.txt, mechs_cet23_t2.txt!
for name, fn, min_r in [
    ("CET3", "mechs_cet3.txt", 4),
    ("CET23_t1", "mechs_cet23_t1.txt", 6),
    ("CET23_t2", "mechs_cet23_t2.txt", 6),
]:
    col1_wins = []
    pot_lines = []
    total = 0
    seen_pot = set()
    for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn):
        total += 1
        m = parse_mech_line(l)
        if not m: continue
        if m["r1"].startswith("R1=COL1:"):
            rkv = dict(x.split("=") for x in m["r1"][8:].split(":") if "=" in x)
            G1 = int(rkv["gap"])
            if G1 in m["events"] and m["events"][G1][0] == "B":
                L2 = int(rkv["x1"]) - int(rkv["r2min"]) + m["events"][G1][1]["mna"]
                res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=30)
                if res and res[0] == "HALT" and len(res[1]) >= min_r:
                    col1_wins.append((len(res[1]), int(rkv["t"]), m["bt"], G1, L2, res[1], m["pair"]))
        elif m["r1"] == "R1=BIG" or m["r1"] == "R1=NOCOL1":
            # Compute max theoretical rounds from graph! Check if >= (5 if name=='CET3' else 9)!
            # Quick: compute R_reach by backward BFS from H gaps (any mod residue reachable via cycle/edge)!
            B = {g: ev[1] for g, ev in m["events"].items() if ev[0] == "B"}
            H = {g for g, ev in m["events"].items() if ev[0] == "H"}
            if not H: continue
            # Upper bound ignoring exact mod residues: longest simple path? No, just test exact_tower_rounds on a fast sample?
            # No, just keep ALL R1=BIG / R1=NOCOL1 lines in CET3 that have >= 1 H and >= 2 B with L_next able to change!
            pot_lines.append(l)
    col1_wins.sort(key=lambda x: (-x[0], x[2], x[1]))
    print(f"\n=== ALL {name} ({fn}: {total} lines) DIRECT R1=COL1 R>={min_r}: {len(col1_wins)} wins | unresolved BIG/NOCOL1={len(pot_lines)} ===")
    seen_w = set()
    shown = 0
    for w in col1_wins:
        k = (w[0], w[2], w[3], w[4], tuple(w[5]))
        if k not in seen_w:
            seen_w.add(k)
            print("  WIN:", w)
            shown += 1
            if shown >= 20: break
