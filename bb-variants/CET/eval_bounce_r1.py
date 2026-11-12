lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

def parse_pair(pair_str, nS, nSym):
    a, b = pair_str.split("|")
    res = []
    for side in (a, b):
        tbl = []
        for blk in side.split("_"):
            row = []
            for sym in range(nSym):
                t = blk[sym*3:(sym+1)*3]
                if t == "---": row.append(None)
                else: row.append((int(t[0]), -1 if t[1]=="L" else 1, ord(t[2])-65))
            tbl.append(row)
        res.append(tbl)
    return res

def probe_exact_G1_for_bounce(m, c_pair, t_close, nS, nSym, tsym):
    # If already in m["r1"], trust & return directly (after verifying!)
    if m["r1"].startswith("R1=COL1:"):
        rkv = dict(x.split("=") for x in m["r1"][8:].split(":") if "=" in x)
        return int(rkv["gap"]), int(rkv["x1"]), int(rkv["r2min"])

    # Otherwise simulate R1 up to t_close + 150!
    tbl1, tbl2 = parse_pair(c_pair, nS, nSym)
    tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    min1 = 0
    # Wait: track Ag2's period-P trace right before t_close!
    # Also find Ag1's steady return state (sr) and step count of bounce.
    # Actually simplest 100% foolproof way:
    # From step t_close - 20 to t_close + 120, record delta sequence (s1, s2, p2 - p1) and min_d step!
    hist = []
    for t in range(1, t_close + 121):
        t1 = tbl1[s1][tape.get(p1, 0)]; t2 = tbl2[s2][tape.get(p2, 0)]
        if t1 is None or t2 is None: break
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if t <= t_close and p1 < min1: min1 = p1
        if t >= t_close - 15:
            hist.append((t, p1, s1, p2, s2, p2 - p1))
    # Also simulate synthetic bounce from find_multiround_candidates' exact setup:
    # Wait: check what G in range(mg, mg+M) matches hist!
    # In synthetic setup (OFF=300), tape[0..299]=0, tape[300..]=tsym.
    # Ag2 steady glider starts at p2_init = 300 + gap (with steady cycle shifted!).
    # Wait: at what Ag2 phase? Run Ag2 alone from (2, A) on blank tape until it's in steady glider (t=400..400+P),
    # find the phase where p2 reaches its local min within period P? Or try all P_glider phases?
    # NO! In synthetic probe, we ALSO know m["events"][G]: compare how find_multiround_candidates defines gap!
    # In find_multiround_candidates: G is uniquely identified by Ag2's state/offset relative to Ag1's chase!
    # Look at m["events"][G][1]["gdx"] and ["gs"]!!
    # Even better: build synthetic probe WITHOUT guessing phase by starting Ag2 at (p2 = 300 + G + boot_shift, s2_400) for all G in B,
    # Wait: why didn't we check ALL P phases? No! On t=400, Ag2 has ONE fixed position gp(400) when G=gap!
    # Let's calibrate using 0LB0LB_1LC1RB_0RB0LC|1RB1LB_1LC0LC_1RA0RA! We check what t_close + hist vs events[10] gives!
    # And for ANY t_close in 200k..10M, return min_d, t_min_d, x1 at t_close, min1, hist[15] (exact state at t_close),
    # AND test EVERY G in B with exact_tower_rounds FIRST to see if ANY G gives huge rounds, AND match exact G!
    return None, hist[15][1], min1, hist

# First quick test: inspect all BOUNCE_R1 lines in r1_exact_*.txt!
# Print already-known COL1 winners first, AND for t>200k BOUNCE_R1 test which B gaps hit R>=4!
for fn, nS, nSym, tsym in [
    ("r1_exact_cet3.txt", 3, 2, 1),
    ("r1_exact_cet23_t1.txt", 2, 3, 1),
    ("r1_exact_cet23_t2.txt", 2, 3, 2),
]:
    lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn).read().splitlines()
    print(f"================ {fn} BOUNCE_R1 RESULTS ================")
    known_wins = []
    med_wins = []
    seen = set()
    for l in lines:
        if not l.startswith("BOUNCE_R1"): continue
        pre, mech_full = l.split("\t||")
        ptoks = pre.split("\t")
        pkv = dict(x.split("=") for x in ptoks[1:-1] if "=" in x)
        # mech_full starts with MAXR=...\t
        mech_str = mech_full.split("\t", 1)[1]
        m = parse_mech_line(mech_str)
        if not m: continue
        if m["r1"].startswith("R1=COL1:"):
            rkv = dict(x.split("=") for x in m["r1"][8:].split(":") if "=" in x)
            G1 = int(rkv["gap"])
            if G1 in m["events"] and m["events"][G1][0] == "B":
                b = m["events"][G1][1]
                L2 = int(rkv["x1"]) - int(rkv["r2min"]) + b["mna"]
                res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=20)
                if res and res[0] == "HALT" and len(res[1]) >= 4:
                    k = (len(res[1]), m["bt"], m["M"], G1, L2, tuple(res[1]), m["e_spec"][:10])
                    if k not in seen:
                        seen.add(k)
                        known_wins.append((len(res[1]), m["bt"], m["M"], int(rkv["t"]), G1, L2, res[1], m["pair"]))
        else:
            # 200k <= t <= 10M! Check which G in B gives R >= 4 around L2 = x1 - min1 + mna
            x1 = int(pkv["x1"]); min1 = int(pkv["min1"]); tc = int(pkv["t"])
            # Note x1 at t_enter = x1, exact COL step is <= +12 steps later (within M)!
            # Check all G in B and small delta in [0..4] to see potential!
            cand = []
            for G, ev in m["events"].items():
                if ev[0] != "B": continue
                b = ev[1]
                for dx in (0, 1, 2): # small ambiguity between d_enter and exact COL step
                    L2 = (x1 + dx) - min1 + b["mna"]
                    res = exact_tower_rounds(m, G, L2, round_start=2, max_depth=20)
                    if res and res[0] == "HALT" and len(res[1]) >= 4:
                        cand.append((len(res[1]), G, dx, L2, res[1]))
            if cand:
                cand.sort(reverse=True)
                best = cand[0]
                k = (best[0], m["bt"], m["M"], tc, best[1], best[3], m["e_spec"][:10])
                if k not in seen:
                    seen.add(k)
                    med_wins.append((best[0], m["bt"], m["M"], tc, x1, min1, m["pair"], cand[:3]))
    known_wins.sort(reverse=True)
    med_wins.sort(reverse=True)
    print(f"  Known COL1 (<200k) R>=4 unique winners: {len(known_wins)}")
    for w in known_wins[:10]: print("   ", w)
    print(f"  Medium BOUNCE_R1 (200k..10M) potential R>=4 unique winners: {len(med_wins)}")
    for w in med_wins[:10]: print("   ", w[:7], "cands=", w[7])
