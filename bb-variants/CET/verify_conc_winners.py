# Verify exact G1 and exact multi-round trace (with direct concrete sim + modular check)
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

def get_exact_G1(m, c_pair, col_t, nS, nSym, tsym):
    # Reconstruct exact G1 by simulating R1 up to col_t and also checking bounce signature!
    # Better: during R1, track when Ag2 settled into its period-P loop!
    # Actually simplest 100% foolproof way: at col_t, simulate +250 steps and match the exact
    # (exit_dt, exit_dx, final_s1, final_s2) OR just compare (col_t - boot_phase) vs probe!
    # Wait: in check_local_gap, Ag2 runs from its fixed phase at x = OFF + gap.
    # Let's simulate standard probe for EVERY G in sorted(m['events']) starting at collision moment:
    # WAIT: at step col_t (right BEFORE moving to pos1 == pos2? No, AFTER step col_t so pos1==pos2!):
    # When Ag1 approaches Ag2 on tsym^inf, the ONLY thing that varies with gap G is the phase of Ag2 when hit!
    # Even simpler: simulate R1 -> COL1 -> continue through Round 2 (up to 5M steps) if it's small, OR match post-COL1 delta (steps until Ag1 exits back to x1 - 10, AND Ag1's state at x1 - 10)!
    tbl1, tbl2 = parse_pair(c_pair, nS, nSym)
    tape = {}
    p1, s1, p2, s2 = 0, 0, 2, 0
    for t in range(1, col_t + 1):
        t1 = tbl1[s1][tape.get(p1, 0)]; t2 = tbl2[s2][tape.get(p2, 0)]
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
    x1 = p1
    # Check post-col_t behavior in real machine!
    # Track exact tape changes + agent trace for 150 steps after col_t:
    trace_real = []
    # Find min tape pos left of x1 during R1
    r1_min = min(tape.keys()) if tape else 0
    # Run for up to 150 steps to collect (s1, s2, p1-x1, p2-x1)
    p1r, s1r, p2r, s2r = p1, s1, p2, s2
    halt2 = None
    for dt in range(1, 200):
        t1 = tbl1[s1r][tape.get(p1r, 0)]; t2 = tbl2[s2r][tape.get(p2r, 0)]
        if t1 is None or t2 is None: halt2 = ("UNDEF", col_t + dt); break
        tape[p2r] = t2[0]; tape[p1r] = t1[0]
        p1r += t1[1]; s1r = t1[2]; p2r += t2[1]; s2r = t2[2]
        trace_real.append((s1r, s2r, p1r - x1, p2r - x1))
        if p1r == p2r: halt2 = ("HALT2", col_t + dt); break
    if halt2: return halt2, None, r1_min
    # Notice: what is Ag1's state at x1, Ag2's state at x1, AND Ag2's velocity?
    # Even better: check find_multiround_candidates' formula:
    # We know b = m["events"][G][1]: during R1, Ag2 entered steady glider long before col_t.
    # Let's check what (col_t - boot) mod P gives, OR compare against find_multiround_candidates' r1_info if concrete!
    # Wait: in mechs_*.txt, lines with exit_t < 200k ALREADY have EXACT R1=COL1:t=...:gap=G1:x1=...:r2min=...:cz=1!
    return ("OK", trace_real[:12]), x1, r1_min

for fn, nS, nSym, tsym in [
    ("r1_cet3.txt", 3, 2, 1),
    ("r1_cet23_t1.txt", 2, 3, 1),
    ("r1_cet23_t2.txt", 2, 3, 2),
]:
    lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn).read().splitlines()
    print(f"=== EXACT CHECK {fn} ===")
    for l in lines:
        if not l.startswith("CONC"): continue
        p = l.split("\t")
        maxr = int(p[1].split("=")[1])
        mech_str = "\t".join(p[2:-7])
        kv = dict(x.split("=") for x in p[-7:-1] if "=" in x)
        m = parse_mech_line(mech_str)
        if not m: continue
        col_t = int(kv["t"])
        if m["r1"] != "R1=BIG" and m["r1"].startswith("R1=COL1:"):
            rkv = dict(x.split("=") for x in m["r1"][8:].split(":") if "=" in x)
            G1 = int(rkv["gap"])
            if G1 in m["events"] and m["events"][G1][0] == "B":
                b = m["events"][G1][1]
                L2 = int(rkv["x1"]) - int(rkv["r2min"]) + b["mna"]
                res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=20)
                if res and res[0] == "HALT" and len(res[1]) >= 4:
                    print(f"  [VERIFIED HALT R={len(res[1])}] bt={m['bt']} M={m['M']}(P={m['P']},D={m['D']}) G1={G1} L2={L2} seq={res[1]} pair={m['pair']}")
        else:
            # R1=BIG in mechs (col_t in 200k..2.5M) OR check why!
            res_info = get_exact_G1(m, m["pair"], col_t, nS, nSym, tsym)
            # Determine actual G1 by running exact Round 2 in C/Python or printing!
            if maxr >= 4:
                print(f"  [200k..2.5M CONC MAXR={maxr}] col_t={col_t} info={res_info[0][0]} x1={kv['x1']} min1={kv['min1']} pair={m['pair']}")
