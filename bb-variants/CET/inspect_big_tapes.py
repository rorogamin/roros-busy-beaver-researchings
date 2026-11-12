import sys
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

def probe_exact_G(c_pair, nS, nSym, tsym, P, mg, M, col_t):
    tbl1, tbl2 = parse_pair(c_pair, nS, nSym)
    # 1. Run actual R1 up to col_t + 80
    tape = {}
    p1, s1, p2, s2 = 0, 0, 2, 0
    r2min_real = 0
    for t in range(1, col_t + 1):
        t1 = tbl1[s1][tape.get(p1, 0)]; t2 = tbl2[s2][tape.get(p2, 0)]
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if t < col_t and p1 < r2min_real: r2min_real = p1
    x1 = p1
    real_trace = []
    # Also find actual r2min after col_t? Wait in eval_towers: L2 = x1 - r2min + mna, where r2min is min(p1) during R1 (the left anchor of R2)!
    p1r, s1r, p2r, s2r = p1, s1, p2, s2
    for dt in range(1, 80):
        t1 = tbl1[s1r][tape.get(p1r, 0)]; t2 = tbl2[s2r][tape.get(p2r, 0)]
        if t1 is None or t2 is None: break
        tape[p2r] = t2[0]; tape[p1r] = t1[0]
        p1r += t1[1]; s1r = t1[2]; p2r += t2[1]; s2r = t2[2]
        real_trace.append((s1r, s2r, p1r - x1, p2r - x1))
        if p1r == p2r:
            real_trace.append("HALT")
            break

    # 2. Match against bounce probe starting from synthetic [0...][tsym...] for every G in mg..mg+M-1!
    # Wait: first calibrate Ag1 exit state & Ag2 glider start phase (exact same way find_multiround_candidates did):
    # Actually simplest: run Ag1 alone on L=12 to get exit_st, run Ag2 alone 500 steps to find steady state,
    # Wait: we can match directly against m['events'] G! Wait: for G in range(mg, mg + M):
    # Just run synthetic probe as in check_local_gap? Even faster: match Ag2's EXACT (s2, cell_phase) right BEFORE col_t!!
    # Wait: let's just do check_local_gap probe for each G in mg..mg+M-1 (10 iterations of 500 steps each = 5ms!).
    # First find steady glider (p2, s2, tape[x..p2+P]) by running Ag2 alone on blank tape for 400 steps:
    gtape = {}; gp2, gs2 = 2, 0
    for _ in range(400):
        tr = tbl2[gs2][gtape.get(gp2, 0)]
        gtape[gp2] = tr[0]; gp2 += tr[1]; gs2 = tr[2]
    # Find exit_st of Ag1 from L=10 counter:
    # We know Ag1's state BEFORE chasing through tsym^inf: let's find exit_st on 0^10 tsym^50 from sr!
    # Wait: even easier!! On pure tsym^inf, what chase cycle does Ag1 have? Try ALL (s1_start in 0..nS-1, gap in mg..mg+M-1)?
    # Better: look at real tape left of x1 at col_t: for how many steps BEFORE col_t was p2 in steady glider cycle?
    # During the chase on tsym^inf (say 100 steps BEFORE col_t), Ag2 was stepping through its glider cycle!
    # Compare Ag2's (s2, tape[p2]) trace at step col_t - 20 .. col_t against steady Ag2!
    # Wait: NO NEED! We ALREADY know G matches at col_t when real_trace[0]..real_trace[40] matches check_local_gap's post-col trace!
    # Wait: in check_local_gap, Ag1 starts at OFF-9 in state exit_st? We can find sr, exit_st automatically from the engine spec!
    # Wait: let's check both! First run exact R1+R2 concretely up to 3,000,000 steps post-col_t if R2 < 3M! And for big R2, compare trace!
    return x1, r2min_real, real_trace

# Actually let's check why some BIG lines had max1=12, first_nz=13!
for label, fname, nS, nSym in [("CET3", "r1_cet3.txt", 3, 2), ("CET23_t1", "r1_cet23_t1.txt", 2, 3), ("CET23_t2", "r1_cet23_t2.txt", 2, 3)]:
    lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fname).read().splitlines()
    bigs = [l for l in lines if l.startswith("BIG")]
    bigs.sort(key=lambda l: int(l.split("\t")[1].split("=")[1]), reverse=True)
    print(f"=== Inspecting top BIG lines for {label} ===")
    seen_p = set()
    for l in bigs:
        p = l.split("\t")
        pair = p[2]
        if pair in seen_p: continue
        seen_p.add(pair)
        if len(seen_p) > 4: break
        tbl1, tbl2 = parse_pair(pair, nS, nSym)
        tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
        for t in range(1, 20001):
            t1 = tbl1[s1][tape.get(p1,0)]; t2 = tbl2[s2][tape.get(p2,0)]
            tape[p2] = t2[0]; tape[p1] = t1[0]
            p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        lo = min(tape); hi = min(lo + 120, max(tape)+1)
        s = "".join(str(tape.get(x,0)) for x in range(lo, min(p2+1, lo+120)))
        print(f"  {p[1]} {pair} t=20k p1={p1}({chr(65+s1)}) p2={p2}({chr(65+s2)}) lo={lo} tape[{lo}..]={s[:110]}")
