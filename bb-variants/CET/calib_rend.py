lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

def parse_pair(pair_str, nS, nSym):
    a, b = pair_str.split("|")
    return [[[(int(blk[i*3]), -1 if blk[i*3+1]=="L" else 1, ord(blk[i*3+2])-65) if blk[i*3]!='-' else None for i in range(nSym)] for blk in side.split("_")] for side in (a,b)]

def find_true_G1_from_bounce(m, c_pair, nS, nSym, tsym, t_close):
    # Wait: how does find_multiround_candidates identify COL and G?
    # Let's match BOTH:
    # 1) Compare real post-t_close bounce trace against synthetic B:G probes where Ag2 runs from exact steady state!
    # Wait: WHY did our synthetic probe earlier miss? Let's test 1LB1RA0LB_2RB2LB2RA|1LB2LA1RB_2RA0RB1RA first to verify 100%!
    tbl1, tbl2 = parse_pair(c_pair, nS, nSym)
    tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    min1 = 0
    for t in range(1, t_close + 250):
        t1 = tbl1[s1][tape.get(p1,0)]; t2 = tbl2[s2][tape.get(p2,0)]
        if t1 is None or t2 is None: break
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if t < t_close + 60 and p1 < min1: min1 = p1
        if t == t_close:
            x_tc = p1; p2_tc = p2
        if t > t_close and p1 <= x_tc - 25:
            # Bounced back left! Check where tsym^inf starts on the right AND check right edge of non-tsym!
            # Wait: check t_return, p2_return!
            r_end = max(k for k, v in tape.items() if k < p2 - 10 and v != tsym)
            # Check what G in B satisfies x_col + xr == r_end + 1 (or check offset constant!)
            return x_tc, min1, t, p2, r_end, p2_tc - x_tc
    return None

# Calibrate r_end - x1 vs b['xr'] on Known COL1!
for fn, nS, nSym, tsym in [("r1_exact_cet23_t1.txt", 2, 3, 1), ("r1_exact_cet3.txt", 3, 2, 1)]:
    for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn):
        if not l.startswith("BOUNCE_R1"): continue
        pre, mech_full = l.split("\t||")
        mech_str = mech_full.split("\t", 1)[1]
        m = parse_mech_line(mech_str)
        if not m or not m["r1"].startswith("R1=COL1:"): continue
        rkv = dict(x.split("=") for x in m["r1"][8:].split(":") if "=" in x)
        G1 = int(rkv["gap"]); x1_k = int(rkv["x1"]); r2m_k = int(rkv["r2min"])
        b = m["events"][G1][1]
        pkv = dict(x.split("=") for x in pre.split("\t")[1:-1] if "=" in x)
        tc = int(pkv["t"])
        info = find_true_G1_from_bounce(m, m["pair"], nS, nSym, tsym, tc)
        if info:
            x_tc, min1, t_ret, p2_ret, r_end, d_tc = info
            print(f"CALIB {fn[:10]} G1={G1} xr={b['xr']} x1_k={x1_k} r_end={r_end} r_end-x1_k={r_end-x1_k} gdx={b['gdx']} p2_ret-x1_k={p2_ret-x1_k} | t_ret-tc={t_ret-tc} t_known={rkv['t']} d_tc={d_tc}")
            break
