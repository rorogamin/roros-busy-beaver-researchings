lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

def parse_pair(pair_str, nS, nSym):
    a, b = pair_str.split("|")
    return [[[(int(blk[i*3]), -1 if blk[i*3+1]=="L" else 1, ord(blk[i*3+2])-65) if blk[i*3]!='-' else None for i in range(nSym)] for blk in side.split("_")] for side in (a,b)]

def find_G1_exact_by_probe_match(m, pair, tc, nS, nSym, tsym):
    tbl1, tbl2 = parse_pair(pair, nS, nSym)
    # 1. Simulate real machine up to tc + 250 until Ag1 exits back left (< max1 - 30)
    tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    min1 = 0
    for t in range(1, tc + 250):
        t1 = tbl1[s1][tape.get(p1,0)]; t2 = tbl2[s2][tape.get(p2,0)]
        if t1 is None or t2 is None: return None
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if t <= tc + 60 and p1 < min1: min1 = p1
        if t == tc:
            real_start = (p1, s1, p2, s2, p2 - p1)
            real_hist = []
        if t > tc:
            real_hist.append((p1 - real_start[0], p2 - p1, s1, s2))
            if len(real_hist) >= 120: break

    # Find exact min_d and pattern of (s1, s2, p2-p1) around min_d!
    min_d = min(x[1] for x in real_hist)
    idx_min = next(i for i, x in enumerate(real_hist) if x[1] == min_d)
    sig_real = tuple((x[1], x[2], x[3]) for x in real_hist[max(0,idx_min-3):idx_min+8])

    # 2. Compute steady Ag1 chase state + steady Ag2 glider cycle from t=400!
    # Find sr of Ag1 on 0^12 | tsym^200 and exit_st into tsym^200:
    # Actually just test ALL gaps G in sorted(m['B']) by finding which probe from find_multiround_candidates
    # matches sig_real AND what exact x1_col step corresponds to G!
    # Wait: in find_multiround_candidates, b['gs'] IS the step in probe(OFF=300, gap=G) when COL occurred,
    # and wait: Ag2 in probe starts at (300+gap, s2_init) -- specifically after running Ag2 alone for N_pre steps!
    # Even simpler!! We don't need N_pre: sweep phase ph in range(P) of steady Ag2 approaching from p2=300+G,
    # wait NO: G already shifts Ag2's phase modulo M! Wait: how does G differ from (G + M)? It doesn't mod M!
    # Let's check for EACH G in sorted(m['B']): run Ag2 alone 300+k steps (k in range(P)), collide with Ag1 chasing on tsym,
    # Wait: if we just want to know EXACTLY which G in m['B'] produces sig_real AND exact x1_col = real_start[0] + shift:
    # Wait: compare L_orig_2 directly via spliced Round 2? YES! Wait no, look: how does G relate to L_orig_2?
    # At step tc + idx_min, Ag1 turns around at max1_bounce! Let's check max1_bounce - min1 vs L2!
    # In calib_rend.py, for 1LB1RA1LB: G=12 had x1_k=10924, r_end=10932, xr=18! Notice max1_bounce at G=12!
    # Even better: check ALL (t_candidate in tc .. tc+P) and compare Ag2's state at t_candidate with steady Ag2!
    # Actually simplest 100% EXACT check: compute L2_cand AND T2_round on spliced R2 (L=12) to verify formula match!
    # Run from real tape at tc+120:
    zeros_left = p1 # wait p1 is back left in 0^{L_rem}
    # Scan rightmost zero before tsym^inf at tc+120:
    r_end = max(k for k,v in tape.items() if k < p2 - 10 and v != tsym)
    return min_d, real_start, min1, r_end, p2 - real_start[0], sig_real

# Inspect top 6 candidates from CET3, CET23_t1, CET23_t2!
targets = [
    ("r1_exact_cet3.txt", 3, 2, 1, "1LB0RB_1LC1RB_0RA0LC|1LB0RC_1RA0LC_1RB1RA"),
    ("r1_exact_cet3.txt", 3, 2, 1, "1LB1RA_1LC0LB_0RC0RA|1LB0LA_1RC0RB_1LC1RA"),
    ("r1_exact_cet3.txt", 3, 2, 1, "1LB1LC_1LC1RB_0RB0LC|1RC1LC_1LC1RB_0RB0LA"),
    ("r1_exact_cet23_t1.txt", 2, 3, 1, "1LB1RA0LB_0RA2LB0LA|1RB0LA1RA_1LB2RB1RA"),
    ("r1_exact_cet23_t1.txt", 2, 3, 1, "1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA"),
    ("r1_exact_cet23_t2.txt", 2, 3, 2, "1LB2LB2RA_0RA---0LB|1RB1LA0LB_2LA2RA2RA"),
    ("r1_exact_cet23_t2.txt", 2, 3, 2, "1LB2LB2RA_0RA---0LB|2LB2RB2RB_1RA0RB0LA"),
    ("r1_exact_cet23_t2.txt", 2, 3, 2, "1LB2LB2RA_0RB2RA1LB|2LB2RB0RB_2RA0RB1LB"),
]
for fn, nS, nSym, tsym, pat in targets:
    for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn):
        if pat in l:
            pre, mech_full = l.split("\t||")
            pkv = dict(x.split("=") for x in pre.split("\t")[1:-1] if "=" in x)
            m = parse_mech_line(mech_full.split("\t", 1)[1])
            tc = int(pkv["t"])
            info = find_G1_exact_by_probe_match(m, pat, tc, nS, nSym, tsym)
            # Check which G in B gives max R around x1 = tc_x1 + offset!
            x1 = int(pkv["x1"]); min1 = int(pkv["min1"])
            # Actually find G by checking which B gap has exact (sig_real) match in probe!
            # Wait: also run exact_tower_rounds across G in B and dx in 0..8 and print!
            hits = []
            for G, ev in sorted(m["events"].items()):
                if ev[0] != "B": continue
                b = ev[1]
                for dx in range(-2, 6):
                    L2 = (x1 + dx) - min1 + b["mna"]
                    res = exact_tower_rounds(m, G, L2, round_start=2, max_depth=20)
                    if res and res[0] == "HALT" and len(res[1]) >= 4:
                        hits.append((len(res[1]), G, dx, res[1]))
            hits.sort(reverse=True)
            print(f"{pat} tc={tc} x1={x1} min1={min1} rend={info[3]} rend-x1={info[3]-x1} min_d={info[0]} | top_hits={hits[:5]}")
            break
