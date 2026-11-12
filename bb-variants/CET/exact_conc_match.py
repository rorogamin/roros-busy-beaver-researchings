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

def find_exact_G1_by_bounce(m, c_pair, nS, nSym, tsym, col_t):
    # First check direct R1 field in m['r1'] if present!
    if m["r1"].startswith("R1=COL1:"):
        rkv = dict(x.split("=") for x in m["r1"][8:].split(":") if "=" in x)
        return int(rkv["gap"]), int(rkv["x1"]), int(rkv["r2min"])
    # Otherwise find exact G1 by simulating R1 up to col_t and checking which G in events produces identical post-col_t trace!
    # Wait: first calibrate steady Ag2 phase & Ag1 chase state from a clean synthetic probe:
    tbl1, tbl2 = parse_pair(c_pair, nS, nSym)
    tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    r2m = 0
    for t in range(1, col_t + 1):
        t1 = tbl1[s1][tape.get(p1, 0)]; t2 = tbl2[s2][tape.get(p2, 0)]
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if t < col_t and p1 < r2m: r2m = p1
    x1 = p1
    # Check post-col_t trace (s1, s2, p1-x1, p2-x1) for 60 steps
    real_tr = []
    p1r, s1r, p2r, s2r = p1, s1, p2, s2
    for dt in range(1, 61):
        t1 = tbl1[s1r][tape.get(p1r, 0)]; t2 = tbl2[s2r][tape.get(p2r, 0)]
        if t1 is None or t2 is None: break
        tape[p2r] = t2[0]; tape[p1r] = t1[0]
        p1r += t1[1]; s1r = t1[2]; p2r += t2[1]; s2r = t2[2]
        real_tr.append((s1r, s2r, p1r - x1, p2r - x1))
        if p1r == p2r: real_tr.append(("HALT", dt)); break

    # Now probe each G in mg..mg+M-1 using steady Ag2 & engine exit_st:
    # 1) Find engine sr & exit_st from e_spec on 0^10 tsym^50:
    # Actually just get steady Ag2 (500 steps on blank tape) shifted to OFF+gap!
    gt = {}; gp, gs = 2, 0
    for _ in range(400):
        tr = tbl2[gs][gt.get(gp, 0)]
        gt[gp] = tr[0]; gp += tr[1]; gs = tr[2]
    gmin = min(k for k in gt if k >= gp - m["P"] - 20)
    # 2) Get Ag1 chase state by running L=10 counter from sr (try all sr in 0..nS-1 on 0^10 tsym^80; only 1 runs counter & exits!)
    e_tbl, _ = parse_pair(m["e_spec"] + "|" + m["e_spec"], nS, nSym)
    # Actually use tbl1 on 0^12 + tsym^300 starting from each state near 12
    chase_st = None
    for cand_sr in range(nS):
        tp = {i: tsym for i in range(12, 200)}
        p, s = 11, cand_sr
        ok = False
        for _ in range(30000):
            tr = tbl1[s][tp.get(p, 0)]
            if tr is None: break
            tp[p] = tr[0]; p += tr[1]; s = tr[2]
            if p < -40: break
            if p >= 25:
                # check if keeps moving right past 80
                for _ in range(300):
                    tr = tbl1[s][tp.get(p, 0)]
                    if tr is None: break
                    tp[p] = tr[0]; p += tr[1]; s = tr[2]
                if p >= 80: chase_st = s; ok = True
                break
        if ok: break

    # Wait: even simpler, try EVERY G in m['events'] and start Ag1 at x_col with EVERY possible (s1_col) -- no,
    # Wait: we ALREADY know b['gs'] from find_multiround_candidates!!
    # At col_t, compare directly against synthetic probe starting with Ag1 at OFF + (G's chase position):
    # Wait why not just test Ag1 starting at OFF - 15 in exit state before hitting gp-shifted?
    # Let's run Ag1 starting at x = 15 (on tape 0^{...} + tsym^{...}) until it hits steady Ag2 starting at OFF+G!
    best_G = []
    mg, M, P = m["mg"], m["M"], m["P"]
    for G in range(mg, mg + M):
        # Put Ag2 at x = 300 + G, in steady (gs, gt) shifted so p2=300+G!
        tp = {}
        for x in range(0, 300): tp[x] = 0
        for x in range(300, 600): tp[x] = tsym
        # Copy Ag2's active neighborhood around gp onto 300+G:
        shift = (300 + G) - gp
        for k, v in gt.items():
            if k >= gp - P: tp[k + shift] = v
        # Run Ag1 starting at x = 285? Wait: we want Ag1 moving right on tsym^inf at steady chase phase!
        # Let's first run Ag1 ALONE on tsym^inf from (20, exit_st) for 100 steps to get chase period!
        # Try ALL 3 phases of Ag1 (or check starting from counter exit at 290!)
        for offset in range(6):
            tp2 = dict(tp)
            # Start Ag1 at 270 - offset on tsym (Wait: 300 is clean; Ag2 starts at 300+G; left edge of tsym at 200!)
            for x in range(200, 300): tp2[x] = tsym
            p1s, s1s = 230 + offset, chase_st if chase_st is not None else 0
            p2s, s2s = 300 + G, gs
            # Run until collision
            col = None
            for step in range(1, 500):
                t1 = tbl1[s1s][tp2.get(p1s, 0)]; t2 = tbl2[s2s][tp2.get(p2s, 0)]
                if t1 is None or t2 is None: break
                tp2[p2s] = t2[0]; tp2[p1s] = t1[0]
                p1s += t1[1]; s1s = t1[2]; p2s += t2[1]; s2s = t2[2]
                if p1s == p2s: col = (step, p1s); break
            if not col: continue
            cx = col[1]
            tr_sim = []
            for dt in range(1, 61):
                t1 = tbl1[s1s][tp2.get(p1s, 0)]; t2 = tbl2[s2s][tp2.get(p2s, 0)]
                if t1 is None or t2 is None: break
                tp2[p2s] = t2[0]; tp2[p1s] = t1[0]
                p1s += t1[1]; s1s = t1[2]; p2s += t2[1]; s2s = t2[2]
                tr_sim.append((s1s, s2s, p1s - cx, p2s - cx))
                if p1s == p2s: tr_sim.append(("HALT", dt)); break
            if tr_sim == real_tr:
                best_G.append(G)
                break
    return best_G, x1, r2m

for fn, nS, nSym, tsym in [("r1_cet3.txt",3,2,1), ("r1_cet23_t1.txt",2,3,1), ("r1_cet23_t2.txt",2,3,2)]:
    lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn).read().splitlines()
    print(f"=== EXACT MATCH {fn} ===")
    best_wins = []
    seen = set()
    for l in lines:
        if not l.startswith("CONC"): continue
        p = l.split("\t")
        mech_str = "\t".join(p[2:-7])
        kv = dict(x.split("=") for x in p[-7:-1] if "=" in x)
        m = parse_mech_line(mech_str)
        if not m: continue
        col_t = int(kv["t"])
        Gs, x1, r2m = find_exact_G1_by_bounce(m, m["pair"], nS, nSym, tsym, col_t)
        if isinstance(Gs, int): Gs = [Gs]
        for G1 in Gs:
            ev = m["events"].get(G1)
            if ev and ev[0] == "B":
                b = ev[1]
                L2 = x1 - r2m + b["mna"]
                res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=20)
                if res and res[0] == "HALT":
                    R = len(res[1])
                    key = (R, m["bt"], G1, L2, tuple(res[1]), m["e_spec"][:12])
                    if R >= 4 and key not in seen:
                        seen.add(key)
                        best_wins.append((R, m["bt"], m["M"], m["P"], m["D"], col_t, G1, L2, res[1], m["pair"]))
    best_wins.sort(reverse=True)
    for w in best_wins[:12]:
        print(" ", w)
