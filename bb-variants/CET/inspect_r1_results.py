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

def probe_r1_conc(m, c_pair, col_t, nS, nSym, tsym):
    # First get ground-truth COL1 -> bounce (for any pair where R1 finishes concretely)
    # Wait: how does find_multiround_candidates find G1 and r2min?
    # Simulate from t=0 up to col_t: track tape and exact state, then continue from col_t
    # until Ag1 reaches tsym boundary or finishes bounce!
    # Wait: even simpler! Run up to col_t + 300, check when Ag1 bounces back left (if H -> HALT at col_t+bounce_stp),
    # and match against m["events"] OR compute L2 from x1 and min_x1 after col_t?
    # Wait: r2min in find_multiround_candidates is min(p1) AFTER exiting left into 0^L (or min(p1) during R1!).
    # Wait: let's check BOTH directly by simulating concrete R1 + small R2 verification!
    tbl1, tbl2 = parse_pair(c_pair, nS, nSym)
    tape = {}
    p1, s1, p2, s2 = 0, 0, 2, 0
    r2min_all = 0
    for t in range(1, col_t + 1):
        sym1 = tape.get(p1, 0); sym2 = tape.get(p2, 0)
        t1 = tbl1[s1][sym1]; t2 = tbl2[s2][sym2]
        if t1 is None or t2 is None: return None
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if t < col_t and p1 < r2min_all: r2min_all = p1
    x1 = p1
    # Continue for up to 300 steps to observe bounce vs halt AND confirm L2!
    # Actually test EVERY G in m["B"] (and m["H"]) by checking post-col_t bounce trace!
    # Compare Ag1+Ag2 trace of first 120 steps post-col_t against bounce probe of G!
    col_p1, col_s1, col_p2, col_s2 = p1, s1, p2, s2
    post_pos1 = []
    p1, s1, p2, s2 = col_p1, col_s1, col_p2, col_s2
    r1_min_post = min(tape.keys()) if tape else 0
    # Wait: check whether post-col_t hits a halt within 100 steps!
    halt_t = None
    for dt in range(1, 200):
        sym1 = tape.get(p1, 0); sym2 = tape.get(p2, 0)
        t1 = tbl1[s1][sym1]; t2 = tbl2[s2][sym2]
        if t1 is None or t2 is None: return ("UNDEF", col_t + dt)
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if p1 == p2:
            halt_t = col_t + dt
            return ("HALT2", halt_t, x1)
    # No immediate HALT2 -> it bounced cleanly! Check if p1 moved left past x1 - 30!
    # We also want the EXACT G1! How is G1 matched? Match post_col_t delta!
    # Actually at col_t, we know Ag2's trail began moving at phase? No, test G in sorted(m["B"]) by checking
    # if (col_t - b["gs"]) % m["P"]? Wait: in round k, q2 = (T_round - gs) % P, wait G only depends on Ag2's phase + p2!
    # Easier: reconstruct exact G1 directly by comparing tape[x1 - 5 .. x1 + 30] and Ag2's (s2, dx) against standard bounce from G!
    #Wait: just run standard bounce from each G in sorted(m["B"]) on [0]*400 + [tsym]*400 at COL1, NO: G is at B:gap BEFORE collision!
    return ("BOUNCE", x1, p1 - x1, r2min_all, col_s1, col_s2, [tape.get(x1+d,0) for d in range(-6, 6)])

for fn, nS, nSym, tsym in [
    ("r1_cet3.txt", 3, 2, 1),
    ("r1_cet23_t1.txt", 2, 3, 1),
    ("r1_cet23_t2.txt", 2, 3, 2),
]:
    lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn).read().splitlines()
    print(f"================ {fn} ================")
    for l in lines:
        if l.startswith("CONC"):
            p = l.split("\t")
            maxr = int(p[1].split("=")[1])
            mech_str = "\t".join(p[2:-7])
            kv = dict(x.split("=") for x in p[-7:-1] if "=" in x)
            m = parse_mech_line(mech_str)
            if not m: continue
            col_t = int(kv["t"])
            info = probe_r1_conc(m, m["pair"], col_t, nS, nSym, tsym)
            if info and info[0] == "BOUNCE":
                x1, dx, r2m = info[1], info[2], info[3]
                # Test every G in B whose bounce matches? Let's print x1, r2m, and check ALL B gaps!
                outs = []
                for G in sorted(g for g,v in m["events"].items() if v[0]=="B"):
                    b = m["events"][G][1]
                    L2 = x1 - r2m + b["mna"]
                    res = exact_tower_rounds(m, G, L2, round_start=2, max_depth=16)
                    if res and res[0] == "HALT":
                        outs.append((len(res[1]), G, L2, res[1]))
                outs.sort(reverse=True)
                if outs and outs[0][0] >= 4:
                    print(f"  [CONC WINNER MAXR={maxr}] col_t={col_t} x1={x1} r2m={r2m} {m['pair']} -> {outs[:2]}")
            elif info and info[0] == "HALT2":
                pass #print("  HALT2", info[1], m["pair"])
    # Also inspect first 6 BIG lines with highest MAXR
    bigs = [l for l in lines if l.startswith("BIG")]
    bigs.sort(key=lambda l: int(l.split("\t")[1].split("=")[1]), reverse=True)
    print("  Top 8 BIG lines:")
    for l in bigs[:8]:
        p = l.split("\t")
        print("   ", p[1], p[2], "\t".join(p[-6:]))
