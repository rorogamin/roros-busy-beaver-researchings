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

def trace_conc_pair(m, pair, col_t, nS, nSym):
    tbl1, tbl2 = parse_pair(pair, nS, nSym)
    # Match exact gap G1 at step BEFORE bounce/collision using m["events"]!
    # Also trace ALL approaches (p2 - p1 <= 30) in 1..col_t to see whether Round 1 bounced earlier or col_t IS COL1!
    tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    approaches = []
    min1 = 0
    in_zone = False
    for t in range(1, col_t + 1):
        t1 = tbl1[s1][tape.get(p1,0)]; t2 = tbl2[s2][tape.get(p2,0)]
        if t1 is None or t2 is None: break
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if p1 < min1: min1 = p1
        d = p2 - p1
        if d <= 30 and not in_zone:
            in_zone = True
            approaches.append((t, d, p1, p2, min1, s1, s2))
        elif d > 35:
            in_zone = False
        if p1 == p2:
            # Verify whether halt or continue
            return t, approaches, min1
    return None, approaches, min1

for fn, nS, nSym in [("r1_cet3.txt",3,2), ("r1_cet23_t1.txt",2,3), ("r1_cet23_t2.txt",2,3)]:
    print(f"================ {fn} CONC FULL TRACE ================")
    lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn).read().splitlines()
    seen = set()
    for l in lines:
        if not l.startswith("CONC"): continue
        p = l.split("\t")
        mech_str = "\t".join(p[2:-7])
        kv = dict(x.split("=") for x in p[-7:-1] if "=" in x)
        m = parse_mech_line(mech_str)
        if not m: continue
        col_t = int(kv["t"])
        sig = (col_t, m["M"], m["bt"], m["e_spec"][:9], m["events"].keys())
        # Group by unique behavior
        t_halt, apps, min1 = trace_conc_pair(m, m["pair"], col_t, nS, nSym)
        # Note: in trace_conc_pair, p1 == p2 stops at FIRST p1 == p2!
        # If len(apps) > 1, earlier round(s) bounced WITHOUT p1==p2, and LAST app collided!
        # Wait: let's check BOTH what find_multiround_candidates' exact G matching gives!
        # In find_multiround_candidates: R1 gap G matches when (T_enter - b['gs'])?! No: check gap at step p1 == x1 - ...!
        # Actually print apps (with p2 - p1 at every step near app[-1])!
        key = (col_t, len(apps), m["bt"], m["M"], apps[-1][1] if apps else None)
        if key in seen: continue
        seen.add(key)
        print(f"  t={t_halt} #apps={len(apps)} bt={m['bt']} M={m['M']} P={m['P']} D={m['D']} mg={m['mg']} B={sorted(g for g,v in m['events'].items() if v[0]=='B')} H={sorted(g for g,v in m['events'].items() if v[0]=='H')} | pair={m['pair']}")
        for idx, a in enumerate(apps):
            print(f"     app[{idx}]: t={a[0]} d={a[1]} p1={a[2]} p2={a[3]} min1={a[4]} s1={chr(65+a[5])} s2={chr(65+a[6])}")
