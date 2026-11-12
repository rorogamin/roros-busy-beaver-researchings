lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
max_theoretical_rounds = ns["max_theoretical_rounds"] if "max_theoretical_rounds" in ns else None

# Wait check exact names in ns!
print("ns keys:", [k for k in ns if callable(ns[k])])

# 1. Check splicing BIG_R1 on our top candidates!
def parse_ag1(s, nSym):
    a = s.split("|")[0]
    return [[(int(blk[i*3]), -1 if blk[i*3+1]=="L" else 1, ord(blk[i*3+2])-65) if blk[i*3]!='-' else None for i in range(nSym)] for blk in a.split("_")]

tests = [
    ("CET3 zc=30", "0LB0LB_1LC1RB_0RB0LC|0RB---_1RC0LC_1LB0RA", 2, 1),
    ("CET3 zc=14", "1LB---_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA", 2, 1),
    ("CET23_t1 zc=16", "1LB1RA2LB_0RA0LB---|2LB2RB1RB_2RA0LA1LB", 3, 1),
    ("CET23_t1 zc=0", "1LB1RA0LB_1RB2LB2RA|2LB2RA1LB_1RB1LA1RA", 3, 1),
    ("CET23_t2 zc=10", "1LB2LB2RA_1RB1RA0LB|2LB2RB0RB_2RA0RB1LB", 3, 2),
    ("CET23_t2 zc=18", "1LB2LB2RA_0RA---0LB|2RB2LA0RB_2LB0RA1LA", 3, 2),
]
for label, pair, nSym, tsym in tests:
    tbl1 = parse_ag1(pair, nSym)
    # Get 20k tape snapshot of R1 using Ag2!
    b = pair.split("|")[1]
    tbl2 = [[(int(blk[i*3]), -1 if blk[i*3+1]=="L" else 1, ord(blk[i*3+2])-65) if blk[i*3]!='-' else None for i in range(nSym)] for blk in b.split("_")]
    tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    min1, max1 = 0, 0
    for t in range(1, 20001):
        t1 = tbl1[s1][tape.get(p1,0)]; t2 = tbl2[s2][tape.get(p2,0)]
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if p1 < min1: min1 = p1
        if p1 > max1: max1 = p1
    # Check cycle in 1M steps on Ag1 alone (since Ag2 is far away!) OR splice 0-block if zc >= 10!
    seen = {}
    loop_info = None
    tp = dict(tape); q1, qs1 = p1, s1
    mx = max1
    for t in range(1, 100001):
        tr = tbl1[qs1][tp.get(q1,0)]
        if tr is None: loop_info = f"HALT_AG1@{t}"; break
        tp[q1] = tr[0]; q1 += tr[1]; qs1 = tr[2]
        if q1 > mx: mx = q1
        if q1 == min1 and t > 10:
            snap = (qs1, tuple(tp.get(i,0) for i in range(min1, mx+1)))
            if snap in seen:
                loop_info = f"LOOP period={t - seen[snap]} t={t} mx={mx}"
                break
            seen[snap] = t
    # Also splice clean zero block (if any) down to L_s = 4,5,6!
    arr = [tape.get(i,0) for i in range(min1, max1+5)]
    # find trailing non-tsym? Look for longest run of 0s before tsym!
    tsym_pos = next((i for i in range(len(arr)-1, -1, -1) if arr[i] != tsym), len(arr)-1) + 1
    z_end = tsym_pos
    while z_end > 0 and arr[z_end-1] != 0: z_end -= 1
    z_start = z_end
    while z_start > 0 and arr[z_start-1] == 0: z_start -= 1
    zc = z_end - z_start
    splice_res = []
    if zc >= 8:
        prefix = arr[:z_start]
        rel_p1 = p1 - min1
        if rel_p1 < z_start:
            for ls in (4, 5, 6):
                st = list(prefix) + [0]*ls + [tsym]*200
                tp2 = {i: v for i, v in enumerate(st)}
                qp, qs = rel_p1, s1
                exit_t = None
                for k in range(1, 200000):
                    tr = tbl1[qs][tp2.get(qp,0)]
                    if tr is None: break
                    tp2[qp] = tr[0]; qp += tr[1]; qs = tr[2]
                    if qp >= len(prefix) + ls + 10:
                        exit_t = (k, chr(65+qs)); break
                splice_res.append((ls, exit_t))
    print(f"{label}: {loop_info} | zc={zc} splices={splice_res}")
