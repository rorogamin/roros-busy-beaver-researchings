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

def probe_exact_G_match(m, c_pair, t_close, nS, nSym, tsym):
    # Simulates actual machine from t=1 to t_close + 150, recording steps [t_close .. t_close+120]
    tbl1, tbl2 = parse_pair(c_pair, nS, nSym)
    tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    min1 = 0
    real_seq = [] # (p2 - p1, s1, s2, p1, p2)
    for t in range(1, t_close + 130):
        t1 = tbl1[s1][tape.get(p1, 0)]; t2 = tbl2[s2][tape.get(p2, 0)]
        if t1 is None or t2 is None: break
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if t <= t_close + 40 and p1 < min1: min1 = p1
        if t >= t_close:
            real_seq.append((t, p2 - p1, s1, s2, p1, p2))

    # Calibrate synthetic probe: find Ag1's steady chase on tsym^inf after exiting L=10 counter,
    # AND find Ag2's steady glider on blank tape!
    # Wait: in check_local_gap, how is Ag2 phased at G?
    # Let's check for EVERY phase ph in range(m['P']) of steady Ag2! Wait: different G = different relative phase mod M!
    # Wait: WHICH phase of Ag2 corresponds to label G in m['events']?
    # Look at m['events'][G][1]['gs'] and ['gdx']!!
    # Even better: when synthetic probe runs from G, compare BOTH (dt_min_d) AND exact trace suffix when Ag1 returns!
    # Wait: in m['events'][G][1]:
    #   gdx = p2_at_return_to_left - x1_col? Wait let's check on 1LB1RA0LB_2RB2LB2RA|1LB2LA1RB_2RA0RB1RA at t=8224!
    return min1, real_seq

# Check exact calibration on known COL1 examples:
for pair, nS, nSym, t_known, g_known, x1_known in [
    ("1LB1RA0LB_2RB2LB2RA|1LB2LA1RB_2RA0RB1RA", 2, 3, 8224, 14, 1630),
    ("0LB0LB_1LC1RB_0RB0LC|1RB1LB_1LC0LC_1RA0RA", 3, 2, 70384, 10, 4684),
]:
    tbl1, tbl2 = parse_pair(pair, nS, nSym)
    tape = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    for t in range(1, t_known + 30):
        t1 = tbl1[s1][tape.get(p1, 0)]; t2 = tbl2[s2][tape.get(p2, 0)]
        tape[p2] = t2[0]; tape[p1] = t1[0]
        p1 += t1[1]; s1 = t1[2]; p2 += t2[1]; s2 = t2[2]
        if t_known - 4 <= t <= t_known + 20:
            print(f"CALIB {pair[:15]} t={t}: p1={p1}({chr(65+s1)}) p2={p2}({chr(65+s2)}) d={p2-p1} sym_p1={tape.get(p1,0)} sym_p2={tape.get(p2,0)}")
