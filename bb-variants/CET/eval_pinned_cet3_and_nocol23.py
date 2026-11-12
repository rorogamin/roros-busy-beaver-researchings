lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

# 1. Evaluate pinned_cet3_exh.txt (607 COL1 items!)
wins3 = []
alives3 = []
seen3 = set()
tot3 = 0
for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/pinned_cet3_exh.txt"):
    col1_str, rest = l.split("\t||", 1)
    if not col1_str.startswith("R1=COL1:"): continue
    tot3 += 1
    rkv = dict(x.split("=") for x in col1_str[8:].split(":") if "=" in x)
    mech_str = rest.split("\t", 1)[1]
    m = parse_mech_line(mech_str)
    if not m: continue
    G1 = int(rkv["gap"]); x1 = int(rkv["x1"]); r2min = int(rkv["r2min"])
    m1 = int(rkv["m1"]); m2 = int(rkv["m2"])
    if G1 not in m["events"] or m["events"][G1][0] != "B": continue
    b = m["events"][G1][1]
    L2 = x1 - r2min + b["mna"]
    res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=6)
    if res and res[0] == "ALIVE" and len(set(res[1][-3:])) > 1:
        res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=11)
    if res and res[0] == "ALIVE" and len(set(res[1][-4:])) > 2:
        res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=16)
    if res and res[0] == "HALT" and len(res[1]) >= 4:
        sig = (len(res[1]), m["bt"], m["M"], G1, L2, tuple(res[1]))
        if sig not in seen3:
            seen3.add(sig)
            wins3.append((len(res[1]), int(rkv["t"]), m["bt"], m["M"], G1, L2, rkv["cz"], rkv["lw"], m1, m2, res[1], m["pair"]))
    elif res and res[0] == "ALIVE":
        alives3.append((len(res[1]), int(rkv["t"]), m["bt"], m["M"], G1, L2, m1, m2, res[1], m["pair"]))

wins3.sort(key=lambda x: (-x[0], x[2], -x[5], x[1]))
print(f"================ EXHAUSTIVE CET(3) PINNED COL1: {tot3} | unique wins (R>=4)={len(wins3)} | ALIVE(>=12R)={len(alives3)} ================")
for w in wins3[:25]:
    print(f"  R={w[0]} t1={w[1]} bt={w[2]} M={w[3]} G1={w[4]} L2={w[5]} cz={w[6]} lw={w[7]} m1={w[8]} m2={w[9]} seq={w[10]} | {w[11]}")
if alives3:
    print("Deep ALIVE CET3:")
    for a in alives3[:10]: print(" ", a)
