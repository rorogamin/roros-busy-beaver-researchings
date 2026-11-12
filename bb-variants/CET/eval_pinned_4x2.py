lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

wins = []
alives = []
seen = set()
tot = 0
for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/pinned_cet4_smoke.txt"):
    col1_str, rest = l.split("\t||", 1)
    if not col1_str.startswith("R1=COL1:"): continue
    tot += 1
    rkv = dict(x.split("=") for x in col1_str[8:].split(":") if "=" in x)
    # Strip MAXR=.. AL7=..
    parts = rest.split("\t")
    idx = 0
    while idx < len(parts) and ("|" not in parts[idx]): idx += 1
    mech_str = "\t".join(parts[idx:])
    m = parse_mech_line(mech_str)
    if not m: continue
    G1 = int(rkv["gap"]); x1 = int(rkv["x1"]); r2min = int(rkv["r2min"])
    m1 = int(rkv["m1"]); m2 = int(rkv["m2"])
    if m1 != 15 or m2 != 15: continue # strictly all 4 states executed in R1!
    if G1 not in m["events"] or m["events"][G1][0] != "B": continue
    b = m["events"][G1][1]
    L2 = x1 - r2min + b["mna"]
    # Step up K = 6, 10, 14 (fast!)
    res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=6)
    if res and res[0] == "ALIVE" and len(set(res[1][-3:])) > 1:
        res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=10)
    if res and res[0] == "ALIVE" and len(set(res[1][-4:])) > 2:
        res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=14)
    if res and res[0] == "HALT" and len(res[1]) >= 4:
        sig = (len(res[1]), m["bt"], m["M"], G1, L2, tuple(res[1]))
        if sig not in seen:
            seen.add(sig)
            wins.append((len(res[1]), int(rkv["t"]), m["bt"], m["M"], G1, L2, rkv["cz"], rkv["lw"], res[1], m["pair"]))
    elif res and res[0] == "ALIVE":
        alives.append((len(res[1]), int(rkv["t"]), m["bt"], m["M"], G1, L2, res[1], m["pair"]))

wins.sort(key=lambda x: (-x[0], x[2], -x[5], x[1]))
print(f"CET4 smoke pinned COL1 (all4 in R1): {tot} | unique wins (R>=4)={len(wins)} | ALIVE(>=11R)={len(alives)}")
for w in wins[:25]:
    print(f"  R={w[0]} t1={w[1]} bt={w[2]} M={w[3]} G1={w[4]} L2={w[5]} cz={w[6]} lw={w[7]} seq={w[8]} | {w[9]}")
if alives:
    print("Non-looping or deep ALIVE:")
    for a in alives[:10]:
        print(" ", a)
