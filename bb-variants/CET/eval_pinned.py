lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

for name, fn in [
    ("CET(3)", "pinned_cet3.txt"),
    ("CET(2,3) t1", "pinned_cet23_t1.txt"),
    ("CET(2,3) t2", "pinned_cet23_t2.txt"),
]:
    print(f"================ {name} PINNED BOUNCE_R1 ================")
    rows = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn).read().splitlines()
    stats = {}
    wins = []
    seen = set()
    mismatches = 0
    for l in rows:
        col1_str, rest = l.split("\t||", 1)
        tag = col1_str.split(":")[0]
        stats[tag] = stats.get(tag, 0) + 1
        if not col1_str.startswith("R1=COL1:"):
            continue
        rkv = dict(x.split("=") for x in col1_str[8:].split(":") if "=" in x)
        # rest is BOUNCE_R1...\t||MAXR=..\t<mech_str>
        mech_full = rest.split("\t||", 1)[1]
        mech_str = mech_full.split("\t", 1)[1]
        m = parse_mech_line(mech_str)
        if not m: continue
        if m["r1"].startswith("R1=COL1:"):
            okv = dict(x.split("=") for x in m["r1"][8:].split(":") if "=" in x)
            if okv["gap"] != rkv["gap"] or okv["t"] != rkv["t"] or okv["x1"] != rkv["x1"]:
                mismatches += 1
        G1 = int(rkv["gap"])
        x1 = int(rkv["x1"])
        r2min = int(rkv["r2min"])
        if G1 in m["events"] and m["events"][G1][0] == "B":
            b = m["events"][G1][1]
            L2 = x1 - r2min + b["mna"]
            res = exact_tower_rounds(m, G1, L2, round_start=2, max_depth=30)
            if res and res[0] == "HALT" and len(res[1]) >= 4:
                sig = (len(res[1]), m["bt"], tuple(res[1]), m["P"], m["D"], m["M"], G1, L2)
                if sig not in seen:
                    seen.add(sig)
                    wins.append((len(res[1]), int(rkv["t"]), m["bt"], m["M"], G1, L2, res[1], rkv["cz"], rkv["lw"], m["pair"]))
            elif res and res[0] == "ALIVE":
                print(f"  ALIVE?! len={len(res[1])} t={rkv['t']} G1={G1} L2={L2} seq={res[1]} {m['pair']}")
    wins.sort(key=lambda x: (-x[0], x[2], -x[5], x[1]))
    print(f"  stats={stats} orig_mismatches={mismatches} unique_wins(R>=4)={len(wins)}")
    for w in wins[:15]:
        print(f"  R={w[0]} t1={w[1]} bt={w[2]} M={w[3]} G1={w[4]} L2={w[5]} cz={w[7]} lw={w[8]} seq={w[6]} | {w[9]}")
