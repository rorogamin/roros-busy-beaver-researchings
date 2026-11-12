lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

# Filter high_cet3_exh.txt: keep all MAXR>=5 AND check K=10 on AL7 sigs (ignoring period 1..4 cycles in seq unless escaping)!
path = "C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/high_cet3_exh.txt"
sig_deep = {}
kept = []
for l in open(path):
    l = l.rstrip("\r\n")
    if not l: continue
    p0, p1, rest = l.split("\t", 2)
    mr = int(p0.split("=")[1]); al7 = int(p1.split("=")[1])
    if mr >= 5:
        kept.append(f"MAXR={mr}\t{rest}")
        continue
    m = parse_mech_line(rest)
    if not m: continue
    ev_key = (m["bt"], m["P"], m["D"], m["mg"],
              tuple((g, ev[0], (ev[1]["xr"], ev[1]["ts"], ev[1]["lp"], ev[1]["w"], ev[1]["gdx"], ev[1]["gs"], ev[1]["mna"], str(ev[1]["form"])) if ev[0]=="B" else ev[1])
                    for g, ev in sorted(m["events"].items())))
    if ev_key not in sig_deep:
        best_r = 0; deep_al = False
        # First check which (G, L2) gave ALIVE at K=6 and check K=11 ONLY if not tiny cycle
        for G, ev in m["events"].items():
            if ev[0] != "B": continue
            for L2 in range(10, 32):
                r6 = exact_tower_rounds(m, G, L2, round_start=2, max_depth=6)
                if r6 and r6[0] == "ALIVE":
                    s = r6[1]
                    # Check period <= 3 on last 4 items (if period 1 or 2 already entered in <=3 steps? No, test K=11 directly only if period != 1,2 OR first time seen!)
                    if s[-1] == s[-2] and s[-2] == s[-3]: continue
                    if len(s) >= 5 and s[-1] == s[-3] and s[-2] == s[-4]: continue
                    if len(s) >= 7 and s[-1] == s[-4] and s[-2] == s[-5] and s[-3] == s[-6]: continue
                    r11 = exact_tower_rounds(m, G, L2, round_start=2, max_depth=11)
                    if r11 and r11[0] == "HALT":
                        rr = len(r11[1])
                        if rr > best_r: best_r = rr
                    elif r11 and r11[0] == "ALIVE":
                        t = r11[1]
                        if not (t[-1]==t[-3] and t[-2]==t[-4]) and not (t[-1]==t[-4] and t[-2]==t[-5]):
                            deep_al = True
        sig_deep[ev_key] = (best_r, deep_al)
    br, dal = sig_deep[ev_key]
    if br >= 5 or dal:
        kept.append(f"MAXR={br if br else 12}\t{rest}")

open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/high5_cet3_exh.txt", "w").write("\n".join(kept) + "\n")
print(f"Filtered CET3 high>=5 / deep_alive -> {len(kept)} lines saved to high5_cet3_exh.txt!", flush=True)
