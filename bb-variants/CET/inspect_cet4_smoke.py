lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

# Check FAST K=6 (catches R<=7 immediately with tiny integers!) on mechs_cet4_smoke.txt!
# Also track which sigs stay ALIVE at R>=7!
path = "C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/mechs_cet4_smoke.txt"
sig_cache = {}
out_lines = []
tot = 0
hist = {}
alive7_lines = []
for l in open(path):
    l = l.rstrip("\r\n")
    tot += 1
    m = parse_mech_line(l)
    if not m: continue
    ev_key = (m["bt"], m["P"], m["D"], m["mg"],
              tuple((g, ev[0], (ev[1]["xr"], ev[1]["ts"], ev[1]["lp"], ev[1]["w"], ev[1]["gdx"], ev[1]["gs"], ev[1]["mna"], str(ev[1]["form"])) if ev[0]=="B" else ev[1])
                    for g, ev in sorted(m["events"].items())))
    if ev_key not in sig_cache:
        best_r = 0
        got_alive7 = False
        for G, ev in m["events"].items():
            if ev[0] != "B": continue
            for L2 in range(10, 32):
                res = exact_tower_rounds(m, G, L2, round_start=2, max_depth=6)
                if not res: break
                if res[0] == "HALT":
                    r = len(res[1])
                    if r > best_r: best_r = r
                elif res[0] == "ALIVE":
                    # Not periodic constant loop?
                    if len(set(res[1][-3:])) > 1:
                        got_alive7 = True
        sig_cache[ev_key] = (best_r, got_alive7)
    mr, al7 = sig_cache[ev_key]
    hist[mr] = hist.get(mr, 0) + 1
    if mr >= 5 or al7:
        out_lines.append(f"MAXR={mr}\tAL7={int(al7)}\t{l}")
open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/high_cet4_smoke.txt", "w").write("\n".join(out_lines) + "\n")
print(f"CET4 smoke: total={tot} unique_sigs={len(sig_cache)} | hist={dict(sorted(hist.items(), reverse=True))} | saved={len(out_lines)}", flush=True)
