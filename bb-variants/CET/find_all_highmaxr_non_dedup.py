lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

def max_r_for_events(m, min_target):
    # Iterative deepening K = 6, 10, 14 so huge get_mod_chain(25) never runs unnecessarily!
    best_r = 0
    for G, ev in m["events"].items():
        if ev[0] != "B": continue
        for L2 in range(10, 40):
            for K in (6, 10, 14):
                res = exact_tower_rounds(m, G, L2, round_start=2, max_depth=K)
                if not res: break
                if res[0] == "HALT":
                    r = len(res[1])
                    if r > best_r: best_r = r
                    if r >= 14: return r
                    break
                if res[0] != "ALIVE": break
    return best_r

for name, mfile, out_file, min_target in [
    ("CET3", "mechs_cet3.txt", "all_high_cet3.txt", 4),
    ("CET23_t1", "mechs_cet23_t1.txt", "all_high_cet23_t1.txt", 9),
    ("CET23_t2", "mechs_cet23_t2.txt", "all_high_cet23_t2.txt", 9),
]:
    full = "C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/"
    sig_cache = {}
    out_lines = []
    tot = 0
    for l in open(full + mfile):
        l = l.rstrip("\r\n")
        tot += 1
        m = parse_mech_line(l)
        if not m: continue
        # Build canonical events key (bt, P, D, H, sorted B formula tuples)
        ev_key = (m["bt"], m["P"], m["D"], m["mg"],
                  tuple((g, ev[0], (ev[1]["xr"], ev[1]["ts"], ev[1]["lp"], ev[1]["w"], ev[1]["gdx"], ev[1]["gs"], ev[1]["mna"], str(ev[1]["form"])) if ev[0]=="B" else ev[1])
                        for g, ev in sorted(m["events"].items())))
        if ev_key not in sig_cache:
            sig_cache[ev_key] = max_r_for_events(m, min_target)
        mr = sig_cache[ev_key]
        if mr >= min_target:
            out_lines.append(f"MAXR={mr}\t{l}")
    with open(full + out_file, "w") as fo:
        fo.write("\n".join(out_lines) + "\n")
    hist = {}
    for s in out_lines:
        r = int(s.split("\t")[0].split("=")[1])
        hist[r] = hist.get(r, 0) + 1
    print(f"{name}: {tot} total lines -> {len(out_lines)} lines with MAXR>={min_target} | unique sigs={len(sig_cache)} | hist={dict(sorted(hist.items(), reverse=True))}")
