lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
for name, fn in [("CET3", "r1_exact_cet3.txt"), ("CET23_t1", "r1_exact_cet23_t1.txt"), ("CET23_t2", "r1_exact_cet23_t2.txt")]:
    bigs = []
    for l in open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/" + fn):
        if l.startswith("BIG_R1"):
            pre, mech_full = l.split("\t||")
            mr = int(mech_full.split("\t")[0].split("=")[1])
            m = parse_mech_line(mech_full.split("\t", 1)[1])
            z = [x for x in pre.split("\t") if x.startswith("z_clean=")]
            zc = int(z[0].split("=")[1]) if z else -1
            bigs.append((mr, m["bt"], zc, m["M"], m["pair"], pre))
    bigs.sort(key=lambda x: (-x[0], x[1], x[2]))
    hist = {r: sum(1 for b in bigs if b[0]==r) for r in sorted(set(b[0] for b in bigs), reverse=True)}
    print(f"=== {name}: {len(bigs)} BIG_R1 | MAXR hist: {hist} ===")
    for b in bigs[:15]:
        print(" ", f"MAXR={b[0]} bt={b[1]} zc={b[2]} M={b[3]}", b[4], "|", " ".join(b[5].split("\t")[1:5]))
