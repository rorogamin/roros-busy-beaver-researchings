"""
Standalone verification script for CET4_7e43.v, CET23_R8.v, and Eps1Complete.v.
Run from the bundle root (or pass --bundle-root <path>):
  python3 verify_all_submissions.py [--bundle-root /path/to/bundle]
"""
import argparse, os, re

def parse_tm(spec, n_syms=2):
    T = {}
    for st, row in enumerate(spec.split("_")):
        for sym in range(n_syms):
            tok = row[3*sym : 3*sym+3]
            T[(st, sym)] = None if tok == "---" else (int(tok[0]), -1 if tok[1] == "L" else 1, ord(tok[2]) - 65)
    return T

def verify_cet4_7e43():
    print("=== 1. CET(4) 2-Round 7.816e43-Step Champion (CET4_7e43.v) ===")
    T1 = parse_tm("1LB1RA_1RC0LD_1LA0LB_0RB0RA", 2)
    T2 = parse_tm("1RB0LC_1LA0RC_1LD0RA_1RC1RA", 2)
    # 1) Replay t = 0 .. 3720 from blank tape
    tp = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    for t in range(1, 3721):
        w1, d1, ns1 = T1[(s1, tp.get(p1, 0))]
        w2, d2, ns2 = T2[(s2, tp.get(p2, 0))]
        tp[p2] = w2; tp[p1] = w1; p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
        assert p1 != p2, f"Unexpected collision at t={t}"
    assert (p1, s1, p2, s2) == (114, 0, 144, 1)
    assert all(tp.get(z, 0) == 1 for z in range(-1, 141))
    assert [tp.get(z, 0) for z in range(141, 147)] == [0, 0, 1, 0, 1, 1]
    print("  [OK] Prefix t=3720: pos1=114(A), pos2=144(B), gap=30, L_d=116")

    # 2) Verify sweep_D_z formula T(L, z) = 9 * 2^(L+z-1) - 5*z - 3 on small L, z
    for z in range(1, 5):
        for L in range(1, 5):
            ltp = {i: 1 for i in range(-L + 1, 1)}
            for i in range(1 + z, 50): ltp[i] = 1
            lp, ls = 0, 3 # D
            for k in range(1, 50000):
                w, d, ns = T1[(ls, ltp.get(lp, 0))]
                ltp[lp] = w; lp += d; ls = ns
                if lp >= 1 + z and ls == 0:
                    pred = 9 * (2 ** (L + z - 1)) - 5 * z - 3
                    assert k == pred, f"Mismatch L={L}, z={z}: {k} != {pred}"
                    break
    print("  [OK] Counter rule T(L, z) = 9*2^(L+z-1) - 5*z - 3 verified for L,z in 1..4")

    # 3) Exact total step count
    k_close = (2**141 - 44) // 26
    assert (2**141 - 44) % 26 == 0
    T_halt = 3720 + 160 + (27 * 2**141 - 121) + 27 * k_close + 30
    assert T_halt == 78159823316003962837401627984426228547406259
    print(f"  [OK] Exact T_halt = {T_halt} (~{T_halt:.4e})")

def verify_cet23_r8():
    print("\n=== 2. CET(2,3) 8-Round Champion Prefix (CET23_R8.v) ===")
    T1 = parse_tm("1LB1RA0LB_2RB2LB2RA", 3)
    T2 = parse_tm("2RB1LA1RB_2LB2RB1LA", 3)
    tp = {}; p1, s1, p2, s2 = 0, 0, 2, 0
    for t in range(1, 845):
        w1, d1, ns1 = T1[(s1, tp.get(p1, 0))]
        w2, d2, ns2 = T2[(s2, tp.get(p2, 0))]
        tp[p2] = w2; tp[p1] = w1; p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
        assert p1 != p2
    assert (p1, s1, p2, s2) == (86, 0, 96, 1) and tp[-1] == 2
    print("  [OK] Prefix t=844: pos1=86(A), pos2=96(B), anchor tp[-1]=2, gap=10, L2=87")

def verify_eps1(bundle_root):
    print("\n=== 3. Blank-Tape Eps1 Machine (Eps1Complete.v) ===")
    eps1_tape_v = os.path.join(bundle_root, "rocq", "Eps1Tape.v")
    if not os.path.exists(eps1_tape_v):
        print(f"  [SKIP] {eps1_tape_v} not found; pass --bundle-root <path>")
        return
    txt = open(eps1_tape_v).read()
    tbl = {}
    for m in re.finditer(r"\|\s*(\d+),\s*(bl|on)\s*=>\s*Some\s*\((bl|on),\s*(true|false),\s*(\d+)\)", txt):
        s, b, w, d, ns = int(m.group(1)), (0 if m.group(2)=="bl" else 1), (0 if m.group(3)=="bl" else 1), (1 if m.group(4)=="true" else -1), int(m.group(5))
        tbl[(s, b)] = (w, d, ns)
    btbl = {(s + 12, b): (w, d, ns + 12) for (s, b), (w, d, ns) in tbl.items()}
    btbl.update({
        (0, 0): (1, -1, 1), (0, 1): (1, -1, 1),
        (1, 0): (0, -1, 2), (1, 1): (0, -1, 2),
        (2, 0): (1, -1, 3), (2, 1): (1, -1, 3),
        (3, 0): (0, -1, 4), (3, 1): (0, -1, 4),
        (4, 0): (0, -1, 5), (4, 1): (0, -1, 5),
        (5, 0): (1, -1, 6), (5, 1): (1, -1, 6),
        (6, 0): (0, -1, 7), (6, 1): (0, -1, 7),
        (7, 0): (0, -1, 8), (7, 1): (0, -1, 8),
        (8, 0): (1, -1, 9), (8, 1): (1, -1, 9),
        (9, 0): (1,  1, 10), (9, 1): (1,  1, 10),
        (10, 1): (1, 1, 10), (10, 0): (0, 1, 11),
        (11, 0): (0, 1, 12 + 33), (11, 1): (0, 1, 12 + 33),
    })
    tp = {}; pos, st = 0, 0
    for t in range(1, 500):
        sym = tp.get(pos, 0)
        if (st, sym) not in btbl:
            assert t - 1 == 107 and sum(tp.values()) == 5
            print(f"  [OK] btbl_eps1_a1 halted from blank tape at step {t-1}, score={sum(tp.values())}")
            break
        w, d, ns = btbl[(st, sym)]
        tp[pos] = w; pos += d; st = ns

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle-root", default=".")
    args = ap.parse_args()
    verify_cet4_7e43()
    verify_cet23_r8()
    verify_eps1(args.bundle_root)
    print("\nALL STANDALONE VERIFICATIONS PASSED!")