"""
verify_bb44_fw12_and_roro_plus1.py
Standalone raw verifier for:
  1. New BB(4,4) f_omega^12 (> f_{omega+1}(12)) champion:
       TNF:  1RB1LA1RZ3LA_1RC3RB2LC1LB_1RD3RD1RC2LB_2LA3RD1LC0RA
       Core: 3RC1RZ2LA3LA_3RD3RB1LC2RD_3RB1LB3LC2RC_1LA3LB0RA2RD
  2. New roro+1 (4x4, nd=14) f_{omega+1} cores:
       Primary:   3LB3RA2RB1LA_---2RA3LB1LC_---1LD3RB1LC_3RA2RD1RD3RD  (csym=2, (c,k,B)->(c-1,B,N+2))
       Variant B: 3LB3RA2RB1LA_---2RA3LB1LC_---1LD3RB1LC_0LA2RD1RD3RD  (csym=2, (c,k,B)->(c-1,B+1,N))
       Variant A: 3LB3RA2RB1LA_0RD2RA3LB1LC_1LD0LD3RB1LC_1RB------0RA  (csym=3, (c,k,B)->(c-1,2,N+B))
"""

def parse(s):
    t = {}
    for st, row in enumerate(s.split("_")):
        for sym in range(4):
            c = row[3*sym:3*sym+3]
            if c == "---": continue
            t[(st, sym)] = (int(c[0]), 1 if c[1] == "R" else -1, -1 if c[2] == "Z" else ord(c[2]) - 65)
    return t

def verify_bb44_fw12():
    tm_core = "3RC1RZ2LA3LA_3RD3RB1LC2RD_3RB1LB3LC2RC_1LA3LB0RA2RD"
    tm_tnf  = "1RB1LA1RZ3LA_1RC3RB2LC1LB_1RD3RD1RC2LB_2LA3RD1LC0RA"
    t = parse(tm_core)
    assert len(t) == 16

    # 1. Raw blank-tape boot @ step 1380
    tp = {}; p = 0; st = 0; vs = {0}; vsym = {0}
    for _ in range(1380):
        sy = tp.get(p, 0); vsym.add(sy)
        w, d, ns = t[(st, sy)]
        assert ns != -1
        vsym.add(w); tp[p] = w; p += d; st = ns; vs.add(st)
    nz = [q for q, v in tp.items() if v != 0]
    s = "".join(str(tp.get(q, 0)) for q in range(min(nz), max(nz) + 1))
    assert vs == {0, 1, 2, 3} and vsym == {0, 1, 2, 3}
    assert st == 3 and p == max(nz) and s == "3" + "2" * 32 + "1"

    # 2. Verify TNF boot @ step 1380
    tt = parse(tm_tnf)
    tp = {}; p = 0; st = 0
    for _ in range(1380):
        w, d, ns = tt[(st, tp.get(p, 0))]
        assert ns != -1
        tp[p] = w; p += d; st = ns
    nz = [q for q, v in tp.items() if v != 0]
    s_tnf = "".join(str(tp.get(q, 0)) for q in range(min(nz), max(nz) + 1))
    assert st == 3 and p == max(nz) and s_tnf == "1" + "3" * 32 + "2"

    # 3. Verify P=4 A-wrapper on B=4..23, N in {13, 29, 45}
    for B in range(4, 24):
        q, rem = divmod(B, 4)
        for N in (13, 29, 45):
            tp = {i: 3 for i in range(N)}
            for i in range(B): tp[N + i] = 2
            p = N + B; st = 3
            for step in range(1, 80000):
                w, d, ns = t[(st, tp.get(p, 0))]
                if ns == -1:
                    assert rem == 3
                    break
                tp[p] = w; p += d; st = ns
                if step >= 3 and st == 3 and tp.get(p, 0) == 1:
                    nz = [x for x, v in tp.items() if v != 0]
                    l, h = min(nz), max(nz)
                    u = p - 1; Bn = 0
                    while u >= l and tp.get(u, 0) == 2: Bn += 1; u -= 1
                    a = 0
                    while u >= l and tp.get(u, 0) == 3: a += 1; u -= 1
                    v = p; r = 0
                    while v <= h and tp.get(v, 0) == 1: r += 1; v += 1
                    if u < l and a == 1 and v > h:
                        assert Bn == N + 5 * q + (2 * rem - 1) and r == 3 - rem
                        break
            else:
                raise AssertionError(f"Wrapper timeout at B={B}, N={N}")

    # 4. Exact 2-adic orbit from B_1 = 32
    mod = 1 << 30; B = 32
    for pass_i in range(1, 20):
        rem = B % 4
        if rem == 3:
            assert pass_i == 13
            break
        q = (B - rem) // 4
        B = (-3 + 5 * q + (2 * rem - 1)) % (mod // 4)
        mod //= 4
    print("[PASS] BB(4,4) f_omega^12 (> f_{omega+1}(12)) champion verified!")

def verify_roro_plus1():
    cores = [
        ("Primary",   2, "3LB3RA2RB1LA_---2RA3LB1LC_---1LD3RB1LC_3RA2RD1RD3RD", "B0", lambda B, N: (B, N + 2)),
        ("Variant B", 2, "3LB3RA2RB1LA_---2RA3LB1LC_---1LD3RB1LC_0LA2RD1RD3RD", "B0", lambda B, N: (B + 1, N)),
        ("Variant A", 3, "3LB3RA2RB1LA_0RD2RA3LB1LC_1LD0LD3RB1LC_1RB------0RA", "D1", lambda B, N: (2, N + B)),
    ]
    for name, csym, tm, exp_exit, fn in cores:
        t = parse(tm)
        assert len(t) == 14
        for c_in in (0, 1, 2, 3):
            for B in (4, 5, 6):
                for N in (12, 28):
                    tp = {}
                    for i in range(c_in): tp[-c_in + i] = csym
                    for i in range(B): tp[i] = 1
                    for i in range(N + 1): tp[B + i] = 3
                    p = 0; st = 2 # [C:1]
                    for step in range(1, 20000):
                        sy = tp.get(p, 0)
                        if (st, sy) not in t:
                            assert c_in == 0 and f"{chr(65+st)}{sy}" == exp_exit
                            break
                        w, d, ns = t[(st, sy)]
                        tp[p] = w; p += d; st = ns
                        if step >= 3 and st == 0 and tp.get(p, 0) == 0:
                            nz = [q for q, v in tp.items() if v != 0]
                            if nz and max(nz) < p:
                                l = min(nz); q = p - 1; Bn = 0
                                while q >= l and tp.get(q, 0) == 3: Bn += 1; q -= 1
                                k = 0
                                while q >= l and tp.get(q, 0) == 2: k += 1; q -= 1
                                if q >= l and tp.get(q, 0) == 1 and k >= 2 and Bn >= 3:
                                    q -= 1; cn = 0
                                    while q >= l and tp.get(q, 0) == csym: cn += 1; q -= 1
                                    if q < l:
                                        ek, eB = fn(B, N)
                                        assert cn == c_in - 1 and k == ek and Bn == eB
                                        break
                    else:
                        raise AssertionError(f"Timeout {name} c={c_in}, B={B}, N={N}")
        print(f"[PASS] roro+1 {name} (nd=14, csym={csym}, exit={exp_exit}) verified: {tm}")

if __name__ == "__main__":
    verify_bb44_fw12()
    verify_roro_plus1()
