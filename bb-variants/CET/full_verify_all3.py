import io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et
from verify_all3_champions import parse_tm, inspect_glider_and_counter

def verify_one(name, line, n_syms, G1, L2, max_depth=20):
    print("=" * 80)
    print(f"FULL VERIFICATION: {name}")
    m = et.parse_mech_line(line)
    st, seq, _ = et.exact_tower_rounds(m, G1, L2, round_start=2, max_depth=max_depth)
    print(f"Tower result: status={st}, rounds={len(seq)}, seq={seq}")

    m, T1, T2, ex, tsym, cp2, cs2, ctp = inspect_glider_and_counter(name, line, n_syms)
    P, D, M = m['P'], m['D'], m['M']
    tp_g = {k - cp2: v for k, v in ctp.items() if k >= cp2 - 5 and k <= cp2 + 15}

    anc = 2 if n_syms == 3 else 0
    unique_Gs = []
    for g in seq[:-1]:
        if g not in unique_Gs: unique_Gs.append(g)

    for G in unique_Gs:
        ev = m['events'][G][1]
        xr, gdx, gs, mna = ev['xr'], ev['gdx'], ev['gs'], ev['mna']
        print(f"\n  --- B[{G}]: L0={ev['L0']} xr={xr} gdx={gdx} gs={gs} mna={mna} form={ev['form']} ---")
        for L in (11, 12, 13, 14):
            # Setup coupled tape: x < -L is 0, x = -L is anc, -L+1 .. G-6 is tsym, G-5..G+15 is tp_g
            tl = {}
            for x in range(-L + 1, G - 5): tl[x] = tsym
            tl[-L] = anc
            for dx, val in tp_g.items():
                tl[G + dx] = val
            p1, s1, p2, s2 = 0, ex, G, cs2
            min_p1 = 0; t_min = 0; snap_min = ""; s_min = ""
            exited = False
            for t in range(1, 5000000):
                v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
                w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
                tl[p2] = w2; tl[p1] = w1
                p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
                if p1 < min_p1:
                    min_p1 = p1; t_min = t; s_min = chr(65+s1)
                    snap_min = ''.join(str(tl.get(x, 0)) for x in range(min_p1 - 2, min_p1 + 16))
                if p1 == p2:
                    print(f"    L={L}: EARLY COLLIDE at t={t}, p1={p1}")
                    break
                if p1 == xr and s1 == ex and t > 20:
                    # Wait: check if all cells ahead up to p2-10 are tsym!
                    # Eval formula at L_eff = L + 1? Let's check exact T_formula(L_eff) from ev['form']!
                    # Note L_eff = 0 - (-L) = L? Wait in ev['form'], L0=11 means L_eff = L + mna? Let's print both!
                    print(f"    L={L}: reach p1=xr={xr}({chr(65+s1)}) at t={t}, min_p1={min_p1}(at t={t_min},{s_min}), p2={p2}({chr(65+s2)}), left={snap_min}")
                    exited = True
                    break
            if not exited:
                print(f"    L={L}: DID NOT REACH xr={xr} cleanly")

    # Verify H[seq[-1]]
    HG = seq[-1]
    tl = {x: tsym for x in range(-40, HG - 20)}
    for dx, val in tp_g.items(): tl[HG + dx] = val
    p1, s1, p2, s2 = 0, ex, HG, cs2
    for t in range(1, 200):
        v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
        w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
        tl[p2] = w2; tl[p1] = w1
        p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
        if p1 == p2:
            print(f"\n  H[{HG}] verified: COLLIDE at t={t}, x={p1}, s1={chr(65+s1)}, s2={chr(65+s2)}")
            break

cet3_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt')
                 if l.startswith('1LB0LA_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA\t'))
cet23_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet23_t1.txt')
                  if l.startswith('1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA\t'))
cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))

verify_one("CET(3) R=7", cet3_line, 2, 18, 178956975, max_depth=10)
verify_one("CET(2,3) R=8", cet23_line, 3, 10, 86, max_depth=12)
verify_one("CET(4) R=15", cet4_line, 2, 18, 190, max_depth=20)
