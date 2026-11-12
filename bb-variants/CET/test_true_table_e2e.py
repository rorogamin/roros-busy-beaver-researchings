import io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et
from verify_all3_champions import parse_tm, inspect_glider_and_counter

def test_e2e(name, line, n_syms, G, Lp_vals):
    print("=" * 60)
    print(f"END-TO-END COUPLED TEST: {name} G={G}")
    m, T1, T2, ex, tsym, cp2, cs2, ctp = inspect_glider_and_counter(name, line, n_syms)
    tp_g = {k - cp2: v for k, v in ctp.items() if k >= cp2 - 5 and k <= cp2 + 15}
    P, D, M = m['P'], m['D'], m['M']
    anc = 2 if n_syms == 3 else 0

    for Lp in Lp_vals:
        x_anc = -Lp
        tl = {x: tsym for x in range(x_anc + 1, G - 5)}
        tl[x_anc] = anc
        for dx, val in tp_g.items(): tl[G + dx] = val
        p1, s1, p2, s2 = 0, ex, G, cs2
        # Run full coupled until Ag1 catches Ag2 in canon phase!
        for t in range(1, 5000000):
            v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
            w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
            tl[p2] = w2; tl[p1] = w1; p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
            if p1 == p2:
                print(f"  Lp={Lp}: COLLIDE at t={t}")
                break
            if p1 >= 25 and s1 == ex and s2 == cs2 and 8 <= p2 - p1 < 8 + M:
                if all(tl.get(p2 + dx, 0) == val for dx, val in tp_g.items()):
                    mn_nz = min(x for x, val in tl.items() if val != 0)
                    new_x_anc = (mn_nz - 1) if anc == 0 else mn_nz
                    L_next = p1 - new_x_anc
                    print(f"  Lp={Lp}: COL_NEXT at t={t}, p1={p1}, p2={p2}, G_next={p2-p1}, new_x_anc={new_x_anc}, L_next={L_next} (dL={L_next - Lp})")
                    break

cet3_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt')
                 if l.startswith('1LB0LA_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA\t'))
cet23_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet23_t1.txt')
                  if l.startswith('1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA\t'))
cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))

test_e2e("CET(3)", cet3_line, 2, 8, [4, 5, 6, 7])
test_e2e("CET(2,3)", cet23_line, 3, 10, [1, 2, 3, 4])
test_e2e("CET(4)", cet4_line, 2, 10, [4, 5, 6, 7])
