import io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et
from verify_all3_champions import parse_tm, inspect_glider_and_counter

def analyze_counter_structure(name, line, n_syms, seq):
    print("=" * 80)
    print(f"COUNTER STRUCTURE: {name}, seq={seq}")
    m, T1, T2, ex, tsym, cp2, cs2, ctp = inspect_glider_and_counter(name, line, n_syms)
    P, D, M = m['P'], m['D'], m['M']
    # Extract clean glider window [wl .. wr] around cp2
    # Run Ag2 solo for P steps from ctp to find exact cells touched
    tp_g = {k - cp2: v for k, v in ctp.items() if k >= cp2 - 30 and k <= cp2 + 30}
    # Check minimal wl <= 0, wr >= 0 such that Ag2 P-step shifts [wl..wr] by D leaving tsym on [wl..wl+D-1]
    for wl in range(-10, 1):
        for wr in range(0, 15):
            # Test on empty dict with x < wl -> tsym, x > wr -> 0
            tl = {x: tp_g.get(x, tsym if x < 0 else 0) for x in range(wl, wr + 1)}
            pp, ss = 0, cs2
            ok = True
            for _ in range(P):
                v = tl.get(pp, tsym if pp < wl else 0)
                w, d, ns = T2[(ss, v)]
                tl[pp] = w; pp += d; ss = ns
            if pp == D and ss == cs2:
                # check [wl .. wl+D-1] == tsym, [wl+D .. wr+D] == orig[wl..wr], and > wr+D == 0
                ok_left = all(tl.get(x, tsym if x < wl else 0) == tsym for x in range(wl, wl + D))
                ok_pat = all(tl.get(x + D, 0) == tl.get(x, tsym if x < wl else 0) if False else
                             tl.get(x + D, 0) == (tp_g.get(x, tsym if x < 0 else 0)) for x in range(wl, wr + 1))
                ok_right = all(tl.get(x, 0) == 0 for x in range(wr + D + 1, wr + D + 20))
                if ok_left and ok_pat and ok_right:
                    pat_bits = ''.join(str(tp_g.get(x, tsym if x < 0 else 0)) for x in range(wl, wr + 1))
                    print(f"  EXACT GLIDER INVARIANT: wl={wl}, wr={wr}, pat={pat_bits}, s2={chr(65+cs2)}, P={P}, D={D}")
                    break
        else:
            continue
        break

    # Now test EACH unique B[G] in seq[:-1] for L = 12, 13, 14, 15!
    unique_Gs = []
    for g in seq[:-1]:
        if g not in unique_Gs: unique_Gs.append(g)
    print(f"  Unique B-gaps in active seq: {unique_Gs}, final H-gap: {seq[-1]}")

    for G in unique_Gs:
        ev = m['events'][G][1]
        print(f"  --- B[{G}]: L0={ev['L0']} xr={ev['xr']} gdx={ev['gdx']} gs={ev['gs']} mna={ev['mna']} form={ev['form']} ---")
        for L in (12, 13, 14):
            # Setup Ag1 at 0 in state ex, Ag2 at G in cs2
            # Left anchor: x = -L is 0, x in [-L+1 .. G + wl - 1] is tsym!
            # Wait: let's check anchor symbol! In CET3 & CET4 anchor is 0; in CET23 anchor is 2!
            anc = 2 if n_syms == 3 else 0
            tl = {}
            for x in range(-L + 1, G + wl): tl[x] = tsym
            tl[-L] = anc
            for x in range(wl, wr + 1): tl[G + x] = tp_g.get(x, tsym if x < 0 else 0)
            p1, s1, p2, s2 = 0, ex, G, cs2
            min_p1 = 0
            # Run until Ag1 returns to > G + wr + 10 in state ex (or max 2M steps)
            t_min = 0
            for t in range(1, 2000000):
                v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
                w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
                tl[p2] = w2; tl[p1] = w1
                p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
                if p1 < min_p1:
                    min_p1 = p1; t_min = t
                    snap_min = ''.join(str(tl.get(x, 0)) for x in range(min_p1 - 2, min_p1 + 12))
                    s_min = chr(65+s1)
                if p1 == p2:
                    print(f"    L={L}: COLLIDED at t={t}!")
                    break
                if p1 > G + 40 and s1 == ex and all(tl.get(p1 + z, 0) == tsym for z in range(6)):
                    # Check exact Ts, xr, gdx
                    print(f"    L={L}: exit t={t}, x_exit={p1} (L_eff={p1 - min_p1}? xr_check={p1 - G}), min_p1={min_p1} at t_min={t_min} ({s_min}) left_at_min={snap_min}")
                    break

    # Also test H[seq[-1]]
    HG = seq[-1]
    tl = {x: tsym for x in range(-30, HG + wl)}
    for x in range(wl, wr + 1): tl[HG + x] = tp_g.get(x, tsym if x < 0 else 0)
    p1, s1, p2, s2 = 0, ex, HG, cs2
    for t in range(1, 200):
        v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
        w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
        tl[p2] = w2; tl[p1] = w1
        p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
        if p1 == p2:
            print(f"  H[{HG}] verified: COLLIDE at t={t}, x={p1}, s1={chr(65+s1)}, s2={chr(65+s2)}")
            break

cet3_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt')
                 if l.startswith('1LB0LA_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA\t'))
cet23_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet23_t1.txt')
                  if l.startswith('1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA\t'))
cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))

analyze_counter_structure("CET(3) R=7", cet3_line, 2, [18, 8, 14, 14, 10, 18, 12])
analyze_counter_structure("CET(2,3) R=8", cet23_line, 3, [10, 10, 10, 10, 10, 10, 12, 14])
# For CET4, first get full seq!
m4 = et.parse_mech_line(cet4_line)
# Wait: inspect exact_tower_rounds signature or compute 15 rounds directly!
print("Checking CET(4) 15-round sequence:")
L = 190; G = 18; seq4 = [G]
for r in range(2, 20):
    ev_type, ev = m4['events'][G]
    if ev_type == 'H':
        print(f"  Round {r}: H[{G}] -> HALT in {ev} steps! seq4={seq4}")
        break
    # eval T(L) mod (P*M)? Wait eval_towers has eval_T_mod!
    form = ev['form']
    # Compute L_next = L + xr, G_next = (G + gdx - D*(Ts % P) - xr) mod M? Wait let's use et.exact_tower_rounds if max_rounds arg exists, or just call et.eval_T_mod!
    T_mod_PM = et.eval_T_mod(form, L, m4['P'] * m4['M']) # wait let's check et.eval_T_mod or et.exact_tower_rounds!
    # Actually let's just check what L_next and G_next are in eval_towers via quick grep? No, Rule 3! We already read eval_towers.py L1-446 in summary, let's check exact_tower_rounds!
    break
