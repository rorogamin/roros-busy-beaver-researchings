import io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et
from verify_all3_champions import parse_tm, inspect_glider_and_counter

def inspect_solo_counter(name, line, n_syms, seq, L_r1_check=False):
    print("=" * 80)
    print(f"SOLO COUNTER & EXACT FORMULA CHECK: {name}")
    m, T1, T2, ex, tsym, cp2, cs2, ctp = inspect_glider_and_counter(name, line, n_syms)
    tp_g = {k - cp2: v for k, v in ctp.items() if k >= cp2 - 5 and k <= cp2 + 15}

    unique_Gs = []
    for g in seq[:-1]:
        if g not in unique_Gs: unique_Gs.append(g)

    if L_r1_check:
        tp = {}; p1, s1, p2, s2 = 0, 0, 2, 0
        for t in range(1, 300):
            w1, d1, ns1 = T1[(s1, tp.get(p1, 0))]
            w2, d2, ns2 = T2[(s2, tp.get(p2, 0))]
            tp[p2] = w2; tp[p1] = w1; p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
            if t in (10, 50, 251):
                mn = min(tp.keys()); mx = max(tp.keys())
                print(f"  R1 t={t}: p1={p1}({chr(65+s1)}) p2={p2}({chr(65+s2)}) tape[{mn}..{mn+30}]={''.join(str(tp.get(x,0)) for x in range(mn, min(mx+1, mn+35)))}")

    for G in unique_Gs:
        ev = m['events'][G][1]
        tl = {x: tsym for x in range(-600, G - 5)}
        for dx, val in tp_g.items(): tl[G + dx] = val
        p1, s1, p2, s2 = 0, ex, G, cs2
        for t in range(1, 1000):
            v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
            w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
            tl[p2] = w2; tl[p1] = w1; p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
            if p1 == -450:
                t450, s1_450 = t, s1
                wipe_sym = tl[-449]
                rw_start = -449
                while tl[rw_start] == wipe_sym: rw_start += 1
                rw_end = p2 - 10
                while tl.get(rw_end, tsym) == tsym and rw_end > rw_start: rw_end -= 1
                rw_str = ''.join(str(tl.get(x, tsym)) for x in range(rw_start, rw_end + 1))
                anc = 2 if n_syms == 3 else 0
                counts = []
                for Lb in (4, 5, 6, 7):
                    x_anc = rw_start - 1 - Lb
                    st_tp = {x: wipe_sym for x in range(x_anc + 1, rw_start)}
                    st_tp[x_anc] = anc
                    for i, ch in enumerate(rw_str): st_tp[rw_start + i] = int(ch)
                    for x in range(rw_end + 1, rw_end + 40): st_tp[x] = tsym
                    ap, as1 = x_anc, s1_450
                    for stp in range(1, 200000):
                        v = st_tp.get(ap, 0 if ap < x_anc else tsym)
                        w, d, ns = T1[(as1, v)]
                        st_tp[ap] = w; ap += d; as1 = ns
                        if ap > rw_end + 2 and as1 == ex and all(st_tp.get(ap + z, tsym) == tsym for z in range(4)):
                            counts.append((Lb, stp, ap - x_anc, ap - rw_start))
                            break
                # Steps from t=0 to p1 == x_anc is t450 - (x_anc - (-450)) = t450 - (rw_start - 1 - Lb + 450)
                total_at_xr = []
                L_effs = []
                for Lb, stp, span_len, dx_rw in counts:
                    t_to_anc = t450 - (rw_start - 1 - Lb + 450)
                    t_exit_xr = t_to_anc + stp + (ev['xr'] - (rw_start + dx_rw))
                    total_at_xr.append(t_exit_xr)
                    L_effs.append(span_len + (ev['xr'] - (rw_start + dx_rw)) + ev['mna'])
                base = ev['form']['base']
                c0, A, B, _ = ev['form']['branches'][0]
                preds = [c0 * (base ** (Le - ev['L0'])) + A * Le + B for Le in L_effs]
                print(f"  B[{G:2d}]: rw@{rw_start}='{rw_str}' t_to_anc(Lb=0)={t450-(rw_start+449)} L_effs={L_effs} s1={chr(65+s1_450)} wipe={wipe_sym}")
                print(f"       T_sim ={total_at_xr}")
                print(f"       T_form={preds} match={total_at_xr == preds}")
                break

cet3_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt')
                 if l.startswith('1LB0LA_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA\t'))
cet23_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet23_t1.txt')
                  if l.startswith('1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA\t'))
cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))

inspect_solo_counter("CET(3) R=7", cet3_line, 2, [18, 8, 14, 14, 10, 18, 12], L_r1_check=True)
inspect_solo_counter("CET(2,3) R=8", cet23_line, 3, [10, 10, 10, 10, 10, 10, 12, 14])
inspect_solo_counter("CET(4) R=15", cet4_line, 2, [18, 16, 16, 22, 10, 24, 20, 30, 18, 26, 16, 14, 14, 20, 8])
