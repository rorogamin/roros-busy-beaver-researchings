import io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et
from verify_all3_champions import parse_tm, inspect_glider_and_counter

def true_bounce_table(name, line, n_syms, G1, L2):
    print("=" * 80)
    print(f"TRUE COUPLED TABLE & TOWER TRACE: {name}")
    m, T1, T2, ex, tsym, cp2, cs2, ctp = inspect_glider_and_counter(name, line, n_syms)
    tp_g = {k - cp2: v for k, v in ctp.items() if k >= cp2 - 5 and k <= cp2 + 15}
    P, D, M = m['P'], m['D'], m['M']
    anc = 2 if n_syms == 3 else 0

    true_events = {}
    for G in sorted(m['events'].keys()):
        if m['events'][G][0] == 'H':
            true_events[G] = ('H', m['events'][G][1])
            continue
        # Run coupled until p1 == -120 (t ~ 130..200, Ag2 is far past bounce zone!)
        tl = {x: tsym for x in range(-250, G - 5)}
        for dx, val in tp_g.items(): tl[G + dx] = val
        p1, s1, p2, s2 = 0, ex, G, cs2
        coll = None
        for t in range(1, 800):
            v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
            w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
            tl[p2] = w2; tl[p1] = w1; p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
            if p1 == p2:
                coll = t; break
            if p1 == -120:
                # Check Ag2 is back in steady glider: find exact gdx, gs when Ag2 next hits canon_s2 & pat
                # Advance solo Ag2 from (p2, s2) in tl[p2-5..p2+15] until it matches tp_g at canon_s2!
                # First compute rw after Ag2 has cleared G+15 (if p2 <= G+20, step Ag2+Ag1 a bit more? No, at p1=-120 we just advance Ag2 alone for 100 steps to clean trail and sync!)
                tl_ag2 = {x: tl.get(x, 0) for x in range(p2 - 5, p2 + 25)}
                pp, ss = p2, s2
                t_ag2 = t
                # Step Ag2 alone up to 200 steps while recording rw cells at >= G - 10
                # Wait: Ag2 only moves right! Just merge tl_ag2 back into tl for rw!
                for k in range(1, 200):
                    v = tl.get(pp, 0)
                    w, d, ns = T2[(ss, v)]
                    tl[pp] = w; pp += d; ss = ns; t_ag2 += 1
                    if k >= 100 and ss == cs2:
                        if all(tl.get(pp + dx, 0) == val for dx, val in tp_g.items()):
                            # True glider sync!
                            # At t_ag2, Ag2 is at pp in canon phase!
                            # Since Ag2 advances D per P steps, gdx mod M? Wait:
                            # In eval_towers: p2(t) = G + gdx + D * ((t - gs) // P) when t == gs (mod P)!
                            gdx_true = pp - G
                            gs_true = t_ag2
                            break
                wipe_sym = tl[-119]
                rw_start = -119
                while tl[rw_start] == wipe_sym: rw_start += 1
                rw_end = pp - 6
                while tl.get(rw_end, tsym) == tsym and rw_end > rw_start: rw_end -= 1
                rw_str = ''.join(str(tl.get(x, tsym)) for x in range(rw_start, rw_end + 1))

                # Measure T_total(L) for Lb = 4, 5, 6, 7 where L_round = rw_start - x_anc (Wait: let's define L_round = number of cells from x_anc+1 to rw_start-1? No!
                # In R2: tape has anc at r2min, and tsym on [r2min+1 .. x1_bounce_anchor]!
                # Specifically, in our notation: x_anc = -(L_body + 1) if p1 starts at 0?
                # Wait: in Round k, p1 starts at x_{k-1} (where Ag1 exited Round k-1)!
                # So L_k = number of tsym=1 cells strictly between x_anc and p1_start (i.e. x_anc+1 .. p1_start-1, length = p1_start - x_anc - 1), OR L_k = p1_start - x_anc!
                # Let's define L_param = 0 - x_anc (distance from x_anc to p1_start=0)!
                # Then Lb = rw_start - 1 - x_anc = L_param + rw_start - 1!
                # Wait: let's test L_param for 4 consecutive values starting from max(6, 5 - rw_start)!)
                Lp0 = 5 - rw_start
                Ts = []
                L_nexts = []
                for Lp in range(Lp0, Lp0 + 4):
                    x_anc = -Lp
                    Lb = rw_start - 1 - x_anc
                    st_tp = {x: wipe_sym for x in range(x_anc + 1, rw_start)}
                    st_tp[x_anc] = anc
                    for i, ch in enumerate(rw_str): st_tp[rw_start + i] = int(ch)
                    for x in range(rw_end + 1, rw_end + 50): st_tp[x] = tsym
                    ap, as1 = x_anc, s1
                    t_to_anc = t - (x_anc - (-120))
                    for stp in range(1, 200000):
                        v = st_tp.get(ap, 0 if ap < x_anc else tsym)
                        w, d, ns = T1[(as1, v)]
                        st_tp[ap] = w; ap += d; as1 = ns
                        if ap > rw_end + 2 and as1 == ex and all(st_tp.get(ap + z, tsym) == tsym for z in range(4)):
                            # Check where the new left anchor is! Find leftmost non-0 cell (for anc=0) or leftmost 2 (for anc=2)!
                            mn_nz = min(x for x, val in st_tp.items() if val != 0)
                            # In CET3/4, anchor is 0 just left of mn_nz (i.e. new x_anc = mn_nz - 1); in CET23, mn_nz IS the '2' anchor!
                            new_x_anc = (mn_nz - 1) if anc == 0 else mn_nz
                            # Wait: advance ap to canon? No, at p1 = ap, tape[new_x_anc+1 .. ap-1] are ALL tsym=1!
                            # Verify!
                            assert all(st_tp.get(x, 0) == tsym for x in range(new_x_anc + 1, ap)), f"Not all tsym! {st_tp}"
                            Ts.append((Lp, t_to_anc + stp, ap, ap - new_x_anc))
                            break
                # Fit exact T(Lp) = c0 * base^(Lp - Lp0) + A * Lp + B!
                base = 3 if n_syms == 3 else 2
                # Compute differences: d_i = Ts[i+1][1] - base * Ts[i][1] = A * (Lp_i+1 - base*Lp_i) + B * (1 - base)
                d0 = Ts[1][1] - base * Ts[0][1]
                d1 = Ts[2][1] - base * Ts[1][1]
                # d1 - d0 = A * ((1 - base))!
                A = (d1 - d0) // (1 - base)
                B = (d0 - A * (Lp0 + 1 - base * Lp0)) // (1 - base)
                c0 = Ts[0][1] - (A * Lp0 + B)
                # Verify all 4!
                assert all(c0 * (base ** (Lp - Lp0)) + A * Lp + B == Tval for (Lp, Tval, _, _) in Ts), f"Fit failed! {Ts}"
                x_exit = Ts[0][2]
                dL = Ts[0][3] - Lp0 # L_next - L_cur!
                # Check all 4 have same x_exit and dL!
                assert all(t_[2] == x_exit and t_[3] - t_[0] == dL for t_ in Ts)
                true_events[G] = ('B', (base, c0, Lp0, A, B, x_exit, dL, gdx_true, gs_true, rw_str))
                break
        if coll is not None:
            true_events[G] = ('H', coll)

    print("True events summary:")
    for G, ev in sorted(true_events.items()):
        if ev[0] == 'H':
            print(f"  G={G:2d}: HALT at t={ev[1]}")
        else:
            base, c0, Lp0, A, B, x_exit, dL, gdx, gs, rw = ev[1]
            print(f"  G={G:2d}: B T(L)={c0}*{base}^(L-{Lp0}) + {A}*L + {B}, x_exit={x_exit}, dL={dL}, gdx={gdx}, gs={gs}, rw='{rw}'")

    # Exact recursive modular evaluator (verified against e2e!)
    def pow_period(base, mod):
        # Returns (preperiod, period) of base^n mod mod
        seen = {}
        cur = 1 % mod
        for n in range(0, mod + 5):
            if cur in seen:
                return seen[cur], n - seen[cur]
            seen[cur] = n
            cur = (cur * base) % mod
        raise RuntimeError("unreachable")

    # Wait: for large mod (e.g. M * P * ... ~ 10^9), we can factor mod cleanly using et.lambda_big?
    # Actually let's just use et.exact_tower_rounds on m_true?
    # Let's check exact L_next formula on small L first AND compare with et.exact_tower_rounds!
    m_true = {
        'pair': m['pair'], 'P': P, 'D': D, 'M': M, 'mg': min(true_events.keys()),
        'bt': 3 if n_syms == 3 else 1, 'events': {}
    }
    for G, ev in true_events.items():
        if ev[0] == 'H':
            m_true['events'][G] = ('H', ev[1])
        else:
            base, c0, Lp0, A, B, x_exit, dL, gdx, gs, rw = ev[1]
            # Wait: check whether L_next = L + dL + dt + P*k_close!
            # In eval_towers: L_next = L + xr + mna? Let's check mna=0 -> xr = dL!
            m_true['events'][G] = ('B', {
                'ts': 0, 'lp': 0, 'w': 0,
                'L0': Lp0, 'xr': dL, 'gdx': gdx, 'gs': gs, 'mna': 0,
                'form': {'base': base, 'per': 1, 'L0': Lp0, 'branches': [(c0, A, B, Lp0)]}
            })
    st, seq, _ = et.exact_tower_rounds(m_true, G1, L2, round_start=2, max_depth=25)
    print(f"  => TRUE TOWER RESULT: status={st}, rounds={len(seq)}, seq={seq}")

cet3_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt')
                 if l.startswith('1LB0LA_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA\t'))
cet23_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet23_t1.txt')
                  if l.startswith('1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA\t'))
cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))

# Note: L_param = x1 - r2min!
# For CET3: x1=178956974, r2min=-2 -> L_param = 178956976!
true_bounce_table("CET(3)", cet3_line, 2, 18, 178956976)
# For CET23: x1=86, r2min=-1 -> L_param = 87!
true_bounce_table("CET(2,3)", cet23_line, 3, 10, 87)
# For CET4: x1=188, r2min=-4 -> L_param = 192!
true_bounce_table("CET(4)", cet4_line, 2, 18, 192)
