import math, io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et
from verify_all3_champions import parse_tm, inspect_glider_and_counter

def carmichael_lambda(n):
    res = 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            p = d; pk = 1
            while n % p == 0:
                n //= p; pk *= p
            if p == 2 and pk >= 8: lam = pk // 4
            elif p == 2: lam = pk // 2 if pk >= 2 else 1
            else: lam = (pk // p) * (p - 1)
            res = math.lcm(res, lam)
        d += 1
    if n > 1:
        res = math.lcm(res, n - 1)
    return res

def pow_base_mod(base, exp_mod_fn, Q):
    if Q == 1: return 0
    Q_bad = 1; Q_good = Q
    for p in (2, 3):
        if base % p == 0:
            while Q_good % p == 0:
                Q_good //= p; Q_bad *= p
    lam = carmichael_lambda(Q_good)
    e_mod = exp_mod_fn(lam)
    r_good = pow(base, e_mod, Q_good) if Q_good > 1 else 0
    if Q_bad == 1: return r_good
    if Q_good == 1: return 0
    inv = pow(Q_bad, -1, Q_good)
    k = (r_good * inv) % Q_good
    return Q_bad * k

def build_true_table(name, line, n_syms):
    m, T1, T2, ex, tsym, cp2, cs2, ctp = inspect_glider_and_counter(name, line, n_syms)
    tp_g = {k - cp2: v for k, v in ctp.items() if k >= cp2 - 5 and k <= cp2 + 15}
    P, D, M = m['P'], m['D'], m['M']
    anc = 2 if n_syms == 3 else 0
    true_events = {}
    for G in sorted(m['events'].keys()):
        if m['events'][G][0] == 'H':
            true_events[G] = ('H', m['events'][G][1])
            continue
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
                pp, ss = p2, s2; t_ag2 = t
                for k in range(1, 200):
                    v = tl.get(pp, 0); w, d, ns = T2[(ss, v)]
                    tl[pp] = w; pp += d; ss = ns; t_ag2 += 1
                    if k >= 100 and ss == cs2 and all(tl.get(pp + dx, 0) == val for dx, val in tp_g.items()):
                        gdx_true = pp - G; gs_true = t_ag2; break
                wipe_sym = tl[-119]
                rw_start = -119
                while tl[rw_start] == wipe_sym: rw_start += 1
                rw_end = pp - 6
                while tl.get(rw_end, tsym) == tsym and rw_end > rw_start: rw_end -= 1
                rw_str = ''.join(str(tl.get(x, tsym)) for x in range(rw_start, rw_end + 1))
                Lp0 = 5 - rw_start
                Ts = []
                for Lp in range(Lp0, Lp0 + 4):
                    x_anc = -Lp
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
                            mn_nz = min(x for x, val in st_tp.items() if val != 0)
                            new_x_anc = (mn_nz - 1) if anc == 0 else mn_nz
                            Ts.append((Lp, t_to_anc + stp, ap, ap - new_x_anc))
                            break
                base = 3 if n_syms == 3 else 2
                d0 = Ts[1][1] - base * Ts[0][1]
                d1 = Ts[2][1] - base * Ts[1][1]
                A = (d1 - d0) // (1 - base)
                B = (d0 - A * (Lp0 + 1 - base * Lp0)) // (1 - base)
                c0 = Ts[0][1] - (A * Lp0 + B)
                x_exit = Ts[0][2]; dL = Ts[0][3] - Lp0
                true_events[G] = ('B', (base, c0, Lp0, A, B, x_exit, dL, gdx_true, gs_true))
                break
        if coll is not None:
            true_events[G] = ('H', coll)
    return P, D, M, min(true_events.keys()), true_events

def eval_exact_seq(P, D, M, mg, true_events, G1, L2, max_rounds=25):
    # Recursive memoized L_mod(r, Q) for r >= 2 where r=2 is L2!
    # Also G_seq[r] = G after Round r (so G_seq[1] = G1, G_seq[2] = G2, ...)
    G_seq = [G1]
    def get_L_mod(r, Q):
        if r == 2:
            return L2 % Q
        G_prev = G_seq[r - 3]  # Wait: G_seq[0]=G1 (for Round 2), G_seq[1]=G2 (for Round 3), ...
        ev = true_events[G_prev]
        assert ev[0] == 'B'
        base, c0, Lp0, A, B, x_exit, dL, gdx, gs = ev[1]
        # Need T_exit mod (P * M * Q) and L_{r-1} mod Q
        PMQ = P * M * Q
        # Note: exp is L_{r-1} - Lp0 >= 80
        exp_fn = lambda lam: (get_L_mod(r - 1, lam) - Lp0) % lam
        T_mod = (c0 * pow_base_mod(base, exp_fn, PMQ) + A * (get_L_mod(r - 1, PMQ)) + B) % PMQ
        dt = (gs - T_mod) % P
        t_sync_mod = (T_mod + dt) % PMQ
        # q = (t_sync - gs) // P; since t_sync == gs (mod P), q mod (M*Q) = ((t_sync_mod - gs) // P) % (M*Q)
        # Wait: if t_sync_mod < gs, add PMQ? No, modulo PMQ, ((t_sync_mod - gs) % PMQ) // P is exact mod (M*Q)!!
        q_mod_MQ = (((t_sync_mod - gs) % PMQ) // P) % (M * Q)
        gap_mod_MQ = (G_prev + gdx + D * q_mod_MQ - x_exit - dt) % (M * Q)
        # k_close = (gap_sync - mg) // M
        # Note: gap_sync - mg mod (M*Q) = (gap_mod_MQ - mg) % (M*Q)
        k_close_mod_Q = (((gap_mod_MQ - mg) % (M * Q)) // M) % Q
        L_next_mod = (get_L_mod(r - 1, Q) + dL + dt + P * k_close_mod_Q) % Q
        return L_next_mod

    for r in range(2, max_rounds + 1):
        G_cur = G_seq[-1]
        ev = true_events[G_cur]
        if ev[0] == 'H':
            return 'HALT', len(G_seq), G_seq, ev[1]
        base, c0, Lp0, A, B, x_exit, dL, gdx, gs = ev[1]
        PM = P * M
        exp_fn = lambda lam: (get_L_mod(r, lam) - Lp0) % lam
        T_mod = (c0 * pow_base_mod(base, exp_fn, PM) + A * get_L_mod(r, PM) + B) % PM
        dt = (gs - T_mod) % P
        t_sync_mod = (T_mod + dt) % PM
        q_mod_M = (((t_sync_mod - gs) % PM) // P) % M
        gap_mod_M = (G_cur + gdx + D * q_mod_M - x_exit - dt) % M
        G_next = mg + ((gap_mod_M - mg) % M)
        G_seq.append(G_next)
    return 'ALIVE', len(G_seq), G_seq, None

cet3_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt')
                 if l.startswith('1LB0LA_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA\t'))
cet23_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet23_t1.txt')
                  if l.startswith('1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA\t'))
cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))

for name, line, ns, G1, L2 in [
    ("CET(3)", cet3_line, 2, 18, 178956976),
    ("CET(2,3)", cet23_line, 3, 10, 87),
    ("CET(4)", cet4_line, 2, 18, 192),
]:
    with contextlib.redirect_stdout(io.StringIO()):
        P, D, M, mg, te = build_true_table(name, line, ns)
    st, rounds, seq, hstp = eval_exact_seq(P, D, M, mg, te, G1, L2, max_rounds=30)
    print(f"{name}: status={st}, rounds={rounds}, halt_step={hstp}, seq={seq}")
