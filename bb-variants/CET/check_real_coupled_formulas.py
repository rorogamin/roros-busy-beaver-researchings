import io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et
from verify_all3_champions import parse_tm, inspect_glider_and_counter

def check_coupled(name, line, n_syms, G_list):
    print("=" * 80)
    print(f"REAL COUPLED FORMULA CHECK: {name}")
    m, T1, T2, ex, tsym, cp2, cs2, ctp = inspect_glider_and_counter(name, line, n_syms)
    tp_g = {k - cp2: v for k, v in ctp.items() if k >= cp2 - 5 and k <= cp2 + 15}
    P, D, M = m['P'], m['D'], m['M']
    anc = 2 if n_syms == 3 else 0

    for G in G_list:
        ev = m['events'][G][1]
        c0, A, B, L0_b = ev['form']['branches'][0]
        base = ev['form']['base']
        # Put anchor far enough left? Wait in real R2, L ~ 86..190..178M, so anc is way left of -20!
        # To keep T small (< 200k), put anc at -10, -11, -12, -13? Wait for CET(4) G=30, bounce goes to ~ -5? No!
        # Let's check min_p1 during bounce first? No, bounce only goes to ~ 0 or -2! Let's check Lb_neg = 12, 13, 14!
        # Wait: 5 * 2^{14+22} is too big! Why? Because in CET(4), if rw is at 16, then distance from -10 to 16 is 26 -> 5 * 2^{26} = 335M!
        # Wait: why did extract_rocq_specs use Lb = 4..7 from rw_start? Because Ag1 ONLY needs Lb >= 1, EXCEPT during bounce Ag1 goes left only as far as min_bounce!
        # What IS min_bounce (before Ag1 enters monotonic left wipe)? Only ~0..G! Never < -5!
        # Wait: then why not put x_anc at -5, -6, -7, -8?
        # Even better: check if x_anc = 2, 3, 4, 5 works? No, p1 starts at 0!
        #Wait: at x_anc = -6, -7, -8: distance to rw_start (~16 for G=18) is 22 -> 5 * 2^22 = 20M! Too slow in Python, INSTANT in C, OR check G=10 (rw=8 -> 14 cells -> 2^14 = 16k!)
        # Wait for CET(4), let's check G=10, 14, 16, 18 with x_anc = -2, -3, -4 (wait: at x_anc = -2, does bounce touch -2? No, bounce turns around at +G+5 and walks left in C!).
        # Actually, let's check rw_start for G=18 at t=480 vs t=100: earlier at p1=-30 (t=64), p2=18(B) and tape[17]=0! At what t did Ag2 write tape[17]=1?!
        tl = {x: tsym for x in range(-200, G - 5)}
        for dx, v in tp_g.items(): tl[G + dx] = v
        p1, s1, p2, s2 = 0, ex, G, cs2
        t_17_changed = None
        for t in range(1, 300):
            old_rw = tl.get(G - 1, tsym)
            v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
            w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
            tl[p2] = w2; tl[p1] = w1; p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
            if tl.get(G - 1, tsym) != old_rw and t > 40:
                print(f"  G={G}: cell {G-1} changed {old_rw}->{tl[G-1]} at t={t} (p1={p1}, p2={p2})")
        print(f"  G={G}: at t=299, p1={p1}({chr(65+s1)}), p2={p2}({chr(65+s2)}), tape[{G-4}..{G+10}]={''.join(str(tl.get(x,0)) for x in range(G-4, G+11))}")

cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))
check_coupled("CET(4)", cet4_line, 2, [18, 16, 22, 10, 24])
