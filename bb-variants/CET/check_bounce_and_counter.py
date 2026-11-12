import io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et
from verify_all3_champions import parse_tm, inspect_glider_and_counter

def check_all_bounces(name, line, n_syms, seq):
    print("=" * 80)
    print(f"BOUNCE & COUNTER DECOMPOSITION: {name}")
    m, T1, T2, ex, tsym, cp2, cs2, ctp = inspect_glider_and_counter(name, line, n_syms)
    tp_g = {k - cp2: v for k, v in ctp.items() if k >= cp2 - 5 and k <= cp2 + 15}
    unique_Gs = []
    for g in seq[:-1]:
        if g not in unique_Gs: unique_Gs.append(g)

    for G in unique_Gs:
        ev = m['events'][G][1]
        # Run with infinite tsym=1 to the left (down to -100) so we see the pure bounce + left-wipe invariant!
        tl = {x: tsym for x in range(-100, G - 5)}
        for dx, val in tp_g.items(): tl[G + dx] = val
        p1, s1, p2, s2 = 0, ex, G, cs2
        reached = None
        for t in range(1, 500):
            v1 = tl.get(p1, 0); v2 = tl.get(p2, 0)
            w1, d1, ns1 = T1[(s1, v1)]; w2, d2, ns2 = T2[(s2, v2)]
            tl[p2] = w2; tl[p1] = w1
            p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
            if p1 == -25 and reached is None:
                # Print tape from -25 to G + 10
                # Find rightmost cell != tsym before p2 - 10, or rightmost non-tsym left of Ag2
                slice_s = ''.join(str(tl.get(x, 0)) for x in range(-25, G + 15))
                # Find index of first non-wipe symbol (e.g. for CET3/4 where wipe writes 0, find first 1 right of -25!)
                reached = (t, chr(65+s1), p2, chr(65+s2), slice_s)
                break
        print(f"  B[{G:2d}] (xr={ev['xr']:2d}, gdx={ev['gdx']:2d}, form={ev['form']['branches']}): at p1=-25 -> t={reached[0]:3d} s1={reached[1]} tape[-25..G+14]={reached[4]}")

cet3_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt')
                 if l.startswith('1LB0LA_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA\t'))
cet23_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet23_t1.txt')
                  if l.startswith('1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA\t'))
cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))

check_all_bounces("CET(3) R=7", cet3_line, 2, [18, 8, 14, 14, 10, 18, 12])
check_all_bounces("CET(2,3) R=8", cet23_line, 3, [10, 10, 10, 10, 10, 10, 12, 14])
check_all_bounces("CET(4) R=15", cet4_line, 2, [18, 16, 16, 22, 10, 24, 20, 30, 18, 26, 16, 14, 14, 20, 8])
