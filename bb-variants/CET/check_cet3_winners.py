import io, contextlib, sys, time
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et

def parse3(spec):
    T = {}
    for s, row in enumerate(spec.split('_')):
        for sym in range(2):
            tok = row[3*sym:3*sym+3]
            T[(s, sym)] = (int(tok[0]), -1 if tok[1] == 'L' else 1, ord(tok[2]) - 65)
    return T

T2 = parse3('1LB0RC_1RA0LC_1RB1RA')
for label, s1_spec, t_exit, p1_e in [
    ('0LB0LA', '0LB0LA_1LC1RB_0RB0LC', 167772456, 224),
    ('1LB0LA', '1LB0LA_1LC1RB_0RB0LC', 536871222, 228),
]:
    T1 = parse3(s1_spec)
    tp = {}
    p1, s1, p2, s2 = 0, 0, 2, 0
    for t in range(1, 2020):
        w1, d1, ns1 = T1[(s1, tp.get(p1, 0))]
        w2, d2, ns2 = T2[(s2, tp.get(p2, 0))]
        tp[p2] = w2; tp[p1] = w1
        p1 += d1; s1 = ns1; p2 += d2; s2 = ns2
        if 2000 <= t <= 2015 and s2 == 0:
            pat = ''.join(str(tp.get(x, 0)) for x in range(p2 - 8, p2 + 6))
            print(f'{label} t={t} (mod16={t%16:2d}) p2={p2} s2=A pat={pat}')

    for line in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt'):
        if line.startswith(s1_spec + '|1LB0RC_1RA0LC_1RB1RA\t'):
            m = et.parse_mech_line(line)
            approx_x = 55924056 if label == '0LB0LA' else 178956974
            print(f'=== {label} M={m["M"]} approx_L2={approx_x} ===')
            for g1, ev in sorted(m['events'].items()):
                if ev[0] == 'B':
                    for dl in range(0, 12):
                        st, seq, _ = et.exact_tower_rounds(m, g1, approx_x + dl, round_start=2)
                        if len(seq) >= 5 or (st == 'HALT' and len(seq) >= 4):
                            print(f'  G1={g1:2d} dl={dl:2d} -> status={st} R={len(seq)} seq={seq}')
            break
