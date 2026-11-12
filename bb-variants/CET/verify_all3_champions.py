import io, contextlib, sys
sys.path.insert(0, 'bbwork/bb-variants/CET')
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et

def parse_tm(spec, n_syms):
    T = {}
    for st, row in enumerate(spec.split('_')):
        for sym in range(n_syms):
            tok = row[3*sym : 3*sym+3]
            if tok == '---':
                T[(st, sym)] = None
            else:
                T[(st, sym)] = (int(tok[0]), -1 if tok[1] == 'L' else 1, ord(tok[2]) - 65)
    return T

def inspect_glider_and_counter(name, line, n_syms):
    print("=" * 80)
    print(f"VERIFYING {name}")
    m = et.parse_mech_line(line)
    ag1_s, ag2_s = m['pair'].split('|')
    T1 = parse_tm(ag1_s, n_syms)
    T2 = parse_tm(ag2_s, n_syms)
    P, D, M = m['P'], m['D'], m['M']

    # 1. Steady glider from SOLO Ag2 start (500 steps)
    tp = {}
    p2, s2 = 2, 0
    hist2 = []
    for t in range(1, 500):
        w2, d2, ns2 = T2[(s2, tp.get(p2, 0))]
        tp[p2] = w2
        p2 += d2; s2 = ns2
        hist2.append((t, p2, s2))
    # Find steady t0 where period P, D holds
    st0 = None
    for t0 in range(250, 400):
        if all(hist2[t0+k+P][1] - hist2[t0+k][1] == D and hist2[t0+k+P][2] == hist2[t0+k][2] for k in range(2*P)):
            st0 = t0 + 1
            break
    # Replay solo Ag2 to st0 to extract exact glider window & tsym
    tp = {}; p2, s2 = 2, 0
    for t in range(1, st0 + 1):
        w2, d2, ns2 = T2[(s2, tp.get(p2, 0))]
        tp[p2] = w2
        p2 += d2; s2 = ns2
    # Also find min_h and max_h over [st0 .. st0 + P - 1]
    min_touch = p2; max_touch = p2
    tp_check = dict(tp); pp, ss = p2, s2
    for _ in range(P):
        min_touch = min(min_touch, pp); max_touch = max(max_touch, pp)
        w2, d2, ns2 = T2[(ss, tp_check.get(pp, 0))]
        tp_check[pp] = w2; pp += d2; ss = ns2
    # Infer tsym from trailing cell written by glider
    tsym = tp_check.get(min_touch, 0)
    win_l = min_touch - p2
    win_r = max_touch - p2
    pat_str = ''.join(str(tp.get(p2 + dx, 0)) for dx in range(win_l, win_r + 1))
    print(f"Glider: P={P}, D={D}, M={M}, tsym={tsym}, steady_t0={st0}, s2={chr(65+s2)}, p2(st0)={p2}")
    print(f"  rel_window=[{win_l}..{win_r}], pat={pat_str}")

    # 2. Test bounce B[G] for active G's on small L = 12, 13, 14, 15
    # First find canon gl_s (where pat in mechs matches) by checking every phase 0..P-1 of steady glider
    # Actually let's just pick one phase (st0 + off) for each G in sorted(events) where G = p2 - p1 at s1=ex?
    # Better: simulate Ag2 solo from steady (p2, s2, tp_window) at G = mg .. mg+M-1?
    # Wait: in eval_towers, G is measured when Ag2 is in the canon phase `gl_s`!
    # Which phase in [0..P-1] is canon `gl_s`? The one whose `H` gaps match `m['events']`!
    events = m['events']
    canon_off = None
    # Find canon phase by checking all offsets 0..P-1 against H gaps in events
    h_gaps = [g for g, ev in events.items() if ev[0] == 'H']
    # Extract Ag1 exit state from an actual B event? Look at T1: state where T1[(ex, tsym)] moves +1 to ex!
    ex_states = [st for st in range(len(ag1_s.split('_'))) if T1[(st, tsym)] == (tsym, 1, st)]
    print(f"  Candidate exit states (read {tsym} -> write {tsym}, R, same): {[chr(65+s) for s in ex_states]}")
    ex = ex_states[0]

    for off in range(P):
        # Advance glider off steps from st0
        tp_g = dict(tp); pp, ss = p2, s2
        for _ in range(off):
            w2, d2, ns2 = T2[(ss, tp_g.get(pp, 0))]
            tp_g[pp] = w2; pp += d2; ss = ns2
        # Test H gaps!
        all_h_match = True
        for hg in h_gaps:
            # Put Ag1 at pp - hg in state ex on tsym^* [glider_pat] 0^*
            tloc = {x: tsym for x in range(pp - hg - 50, pp)}
            for x in range(pp - 20, pp + 40):
                if x in tp_g: tloc[x] = tp_g[x]
            lp1, ls1, lp2, ls2 = pp - hg, ex, pp, ss
            coll_t = None
            for k in range(1, 200):
                w1, d1, ns1 = T1[(ls1, tloc.get(lp1, 0))]
                w2, d2, ns2 = T2[(ls2, tloc.get(lp2, 0))]
                tloc[lp2] = w2; tloc[lp1] = w1
                lp1 += d1; ls1 = ns1; lp2 += d2; ls2 = ns2
                if lp1 == lp2:
                    coll_t = k; break
            if coll_t != events[hg][1]:
                all_h_match = False; break
        if all_h_match:
            canon_off = off
            canon_s2 = ss
            canon_tp = tp_g
            canon_p2 = pp
            print(f"  Matched canon glider phase: off={off} (t={st0+off}), s2={chr(65+ss)}, H-gaps={h_gaps}")
            break
    if canon_off is None:
        print(f"  WARN: could not match canon_off! H-events: {[(g, events[g]) for g in h_gaps]}")
        return m, T1, T2, ex, tsym, p2, s2, tp
    return m, T1, T2, ex, tsym, canon_p2, canon_s2, canon_tp

# Check CET3_R7 (construct mech line from mechs_cet3_exh.txt!)
cet3_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt')
                 if l.startswith('1LB0LA_1LC1RB_0RB0LC|1LB0RC_1RA0LC_1RB1RA\t'))
m3, T1_3, T2_3, ex3, ts3, cp2_3, cs2_3, ctp_3 = inspect_glider_and_counter("CET(3) R=7", cet3_line, 2)
st3, seq3, _ = et.exact_tower_rounds(m3, 18, 178956975, round_start=2)
print(f"  CET(3) R=7 exact_tower_rounds(G1=18, L2=178956975): {st3}, rounds={len(seq3)}, seq={seq3}")

cet23_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet23_t1.txt')
                  if l.startswith('1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA\t'))
m23, T1_23, T2_23, ex23, ts23, cp2_23, cs2_23, ctp_23 = inspect_glider_and_counter("CET(2,3) R=8", cet23_line, 3)
st23, seq23, _ = et.exact_tower_rounds(m23, 10, 86, round_start=2)
print(f"  CET(2,3) R=8 exact_tower_rounds(G1=10, L2=86): {st23}, rounds={len(seq23)}, seq={seq23}")

cet4_line = next(l.strip() for l in open('bbwork/bb-variants/CET/mechs_cet4_smoke.txt')
                 if l.startswith('1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC\t'))
m4, T1_4, T2_4, ex4, ts4, cp2_4, cs2_4, ctp_4 = inspect_glider_and_counter("CET(4) R=15", cet4_line, 2)
st4, seq4, _ = et.exact_tower_rounds(m4, 18, 190, round_start=2)
print(f"  CET(4) R=15 exact_tower_rounds(G1=18, L2=190): {st4}, rounds={len(seq4)}, seq={seq4}")
