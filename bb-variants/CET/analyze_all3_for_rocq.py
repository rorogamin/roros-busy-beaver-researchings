import sys
import os
import io
import contextlib

sys.path.insert(0, os.path.dirname(__file__))
with contextlib.redirect_stdout(io.StringIO()):
    import eval_towers as et

def parse_tm(spec, n_syms):
    parts = spec.split('_')
    table = {}
    for st, row in enumerate(parts):
        for sym in range(n_syms):
            tok = row[3*sym : 3*sym+3]
            if tok == '---':
                table[(st, sym)] = None
            else:
                w = int(tok[0])
                d = -1 if tok[1] == 'L' else 1
                ns = ord(tok[2]) - ord('A')
                table[(st, sym)] = (w, d, ns)
    return table

def find_exact_line(path, prefix):
    with open(path) as f:
        for line in f:
            if prefix in line:
                return line.strip()
    return None

def find_solo_glider(t2, P, D):
    tape2 = {}
    p2, s2 = 2, 0
    hist = []
    for t in range(1, 600):
        v = tape2.get(p2, 0)
        w, d, ns = t2[(s2, v)]
        tape2[p2] = w
        p2 += d; s2 = ns
        hist.append((t, p2, s2))
    steady_t0 = None
    for t0 in range(5, 400):
        ok = True
        for k in range(3 * P):
            _, pA, sA = hist[t0 + k]
            _, pB, sB = hist[t0 + k + P]
            if sA != sB or (pB - pA) != D:
                ok = False; break
        if ok:
            steady_t0 = t0 + 1
            break
    # Replay to steady_t0 .. steady_t0 + P
    tp = {}
    pp, ss = 2, 0
    snap_at_start = None
    period = []
    for stp in range(1, steady_t0 + P + 1):
        if stp == steady_t0:
            pass
        v = tp.get(pp, 0)
        w, d, ns = t2[(ss, v)]
        tp[pp] = w
        pp += d; ss = ns
        if stp >= steady_t0 and stp < steady_t0 + P:
            mn = min((x for x, val in tp.items() if val != 0), default=pp)
            mx = max((x for x, val in tp.items() if val != 0), default=pp)
            # show relative to pp:
            rel_cells = ''.join(str(tp.get(x, 0)) for x in range(min(mn, pp - 15), max(mx, pp) + 1))
            period.append((stp - steady_t0, stp, pp, chr(65+ss), mx - pp, min(mn, pp) - pp,
                           ''.join(str(tp.get(x, 0)) for x in range(pp - 12, mx + 1))))
    return steady_t0, period

def inspect_candidate(name, line_or_path, prefix, n_states, n_syms):
    print("=" * 80)
    print(f"CANDIDATE: {name}")
    line = find_exact_line(line_or_path, prefix) if prefix else line_or_path
    if not line:
        print(f"NOT FOUND: {prefix} in {line_or_path}")
        return
    cols = line.split('\t')
    pair_idx = next(i for i, c in enumerate(cols) if '|' in c and '_' in c and not c.startswith('||'))
    mech_cols = [c for c in cols[pair_idx:] if not c.startswith('||')]
    mech_line = '\t'.join(mech_cols)
    m = et.parse_mech_line(mech_line)
    print("Meta:", {k: v for k, v in m.items() if k != 'events'})
    r1part = line.split('R1=COL1:')[1].split()[0]
    r1d = {}
    for p in r1part.split(':'):
        if '=' in p:
            k, v = p.split('=', 1)
            r1d[k] = v
    t1_col = int(r1d['t'])
    G1 = int(r1d['gap'])
    x1 = int(r1d['x1'])
    r2min = int(r1d['r2min'])
    ev1 = m['events'][G1][1]
    L2_calc = x1 - r2min + ev1['mna']
    ag1_s, ag2_s = m['pair'].split('|')
    print(f"R1: t1={t1_col}, G1={G1}, x1={x1}, r2min={r2min}, cz={r1d.get('cz')}, L2_calc={L2_calc}")

    status, seq, d = et.exact_tower_rounds(m, G1, L2_calc, round_start=2)
    print(f"exact_tower_rounds: status={status}, rounds={len(seq)}, seq={seq}")

    t1 = parse_tm(ag1_s, n_syms)
    t2 = parse_tm(ag2_s, n_syms)

    # 1. Inspect solo glider
    st0, period = find_solo_glider(t2, m['P'], m['D'])
    print(f"Ag2 steady after step {st0} (P={m['P']}, D={m['D']}):")
    for off, stp, pp, ss, rmax, rmin, tail in period[:6]:
        print(f"  phase+{off:2d} (t={stp:3d}): p2={pp:3d} s2={ss} max_nz-p2={rmax:2d} tape[p2-12..max]={tail}")
    print(f"  max(max_nz - p2) over full period = {max(x[4] for x in period)}")

    # 2. Simulate Round 1 exactly up to t1_col and through bounce + left sweep + exit
    tape = {}
    p1, s1 = 0, 0
    p2, s2 = 2, 0
    for t in range(1, t1_col + 1):
        v1 = tape.get(p1, 0); v2 = tape.get(p2, 0)
        w1, d1, ns1 = t1[(s1, v1)]
        w2, d2, ns2 = t2[(s2, v2)]
        tape[p2] = w2; tape[p1] = w1
        p1 += d1; s1 = ns1
        p2 += d2; s2 = ns2
        if p1 == p2:
            print(f"  UNEXPECTED EARLY COLLISION at t={t}!")
            return
    mn = min(tape.keys()); mx = max(tape.keys())
    print(f"At t1_col={t1_col}: p1={p1} s1={chr(65+s1)} p2={p2} s2={chr(65+s2)} gap={p2-p1}")
    print(f"  left region [min={mn}..{mn+20}]: {''.join(str(tape.get(x,0)) for x in range(mn, min(mx+1, mn+25)))}")
    print(f"  mid/right around p1 [{p1-10}..{mx}]: {''.join(str(tape.get(x,0)) for x in range(p1-10, mx+1))}")
    # Check middle region homogeneity!
    mid_vals = set(tape.get(x, 0) for x in range(mn + 25, p1 - 12))
    print(f"  interior [{mn+25}..{p1-13}] symbol set: {mid_vals}")

    # Continue through bounce + left sweep + Round 2 right exit!
    bounce_steps = 0
    min_p1_r2 = p1
    leftmost_t = t1_col
    snapshot_at_min = None
    # Simulate up to 50M? No, L2 is 86..297 -> if T ~ bt^L? Wait for bt=1 L2=297 it's 2^297, CANNOT simulate full R2!
    # We CAN simulate the bounce & left sweep (first ~200 steps after t1_col) up to when Ag1 enters the regular counter loop!
    # Wait: let's inspect the first 250 steps after t1_col to see how the bounce and left sweep leave the tape,
    # AND let's check what T(L) formula in B[G1] says (T starts at bounce step t1_col and ends at GDX steps after!)
    print(f"  ev1 (B[{G1}]) meta: {ev1}")
    print("  First 150 steps after t1_col:")
    prev_mn = mn
    traj = []
    for k in range(1, 200):
        t = t1_col + k
        v1 = tape.get(p1, 0); v2 = tape.get(p2, 0)
        w1, d1, ns1 = t1[(s1, v1)]
        w2, d2, ns2 = t2[(s2, v2)]
        tape[p2] = w2; tape[p1] = w1
        p1 += d1; s1 = ns1
        p2 += d2; s2 = ns2
        if p1 == p2:
            print(f"  COLLIDED during bounce at t={t}!")
            break
        if p1 < min_p1_r2:
            min_p1_r2 = p1
            leftmost_t = t
            snapshot_at_min = (k, t, p1, chr(65+s1), p2, chr(65+s2),
                               min(tape.keys()), max(tape.keys()), dict(tape))
        traj.append((k, p1, chr(65+s1), p2, chr(65+s2)))
    print(f"  Min p1 during 200 steps after t1_col: p1={min_p1_r2} at k={leftmost_t - t1_col} (t={leftmost_t})")
    if snapshot_at_min:
        k, t, sp1, ss1, sp2, ss2, smn, smx, stp = snapshot_at_min
        print(f"  At min p1 (t={t}, k={k}): p1={sp1} s1={ss1} p2={sp2} s2={ss2}")
        print(f"    left [min..min+20]: {''.join(str(stp.get(x,0)) for x in range(smn-3, smn+20))}")
        print(f"    right [x1-10..p2+5]: {''.join(str(stp.get(x,0)) for x in range(x1-10, sp2+5))}")
    print("  Steps around R1 bounce collision/turnaround (k=1..65):")
    print("   ", [(k, p1, s1, p2-p1) for (k, p1, s1, p2, s2) in traj[:65]])

    # Also test concrete counter behavior on a SMALL synthetic tape with L = 12, 13, 14, 15!
    # Wait: by simulating just the LEFT anchor + length-L uniform block + ev1's small-L splice?
    # Even simpler: check the tape just AFTER Round 1 reaches steady counter! In Round 1, t1_col is ONLY 844..5730!
    # That means during Round 1 itself, Ag1 ALREADY ran the counter on tiny L from t=1..t1_col!
    # Let's dump Ag1's trajectory at key left visits in Round 1 to see exact counter mechanics!
    tape = {}
    p1, s1 = 0, 0
    p2, s2 = 2, 0
    visits = []
    cur_min = 0
    for t in range(1, min(t1_col + 1, 2000)):
        v1 = tape.get(p1, 0); v2 = tape.get(p2, 0)
        w1, d1, ns1 = t1[(s1, v1)]
        w2, d2, ns2 = t2[(s2, v2)]
        tape[p2] = w2; tape[p1] = w1
        p1 += d1; s1 = ns1
        p2 += d2; s2 = ns2
        if p1 <= cur_min + 2:
            cur_min = min(cur_min, p1)
            if len(visits) < 40 and (p1 <= 1):
                seg = ''.join(str(tape.get(x,0)) for x in range(cur_min-2, 18))
                visits.append((t, p1, chr(65+s1), cur_min, seg))
    print(f"  Early R1 left visits (t, p1, s1, min, tape[min-2..17]):")
    for v in visits[:20]:
        print("   ", v)

inspect_candidate("CET3_R4", "bbwork/bb-variants/CET/pinned_cet3_exh.txt",
                  "0LB0LA_1LC1RB_0RB0LC|1RB1LA_1LC1RC_1LA0RB", 3, 2)
inspect_candidate("CET23_R8", "bbwork/bb-variants/CET/pinned_cet23_t1.txt",
                  "1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA", 2, 3)
inspect_candidate("CET4_R15", "bbwork/bb-variants/CET/pinned_cet4_smoke.txt",
                  "1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC", 4, 2)
