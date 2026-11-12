import io, contextlib, sys
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

# Simulate coupled Ag1+Ag2 up to step 300 to get exact steady phase of Ag2!
def check_pair(label, spec1, spec2, t_exit, p1_e):
    T1 = parse3(spec1)
    T2 = parse3(spec2)
    tp = {}
    p1, s1, p2, s2 = 0, 0, 2, 0
    max1 = 0
    h2 = {}
    for t in range(1, 5000):
        w1, d1, ns1 = T1[(s1, tp.get(p1, 0))]
        w2, d2, ns2 = T2[(s2, tp.get(p2, 0))]
        tp[p2] = w2; tp[p1] = w1
        p1 += d1; s1 = ns1
        p2 += d2; s2 = ns2
        if p1 > max1: max1 = p1
        h2[t] = (p2, s2, dict(tp)) if 100 <= t <= 120 else (p2, s2, None)
        if p1 == p2:
            print(f"{label}: early collision t={t}")
            return
    # Verify Ag2 period P=16, D=4 after t=100
    assert h2[116][0] - h2[100][0] == 4 and h2[116][1] == h2[100][1]
    # Also find the exact glider window where t % 16 matches the canon pat in mechs_cet3_exh.txt!
    # At t >= t_exit: Ag1 walks right 1 step per t from p1_e in state B (reading 1s written by Ag2)
    # Wait: let's verify all cells right of p1_e are 1 up to Ag2's active window (pat)!
    base = 100
    m = None
    for line in open('bbwork/bb-variants/CET/mechs_cet3_exh.txt'):
        if line.startswith(spec1 + '|' + spec2 + '\t'):
            m = et.parse_mech_line(line)
            break
    if not m:
        print(f"{label}: not found in mechs_cet3_exh.txt")
        return

    print(f"=== {label} (t_exit={t_exit}, p1_e={p1_e}) events={sorted(m['events'].keys())} ===")
    # Check t near (4*t_exit - 4*p1_e)//3 where p2(t) - p1(t) == 30 (just before mg=8..19)
    # Then splice Ag2's actual steady tape window around p2(t) and simulate the exact collision!
    t_near = ((4 * t_exit - 4 * p1_e) // 3) - 60
    ph0 = (t_near - base) % 16
    p2_0, s2_0, tp_0 = h2[base + ph0]
    shift = 4 * ((t_near - base) // 16)
    p2_cur = p2_0 + shift
    p1_cur = p1_e + (t_near - t_exit)
    s1_cur = 1  # state B
    s2_cur = s2_0
    # Reconstruct local tape around [p1_cur - 20 .. p2_cur + 50]
    tp_local = {}
    for x in range(p1_cur - 40, p2_cur + 60):
        tp_local[x] = 1  # Ag2 tsym=1 trail + Ag1 1-walk
    # Overlay Ag2 active window relative to p2_0 -> p2_0 + shift
    for k, v in tp_0.items():
        if k >= p2_0 - 30:
            tp_local[k + shift] = v

    # Simulate coupled for 250 steps and find exact first entry into steady gap G in [mg .. mg+M-1] with canon Ag2 state
    # Wait canon Ag2 state in mechs_cet3_exh is when Ag2 pat matches! Let's just trace to collision OR first steady bounce!
    min1_b = p1_cur
    for dt in range(1, 300):
        t = t_near + dt
        w1, d1, ns1 = T1[(s1_cur, tp_local.get(p1_cur, 1))]
        w2, d2, ns2 = T2[(s2_cur, tp_local.get(p2_cur, 0))]
        tp_local[p2_cur] = w2
        tp_local[p1_cur] = w1
        p1_cur += d1; s1_cur = ns1
        p2_cur += d2; s2_cur = ns2
        gap = p2_cur - p1_cur
        if p1_cur == p2_cur:
            print(f"  !! COLLIDED IN R1 AT t={t} x={p1_cur} !!")
            return
        if gap < 30 and dt <= 100:
            # print only when s1_cur transitions or small gap
            pass
    # Find the exact t where p1_cur = max1 of bounce (when Ag1 turns left)
    # Better: find min p2-p1 during bounce, and check exact (t, p1, s1, p2, s2, gap) at dt where s1_cur=='B' just before first hitting Ag2 pat!
    # Re-run cleanly checking exact match against B/H events at s1=B and s2=gl_s!
    print("  Let's inspect the bounce window directly:")
    p2_cur = p2_0 + shift
    p1_cur = p1_e + (t_near - t_exit)
    s1_cur = 1; s2_cur = s2_0
    tp_local = {x: 1 for x in range(p1_cur - 40, p2_cur + 80)}
    for k, v in tp_0.items():
        if k >= p2_0 - 30:
            tp_local[k + shift] = v
    for dt in range(1, 140):
        t = t_near + dt
        v1 = tp_local.get(p1_cur, 1); v2 = tp_local.get(p2_cur, 0)
        w1, d1, ns1 = T1[(s1_cur, v1)]; w2, d2, ns2 = T2[(s2_cur, v2)]
        tp_local[p2_cur] = w2; tp_local[p1_cur] = w1
        p1_cur += d1; s1_cur = ns1; p2_cur += d2; s2_cur = ns2
        gap = p2_cur - p1_cur
        if dt >= 20 and gap <= 25:
            print(f"    dt={dt} t={t} p1={p1_cur}({chr(65+s1_cur)}) p2={p2_cur}({chr(65+s2_cur)}) gap={gap} head_bits={tp_local.get(p1_cur,1)}{tp_local.get(p1_cur+1,1)}")

check_pair("0LB0LA", "0LB0LA_1LC1RB_0RB0LC", "1LB0RC_1RA0LC_1RB1RA", 167772456, 224)
check_pair("1LB0LA", "1LB0LA_1LC1RB_0RB0LC", "1LB0RC_1RA0LC_1RB1RA", 536871222, 228)
