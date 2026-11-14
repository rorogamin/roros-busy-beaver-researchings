def parse(s):
    T = {}
    for st, row in enumerate(s.split('_')):
        for sym in (0, 1):
            tok = row[3*sym : 3*sym+3]
            T[(st, sym)] = None if tok == '---' else (int(tok[0]), -1 if tok[1] == 'L' else 1, ord(tok[2]) - 65)
    return T

def find_cert(s1, s2, t0_base=10000, max_p=30000):
    T1, T2 = parse(s1), parse(s2)
    tp = {}
    p1, st1, p2, st2 = 0, 0, 2, 0
    for t in range(1, t0_base + 1):
        tr1, tr2 = T1.get((st1, tp.get(p1, 0))), T2.get((st2, tp.get(p2, 0)))
        if tr1 is None or tr2 is None: return None
        tp[p2] = tr2[0]; tp[p1] = tr1[0]
        p1 += tr1[1]; st1 = tr1[2]; p2 += tr2[1]; st2 = tr2[2]
        if p1 == p2: return None

    # Now run solo Agent 1 and solo Agent 2 from t0_base
    # For each agent, find exact repeat using full active window around head
    def find_solo(T, p0, s0, tp0, dx_sign):
        # dx_sign: -1 for <=0, +1 for >=0
        tp_s = dict(tp0)
        p, s = p0, s0
        seen = {}
        for t in range(max_p):
            # Use 31-cell window around p as candidate key
            key = (s, tuple(tp_s.get(p + d, 0) for d in range(-15, 16)))
            if key in seen:
                prev_t, prev_p, prev_tp = seen[key]
                dx = p - prev_p
                period = t - prev_t
                if (dx_sign < 0 and dx <= 0) or (dx_sign > 0 and dx >= 0):
                    # Verify exact!
                    # Re-run from prev_t? We saved prev_tp!
                    return (prev_t, period, dx)
            if t < 200 or t % 1 == 0:
                seen[key] = (t, p, None)
            tr = T.get((s, tp_s.get(p, 0)))
            if tr is None: return None
            tp_s[p] = tr[0]; p += tr[1]; s = tr[2]
        return None

    r1 = find_solo(T1, p1, st1, tp, -1)
    r2 = find_solo(T2, p2, st2, tp, +1)
    if not r1 or not r2: return None
    return (t0_base + max(r1[0], r2[0]), r1[1], r1[2], r2[1], r2[2])

if __name__ == '__main__':
    lines = [l.strip().split('\t') for l in open('bbwork/bb-variants/CET/s18/oob_separated_cand.txt') if l.strip()]
    found = 0
    for l in lines[:50]:
        idx = int(l[0])
        s1, s2 = l[3].split()
        c = find_cert(s1, s2)
        if c:
            found += 1
            if found <= 5:
                print(f'#{idx}: {c}')
    print(f'Found {found}/50')
