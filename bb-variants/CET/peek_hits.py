def parse(spec):
    states = spec.split("_")
    nsym = len(states[0]) // 3
    tbl = []
    for st in states:
        row = []
        for i in range(nsym):
            s = st[3*i:3*i+3]
            row.append((int(s[0]), 1 if s[1]=='R' else -1, ord(s[2])-65))
        tbl.append(row)
    return tbl, nsym

def trace(e_spec, g_spec, steps=2000):
    T1, nsym = parse(e_spec)
    T2, _ = parse(g_spec)
    tp = {}
    p1, s1, p2, s2 = 0, 0, 2, 0
    mn1 = mx1 = 0
    for t in range(1, steps+1):
        r1, r2 = tp.get(p1, 0), tp.get(p2, 0)
        w1, d1, ns1 = T1[s1][r1]
        w2, d2, ns2 = T2[s2][r2]
        tp[p2] = w2
        tp[p1] = w1
        p1 += d1; s1 = ns1
        p2 += d2; s2 = ns2
        mn1 = min(mn1, p1); mx1 = max(mx1, p1)
        if p1 == p2:
            return f"HALT at {t}"
    keys = sorted(k for k, v in tp.items() if v != 0)
    lo = min(keys) if keys else 0
    hi = max([k for k in keys if k < p2 - 15] + [mx1])
    s_tape = "".join(str(tp.get(x, 0)) for x in range(min(mn1, -3), hi+2))
    return f"t={steps} p1={p1}(s={chr(65+s1)}) p2={p2}(s={chr(65+s2)}) mn1={mn1} mx1={mx1} span=[{min(mn1,-3)}..{hi+1}] tape={s_tape}"

print("CET3_3round:", trace("1LB0RA_1LC1RB_0RB0LC", "1RB0LB_0RC0LA_1LB1RC", 1000))
print("CET3 M=32a:", trace("0LB1LA_1LC1RB_0RB0LC", "0RC0RA_1LA1RB_1LB1LC", 5000))
print("CET3 M=24a:", trace("0LB0LA_0RC0LB_1LB1RC", "1LC0RC_1RA1RB_0RB0LB", 5000))
print("CET3 M=22:",  trace("1LB1RA_1RB1LC_0RA0LB", "1RC1LA_0RC1RB_0LA0RB", 5000))
print("CET23 M=34:", trace("1LB1RA0RA_2RA0LB2LA", "1LB0RB1LB_1RA2LA2RB", 5000))
print("CET23 M=30a:", trace("1LB2RA2LA_0RA0LA0LB", "2LB1RA1RB_2RA0LA1LB", 5000))
print("CET23 b3:",  trace("0RB0LA0LA_2LA1RB1LA", "1RB2RB0RA_1LB0RA1LA", 5000))
