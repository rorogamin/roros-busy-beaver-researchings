m_str = "0LB0LC_1RB1LA_1RC0LA|1LB1RA_1RC1LC_0LB1RC"
from simulate_sample import parse_m

tr = parse_m(m_str)
def check_blank_drift(ag, q0, dir_d):
    lt = {}
    p = 64
    q = q0
    hist_p = [p]
    hist_q = [q]
    
    for t in range(1, 49):
        b = lt.get(p, 0)
        w, m, n = tr[ag][q][b]
        lt[p] = w
        p += m
        q = n
        if (p - 64) * dir_d < 0:
            return False
        hist_p.append(p)
        hist_q.append(q)
        for pt in range(t):
            if hist_q[pt] == q:
                dp = (p - hist_p[pt]) * dir_d
                if dp > 0:
                    valid = True
                    for k in range(pt, t + 1):
                        if (hist_p[k] - hist_p[pt]) * dir_d < 0:
                            valid = False
                            break
                    if valid:
                        return True, t, pt, dp
    return False

for q in range(3):
    print(f"Agent 0 state {chr(ord('A')+q)} blank drift L:", check_blank_drift(0, q, -1))
