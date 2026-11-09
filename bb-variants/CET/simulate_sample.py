# Python quick simulator to inspect holdout behaviors
def parse_m(s):
    # returns tr[agent][state][sym] -> (w, m, n)
    agents = s.split('|')
    tr = []
    for a in agents:
        st_trs = []
        for st in a.split('_'):
            # 2 transitions: 0 and 1
            t0 = (int(st[0]), 1 if st[1] == 'R' else -1, ord(st[2]) - ord('A'))
            t1 = (int(st[3]), 1 if st[4] == 'R' else -1, ord(st[5]) - ord('A'))
            st_trs.append((t0, t1))
        tr.append(st_trs)
    return tr

def sim(s, max_steps=50000):
    tr = parse_m(s)
    tape = {}
    p0, p1 = 0, 2
    q0, q1 = 0, 0
    
    p0_hist = []
    p1_hist = []
    
    for step in range(1, max_steps + 1):
        b0 = tape.get(p0, 0)
        b1 = tape.get(p1, 0)
        
        w0, m0, n0 = tr[0][q0][b0]
        w1, m1, n1 = tr[1][q1][b1]
        
        tape[p0] = w0
        tape[p1] = w1
        
        p0 += m0
        p1 += m1
        q0 = n0
        q1 = n1
        
        if p0 == p1:
            return f"HALTED at step {step} (x={p0})"
            
        if step % 5000 == 0 or step == max_steps:
            p0_hist.append(p0)
            p1_hist.append(p1)
            
    # Check tape bounds and positions
    tape_keys = tape.keys()
    min_tape = min(tape_keys) if tape_keys else 0
    max_tape = max(tape_keys) if tape_keys else 0
    num_ones = sum(tape.values())
    
    return f"Alive at {max_steps} | p0={p0}, p1={p1}, dist={abs(p1-p0)} | tape=[{min_tape}, {max_tape}], ones={num_ones}"

with open("holdouts_cet3_harvested.txt") as f:
    holdouts = [line.strip().split("\t") for line in f if line.strip()]

print("Analyzing sample of holdouts at 50,000 steps:\n")
sample_indices = [0, 1, 12, 100, 200, 300, 400, 500, 600, 700, 800, 832]
for idx in sample_indices:
    num, m_str = holdouts[idx]
    res = sim(m_str, 50000)
    print(f"Holdout #{num}: {m_str}")
    print(f"  Result: {res}\n")
