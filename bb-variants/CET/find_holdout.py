import os, sys

# Fast Python simulator to verify and display the CET(3) holdouts
def parse_machine(m_str):
    # e.g. 0RA0RA_0RA0RA_0RA0RA|0RB0RA_0RC0RA_0LA0RA
    agents = m_str.strip().split('|')
    parsed = []
    for ag in agents:
        states = ag.split('_')
        ag_table = []
        for st in states:
            transitions = []
            for b in range(len(st) // 3):
                part = st[b*3 : (b+1)*3]
                w = int(part[0])
                d = 1 if part[1] == 'R' else -1
                n = ord(part[2]) - ord('A')
                transitions.append((w, d, n))
            ag_table.append(transitions)
        parsed.append(ag_table)
    return parsed

def simulate_fast(tables, limit=5000000):
    tape = {}
    p0, q0 = 0, 0
    p1, q1 = 2, 0
    t0 = tables[0]
    t1 = tables[1]
    
    # Track envelope
    mn0, mx0 = 0, 0
    mn1, mx1 = 2, 2
    
    for step in range(1, limit + 1):
        b0 = tape.get(p0, 0)
        b1 = tape.get(p1, 0)
        
        w0, d0, n0 = t0[q0][b0]
        w1, d1, n1 = t1[q1][b1]
        
        tape[p1] = w1
        tape[p0] = w0
        
        p0 += d0
        p1 += d1
        q0 = n0
        q1 = n1
        
        if p0 == p1:
            return step, p0, "COLLISION"
            
        # Quick escape check
        if step % 100000 == 0:
            dist = abs(p0 - p1)
            # If distance exceeds 5000 and growing linearly away
            if dist > 5000 and (p0 > p1 if d0 > 0 and d1 <= 0 else p1 > p0):
                return step, p0, "ESCAPE"
                
    return limit, (p0, p1), "HOLDOUT"

with open("cet3_all_seeds.txt") as f:
    lines = [l.strip().split()[-1] for l in f if '|' in l]

print(f"Loaded {len(lines)} seeds. Finding first holdouts that survived without halting...")

holdouts = []
for idx, seed in enumerate(lines[:50]):
    tables = parse_machine(seed)
    st, pos, res = simulate_fast(tables, limit=2000000)
    if res == "HOLDOUT":
        holdouts.append((seed, st, pos))
        print(f"\n*** [FOUND CET(3) HOLDOUT #{len(holdouts)}] ***")
        print(f"Machine: {seed}")
        print(f"Positions at step {st}: Agent 0 at {pos[0]}, Agent 1 at {pos[1]} (dist={abs(pos[0]-pos[1])})")
        if len(holdouts) >= 3:
            break

if not holdouts:
    print("Testing mutations of seed 0...")
    # Mutate 1 transition
    base = lines[0]
    parsed_base = parse_machine(base)
    for a in range(2):
        for q in range(3):
            for b in range(2):
                for nw in [0, 1]:
                    for nd in [1, -1]:
                        for nn in [0, 1, 2]:
                            m_copy = [
                                [list(row) for row in parsed_base[0]],
                                [list(row) for row in parsed_base[1]]
                            ]
                            m_copy[a][q][b] = (nw, nd, nn)
                            st, pos, res = simulate_fast(m_copy, limit=1000000)
                            if res == "HOLDOUT":
                                def to_str(m):
                                    return "|".join(["_".join(["".join([f"{w}{'R' if d>0 else 'L'}{chr(ord('A')+n)}" for w,d,n in st]) for st in ag]) for ag in m])
                                m_str = to_str(m_copy)
                                holdouts.append((m_str, st, pos))
                                print(f"\n*** [MUTATION CET(3) HOLDOUT #{len(holdouts)}] ***")
                                print(f"Machine: {m_str}")
                                print(f"Positions at step {st}: Agent 0 at {pos[0]}, Agent 1 at {pos[1]}")
                                if len(holdouts) >= 3:
                                    sys.exit(0)
