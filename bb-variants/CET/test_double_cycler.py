def parse_machine(m_str):
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

def test_double_cycler_decider(m_str, max_steps=200):
    tables = parse_machine(m_str)
    t0, t1 = tables[0], tables[1]
    tape = {}
    p0, q0 = 0, 0
    p1, q1 = 2, 0
    mn0, mx0 = 0, 0
    mn1, mx1 = 2, 2
    
    # Track configurations of Agent 0 and Agent 1 when disjoint
    history0 = {} # (p0, q0, tape_window_str) -> step
    history1 = {} # (q1, b1_read) -> (step, p1)
    
    cycle0_detected = None # (period, min_p, max_p)
    cycle1_detected = None # (period, drift_direction)
    
    for step in range(1, max_steps + 1):
        b0 = tape.get(p0, 0)
        b1 = tape.get(p1, 0)
        
        # Are they disjoint? (Agent 0 strictly to the left of Agent 1's visited region)
        if mx0 < mn1:
            # 1. Check if Agent 0 is in a stationary cycle
            tape_window = tuple((tape.get(x, 0) for x in range(mn0, mx0 + 1)))
            state0 = (p0 - mn0, q0, tape_window)
            if state0 in history0 and cycle0_detected is None:
                p_len = step - history0[state0]
                cycle0_detected = (p_len, mn0, mx0)
            else:
                history0[state0] = step
                
            # 2. Check if Agent 1 is in a translated cycle moving right into blank tape
            # (reading 0s outside all touched tape)
            if p1 > mx0 and p1 >= mx1 and b1 == 0:
                sig1 = (q1, 0)
                if sig1 in history1 and cycle1_detected is None:
                    prev_step, prev_p1 = history1[sig1]
                    dp = p1 - prev_p1
                    dt = step - prev_step
                    if dp > 0: # Moving away to the right!
                        cycle1_detected = (dt, dp)
                else:
                    history1[sig1] = (step, p1)
        
        # Did both cycles trigger?
        if cycle0_detected and cycle1_detected:
            return True, f"Double Cycler Proven at step {step}! Agent 0 in stationary cycle (period={cycle0_detected[0]}, window=[{cycle0_detected[1]}, {cycle0_detected[2]}]). Agent 1 in translated cycler (period={cycle1_detected[0]}, drift=+{cycle1_detected[1]} cells)."
            
        w0, d0, n0 = t0[q0][b0]
        w1, d1, n1 = t1[q1][b1]
        tape[p1] = w1
        tape[p0] = w0
        p0 += d0
        p1 += d1
        q0 = n0
        q1 = n1
        if p0 < mn0: mn0 = p0
        if p0 > mx0: mx0 = p0
        if p1 < mn1: mn1 = p1
        if p1 > mx1: mx1 = p1
        
        if p0 == p1:
            return False, f"Halted at step {step}"
            
    return False, "Undecided within max_steps"

m = "0LB0RA_0RA0RA_0RA0RA|0RB0RA_0RC0RA_0LA0RA"
res, msg = test_double_cycler_decider(m, 100)
print("Result for Holdout #1:")
print(f"Decided non-halting? {res}")
print(f"Details: {msg}")
