m_str = "0LB0LC_1RB1LA_1RC0LA|1LB1RA_1RC1LC_0LB1RC" # Holdout #833
from simulate_sample import parse_m

tr = parse_m(m_str)
tape = {}
p0, p1 = 0, 2
q0, q1 = 0, 0

print(f"Holdout #833 ({m_str}) first 30 steps:")
for step in range(1, 31):
    b0 = tape.get(p0, 0)
    b1 = tape.get(p1, 0)
    w0, m0, n0 = tr[0][q0][b0]
    w1, m1, n1 = tr[1][q1][b1]
    tape[p0] = w0
    tape[p1] = w1
    print(f"step {step:2d}: p0={p0:+2d}(q{chr(ord('A')+q0)},r{b0}->w{w0},m{m0:+d},n{chr(ord('A')+n0)}) | p1={p1:+2d}(q{chr(ord('A')+q1)},r{b1}->w{w1},m{m1:+d},n{chr(ord('A')+n1)})")
    p0 += m0
    p1 += m1
    q0 = n0
    q1 = n1

print(f"\nStep 30: p0={p0}, p1={p1}, q0={chr(ord('A')+q0)}, q1={chr(ord('A')+q1)}")
print("Tape around p1:")
for k in range(0, 5):
    print(f"  tape[{k}] = {tape.get(k, 0)}")
