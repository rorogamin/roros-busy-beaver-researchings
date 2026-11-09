m_str = "0LB0LC_0RB1LA_1RB0LA|1LB0RC_1RA1LB_1RA1RC"
from simulate_sample import parse_m

tr = parse_m(m_str)
tape = {}
p0, p1 = 0, 2
q0, q1 = 0, 0

print("Holdout #301 first 20 steps:")
for step in range(1, 21):
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
    if p0 == p1:
        print(f"COLLISION at step {step} at pos {p0}")
        break

print("\nTape non-zero positions after 20 steps:")
for k in sorted(tape.keys()):
    if tape[k] != 0:
        print(f"  tape[{k}] = {tape[k]}")
print(f"Current positions: p0={p0}, q0={chr(ord('A')+q0)} | p1={p1}, q1={chr(ord('A')+q1)}")
