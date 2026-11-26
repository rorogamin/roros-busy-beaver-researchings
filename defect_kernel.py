import sys

def chain_len(c):
    a = 1
    n = 0
    while True:
        n += 1
        if a <= c:
            if a % 2 == 0:
                if c % 2 == 0:
                    return n
                a, c = 1, a // 2 + c + 2
            elif c % 2 == 0:
                a, c = 3 * a, c - a + 4
            else:
                a, c = 3 * a + 2, c - a + 1
        else:
            r = c % 4
            if r in (0, 2):
                a, c = a - c - 1, 3 * (c // 2) + 2
            elif r == 1:
                if a == c + 1:
                    return n
                a, c = a - c - 2, 3 * (c // 2) + 5
            elif a == c + 1:
                return n
            elif a == c + 2:
                a, c = 3 * c + 8, 1
            elif a == c + 3:
                return n
            else:
                a, c = a - c - 4, 3 * (c // 2) + 8
        if a == 1:
            return n

N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
M = 300
L = [0] * (N + 1)
for c in range(1, N + 1):
    L[c] = chain_len(c)

seqs = {
    'D3(m)=L(3m)-L(m)': [L[3*m] - L[m] for m in range(1, N//3 + 1)],
    'Dfloor(c)=L(c)-L(c/3)': [L[c] - L[c//3] for c in range(1, N + 1)],
    'D3plus1(m)=L(3m+1)-L(m)': [L[3*m+1] - L[m] for m in range(1, (N-1)//3 + 1)],
    'D3plus2(m)=L(3m+2)-L(m)': [L[3*m+2] - L[m] for m in range(1, (N-2)//3 + 1)],
}

for name, seq in seqs.items():
    V = len(seq)
    print(f"{name}  values={V} range=[{min(seq)},{max(seq)}]")
    for k in (2, 3, 4, 6):
        e = 0; p = 1
        out = []
        while p <= V // M and e <= 5:
            sigs = set()
            for r in range(p):
                sig = tuple(seq[p*n + r - 1] if p*n + r - 1 < V else -999 for n in range(1, M+1))
                sigs.add(sig)
            out.append((e, p, len(sigs)))
            e += 1; p *= k
        print(f"  base {k}: " + ", ".join(f"e{e}:p{p}:{c}" for e,p,c in out))
    print()
