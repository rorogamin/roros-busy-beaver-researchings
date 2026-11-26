"""wall_residue.py -- is the verified halting wall a residue class mod 3^k?

If every c in [H-42M, H-3.4M] reaches H and that interval is one residue class
modulo 3^16 = 43,046,721 (the width is 38.6M, just under 3^16), then the
halting set has an arithmetic structure instead of being a dense interval, and
the proof obligation becomes "the orbit hits a fixed residue class".

usage: python wall_residue.py [samples]
"""
import random
import sys

H = (3**307 - 8282708212) // 13959275
LO = H - 42000000
HI = H - 3403055


def step(a, c):
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return None
            return (1, a // 2 + c + 2)
        if c % 2 == 0:
            return (3 * a, c - a + 4)
        return (3 * a + 2, c - a + 1)
    r = c % 4
    if r in (0, 2):
        return (a - c - 1, 3 * (c // 2) + 2)
    if r == 1:
        if a == c + 1:
            return None
        return (a - c - 2, 3 * (c // 2) + 5)
    if a == c + 1:
        return None
    if a == c + 2:
        return (3 * c + 8, 1)
    if a == c + 3:
        return None
    return (a - c - 4, 3 * (c // 2) + 8)


def endpoint(c0, cap=200000):
    """Run the chain from A(1,c0).  Returns (halted, last_c, steps)."""
    a, c = 1, c0
    for n in range(1, cap + 1):
        nxt = step(a, c)
        if nxt is None:
            return (True, None, n)
        a, c = nxt
        if a == 1:
            return (False, c, n)
    return ("cap", None, cap)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    print("H bits =", H.bit_length())
    print("H mod 3^16 =", H % 3**16)
    print("wall width =", HI - LO + 1, " 3^16 =", 3**16, " 3^15 =", 3**15)
    random.seed(7)
    cs = [random.randint(LO, HI) for _ in range(n)]
    for k in (14, 15, 16):
        mod = 3**k
        res = {c % mod for c in cs}
        print(f"  mod 3^{k}: {len(res)} distinct out of {len(cs)} samples")
        print("     sample residues:", sorted(res)[:6])
    # do the sampled wall values actually reach H?
    ok = 0
    steps = []
    for c in cs:
        halted, endc, st = endpoint(c)
        steps.append(st)
        if not halted and endc == H:
            ok += 1
    print(f"  reach H: {ok}/{len(cs)}; chain length min/mean/max = "
          f"{min(steps)}/{sum(steps)/len(steps):.1f}/{max(steps)}")
    # and do they share a residue class at all?  compare to random c near H
    rs = {c % (3**16) for c in cs}
    print("  all same residue mod 3^16:", len(rs) == 1)
    print("  residues mod 3^16 (sorted):", sorted(rs))


if __name__ == "__main__":
    main()
