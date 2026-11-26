"""wall_blocks.py -- are wall values partitioned into long blocks with a
constant rule sequence?  A block certificate for the wall needs exactly that:
on an interval [x,y] the chain follows one fixed rule word, and interval
arithmetic then maps [x,y] into a later block.

usage: python wall_blocks.py [samples]
"""
import random
import sys

H = (3**307 - 8282708212) // 13959275
LO = H - 42000000
HI = H - 3403055


def step(a, c):
    """Returns (rule, (a',c')) or (rule, None) on halt."""
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return ("g", None)
            return ("h", (1, a // 2 + c + 2))
        if c % 2 == 0:
            return ("i", (3 * a, c - a + 4))
        return ("j", (3 * a + 2, c - a + 1))
    r = c % 4
    if r in (0, 2):
        return ("a", (a - c - 1, 3 * (c // 2) + 2))
    if r == 1:
        if a == c + 1:
            return ("f", None)
        return ("b", (a - c - 2, 3 * (c // 2) + 5))
    if a == c + 1:
        return ("f", None)
    if a == c + 2:
        return ("e", (3 * c + 8, 1))
    if a == c + 3:
        return ("d", None)
    return ("c", (a - c - 4, 3 * (c // 2) + 8))


def word(c0, cap=200000):
    a, c = 1, c0
    out = []
    for _ in range(cap):
        rule, nxt = step(a, c)
        out.append(rule)
        if nxt is None:
            return "".join(out)
        a, c = nxt
        if a == 1:
            return "".join(out)
    return "".join(out)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    random.seed(11)
    for _ in range(n):
        c0 = random.randint(LO, HI)
        w = word(c0)
        left = right = 0
        while c0 - left - 1 >= LO and word(c0 - left - 1) == w:
            left += 1
        while c0 + right + 1 <= HI and word(c0 + right + 1) == w:
            right += 1
        print(f"c0 digits~{len(str(c0))} wordlen={len(w)} block=[-{left},+{right}] "
              f"width={left+right+1}")
    # how many distinct words along a run of 200 consecutive values?
    c0 = random.randint(LO, HI - 400)
    words = {word(c0 + i) for i in range(200)}
    print(f"200 consecutive wall values: {len(words)} distinct rule words")


if __name__ == "__main__":
    main()
