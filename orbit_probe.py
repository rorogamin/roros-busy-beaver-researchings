#!/usr/bin/env python3
"""Probe the accelerated orbits of the two transducer holdouts.

Iterative (streaming-carry) implementations of `pass` (#397) and `wilyPass` (#531/#532),
matching BusyBeaver/BB33/M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA.lean and WilyCoyote.lean.
Reports halting, the set of two-cell suffixes along the orbit, and the stripped-tail lengths.

Usage: python3 orbit_probe.py [sweeps]
"""

import sys


def wily(w):
    q, out, i, n = "s0", [], 0, len(w)
    while i < n:
        b = w[i]
        i += 1
        if q == "s0":
            out.append(not b)
            q = "s1" if b is False else "s2"
        elif q == "s1":
            out.append(not b)
            q = "s3" if b is False else "s0"
        elif q == "s2":
            out.append(b)
            q = "s2" if b is False else "s1"
        else:  # s3 copies the rest of the word verbatim
            out.append(not b)
            return out + w[i:]
    return {"s0": out + [False], "s1": None,
            "s2": out + [True, True, False, False], "s3": out + [False, False]}[q]


def p397(w):
    q, out, i, n = "ca", [], 0, len(w)
    while i < n:
        b = w[i]
        i += 1
        if q == "ca":
            out.append(not b)
            q = "cc" if b is False else "cb"
        elif q == "cb":  # early exit: rest copied verbatim
            out.append(not b)
            return out + w[i:]
        elif q == "cc":
            out.append(not b)
            q = "ca" if b is False else "cd"
        elif q == "cd":
            out.append(b)
            q = "ce" if b is False else "cf"
        elif q == "ce":
            out.append(b)
            q = "ca" if b is False else "cd"
        else:  # cf
            out.append(b)
            q = "cd" if b is False else "ca"
    term = {"ca": [True], "cb": [False, True], "cc": None,
            "cd": [False, False, True], "ce": None, "cf": [True, False, False, True]}[q]
    return None if term is None else out + term


def blocks2(w):
    n = 0
    while len(w) >= 2 and w[0] is False and w[1] is True:
        n += 1
        w = w[2:]
    return n


def blocks4(w):
    n = 0
    while len(w) >= 4 and w[:4] == [False, True, False, False]:
        n += 1
        w = w[4:]
    return n


def show(bits):
    return "".join("1" if x else "2" for x in bits)


def run(name, start, step, tail, N):
    w, suffix, lens, halt = list(start), {}, [], None
    for k in range(N):
        suffix[show(w[-2:])] = suffix.get(show(w[-2:]), 0) + 1
        lens.append(len(tail(w)))
        out = step(w)
        if out is None:
            halt = k
            break
        w = [False] + out
    print(f"{name}: halt={halt} (searched {k} sweeps) last2={suffix} "
          f"tailLen={min(lens)}..{max(lens)}")


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    run("WILY", [False, False], wily, lambda w: w[2 * blocks2(w):], N)
    run("#397", [True], p397, lambda w: w[4 * blocks4(w):], N)
    print("counterexamples:")
    print("  pass .ca [1,1]      =", p397([True, True]), "(ends 2, so next word ends 2)")
    print("  pass .ca [2,2,2]    =", p397([False, False, False]), "(halt)")
    print("  pass .ca [1,2,1]    =", p397([True, False, True]), "(21-suffix not preserved)")
    print("  wilyPass .s0 [2,2,2]=", wily([False, False, False]))
    print("  wilyPass .s0 [2,1,1,1]=", wily([False, True, True, True]), "(halt)")
