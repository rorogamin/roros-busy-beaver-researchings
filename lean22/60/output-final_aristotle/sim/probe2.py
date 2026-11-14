"""Probe the P3 (or P1) macro step with a general absorbing token and a general follower.

Tape: 0^3 . <prefix> . u^r . U(a,b) . <follower> . u^N , head in state B at offset 3.
Runs to the next B-event (head back at offset 0 in state B) and prints the resulting
token word together with the step count.
"""
import sys
from toklib import parse, fmt as tfmt
from flat import run, fmt

P1 = [0,4,4,2] + [0,4,4,4,4,2]
P2 = [0,4,4,2,2] + [0,4,2]
P3 = [0,4,4,2,2] + [4,3,2] + [0,4,2]

def U(a,b): return [0] + [4]*a + [2]*b
def V(c):   return [4,3] + [2]*c

def probe(prefix, r, tok, follow, N=40, pad=3):
    word = [0]*pad + prefix + U(1,1)*r + tok + follow + U(1,1)*N
    res, n, k, l = run(word, k=pad)
    if res != 'done':
        return res, n, fmt(l)
    return res, n, tfmt(parse(fmt(l)))

if __name__ == '__main__':
    print('=== P3, absorbing token U(a,b), follower u')
    for a in (1,2):
        for b in (2,4,6):
            for r in (0,1):
                print('  a=%d b=%d r=%d : %s' % (a,b,r, probe(P3, r, U(a,b), U(1,1))))
    print('=== P3, absorbing token U(a,b), follower V(c)')
    for a in (1,2):
        for b in (2,4):
            for c in (1,3,5,7):
                print('  a=%d b=%d c=%d : %s' % (a,b,c, probe(P3, 0, U(a,b), V(c))))
    print('=== P1, absorbing token U(a,b), follower u')
    for a in (1,2):
        for b in (2,4):
            for r in (0,1):
                print('  a=%d b=%d r=%d : %s' % (a,b,r, probe(P1, r, U(a,b), U(1,1))))
    print('=== P1, absorbing token U(a,b), follower V(c)')
    for a in (1,2):
        for b in (2,4):
            for c in (1,3,5,7):
                print('  a=%d b=%d c=%d : %s' % (a,b,c, probe(P1, 0, U(a,b), V(c))))
