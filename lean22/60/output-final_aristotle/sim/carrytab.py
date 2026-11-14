"""Extract the carry transducer: for each B-event transition of phase P1 or P3,
print the input suffix R (after the fixed prefix) and the output suffix R'."""
import sys
from be2 import bevents
from toklib import fmt
from probe import U, u, V

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    ev = bevents(3000000)
    W = [e[2] for e in ev]
    for j in range(min(N, len(W) - 1)):
        A, B = W[j], W[j + 1]
        if len(A) < 2:
            print("%4d short %s" % (j, fmt(A))); continue
        if A[0] == U(2, 1):                      # P1
            ph = 'P1'; Rin = A[2:]; pre = B[:2]; Rout = B[2:]
            assert A[1] == U(4, 1), fmt(A)
            assert pre == [U(2, 2), u], fmt(B)
        elif A[0] == U(2, 2) and A[1] == U(1, 1):   # P2
            continue
        elif A[0] == U(2, 2) and A[1] == V(1):     # P3
            ph = 'P3'; Rin = A[3:]; pre = B[:2]; Rout = B[2:]
            assert A[2] == u, fmt(A)
            assert pre == [U(2, 1), U(4, 1)], fmt(B)
        else:
            print('%4d ???  %s' % (j, fmt(A))); continue
        print('%4d %s  %-60s -->  %s' % (j, ph, fmt(Rin)[:60], fmt(Rout)[:90]))
