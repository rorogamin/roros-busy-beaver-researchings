"""The fractal identity.

Claim (checked here by simulation, *not* machine-checked):

  let  W_j  be the tape word at the j-th canonical B-event (j = 0, 1, 2, ...),
  let  core(W) = W with its first token and its trailing run of u = U(1,1) removed.

  Then, when a carry of four 2's reaches a token U(3j+1, 1), that token unfolds into

      u u        ++ core(W_j)      if W_j starts with U(2,1)   (phase P1)
      u U(1,2)   ++ core(W_j)      if W_j starts with U(2,2)   (phases P2, P3)

  i.e. the 4-run of length 3j+1 is a *compressed copy of the tape at B-event j*.
"""
from be2 import bevents
from probe import runto, P3, U, u
from toklib import fmt

def core(W):
    W = W[1:]
    while W and W[-1] == u:
        W = W[:-1]
    return W

def predict(W):
    if W[0] == U(2, 1):
        return [u, u] + core(W)
    if W[0] == U(2, 2):
        return [u, U(1, 2)] + core(W)
    raise ValueError(W)

if __name__ == '__main__':
    import sys
    J = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    ev = bevents(400000)
    ok = bad = 0
    for j in range(J):
        W = ev[j][2]
        a = 3 * j + 1
        pad = 40 + 4 * a
        r = runto(P3 + [U(a, 1)], pad=pad)
        if isinstance(r[0], str):
            print('j=%-3d a=%-4d probe %s' % (j, a, r[0])); bad += 1; continue
        out = r[0]
        # strip the new prefix U(2,1) U(4,1) and the trailing u's
        assert out[0] == U(2, 1) and out[1] == U(4, 1), fmt(out)
        got = out[2:]
        while got and got[-1] == u:
            got = got[:-1]
        exp = predict(W)
        if j == 0:
            # degenerate: U(1,1) just passes the carry on, and the two u tokens it
            # 'unfolds' into are the ones created at the far right end of the tape
            exp = []
        flag = 'OK ' if got == exp else 'MISMATCH'
        if got == exp: ok += 1
        else: bad += 1
        print('j=%-3d a=%-4d %s  W_j = %-40s  unfold = %-40s  predicted = %s'
              % (j, a, flag, fmt(W), fmt(got), fmt(exp)))
    print('ok=%d bad=%d' % (ok, bad))
