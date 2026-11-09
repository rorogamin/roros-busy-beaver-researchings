"""Cross-check: machines/*.txt and rocq/Machine*.v must encode the same table.

Parses the 5-tuple files, parses the Rocq `tbl` match, and compares both to
the Python reference table, then re-runs each machine.
"""
import glob
import re
import tm
import mk_machines as mk
import stack


def parse_txt(path):
    tbl = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            s, r, w, d, ns = line.split()
            tbl[(int(s), int(r))] = (int(w), d, None if ns == 'H' else int(ns))
    return tbl


def parse_rocq(path):
    src = open(path).read()
    body = src[src.index('Definition tbl'):src.index('(** Machine')]
    tbl = {}
    state = None
    for line in body.splitlines():
        m = re.match(r'\s*\| (\d+) => match b with', line)
        if m:
            state = int(m.group(1))
            continue
        m = re.match(r'\s*\| (bl|on) => Some \((bl|on), (true|false), (\d+)\)', line)
        if m and state is not None:
            sym = 0 if m.group(1) == 'bl' else 1
            wr = 0 if m.group(2) == 'bl' else 1
            d = 'R' if m.group(3) == 'true' else 'L'
            tbl[(state, sym)] = (wr, d, int(m.group(4)))
    return tbl


def main():
    for i, c in ((1, 8), (2, 10), (3, 12)):
        ref, n = mk.machine1(c, 2, 1)
        a = parse_txt('machines/machine_%d_omega.txt' % i)
        b = parse_rocq('rocq/Machine%d.v' % i)
        assert a == ref, ('txt mismatch', i, set(a.items()) ^ set(ref.items()))
        assert b == ref, ('rocq mismatch', i, set(b.items()) ^ set(ref.items()))
        t = tm.TM(n, a)
        steps, tape, head, state, halted = t.run(head=0, state=0, max_steps=5_000_000_000)
        print('machine_%d_omega: %d states, halts=%s, %d steps, score %d -- tables agree'
              % (i, n, halted, steps - 1, t.score(tape)))
    ref, n = stack.build([2, 2, 2, 2], 1)
    a = parse_txt('machines/machine_5_stack.txt')
    b = parse_rocq('rocq/Machine5.v')
    assert a == ref, ('txt mismatch', 5, set(a.items()) ^ set(ref.items()))
    assert b == ref, ('rocq mismatch', 5, set(b.items()) ^ set(ref.items()))
    t = tm.TM(n, a)
    steps, tape, head, state, halted = t.run(head=0, state=0, max_steps=50_000_000)
    print('machine_5_stack: %d states, halts=%s, %d steps, score %d -- tables agree'
          % (n, halted, steps - 1, t.score(tape)))


if __name__ == '__main__':
    main()
