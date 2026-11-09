"""Minimal 2-symbol Turing machine simulator for 5-tuple transition tables.

Table format (one transition per line):
    <state> <symbol> <new_symbol> <direction> <next_state>
symbols are 0/1, direction L/R, next_state is an integer or H.
A line starting with '#' is a comment.  Blank lines ignored.
"""

import sys
from collections import defaultdict


class TM:
    def __init__(self, n_states, table):
        # table: dict[(state, sym)] -> (new_sym, dir, next_state or None)
        self.n = n_states
        self.t = table

    def step(self, tape, head, state):
        k = (state, tape.get(head, 0))
        if k not in self.t:
            return None
        ns, d, nxt = self.t[k]
        tape[head] = ns
        head += 1 if d == 'R' else -1
        return head, nxt

    def run(self, head=0, state=0, tape=None, max_steps=10_000_000):
        tape = dict(tape) if tape else {}
        steps = 0
        while steps < max_steps:
            r = self.step(tape, head, state)
            steps += 1
            if r is None:
                return steps, tape, head, state, True
            head, state = r
        return steps, tape, head, state, False

    def score(self, tape):
        return sum(1 for v in tape.values() if v == 1)


def parse_table(text):
    table = {}
    max_state = 0
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.split('#')[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 5:
            raise ValueError(f'line {lineno}: expected 5 fields, got {len(parts)}: {raw!r}')
        s, rs, ws, d, ns = parts
        s, rs, ws = int(s), int(rs), int(ws)
        d = d.upper()
        if d not in ('L', 'R'):
            raise ValueError(f'line {lineno}: bad direction {d!r}')
        nxt = None if ns.upper() in ('H', 'Z', '---') else int(ns)
        table[(s, rs)] = (ws, d, nxt)
        max_state = max(max_state, s, -1 if nxt is None else nxt)
    return TM(max_state + 1, table)


def tape_str(tape, head, pad=3):
    if not tape:
        return '[%d]' % pad
    lo = min(min(tape), head) - pad
    hi = max(max(tape), head) + pad
    out = []
    for i in range(lo, hi + 1):
        v = tape.get(i, 0)
        out.append('<' + str(v) + '>' if i == head else str(v))
    return ''.join(out)


def block(lo, hi):
    """tape dict with ones on [lo,hi] inclusive"""
    return {i: 1 for i in range(lo, hi + 1)}


def load(path):
    with open(path) as f:
        return parse_table(f.read())


if __name__ == '__main__':
    path = sys.argv[1]
    max_steps = int(sys.argv[2]) if len(sys.argv) > 2 else 10_000_000
    m = load(path)
    steps, tape, head, state, halted = m.run(max_steps=max_steps)
    print(f'states={m.n} steps={steps} halted={halted} state={state} head={head} score={m.score(tape)}')
    print(tape_str(tape, head))
