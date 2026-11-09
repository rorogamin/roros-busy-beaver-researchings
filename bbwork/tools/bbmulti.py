"""Run the multi-symbol machines posted with loader3229's level claims.

Format, as in the claims:

    A_1RZ3RB1LC2RA3RD1RC_3RB...     `_` separates the states, in order A, B, C, ...
                                    each state lists one 3-char action per read
                                    symbol, starting at the blank (0)
    <write><dir><next>              write in 0..5, dir in LR, next a state or Z
    ---                             no transition (halt)

So the number of symbols is block length / 3 and the number of states is the
number of blocks.  A machine is blank-tape: start in A on an all-blank tape.

`probe` runs with a step budget and records the score (marks on the tape) at
geometric step counts, because none of these claims can be run to halting: the
BB(4,6) claim alone is a tower of f_(w+1) applications.  What can be measured is
(i) that it does not halt, (ii) how fast the tape grows, and (iii) which states
and symbols the run actually touches -- the last is the interesting one for a
2-symbol search, because a machine that only ever writes 0..3 is not really using
its 6 symbols.
"""

import sys


def parse(text, names=None):
    blocks = text.strip().split('_')
    letters = 'ABCDEFGHIJKLMNOPQRSTUVWXY'
    table = {}
    nsym = None
    for si, blk in enumerate(blocks):
        state = letters[si]
        acts = [blk[i:i + 3] for i in range(0, len(blk), 3)]
        if nsym is None:
            nsym = len(acts)
        if len(acts) != nsym:
            raise ValueError(f'state {state}: {len(acts)} actions, expected {nsym}')
        for sym, a in enumerate(acts):
            if a == '---':
                continue
            w, d, nxt = a[0], a[1], a[2]
            if w == '-':
                continue
            table[(state, sym)] = (int(w), d, None if nxt == 'Z' else nxt)
    return table, len(blocks), nsym


def run(table, max_steps=2_000_000, marks=(), tape=None, head=0, state='A'):
    """Blank-tape run.  Returns steps, halted, score, used states, used symbols."""
    tape = dict(tape or {})
    score = sum(1 for v in tape.values() if v)
    steps = 0
    st = state
    log = []
    used_states = set()
    used_write = set()
    while steps < max_steps:
        a = table.get((st, tape.get(head, 0)))
        used_states.add(st)
        if a is None:
            return steps, True, score, used_states, used_write, log
        w, d, nxt = a
        used_write.add(w)
        if tape.get(head, 0) == 0 and w:
            score += 1
        elif tape.get(head, 0) and w == 0:
            score -= 1
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        st = nxt
        for m in marks:
            if score >= m and (not log or log[-1][0] < m):
                log.append((m, steps))
    return steps, False, score, used_states, used_write, log


MACHINES = [
    ('BB(4,6)  f_(w+1)',
     '3LD3LB5LD2RA4LB3RD_1RZ3RB1LC2RA3RD1RC_3RB1LB3LC2RC4LC0LA_3RB1RC5LC4LD4LC4LD'),
    ('BB(4,6)  f_(w+2)',
     '5LD3LB5LC2RA4LB4LC_1RZ3RB1LC2RA3RD0LA_3RB1LB3LC2RC4LC1RA_3RB0LA2LC4LD4LC4LD'),
    ('BB(5,6)  f_(w+3)',
     '1LE3LB2LA2RA4LB5RA_1RZ3RB1LC2RA3RD4RA_3RB1LB3LC2RC4LC2LB_3RB0LA5LE4LD4LC4LD_4LC5LC0RE5LE1RE2RE'),
    ('BB(6,6)  f_(w*2)',
     '4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB'),
    ('BB(7,6)  f_(w^2)',
     '2LG3LB1RZ2RA4LB---_4LG3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC---3RD_5RB3RE---4LC3LG5LE_5RB5RB---1LF---5LF_5LF---1LC1LG---5LG'),
    ('BB(7,6)  f_(w^2)(28)',
     '2LF3LB1RZ2RA4LB3LD_3LA3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC---3RD_5RB3RE---4LC3LG5LE_5RB5RB0LF1LF---5LF_5LF------1LG---5LG'),
]

BUDGET = 2_000_000
MARKS = (10, 100, 1000, 10_000, 100_000, 1_000_000)


def main():
    print(f'multi-symbol level claims, blank tape, budget {BUDGET:,} steps')
    for name, text in MACHINES:
        table, nst, nsym = parse(text)
        steps, halted, score, used_st, used_w, log = run(table, BUDGET, MARKS)
        print(f'\n{name}   {nst} states x {nsym} symbols, {len(table)} transitions')
        print(f'  halted={halted} after {steps:,} steps, score={score:,}')
        print(f'  states used: {len(used_st)}/{nst}   '
              f'symbols written: {sorted(used_w)}')
        if log:
            print('  score milestones: ' +
                  ', '.join(f'{m:,}@{s:,}' for m, s in log))
        missing = [(st, sym) for st in 'ABCDEFG'[:nst] for sym in range(nsym)
                   if (st, sym) not in table]
        if missing:
            print(f'  undefined transitions: {len(missing)}')


if __name__ == '__main__':
    main()
