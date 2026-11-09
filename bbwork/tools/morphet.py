"""Morphet-syntax Turing machine loader (2 symbols, labels, stay-put moves).

Syntax (from limbms.txt):
    <label> <read> <write> <dir> <next> [ ! ]
    read/write:  `_` = blank (0), `1` = mark (1)
    dir:         `r` = right, `l` = left, `*` = stay (no move)
    next:        a label, or `halt`
    `!` and everything after `;` is a comment/breakpoint marker

Blank-tape entry is state `0` (an alias row) or whichever label is given.
"""

import sys


def parse(path):
    rows = {}
    labels = set()
    with open(path, encoding='utf-8', errors='replace') as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.split(';')[0].strip()
            if not line:
                continue
            line = line.rstrip('!').strip()
            parts = line.split()
            if len(parts) != 5:
                raise ValueError(f'line {lineno}: expected 5 fields, got {parts!r}')
            lab, rd, wr, d, nxt = parts
            # `*` in the read field means "either symbol"; in the write field it
            # means "keep what is there" (only the uncounted alias row uses it)
            syms = (0, 1) if rd == '*' else ({'_': 0, '1': 1}[rd],)
            d = {'r': 'R', 'l': 'L', '*': 'S'}[d.lower()]
            for sym in syms:
                w = sym if wr == '*' else {'_': 0, '1': 1}[wr]
                if (lab, sym) in rows:
                    raise ValueError(f'line {lineno}: duplicate row {lab} {rd}')
                rows[(lab, sym)] = (w, d, None if nxt.lower() in ('halt', 'z', 'h') else nxt)
            labels.add(lab)
            if nxt.lower() not in ('halt', 'z', 'h'):
                labels.add(nxt)
    return rows, labels


def step(rows, tape, head, state):
    k = (state, tape.get(head, 0))
    if k not in rows:
        return None
    w, d, nxt = rows[k]
    tape[head] = w
    if d == 'R':
        head += 1
    elif d == 'L':
        head -= 1
    return head, nxt


def run(rows, max_steps=1_000_000, state='0', head=0, tape=None):
    tape = dict(tape) if tape else {}
    steps = 0
    while steps < max_steps:
        r = step(rows, tape, head, state)
        steps += 1
        if r is None:
            return steps, tape, head, state, True
        head, state = r
    return steps, tape, head, state, False


def score(tape):
    return sum(1 for v in tape.values() if v == 1)


if __name__ == '__main__':
    path = sys.argv[1] if len(sys.argv) > 1 else 'limbms.txt'
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 1_000_000
    rows, labels = parse(path)
    counted = len(labels - {'0'})
    print(f'{path}: {counted} states (excluding the uncounted alias 0), {len(rows)} rows')
    missing = [(l, s) for l in sorted(labels) for s in (0, 1) if (l, s) not in rows]
    print(f'undefined (state, symbol) pairs: {len(missing)}')
    if missing:
        print('  ', ', '.join(f'{l}{s}' for l, s in missing[:20]),
              '...' if len(missing) > 20 else '')
    mods = {}
    for (l, _s) in rows:
        key = l[0]
        mods[key] = mods.get(key, 0) + 1
    print('rows per module:', ' '.join(f'{k}:{v}' for k, v in sorted(mods.items())))
    steps, tape, head, state, halted = run(rows, max_steps=cap)
    print(f'run {steps} steps: halted={halted} state={state} head={head} '
          f'ones={score(tape)} cells={len(tape)}')
