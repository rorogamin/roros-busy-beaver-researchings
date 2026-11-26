"""Turn a bbsearch row string into a 5-tuple table and run it.

bbsearch prints a machine as rows separated by '_'; each row is one state,
each cell three characters ``<write><dir><next>`` with '-' meaning "no
transition" (the machine halts there).  States are A, B, C, ... in row order.

usage:
    python found_machine.py "<rows>" <symbols> [max_steps] [out.txt]
    python found_machine.py --log <logfile> [max_steps]

With --log the last "New Best Config Found" block of a bbsearch log is used.
"""

import re
import sys


def parse_rows(rows, nsym):
    """rows: 'a_b_c...' -> {(state, sym): (write, dir, next)}; None = halt."""
    states = []
    for r in rows.split('_'):
        if len(r) != 3 * nsym:
            raise SystemExit(f'row {r!r} is not {nsym} cells of 3 chars')
        cells = []
        for i in range(nsym):
            c = r[3 * i:3 * i + 3]
            if c == '---':
                cells.append(None)
            else:
                w, d, nxt = c[0], c[1], c[2]
                cells.append((int(w), d, None if nxt == 'Z' else nxt))
        states.append(cells)
    return states


def simulate(states, max_steps):
    """Blank tape, state A, head 0.  Returns (steps, halted, score, span)."""
    tape = {}
    head, st, steps = 0, 'A', 0
    while steps < max_steps:
        idx = ord(st) - 65
        if idx < 0 or idx >= len(states):
            return steps, True, sum(1 for v in tape.values() if v), None
        cell = states[idx][tape.get(head, 0)]
        steps += 1
        if cell is None:
            return steps, True, sum(1 for v in tape.values() if v), None
        w, d, nxt = cell
        if w:
            tape[head] = w
        else:
            tape.pop(head, None)
        head += 1 if d == 'R' else -1
        if nxt is None:
            return steps, True, sum(1 for v in tape.values() if v), None
        st = nxt
    return steps, False, sum(1 for v in tape.values() if v), None


def config_at(states, target):
    """Tape after exactly `target` steps, as 'left HEAD> right'."""
    tape, head, st, steps = {}, 0, 'A', 0
    while steps < target:
        idx = ord(st) - 65
        if idx < 0 or idx >= len(states):
            return None
        cell = states[idx][tape.get(head, 0)]
        if cell is None:
            return None
        w, d, nxt = cell
        if w:
            tape[head] = w
        else:
            tape.pop(head, None)
        head += 1 if d == 'R' else -1
        if nxt is None:
            return None
        st = nxt
        steps += 1
    lo = min(list(tape) + [head])
    hi = max(list(tape) + [head])
    left = ''.join(str(tape.get(i, 0)) for i in range(lo, head))
    right = ''.join(str(tape.get(i, 0)) for i in range(head, hi + 1))
    return f'{left or "0"} {st}> {right}'


def to_txt(states, path):
    lines = []
    for i, row in enumerate(states):
        st = chr(65 + i)
        for sym, cell in enumerate(row):
            if cell is None:
                continue
            w, d, nxt = cell
            tgt = 'H' if nxt is None else str(ord(nxt) - 65)
            lines.append(f'{i} {sym} {w} {d} {tgt}')
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')
    return len(lines)


def from_log(path):
    txt = open(path).read()
    blocks = re.findall(
        r'New Best Config Found:\s*(\S.*?)\n\s*([0-9A-Z_\-]+)', txt)
    if not blocks:
        return None
    cfg, rows = blocks[-1]
    return cfg.strip(), rows.strip()


def main():
    args = sys.argv[1:]
    if not args:
        raise SystemExit(__doc__)
    if args[0] == '--log':
        got = from_log(args[1])
        if got is None:
            print('no landmark configuration found in the log')
            return
        cfg, rows = got
        nsym = 5 if len(rows.split('_')[0]) == 15 else len(rows.split('_')[0]) // 3
        print('config:', cfg)
        print('rows  :', rows)
        max_steps = int(args[2]) if len(args) > 2 else 10_000_000
        out = args[3] if len(args) > 3 else None
    else:
        rows, nsym = args[0], int(args[1])
        max_steps = int(args[2]) if len(args) > 2 else 10_000_000
        out = args[3] if len(args) > 3 else None
    states = parse_rows(rows, nsym)
    steps, halted, score, _ = simulate(states, max_steps)
    print(f'states={len(states)} symbols={nsym} '
          f'steps={steps} halted={halted} ones={score}')
    if '--at' in args:
        n = int(args[args.index('--at') + 1])
        print(f'config at step {n}: {config_at(states, n)}')
    if out:
        n = to_txt(states, out)
        print(f'wrote {out} ({n} transitions, starting state 0)')


if __name__ == '__main__':
    main()
