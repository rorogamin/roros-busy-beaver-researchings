#!/usr/bin/env python3
"""Turnaround-level analysis for 2-state TMs, with a stack/suffix test.

For the BB(2,5) holdout 1RB2LA1LA4RA2LA_0LA3RB3LB2RB--- the local rules make
each pass a deterministic sweep:

  A sweeps left : 1->2, 2->1, 4->2, turns right on 3 (writing 4) or on blank 0
  B sweeps right: 1->3, 3->2, turns left on 2 (writing 3) or on blank 0,
                  and HALTs on 4

So the machine is a billiard between two ends, and the interesting state is the
tape word at the moment the head sits on the leftmost cell in state A ("L
event").  If word[n+k] = prefix + word[n] for a short prefix, the machine is a
stack builder and its dynamics reduce to the prefix sequence.

Usage:
  python sweep25.py "<spec>" [steps] [--l-events N] [--check-k K]
"""
import sys
from collections import Counter


def parse(spec):
    rows = spec.split('_')
    table = {}
    for st, row in enumerate(rows):
        i = 0
        sym = 0
        while i < len(row):
            if row[i:i + 3] == '---':
                i += 3
                sym += 1
                continue
            chunk = row[i:i + 3]
            if len(chunk) == 3 and chunk[0].isdigit() and chunk[1] in 'RL' and chunk[2].isalpha():
                table[(st, sym)] = (int(chunk[0]), 1 if chunk[1] == 'R' else -1, ord(chunk[2]) - 65)
                i += 3
                sym += 1
            else:
                raise ValueError(f"bad chunk {row[i:i+3]!r} in {row!r}")
    return table


def runs_of(tape, lmin, rmax):
    out = []
    cur = None
    cnt = 0
    for p in range(lmin, rmax + 1):
        s = tape.get(p, 0)
        if s == cur:
            cnt += 1
        else:
            if cur is not None:
                out.append((cur, cnt))
            cur, cnt = s, 1
    out.append((cur, cnt))
    return out


def fmt(runs, cap=10):
    if len(runs) <= 2 * cap:
        return ' '.join(f'{s}^{n}' for s, n in runs)
    return (' '.join(f'{s}^{n}' for s, n in runs[:cap]) + ' ... ' +
            ' '.join(f'{s}^{n}' for s, n in runs[-cap:]))


def ends_with(word, suffix):
    if len(suffix) > len(word):
        return False
    return word[len(word) - len(suffix):] == suffix


def main():
    args = sys.argv[1:]
    spec = args[0]
    limit = 200_000
    n_l = 40
    check_k = 4
    k = 1
    while k < len(args):
        if args[k] == '--l-events':
            n_l = int(args[k + 1]); k += 2
        elif args[k] == '--check-k':
            check_k = int(args[k + 1]); k += 2
        else:
            limit = int(args[k]); k += 1

    t = parse(spec)
    tape = {}
    head, st = 0, 0
    lmin = rmax = 0
    prev_dir = 0
    turns = Counter()
    l_events = []
    steps = 0
    for step in range(1, limit + 1):
        steps = step
        key = (st, tape.get(head, 0))
        if key not in t:
            print(f"HALT step={step} state={chr(65+st)} head={head} sym={tape.get(head,0)}")
            break
        w, mv, ns = t[key]
        tape[head] = w
        head += mv
        st = ns
        if head < lmin or head > rmax:
            lmin = min(lmin, head); rmax = max(rmax, head)
        if prev_dir and mv != prev_dir:
            turns[(chr(65+ns), key[1], w)] += 1
        prev_dir = mv
        if st == 0 and head == lmin:
            l_events.append((step, runs_of(tape, lmin, rmax)))

    print(f"steps={steps} turns={sum(turns.values())} l_events={len(l_events)} span={rmax-lmin+1}")
    print("turnaround kinds (state_after, symbol_read, symbol_written):")
    for kind, c in turns.most_common():
        print(f"  {kind}: {c}")

    print(f"\nfirst {n_l} L events:")
    for i, (step, runs) in enumerate(l_events[:n_l]):
        print(f"  L{i:>4} step={step:>9} runs={fmt(runs)}")

    print(f"\nsuffix test: word[n] ends with word[n-{check_k}]?")
    ok = 0
    tested = 0
    for n in range(check_k, len(l_events)):
        tested += 1
        a = l_events[n - check_k][1]
        b = l_events[n][1]
        if ends_with(b, a):
            ok += 1
            prefix = b[:len(b) - len(a)]
            if n < 400 or n % 200 == 0:
                print(f"  n={n:>5} step={l_events[n][0]:>9} PREFIX={fmt(prefix, 6)} (len {len(b)-len(a)} runs)")
        elif n < 60:
            print(f"  n={n:>5} no: A={fmt(a,4)} B={fmt(b,4)}")
    print(f"  suffix holds {ok}/{tested} for k={check_k}")


if __name__ == '__main__':
    main()
