#!/usr/bin/env python3
"""Run-level macro analysis for a small TM.

Runs the machine from the blank tape and records one event per visit to a
brand-new tape extreme (the natural macro decomposition for a 2-state machine:
each event is a "crossing").  Events are printed with the run-length encoding
of the whole tape, truncated to the two ends, plus a diff against earlier
events of the same side.  The diff is what reveals a macro rule: if the
differing window stays short while the span grows, the machine is a bouncer
with a countable parameter.

Usage:
  python macro25.py "<spec>" [steps] [--pairs K] [--max-events N]
"""
import sys
from collections import OrderedDict


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
                raise ValueError(f"bad chunk in {row!r} at {i}: {row[i:i+3]!r}")
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


def fmt(runs, cap=9):
    if len(runs) <= 2 * cap:
        return ' '.join(f'{s}^{n}' for s, n in runs)
    head = ' '.join(f'{s}^{n}' for s, n in runs[:cap])
    tail = ' '.join(f'{s}^{n}' for s, n in runs[-cap:])
    return f'{head} ... [{len(runs)-2*cap} runs] ... {tail}'


def diff_runs(a, b):
    """First/last differing run index and the two differing windows."""
    n = min(len(a), len(b))
    i = 0
    while i < n and a[i] == b[i]:
        i += 1
    j = 0
    while j < n - i and a[len(a) - 1 - j] == b[len(b) - 1 - j]:
        j += 1
    return i, len(a) - j, len(b) - j


def main():
    args = [a for a in sys.argv[1:]]
    spec = args[0]
    limit = 200_000
    pairs = 1
    max_events = 60
    rest = args[1:]
    k = 0
    while k < len(rest):
        if rest[k] == '--pairs':
            pairs = int(rest[k + 1]); k += 2
        elif rest[k] == '--max-events':
            max_events = int(rest[k + 1]); k += 2
        else:
            limit = int(rest[k]); k += 1

    t = parse(spec)
    tape = {}
    head, st = 0, 0
    lmin = rmax = 0
    events = []
    for step in range(1, limit + 1):
        key = (st, tape.get(head, 0))
        if key not in t:
            print(f"HALT step={step} state={chr(65+st)} head={head} span={rmax-lmin+1}")
            return
        w, mv, ns = t[key]
        tape[head] = w
        head += mv
        st = ns
        if head < lmin or head > rmax:
            side = 'L' if head < lmin else 'R'
            lmin = min(lmin, head); rmax = max(rmax, head)
            events.append({'step': step, 'side': side, 'head': head, 'lmin': lmin,
                           'rmax': rmax, 'state': st,
                           'runs': runs_of(tape, lmin, rmax)})

    print(f"spec={spec} steps={limit} events={len(events)} span={rmax-lmin+1}")
    print(f"left={lmin} right={rmax} head={head} state={chr(65+st)}")
    shown = 0
    for idx, ev in enumerate(events):
        if shown >= max_events:
            break
        line = (f"ev={idx:>5} step={ev['step']:>10} {ev['side']} head={ev['head']:>8} "
                f"span={ev['rmax']-ev['lmin']+1:>7} st={chr(65+ev['state'])} "
                f"runs={fmt(ev['runs'])}")
        print(line)
        shown += 1
        # diff against the event K periods back on the same side
        prev = [e for e in events[:idx] if e['side'] == ev['side']]
        if len(prev) >= pairs:
            base = prev[-pairs]
            i, ja, jb = diff_runs(base['runs'], ev['runs'])
            print(f"      vs ev {idx - 2*pairs if idx-2*pairs>=0 else '?'} (same side, -{pairs}): "
                  f"span {base['rmax']-base['lmin']+1}->{ev['rmax']-ev['lmin']+1} "
                  f"runs {len(base['runs'])}->{len(ev['runs'])} diffs at [{i}:{ja}] vs [{i}:{jb}]")
            print(f"      window A: {fmt(base['runs'][i:ja], 5)}")
            print(f"      window B: {fmt(ev['runs'][i:jb], 5)}")


if __name__ == '__main__':
    main()
