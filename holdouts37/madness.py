"""Hunt for the most chaotic looking machine: random 4-state machines over
'_' '1' '2', scored on how much the head moves around, how often it turns, how
unevenly it fills the tape, and how little the picture repeats itself.

Run:  python madness.py [n_machines] [steps] [outdir]
Writes the best few as Morphett text plus 1M-step pictures.
"""

import random
import sys

SYMS = ['_', '1', '2']
DIRS = 'lr'


def random_machine(rnd, states=5):
    """Random total transition table -> Morphett text with one halt rule."""
    rows = []
    for q in range(states):
        for s in SYMS:
            w = rnd.choice(SYMS)
            d = rnd.choice(DIRS)
            n = rnd.randrange(states)
            rows.append('Q%d %s %s %s Q%d' % (q, s, w, d, n))
    return '\n'.join(rows) + '\n'


def run(text, steps):
    rules = {}
    for line in text.splitlines():
        q, s, w, d, n = line.split()
        rules[(q, s)] = (w, d, n)
    tape, head, q = {}, 0, 'Q0'
    turns, last = 0, None
    lo = hi = 0
    seen = {}
    per_row = []
    for step in range(steps):
        sym = tape.get(head, '_')
        move = rules.get((q, sym))
        if move is None:
            return None
        w, d, n = move
        tape[head] = w
        if last is not None and d != last:
            turns += 1
        last = d
        head += 1 if d == 'r' else -1
        q = n
        lo, hi = min(lo, head), max(hi, head)
        if hi - lo > 12000:
            return None
        if step % 200 == 0:
            per_row.append((head, len(tape), lo, hi))
    return {'steps': steps, 'turns': turns, 'lo': lo, 'hi': hi,
            'cells': len(tape), 'rows': per_row}


def score(r):
    import math
    span = r['hi'] - r['lo'] + 1
    cells = r['cells']
    if span < 30 or span > 2500:
        return None
    heads = [h for h, _, _, _ in r['rows']]
    buckets = {}
    for h in heads:
        b = (h - r['lo']) * 16 // span
        buckets[b] = buckets.get(b, 0) + 1
    ent = -sum((c / len(heads)) * math.log2(c / len(heads)) for c in buckets.values())
    # how often the picture was far from its final extent = oscillation, caves
    final = span
    osc = sum(1 for _, _, lo, hi in r['rows'] if (hi - lo + 1) < 0.7 * final) / len(r['rows'])
    turns = r['turns'] / r['steps']
    return math.log2(span) + 4 * turns + ent + 2 * osc


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 60000
    rnd = random.Random(1234)
    best = []
    for trial in range(n):
        text = random_machine(rnd)
        r = run(text, steps)
        if not r:
            continue
        sc = score(r)
        if sc is not None:
            best.append((sc, text, r))
    best.sort(key=lambda t: -t[0])
    print('kept %d machines, top scores:' % len(best), [round(b[0], 3) for b in best[:8]])
    from sim import Session, draw
    for k, (sc, text, r) in enumerate(best[:6]):
        open('mad%d.txt' % k, 'w').write(text)
        print('--- mad%d: score %.3f turns %d span %d..%d cells %d' % (
            k, sc, r['turns'], r['lo'], r['hi'], r['cells']))
        print(text)
        s = Session(0, None, morphett=text, init='*')
        i = s.advance(1000000)
        draw(s.snapshot()).save('mad%d.png' % k)
        print('1M run: step %d cells %d span %d..%d' % (i['step'], i['ones'], i['lo'], i['hi']))


if __name__ == '__main__':
    main()
