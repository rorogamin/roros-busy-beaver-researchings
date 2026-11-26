"""Hunt for chaotic bells: machines that turn thousands of times, stay in frame,
and whose turn spacing is neither constant nor a clean ramp."""
import random

SONE = ('_', '1', '2')


def sample(rnd, states=5, sweep_bias=0.55, syms=3):
    rules = {}
    for q in range(states):
        pref = rnd.choice('lr')
        for s in range(syms):
            w = rnd.choice(('_', '1', '2'))
            d = pref if rnd.random() < sweep_bias else ('r' if pref == 'l' else 'l')
            rules['%d %s' % (q, SONE[s])] = '%s %s %d' % (w, d, rnd.randrange(states))
    return rules


def text_of(rules):
    return '\n'.join('%s %s' % (k, v) for k, v in rules.items()) + '\n'


def trace(rules, steps):
    m = {}
    for k, v in rules.items():
        q, s = k.split()
        w, d, n = v.split()
        m[(q, s)] = (w, d, n)
    tape = {0: '_', 1: '2'}
    head, q, d = 0, '0', 'r'
    turns, alive = [], True
    for step in range(steps):
        sym = tape.get(head, '_')
        if (q, sym) not in m:
            alive = False
            break
        w, nd, nq = m[(q, sym)]
        tape[head] = w
        if nd != d:
            turns.append((step, head))
            d = nd
        head += 1 if nd == 'r' else -1
        q = nq
    return opts(turns, alive, step) if False else (turns, alive, step)


def opts(turns, alive, step):
    return (turns, alive, step)


def stats(turns, alive, step, spent):
    if not alive:
        return None
    iv = [turns[i + 1][0] - turns[i][0] for i in range(len(turns) - 1)]
    if len(iv) < 120:
        return None
    lo = min(turns, key=lambda t: t[1])[1]
    hi = max(turns, key=lambda t: t[1])[1]
    span = hi - lo
    if span > 20000:
        return None
    tail = iv[40:]
    distinct = len(set(tail))
    eq = sum(1 for i in range(1, len(tail)) if tail[i] == tail[i - 1]) / float(len(tail))
    return dict(turns=len(iv), span=span, distinct=distinct,
                repeat=eq, mean=sum(tail) / len(tail),
                score=distinct + 40 * (1 - eq))
