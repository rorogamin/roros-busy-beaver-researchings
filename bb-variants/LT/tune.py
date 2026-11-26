"""Tuning scan: which rule change makes low-length ATS tapes run long?

Token representation matches ATS: primitives are ints 0/1, function tokens are
strings (so fn(0) is "0" and fn(1) is "1").  Length convention is ATS's:
length(primitive) = 1, length(fn(alpha)) = len(alpha).

Only the head rules are parameterised; absorption is ATS's.
"""

import itertools
import sys
from multiprocessing import Pool

CAP = 2000


def is_fn(t):
    return isinstance(t, str)


def tok_len(t):
    return 1 if not isinstance(t, str) else len(t)


def tape_len(tape):
    return sum(tok_len(t) for t in tape)


def zeros(tape):
    n = 0
    for t in tape:
        n += t.count("0") if isinstance(t, str) else (1 if t == 0 else 0)
    return n


def absorb(tape):
    j = 1
    while j < len(tape) - 1:
        if is_fn(tape[j]) and not is_fn(tape[j + 1]):
            tape[j] = str(tape[j + 1]) + tape[j]
            del tape[j + 1]
            continue
        j += 1


def run(tape0, cfg):
    copy_k, zero_add, zero_skip = cfg
    tape = list(tape0)
    steps = 0
    seen = set()
    while tape:
        if steps >= CAP or len(tape) > CAP:
            return ("cap", steps)
        # cycle detection is only worth its cost while the tape is small
        if len(tape) < 64 and steps % 8 == 0:
            key = tuple(tape)
            if key in seen:
                return ("cycle", steps)
            seen.add(key)
        absorb(tape)
        head = tape.pop(0)
        if head == 0:
            pass
        elif head == 1:
            tape.extend(tape[:copy_k])
        else:
            alpha = head
            c0 = alpha.count("0")
            c1 = alpha.count("1")
            if c1 == 0:
                pass
            elif alpha == "1":
                tape.extend(tape[:copy_k])
            else:
                idx = alpha.find("1")
                rest = alpha[:idx] + alpha[idx + 1:] if len(alpha) > 3 else alpha[1:]

                def one_rule():
                    tape.append("1")
                    if rest:
                        tape.append(rest)

                def zero_rule():
                    # variant knobs: skip some firings, and/or pay back fuel
                    if zero_skip and c0 < 2:
                        return
                    if tape:
                        tape.pop()
                    for _ in range(zero_add):
                        tape.append("1")

                if c0 == 0:
                    one_rule()
                elif c1 > c0 or (c1 == c0 and alpha[0] == "1"):
                    one_rule()
                    zero_rule()
                else:
                    zero_rule()
                    one_rule()
        steps += 1
    return ("halt", steps)


def partitions(n):
    yield (n,)
    for first in range(1, n):
        for rest in partitions(n - first):
            yield (first,) + rest


def candidates(n):
    for part in partitions(n):
        choices = []
        for k in part:
            if k == 1:
                choices.append([0, 1, "0", "1"])
            else:
                choices.append(["".join(b) for b in itertools.product("01", repeat=k)])
        for cand in itertools.product(*choices):
            yield list(cand)


def job(args):
    tape, cfg = args
    return run(tape, cfg)


def scan(n, cfgs):
    tapes = list(candidates(n))
    out = []
    for name, cfg in cfgs:
        res = [run(t, cfg) for t in tapes]
        halts = [(s, t) for (r, s), t in zip(res, tapes) if r == "halt"]
        best = max(halts, key=lambda p: p[0]) if halts else (0, [])
        out.append((name, len(halts), len(tapes), best[0], best[1]))
    return out


if __name__ == "__main__":
    cfgs = [
        ("ATS      (k=2, z=0)", (2, 0, False)),
        ("A: k=3", (3, 0, False)),
        ("B: k=2, z=1", (2, 1, False)),
        ("C: k=3, z=1", (3, 1, False)),
    ]
    for n in (3, 4):
        for name, nh, nt, best, tape in scan(n, cfgs):
            print("%-18s n=%d halters=%d/%d best=%d  %s" % (name, n, nh, nt, best, tape), flush=True)
