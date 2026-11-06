"""Busy-beaver holdout workbench: bbchallenge standard format.

Standard format (2-state 5-symbol example):

    1RB---4LB1RA4RA_2LB2LA3RA4LB0RB

  * '_' separates states; block i is state A+i.
  * inside a block, one 3-char token per alphabet symbol, in symbol order:
        <write digit><L|R><next state letter>, or '---' for undefined (halt).
  * a state letter 'Z' also means halt (some writers use it).

This module parses such strings, simulates them (small runs), and compares
configurations up to translation and up to the state/symbol/direction
symmetries used in the BB literature.
"""

from __future__ import annotations

import sys


class TM:
    def __init__(self, n: int, m: int, trans: list[list[tuple[int, int, int] | None]]):
        self.n = n
        self.m = m
        # trans[state][symbol] = (write, dir(+1/-1), next state or -1)
        self.trans = trans

    # -- format ---------------------------------------------------------
    @staticmethod
    def parse(spec: str) -> "TM":
        spec = spec.strip()
        blocks = spec.split("_")
        n = len(blocks)
        if n == 0 or len(blocks[0]) % 3:
            raise ValueError(f"bad machine spec: {spec!r}")
        m = len(blocks[0]) // 3
        if any(len(b) != 3 * m for b in blocks):
            raise ValueError(f"ragged machine spec: {spec!r}")
        trans: list[list[tuple[int, int, int] | None]] = []
        for s, block in enumerate(blocks):
            row = []
            for sym in range(m):
                tok = block[3 * sym:3 * sym + 3]
                if tok == "---":
                    row.append(None)
                    continue
                w = int(tok[0])
                d = {"L": -1, "R": 1}[tok[1]]
                nxt = -1 if tok[2] in "ZH" else ord(tok[2]) - ord("A")
                if nxt < 0:
                    row.append(None)  # explicit halt token
                    continue
                if not (0 <= w < m) or nxt >= n:
                    raise ValueError(f"bad token {tok!r} in {spec!r}")
                row.append((w, d, nxt))
            trans.append(row)
        return TM(n, m, trans)

    def spec(self) -> str:
        out = []
        for s in range(self.n):
            b = []
            for sym in range(self.m):
                tr = self.trans[s][sym]
                if tr is None:
                    b.append("---")
                else:
                    w, d, nxt = tr
                    b.append(f"{w}{'R' if d > 0 else 'L'}{'Z' if nxt < 0 else chr(ord('A') + nxt)}")
            out.append("".join(b))
        return "_".join(out)

    # -- simulation -----------------------------------------------------
    def run(self, max_steps: int, tape: dict[int, int] | None = None,
            head: int = 0, state: int = 0):
        tape = dict(tape) if tape else {}
        trans = self.trans
        steps = 0
        while steps < max_steps:
            v = tape.get(head, 0)
            tr = trans[state][v]
            if tr is None:
                return RunResult(steps, True, tape, head, state)
            w, d, nxt = tr
            if w:
                tape[head] = w
            else:
                tape.pop(head, None)
            head += d
            state = nxt
            steps += 1
        return RunResult(steps, False, tape, head, state)

    def score(self, tape: dict[int, int]) -> int:
        return sum(1 for v in tape.values() if v)

    def rle(self, tape: dict[int, int], head: int, radius: int | None = None) -> str:
        if not tape:
            return f"<{tape.get(head, 0)}>" if radius is None else "[blank]"
        lo = min(tape)
        hi = max(tape)
        if radius is not None:
            lo = max(lo, head - radius)
            hi = min(hi, head + radius)
        out = []
        run_v = None
        run_n = 0
        for i in range(lo, hi + 1):
            v = tape.get(i, 0)
            mark = i == head
            if mark:
                if run_n:
                    out.append(f"{run_v}x{run_n}")
                    run_v, run_n = None, 0
                out.append(f"<{v}>")
                continue
            if v == run_v:
                run_n += 1
            else:
                if run_n:
                    out.append(f"{run_v}x{run_n}")
                run_v, run_n = v, 1
        if run_n:
            out.append(f"{run_v}x{run_n}")
        return " ".join(out)


class RunResult:
    __slots__ = ("steps", "halted", "tape", "head", "state")

    def __init__(self, steps, halted, tape, head, state):
        self.steps = steps
        self.halted = halted
        self.tape = tape
        self.head = head
        self.state = state

    def score(self):
        return sum(1 for v in self.tape.values() if v)


def load_list(path: str) -> list[str]:
    out = []
    with open(path, encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.split("#")[0].strip()
            if not line:
                continue
            # keep only machine-looking lines (a '_' and no spaces)
            if "_" in line and " " not in line:
                out.append(line)
    return out


# -- configuration comparison ------------------------------------------

def normalize_config(tape: dict[int, int], head: int):
    """Return (head_offset, tuple of symbols from leftmost to rightmost)."""
    if not tape:
        return (0, ())
    lo = min(tape)
    hi = max(tape)
    return (head - lo, tuple(tape.get(i, 0) for i in range(lo, hi + 1)))


def same_config_up_to_translation(c1, c2) -> bool:
    """c = (state, tape, head). Compare tape+head up to translation."""
    s1, t1, h1 = c1
    s2, t2, h2 = c2
    if s1 != s2:
        return False
    return normalize_config(t1, h1) == normalize_config(t2, h2)


def transform_config(state: int, tape: dict[int, int], head: int,
                     state_map: dict[int, int], sym_map: dict[int, int],
                     mirror: bool):
    """Apply state renaming, symbol renaming and (optionally) L<->R mirroring."""
    nt = {i: sym_map[v] for i, v in tape.items()}
    if mirror:
        nt = {-i: v for i, v in nt.items()}
        head = -head
    return (state_map[state], nt, head)


def _cycles(*maps):
    pass


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("spec")
    ap.add_argument("steps", nargs="?", type=int, default=1_000_000)
    ap.add_argument("--tape", action="store_true", help="print final tape RLE")
    args = ap.parse_args()
    tm = TM.parse(args.spec)
    r = tm.run(args.steps)
    print(f"n={tm.n} m={tm.m} steps={r.steps} halted={r.halted} "
          f"state={r.state} head={r.head} score={r.score()}")
    if args.tape:
        print(tm.rle(r.tape, r.head, radius=60))


if __name__ == "__main__":
    main()
