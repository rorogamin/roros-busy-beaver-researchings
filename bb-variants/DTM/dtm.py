"""Double Turing Machine (DTM) reference parser, simulator, and standard-TM reduction.

Supports uniformly:
  - DTM(n, m)       : 2 rules, each n states x m symbols
  - DTM(n, m, a)    : a rules, each n states x m symbols (active rule = t % a)
  - DTM(n, m, a, b) : 2 rules, Rule 1 has (n, m) and Rule 2 has (a, b)

Spec string syntax:
  Rules separated by '|', state blocks separated by '_', 3-char tokens <w><L|R><S>:
    - w in '0'..'9' (write symbol)
    - dir in 'L', 'R'
    - next state in 'A'.. ('Z'/'H' = halt), or '---' for undefined (halt)

Step semantics (standard Rado / BusyBeaverWiki convention):
  - Shared single state starting at A (0), head at 0, blank tape (all 0s).
  - Step t executes Rule (t % num_rules).
  - Halting transitions (<w><d>Z, <w><d>H, '---', or state/sym outside active rule)
    take +1 final step before halting.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class Transition:
    write: int
    direction: int  # -1 (L) or +1 (R)
    next_state: int  # -1 means HALT
    explicit: bool = True

    def token(self) -> str:
        if not self.explicit:
            return "---"
        dch = "R" if self.direction > 0 else "L"
        sch = "Z" if self.next_state < 0 else chr(ord("A") + self.next_state)
        return f"{self.write}{dch}{sch}"


@dataclass
class DTMRule:
    states: int
    symbols: int
    table: list[list[Optional[Transition]]]

    @staticmethod
    def parse(block_str: str) -> "DTMRule":
        blocks = block_str.strip().split("_")
        if not blocks or not blocks[0] or len(blocks[0]) % 3 != 0:
            raise ValueError(f"Malformed rule string: {block_str!r}")
        states = len(blocks)
        symbols = len(blocks[0]) // 3
        if any(len(b) != 3 * symbols for b in blocks):
            raise ValueError(f"Inconsistent state block widths in rule: {block_str!r}")
        table: list[list[Optional[Transition]]] = []
        for blk in blocks:
            row: list[Optional[Transition]] = []
            for sym in range(symbols):
                tok = blk[3 * sym : 3 * sym + 3]
                if tok == "---":
                    row.append(None)
                    continue
                if len(tok) != 3 or tok[1] not in ("L", "R"):
                    raise ValueError(f"Invalid transition token {tok!r} in {block_str!r}")
                w = int(tok[0])
                d = 1 if tok[1] == "R" else -1
                ch = tok[2]
                nxt = -1 if ch in ("Z", "H") else (ord(ch) - ord("A"))
                if nxt < -1:
                    raise ValueError(f"Invalid state char {ch!r} in {block_str!r}")
                row.append(Transition(w, d, nxt, explicit=True))
            table.append(row)
        return DTMRule(states=states, symbols=symbols, table=table)

    def spec(self) -> str:
        return "_".join(
            "".join("---" if tr is None else tr.token() for tr in row)
            for row in self.table
        )


@dataclass
class DTMResult:
    steps: int
    halted: bool
    halt_reason: str
    score: int
    nonzeros: int
    head: int
    state: int
    rule_idx: int
    min_pos: int
    max_pos: int
    tape: dict[int, int]
    history: list[dict] | None = None


class DTM:
    def __init__(self, rules: list[DTMRule]):
        if not rules:
            raise ValueError("DTM requires at least 1 rule")
        self.rules = rules

    @staticmethod
    def parse(spec: str) -> "DTM":
        parts = [p.strip() for p in spec.strip().split("|") if p.strip()]
        if not parts:
            raise ValueError(f"Empty DTM spec: {spec!r}")
        return DTM([DTMRule.parse(p) for p in parts])

    def spec(self) -> str:
        return "|".join(r.spec() for r in self.rules)

    def signature(self) -> str:
        k = len(self.rules)
        r0 = self.rules[0]
        if k == 2:
            r1 = self.rules[1]
            if r0.states == r1.states and r0.symbols == r1.symbols:
                return f"DTM({r0.states},{r0.symbols})"
            return f"DTM({r0.states},{r0.symbols},{r1.states},{r1.symbols})"
        if all(r.states == r0.states and r.symbols == r0.symbols for r in self.rules):
            return f"DTM({r0.states},{r0.symbols},{k})"
        dims = ",".join(f"{r.states}x{r.symbols}" for r in self.rules)
        return f"DTM[{dims}]"

    def to_equivalent_standard_tm(self) -> Optional[str]:
        """Convert equal-dimension DTM(n, m, k) into an equivalent (k*n, m) standard TM spec."""
        r0 = self.rules[0]
        if not all(r.states == r0.states and r.symbols == r0.symbols for r in self.rules):
            return None
        k = len(self.rules)
        n = r0.states
        if k * n > 25:  # Z/H reserved for halt
            return None
        blocks: list[str] = []
        for r_idx, rule in enumerate(self.rules):
            nxt_rule = (r_idx + 1) % k
            for s in range(n):
                toks: list[str] = []
                for sym in range(r0.symbols):
                    tr = rule.table[s][sym]
                    if tr is None:
                        toks.append("---")
                    elif tr.next_state < 0:
                        dch = "R" if tr.direction > 0 else "L"
                        toks.append(f"{tr.write}{dch}Z")
                    else:
                        dch = "R" if tr.direction > 0 else "L"
                        mapped_state = nxt_rule * n + tr.next_state
                        toks.append(f"{tr.write}{dch}{chr(ord('A') + mapped_state)}")
                blocks.append("".join(toks))
        return "_".join(blocks)

    def run(
        self,
        max_steps: int = 100000,
        record_history_limit: int = 0,
    ) -> DTMResult:
        tape: dict[int, int] = {}
        head = 0
        state = 0
        steps = 0
        min_pos = 0
        max_pos = 0
        k = len(self.rules)
        history: list[dict] | None = [] if record_history_limit > 0 else None

        while steps < max_steps:
            r_idx = steps % k
            rule = self.rules[r_idx]
            sym = tape.get(head, 0)

            if state >= rule.states or sym >= rule.symbols:
                steps += 1
                reason = (
                    f"Halted: state {chr(ord('A') + state)} out of range for Rule {r_idx + 1}"
                    if state >= rule.states
                    else f"Halted: symbol {sym} out of range for Rule {r_idx + 1}"
                )
                return self._make_result(steps, True, reason, head, -1, r_idx, min_pos, max_pos, tape, history)

            tr = rule.table[state][sym]
            if tr is None:
                steps += 1
                return self._make_result(
                    steps, True,
                    f"Halted on undefined --- (Rule {r_idx + 1}, {chr(ord('A') + state)}{sym})",
                    head, -1, r_idx, min_pos, max_pos, tape, history,
                )

            old_head = head
            if tr.write:
                tape[head] = tr.write
            else:
                tape.pop(head, None)
            if head < min_pos:
                min_pos = head
            if head > max_pos:
                max_pos = head

            head += tr.direction
            if head < min_pos:
                min_pos = head
            if head > max_pos:
                max_pos = head

            steps += 1
            if history is not None and len(history) < record_history_limit:
                history.append({
                    "step": steps,
                    "rule": r_idx,
                    "state": state,
                    "read": sym,
                    "write": tr.write,
                    "dir": tr.direction,
                    "next_state": tr.next_state,
                    "pos": old_head,
                    "next_pos": head,
                })

            if tr.next_state < 0:
                return self._make_result(
                    steps, True,
                    f"Halted cleanly via {tr.token()} (Rule {r_idx + 1}, {chr(ord('A') + state)}{sym})",
                    head, -1, r_idx, min_pos, max_pos, tape, history,
                )
            state = tr.next_state

        return self._make_result(
            steps, False, f"Step limit reached ({max_steps:,})",
            head, state, steps % k, min_pos, max_pos, tape, history,
        )

    @staticmethod
    def _make_result(steps, halted, reason, head, state, rule_idx, min_pos, max_pos, tape, history):
        nonzeros = sum(1 for v in tape.values() if v)
        ones = sum(1 for v in tape.values() if v == 1)
        return DTMResult(
            steps=steps,
            halted=halted,
            halt_reason=reason,
            score=nonzeros,
            nonzeros=ones,
            head=head,
            state=state,
            rule_idx=rule_idx,
            min_pos=min_pos,
            max_pos=max_pos,
            tape=tape,
            history=history,
        )
