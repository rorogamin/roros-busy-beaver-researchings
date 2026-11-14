#!/usr/bin/env python3
"""Exact-integer event simulator. See RESULTS.md for the mathematical rules.

No floating-point arithmetic is used to evolve the machine. This is tested
software, not a kernel-checked certificate of the checkpoint or of nonhalting.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
import time
from overflow import (TABLE, PAIR_DIGIT, TERNARY_ENCODE, TERNARY_DECODE,
                      return_plan, drain_plan, ternary_digits)

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

class ProductiveFamilyReached(Exception):
    """An A-entry with a blank-left ternary counter and a productive suffix."""

class LeftEscapeReached(Exception):
    """B can scan only 0/2 forever to its left."""

class Machine:
    def __init__(self, cells: int = 40000):
        if cells < 100:
            raise ValueError('provide at least 100 storage cells')
        self.tape = [0] * cells
        self.origin = cells // 2
        self.p = self.lo = self.hi = self.origin
        self.q = self.t = 0
        self.counts = dict(drains=0, batches=0, returns=0, cascades=0,
                           sweeps=0, literal=0)
        self.min_a3: dict[int, dict] = {}

    def counter(self):
        i, value, power, ds = self.p - 1, 0, 1, []
        while i >= self.lo and self.tape[i] in TERNARY_DECODE:
            digit = TERNARY_DECODE[self.tape[i]]
            ds.append(digit)
            value += power * digit
            power *= 3
            i -= 1
        if i < self.lo or self.tape[i] != 1:
            return None
        return value, ds, i == self.lo

    def productive_suffix(self) -> bool:
        """Tokens 2/40/42/43/44 followed by 432 and only blank thereafter."""
        j = self.p
        while j <= self.hi:
            if (self.tape[j:j + 3] == [4, 3, 2]
                    and all(s == 0 for s in self.tape[j + 3:self.hi + 1])):
                return True
            if self.tape[j] == 2:
                j += 1
            elif self.tape[j] == 4 and self.tape[j + 1] in PAIR_DIGIT:
                j += 2
            else:
                return False
        return False

    def set_counter(self, ds: list[int]) -> None:
        for j, digit in enumerate(ds):
            self.tape[self.p - 1 - j] = TERNARY_ENCODE[digit]
        frontier = self.p - len(ds) - 1
        if frontier < 2:
            raise MemoryError('counter would exceed allocated tape')
        self.tape[frontier] = 1
        self.lo = min(self.lo, frontier)

    def note_a3(self, pos: int, dt: int = 0) -> None:
        when = self.t + dt
        bucket = (len(str(when)) - 1) // 100
        x = pos - self.origin
        if bucket not in self.min_a3 or x < self.min_a3[bucket]['x']:
            self.min_a3[bucket] = dict(t=str(when), x=x, lo=self.lo-self.origin)

    def literal(self) -> bool:
        if not 2 <= self.p < len(self.tape) - 2:
            raise MemoryError('head near allocated tape boundary')
        tr = TABLE[self.q][self.tape[self.p]]
        if tr is None:
            return False
        if self.q == 0 and self.tape[self.p] == 3:
            self.note_a3(self.p)
        symbol, delta, state = tr
        self.tape[self.p] = symbol
        self.p += delta
        self.q = state
        self.t += 1
        self.lo = min(self.lo, self.p)
        self.hi = max(self.hi, self.p)
        self.counts['literal'] += 1
        return True

    def advance(self, target: int, *, slow: bool = False) -> bool:
        if target <= self.t:
            raise ValueError('target must exceed current time')
        if slow:
            return self.literal()
        a, p, remain = self.tape, self.p, target - self.t
        if not 2 <= p < len(a) - 2:
            raise MemoryError('head near allocated tape boundary')
        if self.q == 0:
            counter = self.counter()
            if counter is not None:
                value, oldds, can_grow = counter
                if can_grow and self.productive_suffix():
                    raise ProductiveFamilyReached
                dp = drain_plan(a, p)
                if dp.end >= len(a)-2:
                    raise MemoryError('drain would exceed allocated tape')
                cap = dp.capacity
                if dp.end > p and (can_grow or value + cap < 3 ** len(oldds)):
                    newds = ternary_digits(value + cap, len(oldds))
                    extra = 2 * cap + sum(oldds) - sum(newds) + 2 * (len(newds)-len(oldds))
                    if dp.cost + extra <= remain:
                        for j, symbol in dp.edits:
                            a[j] = symbol
                        self.set_counter(newds)
                        self.p = dp.end
                        self.hi = max(self.hi, self.p)
                        self.t += dp.cost + extra
                        self.counts['drains'] += 1
                        return True
                if not can_grow:
                    cap = min(cap, 3 ** len(oldds) - 1 - value)
                # Fit a completed batch near an exact requested endpoint.
                k = cap
                for attempt in range(14):
                    if k <= 0:
                        break
                    rp = return_plan(a, p, k)
                    if rp is None:
                        raise AssertionError('capacity/return-plan disagreement')
                    newds = ternary_digits(value + k, len(oldds))
                    cost = rp.cost + 2*k + sum(oldds)-sum(newds)+2*(len(newds)-len(oldds))
                    if cost <= remain:
                        for j, symbol in rp.edits:
                            a[j] = symbol
                        self.set_counter(newds)
                        self.hi = max(self.hi, rp.end - 1)
                        self.t += cost
                        self.counts['batches'] += 1
                        return True
                    k = k * remain // cost - 1 if attempt < 8 else k // 2
            rp = return_plan(a, p)
            if rp is not None and rp.cost <= remain:
                for j, symbol in rp.edits:
                    a[j] = symbol
                self.p -= 1
                self.q = 1
                self.t += rp.cost
                self.hi = max(self.hi, rp.end - 1)
                self.lo = min(self.lo, self.p)
                self.counts['returns'] += 1
                return True
            # Literal cascade crossings grouped into one exact event.
            j, mode, cost = p, a[p + 1], 0
            max_right = p
            edits, seen_a3 = [], []
            if a[j] == 0 and mode == 0:
                edits.extend(((j, 3), (j + 1, 2)))
                j -= 1
                mode, cost = 3, 3
                max_right = p + 1
            while j >= 2:
                if a[j] == 3:
                    seen_a3.append((j, cost))
                    edits.append((j, 2))
                    j, mode, cost = j-1, 2, cost+1
                elif a[j] == 0 and mode == 2:
                    max_right = max(max_right, j + 1)
                    edits.extend(((j, 3), (j+1, 4)))
                    j, mode, cost = j-1, 3, cost+3
                elif a[j] == 2 and mode == 3:
                    max_right = max(max_right, j + 1)
                    seen_a3.extend(((j+1, cost+1), (j, cost+2)))
                    edits.extend(((j, 2), (j+1, 2)))
                    j, mode, cost = j-1, 2, cost+3
                else:
                    break
            if cost and cost <= remain:
                if j < 2:
                    raise MemoryError('cascade would exceed allocated tape')
                for pos, symbol in edits:
                    a[pos] = symbol
                for pos, dt in seen_a3:
                    self.note_a3(pos, dt)
                self.p = j
                self.t += cost
                self.lo = min(self.lo, j)
                self.hi = max(self.hi, max_right)
                self.counts['cascades'] += 1
                return True
            # Direct A sweeps; no assumptions about eventual return.
            j, edits = p, []
            while j < len(a)-2:
                if a[j] == 2:
                    edits.append((j, 3))
                    j += 1
                elif a[j] == 4 and a[j+1] in (3, 4):
                    edits.extend(((j, 2), (j+1, 4 if a[j+1] == 3 else 0)))
                    j += 2
                else:
                    break
            if j > p and j-p <= remain:
                for pos, symbol in edits:
                    a[pos] = symbol
                self.p = j
                self.t += j-p
                self.hi = max(self.hi, j)
                self.counts['sweeps'] += 1
                return True
        else:
            j = p
            while j >= self.lo and a[j] in (0, 2):
                j -= 1
            if j < self.lo:
                raise LeftEscapeReached
            if j < p and p-j <= remain:
                for pos in range(j+1, p+1):
                    a[pos] = 2 if a[pos] == 0 else 4
                self.p = j
                self.t += p-j
                self.counts['sweeps'] += 1
                return True
        return self.literal()

    def snapshot(self):
        return dict(t=str(self.t), p=self.p-self.origin, q=self.q,
                    lo=self.lo-self.origin, hi=self.hi-self.origin,
                    tape=''.join(map(str, self.tape[self.lo:self.hi+1])),
                    counts=self.counts.copy(), min_a3=self.min_a3)

    @classmethod
    def from_snapshot(cls, snap: dict, cells: int = 40000):
        m = cls(cells)
        m.p = m.origin + snap['p']
        m.q = snap['q']
        m.t = int(snap['t'])
        m.lo = m.origin + snap['lo']
        m.hi = m.origin + snap['hi']
        if not 2 <= m.lo <= m.hi < cells-2:
            raise ValueError('snapshot exceeds requested storage')
        m.tape[m.lo:m.hi+1] = list(map(int, snap['tape']))
        return m


def selftest():
    accelerated, reference = Machine(1000), Machine(1000)
    endpoints, target = 0, 10**6
    while accelerated.t < target:
        assert accelerated.advance(target)
        while reference.t < accelerated.t:
            assert reference.advance(accelerated.t, slow=True)
        assert (accelerated.p, accelerated.q, accelerated.lo, accelerated.hi, accelerated.tape) == (
            reference.p, reference.q, reference.lo, reference.hi, reference.tape)
        endpoints += 1
    return dict(status='PASS', literal_bound=target, endpoints=endpoints,
                counts=accelerated.counts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--power', type=int, default=100)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--resume', type=Path)
    parser.add_argument('--test', action='store_true')
    args = parser.parse_args()
    if args.power < 0:
        parser.error('power must be nonnegative')
    if args.test:
        print(json.dumps(selftest()), flush=True)
    cells = max(40000, 30 * args.power)
    machine = (Machine.from_snapshot(json.loads(args.resume.read_text()), cells)
               if args.resume else Machine(cells))
    target, started, events, status = 10**args.power, time.monotonic(), 0, 'REACHED_TARGET'
    if machine.t > target:
        parser.error('snapshot is later than the requested target')
    while machine.t < target:
        try:
            if not machine.advance(target):
                status = 'HALT'
                break
        except ProductiveFamilyReached:
            status = 'PRODUCTIVE_FAMILY_REACHED'
            break
        except LeftEscapeReached:
            status = 'LEFT_ESCAPE_REACHED'
            break
        events += 1
        if events % 50000 == 0:
            print(f'events={events} time_digits={len(str(machine.t))}', file=sys.stderr, flush=True)
    result = machine.snapshot()
    result.update(status=status, elapsed=time.monotonic()-started,
                  resumed_from=str(args.resume) if args.resume else None)
    if args.out:
        args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))

if __name__ == '__main__':
    main()
