#!/usr/bin/env python3
"""Constructive finite longitudinal rectangles for the BB(2,5) machine.

No ordinary-orbit sampling or guessed crossings are used.  The parameterized
construction implements the mutual induction in PROOF.md.  An independent
single-cell TM interpreter checks every cell of any instantiated rectangle.
This is executable proof evidence, not a Lean/Rocq kernel certification.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import time
from typing import Sequence

MACHINE = '1RB2LA3LB4LB---_0LA4LB3RA4LA0RB'
D = 'cab'
E = 'cba'
PAIR = {'a': ('A', 'B'), 'b': ('B', 'B'), 'c': ('A', 'A')}
# The table is interpreted directly; the rectangle builder never consults it.
TM = {
    ('A', 0): (1, 1, 'B'), ('A', 1): (2, -1, 'A'),
    ('A', 2): (3, -1, 'B'), ('A', 3): (4, -1, 'B'),
    ('B', 0): (0, -1, 'A'), ('B', 1): (4, -1, 'B'),
    ('B', 2): (3, 1, 'A'), ('B', 3): (4, -1, 'A'),
    ('B', 4): (0, 1, 'B'),
}

class InvalidCertificate(ValueError):
    pass

def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidCertificate(message)

@dataclass(frozen=True)
class Rectangle:
    """Cells and boundaries are ordered from right to left.

    boundary[i] is the input history of cell i; boundary[i+1] its output.
    """
    top: tuple[int, ...]
    bottom: tuple[int, ...]
    boundary: tuple[str, ...]

    def __post_init__(self) -> None:
        require(len(self.top) == len(self.bottom), 'Tape widths differ')
        require(len(self.boundary) == len(self.top) + 1, 'Bad boundary count')

    @property
    def width(self) -> int:
        return len(self.top)

    def cut(self, start: int, stop: int) -> Rectangle:
        require(0 <= start <= stop <= self.width, 'Bad spatial cut')
        return Rectangle(self.top[start:stop], self.bottom[start:stop],
                         self.boundary[start:stop+1])

    def payload(self) -> dict:
        return {'machine': MACHINE, 'orientation': 'right-to-left',
                'top': list(self.top), 'bottom': list(self.bottom),
                'boundary': list(self.boundary)}

    @staticmethod
    def load(payload: dict) -> Rectangle:
        require(payload.get('machine') == MACHINE, 'Wrong machine')
        require(payload.get('orientation') == 'right-to-left', 'Wrong orientation')
        return Rectangle(tuple(payload['top']), tuple(payload['bottom']),
                         tuple(payload['boundary']))


def spatial(*rects: Rectangle) -> Rectangle:
    require(bool(rects), 'Empty spatial composition')
    a = rects[0]
    for b in rects[1:]:
        require(a.boundary[-1] == b.boundary[0], 'Spatial histories do not match')
        a = Rectangle(a.top+b.top, a.bottom+b.bottom,
                      a.boundary+b.boundary[1:])
    return a


def temporal(*rects: Rectangle) -> Rectangle:
    require(bool(rects), 'Empty temporal composition')
    a = rects[0]
    for b in rects[1:]:
        require(a.bottom == b.top, 'Temporal tapes do not match')
        a = Rectangle(a.top, b.bottom,
                      tuple(x+y for x, y in zip(a.boundary, b.boundary)))
    return a


def uniform(width: int, top: int, bottom: int, boundary: Sequence[str]) -> Rectangle:
    return Rectangle((top,)*width, (bottom,)*width, tuple(boundary))


def reset_ones(width: int) -> Rectangle:
    # Each 1-cell accepts b, emits b, and becomes 0.
    return uniform(width, 1, 0, ['b']*(width+1))


def theta(m: int, k: int) -> str:
    return '' if m == 0 else 'a'*k + D*m


def dimensions(rank: int) -> tuple[int, int, int, int]:
    require(rank >= 1, 'Rank must be positive')
    n, d = 3**rank, 2**rank
    return n, d, n-d, d//2


@lru_cache(maxsize=None)
def prefix(rank: int) -> str:
    if rank == 1:
        return 'ab'
    _, _, old_w, _ = dimensions(rank-1)
    return echo(rank-1).boundary[old_w] + 'b' + prefix(rank-1)


def ones_wall(length: int, m: int, q: int, k: int) -> Rectangle:
    """1^length: D^m E^q -> a^length b a^k D^(m-1)c a^(2q-length+1)."""
    require(length >= 1 and length % 2 == 1, 'Wall length must be positive odd')
    h = (length-1)//2
    require(m >= 1 and q >= h and k >= 0, 'Bad wall parameters')
    boundary = [D*m + E*q]
    for j in range(h+1):
        # A first cell emits this; intermediate pairs take loop count zero.
        boundary.append('a'*(2*j+1)+'b'+('a'*k if j == h else '')
                        +D*(m-1)+'c'+'a'*(2*(q-j)))
        if j < h:
            boundary.append(E*(j+1)+D*m+E*(q-j-1))
    return uniform(length, 1, 1, boundary)


def check_shape(rect: Rectangle, width: int, right: str, left: str) -> Rectangle:
    require(rect.width == width, 'Unexpected width')
    require(rect.top == (0,)*width and rect.bottom == (1,)*width,
            'Unexpected top or bottom tape')
    require(rect.boundary[0] == right, 'Unexpected right boundary')
    require(rect.boundary[-1] == left, 'Unexpected left boundary')
    return rect


def reset(rank: int, m: int = 0, q: int = 0, k: int = 0) -> Rectangle:
    """R_r(m,q,k), valid for all nonnegative m,q,k."""
    require(min(m,q,k) >= 0, 'Negative reset parameter')
    _, d, _, M = dimensions(rank)
    P = prefix(rank)
    right = P+'bca'*m+'a'*(d+1+2*q)
    left = 'a'*k+D*(M-1+m)+'c'+'a'*(2*q+2)
    if rank == 1:
        rect = uniform(2, 0, 1,
                       (right, 'b'+D*m+E*(q+1), left))
    else:
        old = rank-1
        old_n, old_d, old_w, old_M = dimensions(old)
        Y = echo(old).cut(old_w, old_n)
        first = temporal(Y, reset_ones(old_d), reset(old, m, q+old_M, 0))
        second = reset(old, m+old_M, q, k)
        rect = spatial(first, second)
    return check_shape(rect, d, right, left)


def triangle(rank: int, m: int = 0, q: int = 0, k: int = 0) -> Rectangle:
    """T_r(m,q,k), valid for all nonnegative m,q,k."""
    require(min(m,q,k) >= 0, 'Negative triangle parameter')
    _, _, w, M = dimensions(rank)
    P = prefix(rank)
    right = 'a'+D*(M-1+m)+'c'+'a'*(w+1+2*q)
    left = P+theta(m,k)+E*q
    if rank == 1:
        rect = uniform(1, 0, 1, (right,left))
    else:
        old = rank-1
        n, _, old_w, old_M = dimensions(old)
        old_echo = echo(old)
        X = old_echo.cut(0, old_w)
        first = triangle(old, old_M+m, n-old_M+q, n)
        middle = temporal(old_echo,
                          ones_wall(n, old_M+m, n-old_M+q, 1))
        last = temporal(X, reset_ones(old_w), triangle(old,m,q,k))
        rect = spatial(first, middle, last)
    return check_shape(rect, w, right, left)


@lru_cache(maxsize=None)
def echo(rank: int) -> Rectangle:
    """Derived echo: 0^n, right P a^n, left P, bottom 1^n."""
    n, _, w, _ = dimensions(rank)
    rect = spatial(reset(rank,0,(w-1)//2,1), triangle(rank,0,0,0))
    return check_shape(rect,n,prefix(rank)+'a'*n,prefix(rank))


def check_cell(top: int, right: str, left: str, bottom: int) -> tuple[int,int]:
    """Independent direct interpretation of all completed visits to one cell.

    No seven-row macro table or rectangle-construction code is used here.
    Each left departure must consume a pair of the supplied left boundary.
    """
    require(top in range(5) and bottom in range(5), 'Bad cell symbol')
    require(all(ch in PAIR for ch in right+left), 'Bad boundary letter')
    symbol, j, steps = top, 0, 0
    for i, letter in enumerate(right):
        state, expected_exit = PAIR[letter]
        while True:
            action = TM.get((state,symbol))
            if action is None:
                raise InvalidCertificate(f'A4 halt at input {i}, output {j}')
            symbol, direction, state = action
            steps += 1
            if direction == 1:
                if state != expected_exit:
                    raise InvalidCertificate(f'Wrong right exit at input {i}')
                break
            if j >= len(left):
                raise InvalidCertificate(f'Left history exhausted at input {i}')
            entry, returned = PAIR[left[j]]
            if state != entry:
                raise InvalidCertificate(f'Wrong left departure at output {j}')
            state = returned
            j += 1
    require(j == len(left), 'Unused left boundary suffix')
    require(symbol == bottom, f'Wrong final symbol: {symbol} != {bottom}')
    return len(right), steps


def verify(rect: Rectangle) -> dict:
    visits, steps = 0, 0
    for i in range(rect.width):
        try:
            v,s = check_cell(rect.top[i],rect.boundary[i],
                             rect.boundary[i+1],rect.bottom[i])
        except InvalidCertificate as exc:
            raise InvalidCertificate(f'Column {i}: {exc}') from exc
        visits += v
        steps += s
    # This is an ordinary conditional finite execution count, not orbit time.
    encoded = json.dumps(rect.payload(), separators=(',',':')).encode()
    return {'width':rect.width, 'right_letters':len(rect.boundary[0]),
            'left_letters':len(rect.boundary[-1]), 'cell_visits':visits,
            'local_tm_steps':steps, 'sha256':hashlib.sha256(encoded).hexdigest()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, default=6)
    parser.add_argument('--kind', choices=['triangle','echo','reset'], default='triangle')
    parser.add_argument('--m', type=int, default=0)
    parser.add_argument('--q', type=int, default=0)
    parser.add_argument('--k', type=int, default=0)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path, help='Check a saved certificate instead of generating')
    args = parser.parse_args()
    started = time.monotonic()
    if args.check:
        rect = Rectangle.load(json.loads(args.check.read_text()))
    elif args.kind == 'echo':
        rect = echo(args.rank)
    elif args.kind == 'reset':
        rect = reset(args.rank,args.m,args.q,args.k)
    else:
        rect = triangle(args.rank,args.m,args.q,args.k)
    result = verify(rect)
    result.update({'machine':MACHINE, 'elapsed_seconds':round(time.monotonic()-started,3)})
    if not args.check:
        n,d,w,M = dimensions(args.rank)
        result.update({'rank':args.rank, 'kind':args.kind, 'n':n,'d':d,'w':w,
                       'prefix':prefix(args.rank)})
    if args.output:
        args.output.write_text(json.dumps(rect.payload(),separators=(',',':'))+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
