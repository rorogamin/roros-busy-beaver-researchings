"""GlyphCalc Busy Beaver (GCBB): a tiny reference core.

This is deliberately *not* the full GlyphCalc Studio language.  It is the
small, closed subset used to make the BB-style definition executable:

  * one-letter variables, integer/string/boolean values;
  * `let`, assignment, `if`/`else`, `while`, `return`;
  * string primitives `join`, `head`, `tail`, `init`, `last`, `slice`,
    `contains`, `len`, `str`, `int`;
  * integer `+`, `-`, comparisons, and boolean `!`, `&&`, `||`.

There are no function definitions, arrays, `for`, `break`, `print`, or
single-digit steppers in this core.  Those belong in the full GlyphCalc
language; this subset is only a reproducible measuring stick.

A program halts when it executes `return`.  Runtime steps count one for
each expression node evaluated and one for each `let`, assignment, or
`return` statement.  A `while`/`if` condition is an expression; there is no
extra charge for the control node itself.  `GCBB(n)` is the maximum number
of steps of a closed program of AST size <= n that halts; `GCSigma(n)` is the
maximum length of a string returned by such a program.  Those maxima are
finite because the core grammar has finitely many programs at each size.
No value in this file is claimed to be an exact GCBB value.

Usage:
    python gcbb.py run examples/double.glyph [--limit 100000]
    python gcbb.py size examples/double.glyph
    python gcbb.py selftest
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


class GlyphError(Exception):
    """Base class for parser/evaluator errors."""


class ParseError(GlyphError):
    pass


class EvalError(GlyphError):
    pass


class StepLimit(GlyphError):
    pass


class Halt(Exception):
    def __init__(self, value: Any):
        self.value = value


# ---------------------------------------------------------------------------
# Lexer
# ---------------------------------------------------------------------------

KEYWORDS = {"let", "if", "else", "while", "return", "true", "false"}
BUILTINS = {
    "join",
    "head",
    "tail",
    "init",
    "last",
    "slice",
    "contains",
    "len",
    "str",
    "int",
}
MULTI_OPS = ("==", "!=", "<=", ">=", "&&", "||")
SINGLE_OPS = set("+-<>=!(){} ,;")


@dataclass(frozen=True)
class Token:
    kind: str  # id | int | str | op | eof
    text: str
    pos: int


def lex(src: str) -> list[Token]:
    out: list[Token] = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c.isspace():
            i += 1
            continue
        if src.startswith("//", i):
            j = src.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                if src[j] not in "01":
                    raise ParseError(
                        f"string literal at {i} must use only 0/1 glyphs"
                    )
                j += 1
            if j >= n:
                raise ParseError(f"unterminated string literal at {i}")
            out.append(Token("str", src[i + 1 : j], i))
            i = j + 1
            continue
        if c.isdigit():
            j = i + 1
            while j < n and src[j].isdigit():
                j += 1
            out.append(Token("int", src[i:j], i))
            i = j
            continue
        if c.isalpha() or c == "_":
            j = i + 1
            while j < n and (src[j].isalnum() or src[j] == "_"):
                j += 1
            word = src[i:j]
            out.append(Token("kw" if word in KEYWORDS else "id", word, i))
            i = j
            continue
        matched = next((op for op in MULTI_OPS if src.startswith(op, i)), None)
        if matched:
            out.append(Token("op", matched, i))
            i += len(matched)
            continue
        if c in SINGLE_OPS:
            out.append(Token("op", c, i))
            i += 1
            continue
        raise ParseError(f"unexpected character {c!r} at {i}")
    out.append(Token("eof", "", n))
    return out


# ---------------------------------------------------------------------------
# AST
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Lit:
    value: Any


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Call:
    name: str
    args: tuple[Any, ...]


@dataclass(frozen=True)
class Bin:
    op: str
    left: Any
    right: Any


@dataclass(frozen=True)
class Un:
    op: str
    operand: Any


@dataclass(frozen=True)
class Let:
    name: str
    expr: Any


@dataclass(frozen=True)
class Assign:
    name: str
    expr: Any


@dataclass(frozen=True)
class If:
    cond: Any
    then_body: tuple[Any, ...]
    else_body: tuple[Any, ...]


@dataclass(frozen=True)
class While:
    cond: Any
    body: tuple[Any, ...]


@dataclass(frozen=True)
class Return:
    expr: Any


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------


class Parser:
    def __init__(self, tokens: list[Token]):
        self.tokens = tokens
        self.i = 0

    @property
    def tok(self) -> Token:
        return self.tokens[self.i]

    def at(self, text: str) -> bool:
        return self.tok.text == text

    def take(self) -> Token:
        t = self.tok
        self.i += 1
        return t

    def expect(self, text: str) -> Token:
        if not self.at(text):
            raise ParseError(
                f"expected {text!r} at {self.tok.pos}, got {self.tok.text!r}"
            )
        return self.take()

    def expect_ident(self) -> str:
        t = self.tok
        if t.kind != "id":
            raise ParseError(f"expected identifier at {t.pos}, got {t.text!r}")
        self.i += 1
        if len(t.text) != 1:
            raise ParseError(
                f"core variables are one letter, got {t.text!r} at {t.pos}"
            )
        return t.text

    def parse_program(self) -> tuple[Any, ...]:
        stmts: list[Any] = []
        while self.tok.kind != "eof":
            stmts.append(self.parse_stmt())
        return tuple(stmts)

    def parse_stmt(self) -> Any:
        if self.at("let"):
            self.take()
            name = self.expect_ident()
            self.expect("=")
            expr = self.parse_expr()
            self.expect(";")
            return Let(name, expr)
        if self.at("if"):
            self.take()
            self.expect("(")
            cond = self.parse_expr()
            self.expect(")")
            then_body = self.parse_block()
            else_body: tuple[Any, ...] = ()
            if self.at("else"):
                self.take()
                if self.at("if"):
                    raise ParseError("use a block after else; else-if is not in core")
                else_body = self.parse_block()
            return If(cond, then_body, else_body)
        if self.at("while"):
            self.take()
            self.expect("(")
            cond = self.parse_expr()
            self.expect(")")
            return While(cond, self.parse_block())
        if self.at("return"):
            self.take()
            expr = self.parse_expr()
            self.expect(";")
            return Return(expr)
        if self.tok.kind == "id" and self.tokens[self.i + 1].text == "=":
            name = self.expect_ident()
            self.expect("=")
            expr = self.parse_expr()
            self.expect(";")
            return Assign(name, expr)
        raise ParseError(
            f"expected statement at {self.tok.pos}, got {self.tok.text!r}"
        )

    def parse_block(self) -> tuple[Any, ...]:
        self.expect("{")
        body: list[Any] = []
        while not self.at("}"):
            if self.tok.kind == "eof":
                raise ParseError("unterminated block")
            body.append(self.parse_stmt())
        self.expect("}")
        return tuple(body)

    # -- expressions -------------------------------------------------------
    def parse_expr(self) -> Any:
        return self.parse_or()

    def parse_or(self) -> Any:
        node = self.parse_and()
        while self.at("||"):
            op = self.take().text
            node = Bin(op, node, self.parse_and())
        return node

    def parse_and(self) -> Any:
        node = self.parse_eq()
        while self.at("&&"):
            op = self.take().text
            node = Bin(op, node, self.parse_eq())
        return node

    def parse_eq(self) -> Any:
        node = self.parse_rel()
        while self.at("==") or self.at("!="):
            op = self.take().text
            node = Bin(op, node, self.parse_rel())
        return node

    def parse_rel(self) -> Any:
        node = self.parse_add()
        while self.at("<") or self.at("<=") or self.at(">") or self.at(">="):
            op = self.take().text
            node = Bin(op, node, self.parse_add())
        return node

    def parse_add(self) -> Any:
        node = self.parse_unary()
        while self.at("+") or self.at("-"):
            op = self.take().text
            node = Bin(op, node, self.parse_unary())
        return node

    def parse_unary(self) -> Any:
        if self.at("!") or self.at("-"):
            op = self.take().text
            return Un(op, self.parse_unary())
        return self.parse_primary()

    def parse_primary(self) -> Any:
        t = self.tok
        if t.kind == "str":
            self.take()
            return Lit(t.text)
        if t.kind == "int":
            self.take()
            return Lit(int(t.text))
        if self.at("true") or self.at("false"):
            self.take()
            return Lit(t.text == "true")
        if t.kind == "id":
            self.take()
            name = t.text
            if self.at("("):
                if name not in BUILTINS:
                    raise ParseError(
                        f"unknown function {name!r} at {t.pos}; core calls are fixed builtins"
                    )
                self.take()
                args: list[Any] = []
                if not self.at(")"):
                    while True:
                        args.append(self.parse_expr())
                        if self.at(","):
                            self.take()
                            continue
                        break
                self.expect(")")
                return Call(name, tuple(args))
            if len(name) != 1:
                raise ParseError(
                    f"core variables are one letter, got {name!r} at {t.pos}"
                )
            return Var(name)
        if self.at("("):
            self.take()
            node = self.parse_expr()
            self.expect(")")
            return node
        raise ParseError(f"expected expression at {t.pos}, got {t.text!r}")


def parse(src: str) -> tuple[Any, ...]:
    return Parser(lex(src)).parse_program()


# ---------------------------------------------------------------------------
# Size metric
# ---------------------------------------------------------------------------


def size(node: Any) -> int:
    """AST size.  String-glyph characters each count one; names are one letter."""
    if isinstance(node, Lit):
        if isinstance(node.value, str):
            return 1 + len(node.value)
        if isinstance(node.value, int):
            return 1 + len(str(node.value))
        return 1
    if isinstance(node, Var):
        return 1
    if isinstance(node, Call):
        return 1 + sum(size(a) for a in node.args)
    if isinstance(node, Bin):
        return 1 + size(node.left) + size(node.right)
    if isinstance(node, Un):
        return 1 + size(node.operand)
    if isinstance(node, (Let, Assign, Return)):
        return 1 + size(node.expr)
    if isinstance(node, If):
        return (
            1
            + size(node.cond)
            + sum(size(s) for s in node.then_body)
            + sum(size(s) for s in node.else_body)
        )
    if isinstance(node, While):
        return 1 + size(node.cond) + sum(size(s) for s in node.body)
    raise TypeError(f"not an AST node: {node!r}")


def program_size(program: tuple[Any, ...]) -> int:
    return sum(size(s) for s in program)


# ---------------------------------------------------------------------------
# Evaluator
# ---------------------------------------------------------------------------


@dataclass
class Budget:
    limit: int
    steps: int = 0

    def tick(self, n: int = 1) -> None:
        if self.steps + n > self.limit:
            self.steps = self.limit
            raise StepLimit(f"step limit {self.limit} reached")
        self.steps += n


@dataclass
class RunResult:
    status: str
    steps: int
    value: Any = None
    error: str | None = None

    def as_json(self) -> str:
        value = self.value
        if isinstance(value, str):
            shown: Any = {"type": "string", "length": len(value), "value": value}
        elif isinstance(value, bool):
            shown = {"type": "bool", "value": value}
        elif isinstance(value, int):
            shown = {"type": "int", "value": value}
        else:
            shown = {"type": type(value).__name__, "value": repr(value)}
        return json.dumps(
            {
                "status": self.status,
                "steps": self.steps,
                "value": shown,
                "error": self.error,
            },
            sort_keys=True,
        )


def _require_int(v: Any, what: str) -> int:
    if isinstance(v, bool) or not isinstance(v, int):
        raise EvalError(f"{what} expects int, got {type(v).__name__}")
    if v < 0:
        raise EvalError(f"{what} expects a non-negative int, got {v}")
    return v


def _require_str(v: Any, what: str) -> str:
    if not isinstance(v, str):
        raise EvalError(f"{what} expects string, got {type(v).__name__}")
    return v


def _require_bool(v: Any, what: str) -> bool:
    if not isinstance(v, bool):
        raise EvalError(f"{what} expects bool, got {type(v).__name__}")
    return v


def call_builtin(name: str, args: tuple[Any, ...]) -> Any:
    if name == "join":
        if not args:
            raise EvalError("join expects at least one argument")
        return "".join(_require_str(a, "join") for a in args)
    if name in ("head", "tail", "init", "last"):
        if len(args) != 1:
            raise EvalError(f"{name} expects one argument")
        s = _require_str(args[0], name)
        if not s:
            return ""
        if name == "head":
            return s[0]
        if name == "tail":
            return s[1:]
        if name == "init":
            return s[:-1]
        return s[-1]
    if name == "slice":
        if len(args) != 3:
            raise EvalError("slice expects (string, start, end)")
        s = _require_str(args[0], "slice")
        start = _require_int(args[1], "slice start")
        end = _require_int(args[2], "slice end")
        if end < start:
            raise EvalError("slice end is before start")
        return s[start:end]
    if name == "contains":
        if len(args) != 2:
            raise EvalError("contains expects (string, substring)")
        return _require_str(args[1], "contains") in _require_str(args[0], "contains")
    if name == "len":
        if len(args) != 1:
            raise EvalError("len expects one argument")
        return len(_require_str(args[0], "len"))
    if name == "str":
        if len(args) != 1:
            raise EvalError("str expects one argument")
        v = args[0]
        if isinstance(v, bool):
            return "true" if v else "false"
        if isinstance(v, int):
            return str(v)
        if isinstance(v, str):
            return v
        raise EvalError(f"str cannot convert {type(v).__name__}")
    if name == "int":
        if len(args) != 1:
            raise EvalError("int expects one argument")
        s = _require_str(args[0], "int")
        if not s or not all(c.isdigit() for c in s):
            raise EvalError(f"int expects decimal digits, got {s!r}")
        return int(s)
    raise EvalError(f"unknown function or builtin {name!r}")


def eval_expr(node: Any, env: dict[str, Any], budget: Budget) -> Any:
    budget.tick()
    if isinstance(node, Lit):
        return node.value
    if isinstance(node, Var):
        if node.name not in env:
            raise EvalError(f"unbound variable {node.name!r}")
        return env[node.name]
    if isinstance(node, Call):
        vals = tuple(eval_expr(a, env, budget) for a in node.args)
        return call_builtin(node.name, vals)
    if isinstance(node, Un):
        v = eval_expr(node.operand, env, budget)
        if node.op == "!":
            return not _require_bool(v, "!")
        if node.op == "-":
            return -_require_int(v, "unary -")
        raise EvalError(f"unknown unary operator {node.op!r}")
    if isinstance(node, Bin):
        if node.op == "&&":
            left = _require_bool(eval_expr(node.left, env, budget), "&&")
            if not left:
                return False
            return _require_bool(eval_expr(node.right, env, budget), "&&")
        if node.op == "||":
            left = _require_bool(eval_expr(node.left, env, budget), "||")
            if left:
                return True
            return _require_bool(eval_expr(node.right, env, budget), "||")
        left = eval_expr(node.left, env, budget)
        right = eval_expr(node.right, env, budget)
        if node.op == "+":
            return _require_int(left, "+") + _require_int(right, "+")
        if node.op == "-":
            return _require_int(left, "-") - _require_int(right, "-")
        if node.op in ("<", "<=", ">", ">="):
            a = _require_int(left, node.op)
            b = _require_int(right, node.op)
            return {"<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b}[node.op]
        if node.op in ("==", "!="):
            if type(left) is not type(right):
                return node.op == "!="
            eq = left == right
            return eq if node.op == "==" else not eq
        raise EvalError(f"unknown binary operator {node.op!r}")
    raise EvalError(f"not an expression: {node!r}")


def exec_stmt(stmt: Any, env: dict[str, Any], budget: Budget) -> None:
    if isinstance(stmt, Let):
        env[stmt.name] = eval_expr(stmt.expr, env, budget)
        budget.tick()
        return
    if isinstance(stmt, Assign):
        if stmt.name not in env:
            raise EvalError(f"assignment to unbound variable {stmt.name!r}")
        env[stmt.name] = eval_expr(stmt.expr, env, budget)
        budget.tick()
        return
    if isinstance(stmt, Return):
        value = eval_expr(stmt.expr, env, budget)
        budget.tick()
        raise Halt(value)
    if isinstance(stmt, If):
        if _require_bool(eval_expr(stmt.cond, env, budget), "if"):
            for s in stmt.then_body:
                exec_stmt(s, env, budget)
        else:
            for s in stmt.else_body:
                exec_stmt(s, env, budget)
        return
    if isinstance(stmt, While):
        while _require_bool(eval_expr(stmt.cond, env, budget), "while"):
            for s in stmt.body:
                exec_stmt(s, env, budget)
        return
    raise EvalError(f"not a statement: {stmt!r}")


def run(program: tuple[Any, ...], limit: int = 100_000) -> RunResult:
    budget = Budget(limit)
    env: dict[str, Any] = {}
    try:
        for stmt in program:
            exec_stmt(stmt, env, budget)
    except Halt as halt:
        return RunResult("halted", budget.steps, halt.value)
    except StepLimit as exc:
        return RunResult("step-limit", budget.steps, error=str(exc))
    except EvalError as exc:
        return RunResult("error", budget.steps, error=str(exc))
    return RunResult("error", budget.steps, error="program ended without return")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _read(path: str) -> str:
    return Path(path).read_text(encoding="utf-8")


def selftest() -> int:
    cases = [
        ('return "01";', "halted", 2, "01"),
        ("return 7;", "halted", 2, 7),
        ("let x = 2; x = x + 3; return x;", "halted", 8, 5),
        (
            'let s = "1"; let i = 0; while (i < 3) { s = join(s, s); i = i + 1; } return s;',
            "halted",
            None,
            "11111111",
        ),
        ("while (true) { } return 0;", "step-limit", None, None),
        ("return z;", "error", None, None),
    ]
    for i, (src, status, steps, value) in enumerate(cases, 1):
        res = run(parse(src), limit=100)
        if res.status != status:
            print(f"selftest {i}: status {res.status!r} != {status!r}: {res.error}")
            return 1
        if steps is not None and res.steps != steps:
            print(f"selftest {i}: steps {res.steps} != {steps}")
            return 1
        if value is not None and res.value != value:
            print(f"selftest {i}: value {res.value!r} != {value!r}")
            return 1
    print("gcbb selftest: OK")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="GlyphCalc-Core GCBB reference harness")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p_run = sub.add_parser("run", help="run a .glyph core program")
    p_run.add_argument("path")
    p_run.add_argument("--limit", type=int, default=100_000)
    p_size = sub.add_parser("size", help="print AST size")
    p_size.add_argument("path")
    sub.add_parser("selftest", help="run built-in evaluator checks")
    args = ap.parse_args(argv)

    if args.cmd == "selftest":
        return selftest()
    src = _read(args.path)
    try:
        program = parse(src)
    except ParseError as exc:
        print(f"parse error: {exc}", file=sys.stderr)
        return 2
    if args.cmd == "size":
        print(program_size(program))
        return 0
    if args.cmd == "run":
        res = run(program, limit=args.limit)
        print(res.as_json())
        return 0 if res.status == "halted" else 1
    raise AssertionError(args.cmd)


if __name__ == "__main__":
    raise SystemExit(main())
