# GlyphCalc Busy Beaver (GCBB)

A **proposal** for a language-level Busy Beaver variant built on GlyphCalc, the
string-native esolang described by the supplied *GlyphCalc Language Manual &
Reference Guide*.  This is a BB-adjacent function over programs, **not** a
Turing-machine champion and not a replacement for `BB(n)`.

The key idea is to take the manual's native representation seriously: numbers
are glyph strings, `join`/`head`/`tail`/`slice` are the arithmetic, and control
flow is ordinary `while`/`if`/`return`.  A closed program is then a candidate
for a Busy-Beaver-style runtime and output-size function.

## The core measured here

`gcbb.py` implements a deliberately small, closed **GlyphCalc-Core**:

- one-letter variables; string, non-negative integer, and boolean values;
- `let`, assignment, `if`/`else`, `while`, `return`;
- `join`, `head`, `tail`, `init`, `last`, `slice`, `contains`, `len`, `str`,
  `int`;
- `+`, `-`, comparisons, `!`, `&&`, `||`.

It does **not** implement functions/recursion, arrays, `for`, `break`, `print`,
or `step_add`/`step_sub`.  Those are part of the full GlyphCalc language; the
core is only a reproducible measuring stick.

## Size and steps

A program is an AST with these size conventions:

- a string literal contributes one node plus one per glyph (`"101"` is 4);
- an integer literal contributes one plus its decimal digit count;
- a variable is one node; variables are one letter;
- each operator, call, `let`, assignment, `if`, `while`, and `return` is one
  node; bodies are their statement nodes.

This makes the set of programs at each size finite: string literals are over
`0`/`1`, variable names are one letter, the call vocabulary is the fixed
builtin set, and integer literals have finite digit counts at fixed size.

A program **halts** when it executes `return`.  Runtime steps count:

- one for each expression node evaluated;
- one for each `let`, assignment, or `return` statement.

A `while`/`if` condition is an expression; there is no extra charge for the
control node.  Type errors, an unbound variable, a program that falls off the
end, and a harness step-limit are **not** halts.

## The BB-style functions

For `n >= 0`, define

```text
GCBB(n) = max { steps(P) : P is a closed GlyphCalc-Core program,
                            |P| <= n, and P halts }

GCSigma(n) = max { len(P()) : P is a closed GlyphCalc-Core program,
                             |P| <= n, and P halts with a string }
```

`GCBB` counts all halting programs; `GCSigma` counts only string results.  Both
maxima are finite because there are finitely many programs of size at most `n`
and each halting run has finite length.  No exact `GCBB(n)` or `GCSigma(n)` is
claimed here; the examples below are one-program lower bounds.

The core's halting problem is not proved undecidable in this note.  In
particular, do **not** read `GCBB` as a proved uncomputable function until the
core's Turing-completeness (or a reduction) is established.  The definition is
BB-shaped; the metamathematics is open.

## Measured witnesses

Run from this directory:

```text
python gcbb.py selftest
python gcbb.py run examples/double.glyph
python gcbb.py size examples/double.glyph
```

| program | size | steps | result | consequence |
|---|---:|---:|---|---|
| `examples/countdown.glyph` | 16 | 71 | `"0"` | `GCBB(16) >= 71`, `GCSigma(16) >= 1` |
| `examples/double.glyph` | 22 | 64 | 32 glyphs | `GCBB(22) >= 64`, `GCSigma(22) >= 32` |
| `examples/nested.glyph` | 42 | 4,652 | `"400"` | `GCBB(42) >= 4,652`, `GCSigma(42) >= 3` |

These are measured by the local harness on 2026-11-11 and are lower bounds, not
`GCBB` values: a larger program of the same size may do more.

### A linear-size family with exponential output

For `k >= 1`, the program

```glyph
let s = "1";
let i = 0;
while (i < k) {
    s = join(s, s);
    i = i + 1;
}
return s;
```

has size `21 + digits(k)`, runs `11k + 9` steps, and returns `2^k` glyphs.
Therefore

```text
GCSigma(21 + digits(k)) >= 2^k
GCBB(21 + digits(k))    >= 11k + 9
```

This is the cleanest small growth witness in the core.  It uses `join` as one
step even though the returned string doubles; output size, not string work, is
what `GCSigma` measures.

## Files

- `gcbb.py` — reference lexer, parser, evaluator, step counter, size metric,
  and self-tests.
- `examples/` — the three witness programs above.
- `DISCORD_POST.md` — local-only BBChallenge Discord draft.  It is listed in
  `bbwork/.gitignore`; do not commit it.

## Status

No champions, no exact values, no Rocq proof, and no claim that this is the
official GlyphCalc BB variant.  It is a concrete proposal with a runnable
reference harness and explicit lower bounds.
