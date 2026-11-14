This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# `1RB2LA0RB---4LA_1LA3LA1RA4RA1LB` does not halt

Lean 4 proof (toolchain in `lean-toolchain`, no other dependencies — not even Mathlib) that
the Turing machine `1RB2LA0RB---4LA_1LA3LA1RA4RA1LB`, started in state `A` on a blank tape,
never halts:

```lean
theorem TM25.not_halts_init : ¬ Halts init
```

Build with `lake build` (about 10 seconds). `#print axioms TM25.not_halts_init` reports only
`propext`, `Classical.choice`, `Quot.sound`.

| file | contents |
|---|---|
| `RequestProject/Machine.lean` | **the statement**: transition table, `step`, `Reaches`, `Halts`, `init`; basic sweeps |
| `RequestProject/Cycles.lean` | binary counter / ternary digit encodings and the single moves of a cycle |
| `RequestProject/Macro.lean` | carry rules for cell pairs, `carryF` (many carries at once) and the verified macro step `macroStep_sound` |
| `RequestProject/NonHalt.lean` | the loop `loop_not_halts`, the concrete run (681 steps + 41 macro steps, checked by `decide +kernel`) and `not_halts_init` |

Proof outline: after 681 steps the tape is `2^13 4 | 24 21 21`; 41 verified macro steps later
it is `2^100 1 1 2^4 4 | Z` with `Z` an ordinary ternary counter.  From any configuration
`2^(2n) 1 1 2^a 4 | Z` with `n ≡ 2 (mod 6)`, one binary-counter cycle sends
`1 + (2^n-4)/6` carries rightwards; the first turns the leading `12` into a doubler `22`, all
later ones are doubled and hit either a wall `4…` or the digit `24`, which receives a multiple
of 3 carries (since `2^n ≡ 4 mod 18`) and stays `24`.  The result is
`2^(2n) 1 1 2^(a+1) 4 | Z'`, so the machine loops through this family forever.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).
