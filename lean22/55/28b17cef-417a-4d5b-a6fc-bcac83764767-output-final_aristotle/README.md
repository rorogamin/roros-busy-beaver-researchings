This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` never halts

A Lean 4 / Mathlib development proving that the Turing machine
`1RB2LA0RB4LB0LA_1LA3LA1RA4RA---`, started on the blank tape, never halts:

```lean
theorem ShiftOverflow.Counter.never_halts : ∀ n, steps n init ≠ none
```

in `RequestProject/NoHalt.lean`.  Build with `lake build`.

`PROOF.md` documents the argument, the eleven files it is spread over, and what
a translation to another proof assistant has to take care of.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
