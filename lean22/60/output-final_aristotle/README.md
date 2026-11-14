This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Non-halting of the BB(2,5) machine `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`

Main theorem (`RequestProject/NonHalting.lean`):

```lean
theorem BB25.never_halts : ∀ n : Nat, ¬ Halted (run n)
```

* Plain Lean 4 (`v4.28.0`), **no Mathlib and no other dependencies**. `lake build` takes a few seconds.
* Only core tactics are used: `omega`, `simp`, `rw`, `induction`/`cases`, `funext`, `rfl`.
* `#print axioms BB25.never_halts` gives `[propext, Quot.sound]`: no `Classical.choice`, no
  `sorry`. `Quot.sound` comes in through function extensionality on tapes (`Int → Sym`).

## Files (in dependency order, ~1200 lines total)

| File | Contents |
|---|---|
| `Machine.lean` | **Trusted spec**: states, symbols (`Fin 5`), `step`, `init`, `run`, `Halted`. |
| `Rect.lean` | Letters `a=(A→B)`, `b=(B→B)`, `c=(A→A)`; the non-halting table `tr`; the inductive predicates `Visit`, `Cell`, `Rect`; how rectangles compose in time and space and how they are cut; words `pw`, `A k = a^k`, `D=cab`, `E=cba`, `F=bca`; the single-cell table. |
| `Fractal.lean` | `Z ℓ R L` (rectangle turning `0^ℓ` into `1^ℓ`), the all-ones lemmas, the odd wall, `Good d w M P` (reset + triangle families), `good_base`, `echo`, `good_step`, `all_ranks`. |
| `Oracle.lean` | `iter` (with notation `f^[n]`), the oracle machine `ostep lo`, agreement of `step` with `tr`, tape windows `Holds`/`wl`, and `rect_sound`: every `Rect` is actually executed. |
| `Driver.lean` | Right half of the tape `(042)^m`: `rule1`, `rule2`, `rule3`. |
| `NonHalting.lean` | `driver_inv` and the final theorem `never_halts`. |

## The argument

1. **Rectangles.** A *letter* records one visit of the head to the region left of a cell:
   entered from the right in state `X`, left to the right in state `Y`. `Rect S R L T` says:
   a window carrying `S` (cells listed right to left), visited from the right according to the
   word `R`, makes the excursions `L` beyond its left end and ends up carrying `T`.
   Rectangles compose side by side (`Rect.space`) and one after another (`Rect.append`),
   and can be cut in both directions (`Rect.cut`, `Rect.split`).
2. **All-rank induction** (`Fractal.lean`). `Good d w M P` states that for all `m q k`:
   * reset: `Z d (P F^m a^(d+1+2q)) (a^k D^(M-1+m) c a^(2q+2))`,
   * triangle: `Z w (a D^(M-1+m) c a^(w+1+2q)) (P θ(m,k) E^q)`, where `θ(0,k) = []` and
     `θ(m,k) = a^k D^m` otherwise.

   Base: `Good 2 1 1 [a,b]`. Step: `Good d w M P → Good (2d) (3w+d) (2M) (H ++ [b] ++ P)`.
   Here `H` is the middle boundary obtained by cutting the *echo* rectangle
   `Z (d+w) (P a^(d+w)) P` after its first `w` cells. So `w` and `M` are unbounded (`all_ranks`).
3. **Soundness** (`Oracle.lean`). `ostep lo` is the real machine, except that on reaching cell
   `lo - 1` it takes the return state from an oracle list of letters. `rect_sound`: a rectangle
   `Rect S [r] L T` really is executed by this machine and uses up exactly `L` of the oracle list.
4. **Driver** (`Driver.lean`). Right of cell `0`, the blank tape builds `(042)^j`. It answers
   the window's exits so that the window sees exactly `a (cab)^(M-1) …`.
5. **Assembly** (`NonHalting.lean`). Suppose the machine halts at time `h`. Take a rank with
   `w, M > h` and window `[1-w, 0]`. The head moves at most one cell per step, so it cannot
   reach cell `-w` before time `w`. Up to time `h` the oracle is therefore never consulted, and
   the oracle machine agrees with the real one. But the triangle rectangle plus the driver
   show the oracle machine is still running (state `A`) at some time `t ≥ M - 1 ≥ h`, and
   halting is absorbing: contradiction.

## Notes for a Rocq port

* `Visit`, `Cell`, `Rect` translate directly to Rocq `Inductive` predicates. `pw`, `iter`,
  `Holds`, `wl`, `U` are simple `Fixpoint`s.
* `omega` corresponds to `lia`. Most `simp` calls only normalise list appends
  (`List.append_assoc`, `List.nil_append`, …) or unfold small definitions.
* Function extensionality is used for tape equalities (`wr_same`, `wr_wr`, `wr_comm`, `wl_wl`,
  and the `B`/`0` case of `step_left`). In Rocq, either use `FunctionalExtensionality` or replace
  `=` on tapes by pointwise equality.
* In `Machine.lean`, `run` is plain recursion (`run (n+1) = step (run n)`), and `Halted c` is `c.st = H`.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
