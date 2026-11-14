# Non-halting of `1RB3LA3LA0RB2LB_2LA4LA4RA2RA---`: formal proof

```lean
theorem BB25.not_halts : ¬ BB25.Halts      -- RequestProject/NonHalt.lean
```

The proof formalizes the two-epoch argument from `bb25_two_epoch_nonhalting.zip`
(a copy is in `external/bb25_nonhalting_proof/`, unchanged).

* It builds with no `sorry`. `#print axioms BB25.not_halts` reports only
  `propext`, `Classical.choice` and `Quot.sound`.
* It does not use `native_decide`. The three finite computations are checked by
  the kernel (`rfl` / `decide +kernel`).
* Every declaration in the project is used by `not_halts`. Code from earlier
  sessions that the proof does not use has been removed; it is still in the
  git history.

## Files, in dependency order (≈2200 lines)

| File | Contents |
|---|---|
| `Machine.lean` | the TM: `tr`, `Cfg`, `step`, `steps`, `init`, `Halts`, `steps_add`, `steps_trans` |
| `Tokens.lean` | tokens `F C P`, token configurations `MCfg`, their meaning `ecfg`, the macro step `estep` with its exact cost (`estep_sound`), `Reaches`/`RunPos` = "the real machine gets from `c` to `c'` (in `> 0` steps)" |
| `Carry.lean` | `carry`, `carry_double`, the crossing law `crossCarry`, the pass law `cascade_pass_tok`, capacity `cap`, `cap_carry_iff`, `cap_carry` |
| `Overflow.lean` | `spill` / `spillLaw` / `overflow_pass`, the rebuild `rebG` / `rebG_reaches`, `tail_pass` |
| `Chunks.lean` | chunks `M S B`, `ck`, `spill_ck`, the capacity scan `ckStep` / `ckFold`, height `ctot` |
| `Price.lean` | total scan `foldT`, emission `emitW` (A), conversions `conv` (k), `bitsLSB`, the map `epochMap` (T), price `rho`, `Phi`, `eps`, `Good`; Lemma 4.1 `safe_scan` |
| `Pair.lean` | Lemmas 5.1 (`terminal_facts`, `epochMap_shape`), 6.1 (`conv_forced`), 7.1 (`rho_emit`), 7.2 (`rho_emit2_top`), bound (20) (`suffix_bound`, `suffix_small`), 8.1 + pair closure `good_pair` |
| `Epoch.lean` | decoration `decor`, Lemmas 2.1 (`carry_decor`), 2.2 (`ck_eq_decor`), 3.1 (`rebG_decor`), the machine epoch law `epoch_step` (Lemma 3.2 / Cor. 3.3) |
| `NonHalt.lean` | 4011 steps from blank to overflow 5 (`blank_to_seed`), seven epochs to overflow 12 (`reach_iter`, `ok_to_12`), the base pair (`base_good`), the induction (`forever`), `not_halts` |

## Notes for a Rocq port

* **Finite computations (kernel):**
  * `blank_to_seed`: 4011 raw steps, by `rfl`.
  * `ok_to_12`: the scans at overflows 5–11 succeed with value ≥ 3.
  * `base_good`: `Good` for the chunk words at overflows 12 and 13. This
    includes an exact rational check of `Φ ≤ 2^-13`.

  The last two involve naturals of several hundred bits and dyadic rationals
  with denominators up to about `2^621`. In Rocq, use `N`/`Z`/`Q` (or `vm_compute`).
* **Well-founded definitions:** `ck` (by length), `spill` (by length, then
  `d`), `rebG` (by the length of the cell list). Everything else is structural.
* **Arithmetic:** `rho`/`Phi` use integer powers `(2 : ℚ) ^ (z : ℤ)`, because
  heights can go negative inside the walk. Everything else is `ℕ`/`ℤ`
  arithmetic, closed by `omega`, `linarith`/`nlinarith`, `positivity`,
  `field_simp`.
* **Proof by fuel:** the machine laws `crossCarry`, `spillLaw` and
  `rebG_reaches` are proved by induction on a length bound `n`, with an inner
  induction on `d`. `carry_double` (`carry (d+1) = carry d ∘ carry d`) drives
  the inner step.
* `Reaches c c'` is just `∃ t, steps t (ecfg c) = some (ecfg c')`, so every
  machine lemma is a statement about the raw TM.
