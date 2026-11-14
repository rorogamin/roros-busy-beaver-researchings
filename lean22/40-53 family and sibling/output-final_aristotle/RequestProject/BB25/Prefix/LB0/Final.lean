/-
# `0LB` never halts

The blank tape reaches, after exactly `931` base steps, the Z checkpoint

```
  L ZXZZX Z <B1 22^7 1        (bottom first)
```

whose core `ZXZZX` is `D⁹ (T (YYYYY))` (`entry_run`).  It satisfies the
invariant `ZInv` of `Return.lean` (`zinv_entry`): counter `22`, height `5`,
energy `31 ≥ 9`, decoded value `31` (`24 · 32 ≥ 23 · 32`) and decoded energy
`31 ≥ 3 · 2³ + 4`.  Iterating the positive-time return theorem
`zinv_return` gives defined runs of every length, so the machine never halts.
-/
import RequestProject.BB25.Prefix.LB0.Return

namespace BB25.Prefix

open BB25

set_option maxRecDepth 100000

/-- The reset word of the entry checkpoint. -/
def entryWord : List RB := [.Y, .Y, .Y, .Y, .Y]

/-- The core of the entry checkpoint is `ZXZZX` (bottom first). -/
theorem entry_core : dpow 9 (TW entryWord) = [.X, .Z, .Z, .X, .Z, .L] := by decide

/-- **The blank tape reaches the entry checkpoint in `931` steps.** -/
theorem entry_run : steps (M b4_0LB) 931 init = some (zCfg (dpow 9 (TW entryWord)) 7).den := by
  rw [entry_core]; rfl

/-- The entry checkpoint satisfies the invariant. -/
theorem zinv_entry : ZInv entryWord 9 7 := by
  refine ⟨?_, ⟨[.Y, .Y], rfl, ?_⟩, by decide, by decide, ⟨5, by decide, by norm_num, ?_, ?_⟩,
    by norm_num⟩
  · intro b hb
    simp [entryWord] at hb
    rw [hb]
    exact Or.inl rfl
  · exact (DyckPre.nil.cons_Y).cons_Y
  · decide
  · decide

theorem not_halts_of_zinv :
    ∀ (n : ℕ) (w : List RB) (k r : ℕ), ZInv w k r →
      steps (M b4_0LB) n (zCfg (dpow k (TW w)) r).den ≠ none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro w k r hI hn
      obtain ⟨w', k', r', T, hT, hrun, hI'⟩ := zinv_return hI
      obtain ⟨hlt, hn'⟩ := halt_time_of_run hrun hn
      exact ih (n - T) (by omega) w' k' r' hI' hn'

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB0LB` never halts.** -/
theorem not_halts_0LB : ¬ Halts (M b4_0LB) init := by
  rintro ⟨n, hn⟩
  have hlt : 931 < n := by
    by_contra hc
    exact not_halts_within entry_run n (by omega) hn
  have h2 : steps (M b4_0LB) (931 + (n - 931)) init = none := by
    rw [show 931 + (n - 931) = n by omega]
    exact hn
  rw [steps_add, entry_run] at h2
  simp only [Option.bind_some] at h2
  exact not_halts_of_zinv (n - 931) entryWord 9 7 zinv_entry h2

end BB25.Prefix
