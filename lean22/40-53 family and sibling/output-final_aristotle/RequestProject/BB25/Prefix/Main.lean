/-
# The members proved non-halting from the blank tape

The blank tape reaches the safe checkpoint

```
  L 222 111 <B1 22 1$        (the stack bottom first: `L ZZZ XXX`)
```

after exactly `156` base steps, using no transition of the head `B4`
(`seed_run`).  Its counter is `56` and its decoded value is `63`, so the
checkpoint is safe (`safeCP_seed`).  The return theorem of
`RequestProject.BB25.Prefix.Return` then shows that a member whose `W` case is
settled never halts: this gives `not_halts_3RA`, `not_halts_2LA`,
`not_halts_1RA`, `not_halts_0LA` and `not_halts_2LB`.
-/
import RequestProject.BB25.Prefix.Bit
import RequestProject.BB25.Prefix.Zero
import RequestProject.BB25.Prefix.Two
import RequestProject.BB25.Prefix.Marker
import RequestProject.BB25.Prefix.One
import RequestProject.BB25.Prefix.K0
import RequestProject.BB25.Prefix.JOne

namespace BB25.Prefix

open BB25

set_option maxRecDepth 100000

variable {b4 : Option (Sym × Dir × St)}

/-- The counter stack of the seed checkpoint, nearest to the head first. -/
def seedStack : List LB := [.X, .X, .X, .Z, .Z, .Z, .L]

/-- The blank tape reaches the seed checkpoint in `156` steps; no transition of
the head `B4` is used, so this holds for every member of the family. -/
theorem seed_run : steps (M b4) 156 init = some (cpCfg seedStack).den := rfl

theorem cval_seedStack : cval seedStack = 56 := rfl

/-- The seed checkpoint is safe. -/
theorem safeCP_seed : SafeCP seedStack := by
  refine ⟨?_, ?_, ?_, ?_, ⟨[.X, .X, .Z, .Z, .Z, .L], rfl⟩⟩
  · exact (((((CStack.base.consZ).consZ).consZ).consX).consX).consX
  · exact adm_consX (adm_consX (adm_consX (adm_consZ (adm_consZ (adm_consZ adm_L)))))
  · exact good_consX (good_consX (good_consX (good_consZ (good_consZ (good_consZ good_L)))))
  · rw [cval_seedStack]
    omega

/-- **Non-halting from the blank tape**, for any member whose `W` case of the
`<B1` sweep is settled. -/
theorem not_halts_init (hW : WCase b4) : ¬ Halts (M b4) init := by
  rintro ⟨n, hn⟩
  have hlt : 156 < n := by
    by_contra hc
    exact not_halts_within (seed_run (b4 := b4)) n (by omega) hn
  have h2 : steps (M b4) (156 + (n - 156)) init = none := by
    rw [show 156 + (n - 156) = n by omega]
    exact hn
  rw [steps_add, seed_run] at h2
  simp only [Option.bind_some] at h2
  exact not_halts_of_safeCP hW (n - 156) seedStack safeCP_seed h2

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB3RA` never halts.** -/
theorem not_halts_3RA : ¬ Halts (M b4_3RA) init :=
  not_halts_init (wcase_of_gBit gBit_3RA (Or.inl rfl))

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB2LA` never halts.** -/
theorem not_halts_2LA : ¬ Halts (M b4_2LA) init :=
  not_halts_init (wcase_of_gBit gBit_2LA (Or.inr rfl))

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB1RA` never halts.** -/
theorem not_halts_1RA : ¬ Halts (M b4_1RA) init :=
  not_halts_init wcase_1RA

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB0LA` never halts.** -/
theorem not_halts_0LA : ¬ Halts (M b4_0LA) init :=
  not_halts_init wcase_0LA

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB2LB` never halts.** -/
theorem not_halts_2LB : ¬ Halts (M b4_2LB) init :=
  not_halts_init wcase_2LB

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB0RA` never halts.** -/
theorem not_halts_0RA : ¬ Halts (M b4_0RA) init :=
  not_halts_init wcase_0RA

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB2RB` never halts.** -/
theorem not_halts_2RB : ¬ Halts (M b4_2RB) init :=
  not_halts_init wcase_2RB

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB1LB` never halts.** -/
theorem not_halts_1LB : ¬ Halts (M b4_1LB) init :=
  not_halts_init wcase_1LB

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB2RA` never halts.** -/
theorem not_halts_2RA : ¬ Halts (M b4_2RA) init :=
  not_halts_init wcase_2RA

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB1RB` never halts.** -/
theorem not_halts_1RB : ¬ Halts (M b4_1RB) init :=
  not_halts_init wcase_1RB

end BB25.Prefix
