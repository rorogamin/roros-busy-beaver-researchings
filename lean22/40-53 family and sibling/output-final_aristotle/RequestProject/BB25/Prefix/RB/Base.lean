/-
# The `0RB` checkpoint class and its return predicate

Two ingredients of the `0RB` argument that do not depend on the rest.

* The checkpoint class `CP0`: a safe checkpoint which is ready for the two
  decrement scan and strictly admissible.

* The return predicate `Ret0`, stated at the level of *base* configurations
  rather than block configurations, so that two block configurations denoting
  the same tape may be exchanged freely (`Ret0.of_den`).  The `0RB` right words
  are only defined up to the re-parsing `2> 22^k 1$ = 22^k 21 $`, and this is
  where that is absorbed.
-/
import RequestProject.BB25.Prefix.RB.Count

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The `0RB` checkpoint -/

/-- **A `0RB` checkpoint**: a safe checkpoint whose two-decrement scan succeeds
and which is strictly admissible. -/
structure CP0 (s : List LB) : Prop where
  cp : SafeCP s
  ready : Ready s
  strict : Strict s

theorem ReadyCP.toCP0 {s : List LB} (h : ReadyCP s) : CP0 s := ⟨h.cp, h.ready, h.strict⟩

/-! ## The return predicate, at the level of base configurations -/

/-- From the base configuration `c` the machine either reaches a `0RB`
checkpoint or never halts. -/
def Ret0 (b4 : Option (Sym × Dir × St)) (c : Cfg) : Prop :=
  (∃ (s : List LB) (k : ℕ), CP0 s ∧ steps (M b4) k c = some (cpCfg s).den) ∨ ¬ Halts (M b4) c

theorem Ret0.of_den {c c' : Cfg} (h : c = c') (hr : Ret0 b4 c') : Ret0 b4 c := by
  subst h; exact hr

/-- A block run in front of a return. -/
theorem Ret0.of_run {c c' : BCfg} {k : ℕ} (hr : BRun b4 c c' k) (h : Ret0 b4 c'.den) :
    Ret0 b4 c.den := by
  rcases h with ⟨s, k', hs, hst⟩ | hnh
  · refine Or.inl ⟨s, k + k', hs, ?_⟩
    rw [steps_add, hr.sound]
    simpa using hst
  · exact Or.inr (hr.not_halts hnh)

/-- The halting-time bookkeeping, for a run given as iterated `steps`. -/
theorem halt_time_of_steps {c c' : Cfg} {k n : ℕ} (hr : steps (M b4) k c = some c')
    (hn : steps (M b4) n c = none) : k < n ∧ steps (M b4) (n - k) c' = none := by
  have hlt : k < n := by
    by_contra hc
    exact not_halts_within hr n (by omega) hn
  refine ⟨hlt, ?_⟩
  have h2 : steps (M b4) (k + (n - k)) c = none := by
    rw [show k + (n - k) = n by omega]
    exact hn
  rw [steps_add, hr] at h2
  simpa using h2

theorem Ret0.of_step {c c' : BCfg} {k : ℕ} (hs : bstep b4 c = some (c', k))
    (h : Ret0 b4 c'.den) : Ret0 b4 c.den :=
  Ret0.of_run (BRun.of_step hs) h

end BB25.Prefix
