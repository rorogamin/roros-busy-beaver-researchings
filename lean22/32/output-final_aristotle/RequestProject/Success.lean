import RequestProject.Fast

/-!
# The executable revolution never fails, and non-halting follows

`RequestProject.Fast` turns one revolution into the function `revolutionF`,
which returns `none` exactly at the configurations where the machine would be in
danger, and proves that a successful computation is a genuine run of the
machine.  This file adds what is needed in the other direction:

* `addT_of_le_gap` — a bulk increment of `t ≤ gap w` always succeeds and uses up
  exactly `t` of the gap;
* `junctionF_isSome` — the junction computes whenever the counter has a binary
  lowest digit and can pay nine increments;
* `neverHalts_of_revIter` — **if every revolution computes, the machine never
  halts**: the revolutions form an infinite chain of positive-length runs from a
  configuration the blank tape reaches.

That last theorem is the bridge over which `RequestProject.Completion` delivers
the final result.
-/

namespace SOC

/-! ## Bulk increments always succeed inside the gap -/

/-- **A bulk increment of at most `gap w` succeeds**, and uses exactly that much
of the gap. -/
theorem addT_of_le_gap : ∀ (t : Nat) {w : List LD}, t ≤ gap w →
    ∃ w', addT w t = some w' ∧ gap w' + t = gap w
  | 0, w, _ => ⟨w, by simp, by simp⟩
  | t + 1, w, h => by
      obtain ⟨u, hu, hgu⟩ := addT_of_le_gap t (w := w) (by omega)
      have hpos : 0 < gap u := by omega
      obtain ⟨u', hu'⟩ := inc_exists hpos
      refine ⟨u', ?_, ?_⟩
      · rw [show t + 1 = t + 1 from rfl, addT_add, hu, Option.bind_some, inc_addT_one hu']
      · have := hu'.gap_eq
        omega

/-! ## The overflow and the normal phase -/

/-! ## The junction -/

/-- **The junction computes** when the counter can pay for it. -/
theorem junctionF_isSome {w : List LD} (hb : BinHead w) (hg : 9 ≤ gap w) :
    (junctionF w).isSome := by
  match w, hb with
  | .d0 :: v, _ =>
      have hv : 4 ≤ gap v := by simp only [gap_d0] at hg; omega
      obtain ⟨v', hv', -⟩ := addT_of_le_gap 4 hv
      rw [junctionF, hv']
      rfl
  | .d1 :: v, _ =>
      have hv : 4 ≤ gap v := by simp only [gap_d1] at hg; omega
      obtain ⟨v', hv', -⟩ := addT_of_le_gap 4 hv
      rw [junctionF, hv']
      rfl

/-! ## The reset phase -/

/-! ## One revolution -/

/-! ## Non-halting from the computed sequences -/

/--
**If every revolution computes, the machine never halts.**

`revIter n` is the block sequence of the `n`-th reset phase; if the computation
never returns `none`, the machine runs through infinitely many revolutions.
-/
theorem neverHalts_of_revIter (h : ∀ n, (revIter n).isSome) : NeverHalts := by
  -- the sequence of block sequences
  have hval : ∀ n, ∃ L, revIter n = some L := by
    intro n
    cases hn : revIter n with
    | none => have := h n; rw [hn] at this; simp at this
    | some L => exact ⟨L, rfl⟩
  let F : Nat → List Sym := fun n => Classical.choose (hval n)
  have hF : ∀ n, revIter n = some (F n) := fun n => Classical.choose_spec (hval n)
  have hstep : ∀ n, MPlus (phaseStart (F n)) (phaseStart (F (n + 1))) := by
    intro n
    have hn1 : revIter (n + 1) = some (F (n + 1)) := hF (n + 1)
    rw [revIter, hF n, Option.bind_some] at hn1
    exact (revolutionF_spec hn1).2
  have hforever : ∀ n, (run (enc (phaseStart (F 0))) n).isSome := by
    intro n
    obtain ⟨N, hN, hrun⟩ := plus_chain_reaches (fun i => phaseStart (F i)) hstep n
    exact isSome_of_run_le (by rw [hrun]; rfl) hN
  have hreach : init ⟶* enc (phaseStart (F 0)) := revIter_reaches (hF 0)
  exact forever_of_reaches hreach hforever

end SOC
