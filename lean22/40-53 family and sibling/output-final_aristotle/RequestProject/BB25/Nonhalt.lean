/-
# A non-halting criterion for the whole family

Every member of `1RB2LA0RB1LB---_1LA3RA1RA4LB---` shares the following
behaviour at the *left* end of the tape.

The head can only leave the region it has already visited on the left in one
of two ways: in state `<A`, in which case it bounces straight back
(`L <A → L A> 2>`), or in state `<B1`.  We show here that
the second case is fatal *for the halting problem*: a `<B1` head that reaches
the left end of the tape sends the machine into a left spinout which repeats
with period 8 forever, so the machine never halts.

This holds for all 13 members simultaneously, since none of the transitions
used depends on `B4`.
-/
import RequestProject.BB25.Machine

namespace BB25

variable {b4 : Option (Sym × Dir × St)}

/-- If a run of length `k` reaches `c'` and the machine halts from `c`, then it
halts from `c'` as well. -/
theorem Halts.of_run {m : Machine} {k : ℕ} {c c' : Cfg} (h : steps m k c = some c')
    (hc : Halts m c) : Halts m c' := by
  obtain ⟨n, hn⟩ := hc
  rcases le_or_gt n k with hle | hgt
  · exact absurd hn (not_halts_within h n hle)
  · obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
    refine ⟨j, ?_⟩
    rw [steps_add, h] at hn
    simpa using hn

/-- The spinout step: with the tape `…0 0 <A 1122…` the head walks two cells
further into the blank region every 8 steps, writing `22`. -/
theorem spinout_step (t : List Sym) :
    steps (M b4) 8 ⟨[], .A, .L, 1 :: 1 :: 2 :: 2 :: t⟩
      = some ⟨[], .A, .L, 1 :: 1 :: 2 :: 2 :: 2 :: 2 :: t⟩ := rfl

/-- Iterating the spinout. -/
theorem spinout_iter (t : List Sym) : ∀ j : ℕ,
    steps (M b4) (8 * j) ⟨[], .A, .L, 1 :: 1 :: 2 :: 2 :: t⟩
      = some ⟨[], .A, .L, 1 :: 1 :: 2 :: 2 :: (List.replicate (2 * j) 2 ++ t)⟩ := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have h := spinout_step (b4 := b4) (List.replicate (2 * j) 2 ++ t)
      have := steps_trans ih h
      rw [show 8 * j + 8 = 8 * (j + 1) by ring] at this
      rw [this, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
      rfl

/-- **The left spinout never halts.** -/
theorem not_halts_spinout (t : List Sym) : ¬ Halts (M b4) ⟨[], .A, .L, 1 :: 1 :: 2 :: 2 :: t⟩ := by
  rintro ⟨n, hn⟩
  exact not_halts_within (spinout_iter (b4 := b4) t n) n (by omega) hn

/-- The head arriving at the left end of the tape in state `<B1` (that is, at
the block `L = ^11`) reaches the spinout in 7 steps. -/
theorem leftend_B1_run (t : List Sym) :
    steps (M b4) 7 ⟨[1, 1], .B, .L, 1 :: t⟩ = some ⟨[], .A, .L, 1 :: 1 :: 2 :: 2 :: t⟩ := rfl

/--
**Non-halting criterion.**  If the head of any member of the family ever
reaches the left end of the tape in state `<B1` -- i.e. the configuration
`^11 <B1 t` with nothing but blanks to the left -- then the machine never
halts.
-/
theorem not_halts_leftend_B1 (t : List Sym) : ¬ Halts (M b4) ⟨[1, 1], .B, .L, 1 :: t⟩ :=
  fun h => not_halts_spinout t (h.of_run (leftend_B1_run t))

end BB25
