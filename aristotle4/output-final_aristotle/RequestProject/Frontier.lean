import RequestProject.Counter

/-!
# Every halt is a left-arrival on a `1`

The whole analysis rests on the standing assumption that the machine can only
halt when a left-moving cascade reaches a cell holding `1`.  `pre_halt_shape`
alone does not give that: it leaves five local situations, three of which have
the head *moving right* onto a `1`.

This file removes those three.  The key is a one-line invariant:

> **no cell to the right of the head ever holds a `1`** (`NoOneRight`).

It holds initially and is preserved by every step, because the only transition
that writes a `1` is `A0 → 1RB`, which moves **right** — so the `1` it writes is
left behind — while every left-moving transition writes a `2`, a `3` or a `4`.

Consequently (`halt_needs_left_arrival`) a halt is always caused by the head
moving *left* onto a cell holding `1`, from one of exactly two situations:
state `A` on a `3`, or state `B` on a `1`, with a `1` in the cell to the left.
-/

namespace TM2x5

/-- The cell the head moves onto when it moves left is prepended to the tape on
its right. -/
theorem wL_right (c : Cfg) (w : Sym) (s : St) : (c.wL w s).right = w :: c.right := by
  unfold Cfg.wL; cases c.left <;> rfl

/-- Moving right drops one cell from the tape on the right. -/
theorem wR_right (c : Cfg) (w : Sym) (s : St) : (c.wR w s).right = c.right.tail := by
  unfold Cfg.wR; cases c.right <;> rfl

/-- No cell strictly to the right of the head holds the symbol `1`. -/
def NoOneRight (c : Cfg) : Prop := (1 : Sym) ∉ c.right

theorem noOneRight_init : NoOneRight init := by
  simp [NoOneRight, init]

/-- The invariant is preserved by every step: the only transition writing a `1`
moves right, and no left-moving transition writes a `1`. -/
theorem noOneRight_step {c d : Cfg} (h : NoOneRight c) (hs : step c = some d) :
    NoOneRight d := by
  have keyL : ∀ (w : Sym) (st : St), w ≠ 1 → NoOneRight (c.wL w st) := by
    intro w st hw
    simp only [NoOneRight, wL_right, List.mem_cons, not_or]
    exact ⟨fun hEq => hw hEq.symm, h⟩
  have keyR : ∀ (w : Sym) (st : St), NoOneRight (c.wR w st) := by
    intro w st
    simp only [NoOneRight, wR_right]
    intro hmem
    exact h (List.mem_of_mem_tail hmem)
  unfold step at hs
  cases hst : c.st <;> cases hcur : c.cur <;> rw [hst, hcur] at hs <;>
    simp only [Option.some.injEq] at hs <;>
    first
      | exact absurd hs (by simp)
      | (subst hs; first
          | exact keyR _ _
          | exact keyL _ _ (by decide))

/-- The invariant holds at every reachable configuration. -/
theorem noOneRight_run : ∀ (n : ℕ) (c : Cfg), run n = some c → NoOneRight c := by
  intro n
  induction n with
  | zero =>
    intro c hc
    rw [run_zero] at hc
    cases hc
    exact noOneRight_init
  | succ n ih =>
    intro c hc
    rw [run_succ] at hc
    cases hr : run n with
    | none => rw [hr] at hc; simp at hc
    | some c' =>
      rw [hr] at hc
      exact noOneRight_step (ih c' hr) hc

theorem noOneRight_reachable {c : Cfg} (h : Reachable c) : NoOneRight c := by
  obtain ⟨n, hn⟩ := h
  exact noOneRight_run n c hn

/-- **A halt is always a left-arrival on a `1`.**  If the machine halts, then it
passes through a reachable configuration whose left neighbour holds a `1` and
which is either state `A` on a `3` (the last step of a cascade, `A3 → 2LA`) or
state `B` on a `1` (`B1 → 3LA`); in both cases the next step moves the head
**left** onto the `1` and the machine halts there.

This is the rigorous form of the assumption used throughout `ANALYSIS.md`: the
head never walks onto a `1` from the left, so a halt can only be caused by
something arriving from the right — a cascade. -/
theorem halt_needs_left_arrival (h : Halts) :
    ∃ (c : Cfg) (l : List Sym), Reachable c ∧ c.left = 1 :: l ∧
      ((c.st = St.A ∧ c.cur = 3) ∨ (c.st = St.B ∧ c.cur = 1)) := by
  obtain ⟨n, d, hd, hA, h1⟩ := halts_iff_state_A_reads_one.mp h
  cases n with
  | zero =>
    rw [run_zero] at hd
    cases hd
    exact absurd h1 (by decide)
  | succ m =>
    rw [run_succ] at hd
    cases hr : run m with
    | none => rw [hr] at hd; simp at hd
    | some c =>
      rw [hr] at hd
      have hstep : step c = some d := hd
      have hno : NoOneRight c := noOneRight_run m c hr
      rcases pre_halt_shape c d hstep hA h1 with
        ⟨hs, hc, l, hl⟩ | ⟨hs, hc, l, hl⟩ | ⟨_, _, r, hr'⟩ | ⟨_, _, r, hr'⟩ | ⟨_, _, r, hr'⟩
      · exact ⟨c, l, ⟨m, hr⟩, hl, Or.inl ⟨hs, hc⟩⟩
      · exact ⟨c, l, ⟨m, hr⟩, hl, Or.inr ⟨hs, hc⟩⟩
      · exact absurd (show (1 : Sym) ∈ c.right by rw [hr']; exact List.mem_cons_self ..) hno
      · exact absurd (show (1 : Sym) ∈ c.right by rw [hr']; exact List.mem_cons_self ..) hno
      · exact absurd (show (1 : Sym) ∈ c.right by rw [hr']; exact List.mem_cons_self ..) hno

/-- Contrapositive: if the head never arrives on a `1` from the right, the
machine does not halt. -/
theorem not_halts_of_no_left_arrival
    (h : ∀ (c : Cfg) (l : List Sym), Reachable c → c.left = 1 :: l →
      ¬ ((c.st = St.A ∧ c.cur = 3) ∨ (c.st = St.B ∧ c.cur = 1))) : ¬ Halts := by
  intro hh
  obtain ⟨c, l, hr, hl, hcase⟩ := halt_needs_left_arrival hh
  exact h c l hr hl hcase

end TM2x5
