import tm_mixed_radix_result.RequestProject.MixedRadix

/-!
# The exhaustion normal form of a token word

A *token word* is a finite word over the tokens `2`, `40`, `42`, `43`, `44`.
Entering such a word in state `A` from the left, the machine performs some
number of complete *returns* (excursions that come back to the cell left of the
word in state `B`), each of which has to be restarted from the left, and finally
leaves the word on the right in state `A`.

`exh w = (C, H, T)` computes, by a single right-to-left recursion, the maximal
number `C` of returns, the word `H` left behind when the head finally enters the
cell after the word, and the number `T` of steps spent inside the word.
`exh_spec` proves that this is exactly what the machine does, for arbitrary
surrounding tape.  The physical driver which restarts the returns (the base-3
counter) is treated in `Accel/Drain.lean`.
-/

namespace TM2x5

theorem iter_one (c : Cfg) : iter 1 (some c) = step c := rfl

/-- A head in state `A` entering a word `u` from the left leaves it on the right,
in state `A`, after `n` steps, having rewritten `u` to `h`. -/
def Enter (u h : List Sym) (n : ℕ) : Prop :=
  ∀ l r, iter n (some (onFirst St.A l (u ++ r))) = some (onFirst St.A (h.reverse ++ l) r)

theorem enter_nil : Enter [] [] 0 := by
  intro l r
  rfl

/-! ## Basic one- and two-step rules -/

theorem step_A_two' (l xs : List Sym) :
    iter 1 (some (onFirst St.A l ((2 : Sym) :: xs))) = some (onFirst St.A ((3 : Sym) :: l) xs) := by
  cases xs <;> rfl

theorem step_B_three' (l xs : List Sym) :
    iter 1 (some (Cfg.mk St.B l 3 xs)) = some (onFirst St.A ((4 : Sym) :: l) xs) := by
  cases xs <;> rfl

theorem step_B_four' (l xs : List Sym) :
    iter 1 (some (Cfg.mk St.B l 4 xs)) = some (onFirst St.A ((0 : Sym) :: l) xs) := by
  cases xs <;> rfl

theorem step_A_44 (l xs : List Sym) :
    iter 2 (some (onFirst St.A l ((4 : Sym) :: 4 :: xs))) =
      some (onFirst St.A ((0 : Sym) :: 2 :: l) xs) := by
  cases xs <;> rfl

theorem step_A_43 (l xs : List Sym) :
    iter 2 (some (onFirst St.A l ((4 : Sym) :: 3 :: xs))) =
      some (onFirst St.A ((4 : Sym) :: 2 :: l) xs) := by
  cases xs <;> rfl

/-! ## Returns through the new pair tokens `40` and `43` -/

theorem return_40 (w : List Sym) :
    ReturnRule ((4 : Sym) :: 0 :: w) ((4 : Sym) :: 2 :: w) 3 := by
  intro a l r
  rfl

theorem return_43 {u v w : List Sym} {n m : ℕ}
    (h1 : ReturnRule u v n) (h2 : ReturnRule v w m) :
    ReturnRule ((4 : Sym) :: 3 :: u) ((4 : Sym) :: 2 :: w) (n + m + 5) := by
  intro a l r
  have hs : iter 2 (some (onFirst St.A (a :: l) (((4 : Sym) :: 3 :: u) ++ r))) =
      some (onFirst St.A ((4 : Sym) :: 2 :: a :: l) (u ++ r)) := by
    simp only [List.cons_append]
    exact step_A_43 _ _
  have hm := step_B_four' ((2 : Sym) :: a :: l) (v ++ r)
  have he : iter 2 (some (Cfg.mk St.B ((2 : Sym) :: a :: l) 0 (w ++ r))) =
      some (Cfg.mk St.B l a (((4 : Sym) :: 2 :: w) ++ r)) := rfl
  rw [show n + m + 5 = 2 + (n + (1 + (m + 2))) by omega,
    iter_add, hs, iter_add, h1 4 ((2 : Sym) :: a :: l) r,
    iter_add, hm, iter_add, h2 0 ((2 : Sym) :: a :: l) r, he]

/-! ## Splitting batches -/

theorem batch_zero_inv {u v : List Sym} {n : ℕ} (h : ReturnBatch 0 u v n) : v = u ∧ n = 0 := by
  cases h
  exact ⟨rfl, rfl⟩

theorem batch_split : ∀ (a : ℕ) {b : ℕ} {u w : List Sym} {n : ℕ},
    ReturnBatch (a + b) u w n →
      ∃ v n1 n2, ReturnBatch a u v n1 ∧ ReturnBatch b v w n2 ∧ n = n1 + n2 := by
  intro a
  induction a with
  | zero =>
    intro b u w n h
    exact ⟨u, 0, n, ReturnBatch.nil u, by simpa using h, by simp⟩
  | succ a ih =>
    intro b u w n h
    have h' : ReturnBatch ((a + b) + 1) u w n := by
      convert h using 1; omega
    obtain ⟨u1, n0, n', hr, hb, hn⟩ := batch_inv h'
    obtain ⟨v, n1, n2, h1, h2, hn'⟩ := ih hb
    exact ⟨v, n0 + n1, n2, ReturnBatch.cons hr h1, h2, by omega⟩

/-! ## Batches through a pair token ending on `44`

When a pair token receives exactly as many returns as are needed to consume
`c` returns of its suffix and end in the state `44`, the cost is `3k + c` local
steps, where `k` is the number of returns through the pair. -/

theorem batch_p2_full {c : ℕ} {x v : List Sym} {t : ℕ} (h : ReturnBatch c x v t) :
    ReturnBatch (2 * c + 1) ((4 : Sym) :: 2 :: x) ((4 : Sym) :: 4 :: v)
      (3 * (2 * c + 1) + c + t) := by
  have := batch_odd_zero h
  convert this using 1; omega

theorem batch_p4_full {c : ℕ} {x v : List Sym} {t : ℕ} (h : ReturnBatch c x v t) :
    ReturnBatch (2 * c) ((4 : Sym) :: 4 :: x) ((4 : Sym) :: 4 :: v)
      (3 * (2 * c) + c + t) := by
  have := batch_even_one h
  convert this using 1; omega

theorem batch_p0_full {c : ℕ} {x v : List Sym} {t : ℕ} (h : ReturnBatch c x v t) :
    ReturnBatch (2 * c + 2) ((4 : Sym) :: 0 :: x) ((4 : Sym) :: 4 :: v)
      (3 * (2 * c + 2) + c + t) := by
  have := ReturnBatch.cons (return_40 x) (batch_p2_full h)
  convert this using 1; omega

theorem batch_p3_full {c : ℕ} {x v : List Sym} {t : ℕ} (h : ReturnBatch (c + 2) x v t) :
    ReturnBatch (2 * (c + 2) - 2) ((4 : Sym) :: 3 :: x) ((4 : Sym) :: 4 :: v)
      (3 * (2 * (c + 2) - 2) + (c + 2) + t) := by
  have h' : ReturnBatch (c + 1 + 1) x v t := h
  obtain ⟨x1, a, t1, ha, h1, ht1⟩ := batch_inv h'
  obtain ⟨x2, b, t2, hb, h2, ht2⟩ := batch_inv h1
  have := ReturnBatch.cons (return_43 ha hb) (batch_p2_full h2)
  convert this using 1 <;> omega

/-! ## Tokens and the exhaustion recursion -/

/-- The tokens: `2`, and the pairs `40`, `42`, `43`, `44`. -/
inductive Tok
  | two
  | p0
  | p2
  | p3
  | p4
  deriving DecidableEq, Repr

/-- The cells of a token. -/
def Tok.syms : Tok → List Sym
  | Tok.two => [2]
  | Tok.p0 => [4, 0]
  | Tok.p2 => [4, 2]
  | Tok.p3 => [4, 3]
  | Tok.p4 => [4, 4]

/-- The cells of a token word. -/
def decode : List Tok → List Sym
  | [] => []
  | t :: ts => t.syms ++ decode ts

/-- The symbol of a ternary residue: `0 ↦ 3`, `1 ↦ 4`, `2 ↦ 0`. -/
def dsym (r : ℕ) : Sym :=
  if r = 0 then 3 else if r = 1 then 4 else 0

/-- One step of the exhaustion recursion: from the data `(c, h, t)` of the suffix
compute the data of the word with one more token in front. -/
def exhStep : Tok → ℕ → List Sym → ℕ → ℕ × List Sym × ℕ
  | Tok.two, c, h, t => (c / 3, dsym (c % 3) :: h, t + 4 * (c / 3) + 1 + c % 3)
  | Tok.p0, c, h, t => (2 * c + 2, (2 : Sym) :: 0 :: h, t + 3 * (2 * c + 2) + c + 2)
  | Tok.p2, c, h, t => (2 * c + 1, (2 : Sym) :: 0 :: h, t + 3 * (2 * c + 1) + c + 2)
  | Tok.p4, c, h, t => (2 * c, (2 : Sym) :: 0 :: h, t + 3 * (2 * c) + c + 2)
  | Tok.p3, c, h, t =>
      (2 * c - 2, (2 : Sym) :: (if c = 0 then (4 : Sym) else 0) :: h,
        t + 3 * (2 * c - 2) + c + 2)

/-- The exhaustion normal form `(C, H, T)` of a token word. -/
def exh : List Tok → ℕ × List Sym × ℕ
  | [] => (0, [], 0)
  | t :: x => exhStep t (exh x).1 (exh x).2.1 (exh x).2.2

/-- The specification of exhaustion data: `c` complete returns rewriting `u` to
some `v`, followed by an exit to the right leaving `h`, in `t` steps overall. -/
def ExhSpec (u : List Sym) (c : ℕ) (h : List Sym) (t : ℕ) : Prop :=
  ∃ v t1 t2, ReturnBatch c u v t1 ∧ Enter v h t2 ∧ t = t1 + t2

/-- After `r ≤ 2` further returns of its suffix, a cell freshly turned to `3` by
an entering `A` holds `dsym r`, and the head leaves to the right. -/
theorem enter_after_three (r : ℕ) (hr : r < 3) {v1 v h : List Sym} {n2 t2 : ℕ}
    (hb : ReturnBatch r v1 v n2) (he : Enter v h t2) (l rr : List Sym) :
    iter (r + n2 + t2) (some (onFirst St.A ((3 : Sym) :: l) (v1 ++ rr))) =
      some (onFirst St.A (h.reverse ++ dsym r :: l) rr) := by
  interval_cases r
  · obtain ⟨rfl, rfl⟩ := batch_zero_inv hb
    simpa [dsym] using he ((3 : Sym) :: l) rr
  · obtain ⟨w, a, b, ha, hb', hn⟩ := batch_inv (k := 0) hb
    obtain ⟨rfl, rfl⟩ := batch_zero_inv hb'
    rw [show 1 + n2 + t2 = a + (1 + t2) by omega, iter_add, ha 3 l rr, iter_add,
      step_B_three', he]
    simp [dsym]
  · obtain ⟨w, a, b, ha, hb', hn⟩ := batch_inv (k := 1) hb
    obtain ⟨w', a', b', ha', hb'', hn'⟩ := batch_inv (k := 0) hb'
    obtain ⟨rfl, rfl⟩ := batch_zero_inv hb''
    rw [show 2 + n2 + t2 = a + (1 + (a' + (1 + t2))) by omega, iter_add, ha 3 l rr,
      iter_add, step_B_three', iter_add, ha' 4 l rr, iter_add, step_B_four', he]
    simp [dsym]

theorem exhStep_spec (tok : Tok) (x : List Sym) (c : ℕ) (h : List Sym) (t : ℕ)
    (hx : ExhSpec x c h t) :
    ExhSpec (tok.syms ++ x) (exhStep tok c h t).1 (exhStep tok c h t).2.1
      (exhStep tok c h t).2.2 := by
  obtain ⟨v, t1, t2, hb, he, rfl⟩ := hx
  cases tok with
  | two =>
    have hc : c = 3 * (c / 3) + c % 3 := (Nat.div_add_mod c 3).symm
    rw [hc] at hb
    obtain ⟨v1, n1, n2, hb1, hb2, hn⟩ := batch_split (3 * (c / 3)) hb
    refine ⟨(2 : Sym) :: v1, 4 * (c / 3) + n1, 1 + (c % 3 + n2 + t2),
      batch_two (c / 3) hb1, ?_, ?_⟩
    · intro l r
      rw [iter_add, show (2 : Sym) :: v1 ++ r = (2 : Sym) :: (v1 ++ r) from rfl,
        step_A_two', enter_after_three (c % 3) (Nat.mod_lt _ (by norm_num)) hb2 he]
      simp [exhStep]
    · simp only [exhStep]; omega
  | p0 =>
    refine ⟨(4 : Sym) :: 4 :: v, 3 * (2 * c + 2) + c + t1, 2 + t2, batch_p0_full hb, ?_, ?_⟩
    · intro l r
      rw [iter_add, show (4 : Sym) :: 4 :: v ++ r = (4 : Sym) :: 4 :: (v ++ r) from rfl,
        step_A_44, he]
      simp [exhStep]
    · simp only [exhStep]; omega
  | p2 =>
    refine ⟨(4 : Sym) :: 4 :: v, 3 * (2 * c + 1) + c + t1, 2 + t2, batch_p2_full hb, ?_, ?_⟩
    · intro l r
      rw [iter_add, show (4 : Sym) :: 4 :: v ++ r = (4 : Sym) :: 4 :: (v ++ r) from rfl,
        step_A_44, he]
      simp [exhStep]
    · simp only [exhStep]; omega
  | p4 =>
    refine ⟨(4 : Sym) :: 4 :: v, 3 * (2 * c) + c + t1, 2 + t2, batch_p4_full hb, ?_, ?_⟩
    · intro l r
      rw [iter_add, show (4 : Sym) :: 4 :: v ++ r = (4 : Sym) :: 4 :: (v ++ r) from rfl,
        step_A_44, he]
      simp [exhStep]
    · simp only [exhStep]; omega
  | p3 =>
    rcases c with _ | _ | c
    · -- no return of the suffix is available: the `4` survives
      obtain ⟨rfl, rfl⟩ := batch_zero_inv hb
      refine ⟨(4 : Sym) :: 3 :: v, 0, 2 + t2, ReturnBatch.nil _, ?_, ?_⟩
      · intro l r
        rw [iter_add, show (4 : Sym) :: 3 :: v ++ r = (4 : Sym) :: 3 :: (v ++ r) from rfl,
          step_A_43, he]
        simp [exhStep]
      · simp only [exhStep]; omega
    · -- exactly one return of the suffix is available
      obtain ⟨w, a, b, ha, hb', hn⟩ := batch_inv (k := 0) hb
      obtain ⟨rfl, rfl⟩ := batch_zero_inv hb'
      refine ⟨(4 : Sym) :: 3 :: x, 0, 2 + (a + (1 + t2)), ReturnBatch.nil _, ?_, ?_⟩
      · intro l r
        rw [iter_add, show (4 : Sym) :: 3 :: x ++ r = (4 : Sym) :: 3 :: (x ++ r) from rfl,
          step_A_43, iter_add, ha 4 ((2 : Sym) :: l) r, iter_add, step_B_four', he]
        simp [exhStep]
      · simp only [exhStep]; omega
    · refine ⟨(4 : Sym) :: 4 :: v, 3 * (2 * (c + 2) - 2) + (c + 2) + t1, 2 + t2,
        batch_p3_full hb, ?_, ?_⟩
      · intro l r
        rw [iter_add, show (4 : Sym) :: 4 :: v ++ r = (4 : Sym) :: 4 :: (v ++ r) from rfl,
          step_A_44, he]
        simp [exhStep]
      · simp only [exhStep]; omega

/-- **Exhaustion normal form.**  For every token word `w`, with `exh w = (C, H, T)`:
the word admits exactly `C` complete returns (rewriting it to some `v`), after
which an entering `A` crosses `v` to the right in the remaining time, leaving `H`;
the total time inside the word is `T`. -/
theorem exh_spec (w : List Tok) : ExhSpec (decode w) (exh w).1 (exh w).2.1 (exh w).2.2 := by
  induction w with
  | nil => exact ⟨[], 0, 0, ReturnBatch.nil _, enter_nil, rfl⟩
  | cons t x ih => exact exhStep_spec t (decode x) _ _ _ ih

end TM2x5
