/-
# The reverse-debt interpreter of the `1LA` scan, and the dual-credit lemma

The `<B1` scan of `1LA` (`Ready` of `RequestProject.BB25.Prefix.LA`) reads a
stack from the head down.  The stacks it has to be run on are the **paid reset
stacks** `T(w) = tfold [L] w` of a reset word `w`, possibly after a number `n`
of decrements — the *debt* already charged by the part of the scan that has
been performed.  This file develops that reading.

* `dpow n s` is the stack after `n` decrements, and the three identities
  `dpow_W`, `dpow_X_even`, `dpow_X_odd` say how a debt travels through a block.

* The **reverse-debt rules**: reading the word `w` from the right, a final `Y`
  stops the scan when the debt is even and halves it (after removing the
  produced zero bit) when it is odd; a final `V` is the same with the parities
  exchanged; a final `X` is a pop, which costs the two extra decrements of the
  `1LA` rule and turns the debt `n` into `2n+4`.  These are
  `ready_Y_even`, `ready_Y_odd`, `ready_V_odd`, `ready_V_even`, `ready_X`.

* The **dual-credit lemma** `dual_credit`: for a good stack `c`, the scan of
  `D^n(T(P(c)))` is safe as soon as `2n+2 ≤ cval c`.  The induction is on the
  stack and needs a second, *credit* alternative — the invariant `n + 4 ≤ 2a`
  and `n + 2 ≤ b` — because a pop doubles the debt while only doubling the
  counter.  The credit alternative is what the machine is in while it works
  through a run of pops; it is inductive on its own, and the counter
  alternative feeds into it.
-/
import RequestProject.BB25.Prefix.LA

namespace BB25.Prefix

open BB25

/-! ## Iterated decrements -/

/-- The stack after `n` decrements. -/
def dpow : ℕ → List LB → List LB
  | 0, s => s
  | n + 1, s => cdec (dpow n s)

@[simp] theorem dpow_zero (s : List LB) : dpow 0 s = s := rfl

theorem dpow_succ (n : ℕ) (s : List LB) : dpow (n + 1) s = cdec (dpow n s) := rfl

theorem dpow_succ' (n : ℕ) (s : List LB) : dpow (n + 1) s = dpow n (cdec s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [dpow_succ, ih, ← dpow_succ]

theorem dpow_add (a b : ℕ) (s : List LB) : dpow (a + b) s = dpow a (dpow b s) := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by omega, dpow_succ, ih, dpow_succ]

theorem CStack_dpow {s : List LB} (hst : CStack s) (n : ℕ) : CStack (dpow n s) := by
  induction n with
  | zero => exact hst
  | succ n ih => exact cdec_CStack_all ih

theorem cval_dpow {s : List LB} (hst : CStack s) : ∀ n : ℕ, n ≤ cval s →
    cval (dpow n s) = cval s - n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have h1 : cval (dpow n s) = cval s - n := ih (by omega)
      have h2 : 1 ≤ cval (dpow n s) := by omega
      rw [dpow_succ, cdec_cval (CStack_dpow hst n) h2, h1]
      omega

@[simp] theorem dpow_L (n : ℕ) (s : List LB) : dpow n (.L :: s) = .L :: s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dpow_succ, ih, cdec_L]

/-- A debt above a pop is twice the debt below it. -/
theorem dpow_W (n : ℕ) (s : List LB) : dpow n (.W :: s) = .W :: dpow (2 * n) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [dpow_succ, ih, cdec_W, show 2 * (n + 1) = (2 * n) + 1 + 1 by ring,
        dpow_succ, dpow_succ]

/-- An even debt above a zero bit is half the debt below it. -/
theorem dpow_X_even (k : ℕ) (s : List LB) : dpow (2 * k) (.X :: s) = .X :: dpow k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k) + 1 + 1 by ring, dpow_succ, dpow_succ, ih,
        cdec_X, cdec_Z, dpow_succ]

/-- An odd debt above a zero bit turns it into a one bit. -/
theorem dpow_X_odd (k : ℕ) (s : List LB) : dpow (2 * k + 1) (.X :: s) = .Z :: dpow (k + 1) s := by
  rw [dpow_succ, dpow_X_even, cdec_X, dpow_succ]

/-! ## The paid stack of a word -/

/-- The paid reset stack of a word, built over the bottom block. -/
def TW (u : List RB) : List LB := tfold [LB.L] u

@[simp] theorem TW_nil : TW [] = [LB.L] := rfl

theorem TW_Y (u : List RB) : TW (u ++ [.Y]) = .Z :: TW u := by
  rw [TW, tfold_append]; rfl

theorem TW_V (u : List RB) : TW (u ++ [.V]) = .X :: TW u := by
  rw [TW, tfold_append]; rfl

theorem TW_X (u : List RB) : TW (u ++ [.X]) = .W :: dpow 2 (TW u) := by
  rw [TW, tfold_append]
  show cdec (.W :: tfold [LB.L] u) = _
  rw [cdec_W]
  rfl

theorem CStack_TW_Y {u : List RB} (h : CStack (TW u)) : CStack (TW (u ++ [.Y])) := by
  rw [TW_Y]; exact h.consZ

theorem CStack_TW_V {u : List RB} (h : CStack (TW u)) : CStack (TW (u ++ [.V])) := by
  rw [TW_V]; exact h.consX

theorem CStack_TW_X {u : List RB} (h : CStack (TW u)) : CStack (TW (u ++ [.X])) := by
  rw [TW_X]; exact (CStack_dpow h 2).consW

/-- The counter of the paid stack of a word ending in a one bit. -/
theorem cval_TW_Y (u : List RB) : cval (TW (u ++ [.Y])) = 2 * cval (TW u) + 1 := by
  rw [TW_Y]; rfl

theorem cval_TW_V (u : List RB) : cval (TW (u ++ [.V])) = 2 * cval (TW u) := by
  rw [TW_V]; rfl

theorem cval_TW_X {u : List RB} (h : CStack (TW u)) (h2 : 2 ≤ cval (TW u)) :
    cval (TW (u ++ [.X])) = (cval (TW u) - 2) / 2 := by
  rw [TW_X, cval_W, cval_dpow h 2 h2]

/-! ## The reverse-debt rules -/

variable {u : List RB} {n : ℕ}

/-- A final one bit with an even debt: the scan stops. -/
theorem ready_Y_even (h : n % 2 = 0) : Ready (dpow n (TW (u ++ [.Y]))) := by
  rw [TW_Y]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Ready.zero _
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨(n - 2) / 2, by omega⟩
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, dpow_succ', cdec_Z, dpow_X_odd]
    exact Ready.zero _

/-- A final one bit with an odd debt: the scan strips the zero bit it has
become, and the debt is halved. -/
theorem ready_Y_odd (h : n % 2 = 1) (ih : Ready (dpow ((n - 1) / 2) (TW u))) :
    Ready (dpow n (TW (u ++ [.Y]))) := by
  rw [TW_Y]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨(n - 1) / 2, by omega⟩
  rw [show 2 * k + 1 = (2 * k) + 1 by ring, dpow_succ', cdec_Z, dpow_X_even]
  refine Ready.bit ?_
  simpa using ih

/-- A final zero bit with an odd debt: the scan stops. -/
theorem ready_V_odd (h : n % 2 = 1) : Ready (dpow n (TW (u ++ [.V]))) := by
  rw [TW_V]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨(n - 1) / 2, by omega⟩
  rw [dpow_X_odd]
  exact Ready.zero _

/-- A final zero bit with an even debt: the scan strips it, and the debt is
halved. -/
theorem ready_V_even (h : n % 2 = 0) (ih : Ready (dpow (n / 2) (TW u))) :
    Ready (dpow n (TW (u ++ [.V]))) := by
  rw [TW_V]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rw [dpow_X_even]
  refine Ready.bit ?_
  simpa using ih

/-- A final pop: the scan pays the two decrements of the `1LA` rule, so the
debt `n` becomes `2n+4`, and the counter below must be able to afford it. -/
theorem ready_X (hst : CStack (TW u)) (hv : 2 * n + 4 ≤ cval (TW u))
    (ih : Ready (dpow (2 * n + 4) (TW u))) : Ready (dpow n (TW (u ++ [.X]))) := by
  rw [TW_X, dpow_W, ← dpow_add]
  refine Ready.pop ?_ ?_
  · rw [cval_dpow hst _ (by omega)]
    omega
  · rw [show cdec (cdec (dpow (2 * n + 2) (TW u)))
      = dpow 2 (dpow (2 * n + 2) (TW u)) from rfl, ← dpow_add]
    simpa [show 2 + (2 * n + 2) = 2 * n + 4 by ring] using ih

/-! ## The dual-credit lemma -/

/-- The counter of the paid stack of the decoded word of a stack is its decoded
value. -/
theorem cval_TW_pdec {c : List LB} (hg : Good c) : (cval (TW (pdec c)) : ℤ) = bval c := by
  have h0 : (0 : ℤ) ≤ rrun (pdec c) (cval ([LB.L] : List LB)) := by
    have := hg.head
    have h1 : (0 : ℤ) ≤ (cval c : ℤ) := Int.natCast_nonneg _
    have : bval c = rrun (pdec c) 0 := bval_eq_rrun c
    rw [show cval ([LB.L] : List LB) = 0 from rfl]
    simp only [Nat.cast_zero]
    omega
  obtain ⟨-, -, -, hcv, -, -⟩ :=
    tfold_props (pdec c) (pdec_digs c) (σ := [LB.L]) CStack.base adm_L good_L h0
  rw [TW, hcv, show cval ([LB.L] : List LB) = 0 from rfl, Nat.cast_zero, ← bval_eq_rrun]

theorem CStack_TW_pdec {c : List LB} (hg : Good c) : CStack (TW (pdec c)) := by
  have h0 : (0 : ℤ) ≤ rrun (pdec c) (cval ([LB.L] : List LB)) := by
    have := hg.head
    have h1 : (0 : ℤ) ≤ (cval c : ℤ) := Int.natCast_nonneg _
    have : bval c = rrun (pdec c) 0 := bval_eq_rrun c
    rw [show cval ([LB.L] : List LB) = 0 from rfl]
    simp only [Nat.cast_zero]
    omega
  obtain ⟨hst, -, -, -, -, -⟩ :=
    tfold_props (pdec c) (pdec_digs c) (σ := [LB.L]) CStack.base adm_L good_L h0
  exact hst

/-- The two alternatives of the dual-credit induction: either the counter of
the source stack pays for the debt outright, or the scan is inside a run of
pops, where the debt is even and both the counter and the decoded value carry
enough credit. -/
def Credit (c : List LB) (n : ℕ) : Prop :=
  2 * n + 2 ≤ cval c ∨ (n % 2 = 0 ∧ n + 4 ≤ 2 * cval c ∧ (n : ℤ) + 2 ≤ bval c)

/-- **The dual-credit lemma.**  From a good stack `c` whose counter pays for
the debt, the `1LA` scan of the paid reset stack `T(P(c))`, already charged
with `n` decrements, is safe. -/
theorem dual_credit : ∀ (m : ℕ) (c : List LB), c.length ≤ m → ∀ n : ℕ, Good c →
    Credit c n → Ready (dpow n (TW (pdec c))) := by
  intro m
  induction m with
  | zero =>
      intro c hlen n _ _
      obtain rfl : c = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      simpa using Ready.bottom
  | succ m ih =>
      intro c hlen n hg hcr
      match c with
      | [] => simpa using Ready.bottom
      | .L :: t => simpa using Ready.bottom
      | .J :: t =>
          rw [show pdec (LB.J :: t) = [] from rfl]
          simpa using Ready.bottom
      | .J0 :: t =>
          rw [show pdec (LB.J0 :: t) = [] from rfl]
          simpa using Ready.bottom
      | .J1 :: t =>
          rw [show pdec (LB.J1 :: t) = [] from rfl]
          simpa using Ready.bottom
      | .K0 :: t =>
          rw [show pdec (LB.K0 :: t) = [] from rfl]
          simpa using Ready.bottom
      | .K1 :: t =>
          rw [show pdec (LB.K1 :: t) = [] from rfl]
          simpa using Ready.bottom
      | .X :: t =>
          have hlt : t.length ≤ m := by simp at hlen; omega
          have hgt : Good t := hg.suffix (List.suffix_cons _ _)
          rw [pdec_X]
          by_cases hpar : n % 2 = 0
          · exact ready_Y_even hpar
          · refine ready_Y_odd (by omega) (ih t hlt _ hgt (Or.inl ?_))
            rcases hcr with h | ⟨h0, -, -⟩
            · simp only [cval_X] at h
              omega
            · omega
      | .Z :: t =>
          have hlt : t.length ≤ m := by simp at hlen; omega
          have hgt : Good t := hg.suffix (List.suffix_cons _ _)
          rw [pdec_Z]
          by_cases hpar : n % 2 = 0
          · exact ready_Y_even hpar
          · refine ready_Y_odd (by omega) (ih t hlt _ hgt (Or.inl ?_))
            rcases hcr with h | ⟨h0, -, -⟩
            · simp only [cval_Z] at h
              omega
            · omega
      | .W :: t =>
          have hlt : t.length ≤ m := by simp at hlen; omega
          have hgt : Good t := hg.suffix (List.suffix_cons _ _)
          have hgh : (cval (.W :: t) : ℤ) ≤ bval (.W :: t) := hg.head
          rw [pdec_W]
          by_cases hodd : cval t % 2 = 1
          · rw [if_pos hodd]
            by_cases hpar : n % 2 = 1
            · exact ready_V_odd hpar
            · refine ready_V_even (by omega) (ih t hlt _ hgt (Or.inl ?_))
              have hct : cval (.W :: t) = cval t / 2 := rfl
              rcases hcr with h | ⟨h0, h1, h2⟩
              · rw [hct] at h
                omega
              · rw [hct] at h1
                omega
          · rw [if_neg hodd]
            -- the pop is matched to a zero bit: the credit alternative
            have hct : cval (.W :: t) = cval t / 2 := rfl
            have hbt : bval (.W :: t) = bval t / 2 - 1 := by
              simp only [bval_W, if_neg hodd]
            have hbge : 2 * bval (.W :: t) + 2 ≤ bval t := by
              rw [hbt]
              omega
            have hcge : cval t = 2 * cval (.W :: t) := by omega
            have hleg : 2 * n + 4 ≤ cval (TW (pdec t)) := by
              have hcv := cval_TW_pdec hgt
              rcases hcr with h | ⟨h0, h1, h2⟩
              · have : (cval (.W :: t) : ℤ) ≤ bval (.W :: t) := hgh
                omega
              · omega
            refine ready_X (CStack_TW_pdec hgt) hleg (ih t hlt _ hgt (Or.inr ⟨by omega, ?_, ?_⟩))
            · rcases hcr with h | ⟨h0, h1, h2⟩
              · omega
              · omega
            · rcases hcr with h | ⟨h0, h1, h2⟩
              · have : (cval (.W :: t) : ℤ) ≤ bval (.W :: t) := hgh
                have hc0 : (0 : ℤ) ≤ (cval (.W :: t) : ℤ) := Int.natCast_nonneg _
                push_cast
                omega
              · push_cast
                omega

/-- The dual-credit lemma, in the form it is used. -/
theorem ready_dpow_of_cval {c : List LB} {n : ℕ} (hg : Good c) (h : 2 * n + 2 ≤ cval c) :
    Ready (dpow n (TW (pdec c))) :=
  dual_credit c.length c (le_refl _) n hg (Or.inl h)

end BB25.Prefix
