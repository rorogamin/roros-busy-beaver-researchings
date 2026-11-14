/-
# The reverse two-decrement scan of a reset word, over an arbitrary base

`LA/Debt.lean` reads the `<B1` scan of a paid reset stack `T(w)` built from the
*empty* stack.  The `0RB` return builds its resets over a base stack `σ` that
is already there, so this file redoes the reading over an arbitrary base.

* The three stack identities `tfoldS_Y`, `tfoldS_V`, `tfoldS_X` say what the
  last letter of a reset word does to the paid stack.

* `ready_dpow_*` are the five reverse-debt rules, stated directly about a
  stack: a zero bit stops an odd debt and halves an even one, a one bit stops
  an even debt and halves an odd one, and a pop turns the debt `n` into
  `2n+4` — which the counter below it must be able to afford.

* `Scan w n a Q` runs those rules over the word `w`, read from the right,
  starting from the debt `n` over a base of counter `a`.  It is `True` as soon
  as the scan stops inside `w`, and otherwise hands the debt it leaves `w` with
  to `Q`.  `ready_scan` turns it into readiness of the paid stack.

So `Scan w n a (fun _ => False)` says "the scan of `w` stops inside `w`", which
is what the generated right words of the sweep have to satisfy, and
`Scan w n a (fun n' => 2 * n' + 2 ≤ cval c)` is the entry point of the
dual-credit lemma.
-/
import RequestProject.BB25.Prefix.RB.Gen

namespace BB25.Prefix

open BB25

/-! ## The last letter of a reset word -/

variable {σ : List LB} {u : List RB} {n : ℕ}

theorem tfoldS_Y (σ : List LB) (u : List RB) : tfold σ (u ++ [.Y]) = .Z :: tfold σ u := by
  rw [tfold_append]; rfl

theorem tfoldS_V (σ : List LB) (u : List RB) : tfold σ (u ++ [.V]) = .X :: tfold σ u := by
  rw [tfold_append]; rfl

theorem tfoldS_X (σ : List LB) (u : List RB) :
    tfold σ (u ++ [.X]) = .W :: dpow 2 (tfold σ u) := by
  rw [tfold_append]
  show cdec (.W :: tfold σ u) = _
  rw [cdec_W]
  rfl

/-! ## The five reverse-debt rules -/

/-- A one bit with an even debt: the scan stops. -/
theorem ready_dpow_consZ_even {s : List LB} (h : n % 2 = 0) : Ready (dpow n (.Z :: s)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Ready.zero _
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨(n - 2) / 2, by omega⟩
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, dpow_succ', cdec_Z, dpow_X_odd]
    exact Ready.zero _

/-- A one bit with an odd debt: the scan strips the zero bit it has become,
and the debt is halved. -/
theorem ready_dpow_consZ_odd {s : List LB} (h : n % 2 = 1)
    (ih : Ready (dpow ((n - 1) / 2) s)) : Ready (dpow n (.Z :: s)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨(n - 1) / 2, by omega⟩
  rw [dpow_succ', cdec_Z, dpow_X_even]
  refine Ready.bit ?_
  simpa using ih

/-- A zero bit with an odd debt: the scan stops. -/
theorem ready_dpow_consX_odd {s : List LB} (h : n % 2 = 1) : Ready (dpow n (.X :: s)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨(n - 1) / 2, by omega⟩
  rw [dpow_X_odd]
  exact Ready.zero _

/-- A zero bit with an even debt: the scan strips it, and the debt is
halved. -/
theorem ready_dpow_consX_even {s : List LB} (h : n % 2 = 0)
    (ih : Ready (dpow (n / 2) s)) : Ready (dpow n (.X :: s)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rw [dpow_X_even]
  refine Ready.bit ?_
  simpa using ih

/-- A pop: the scan pays the two decrements of the `241` rule, so the debt `n`
becomes `2n+4`, and the counter below must be able to afford it. -/
theorem ready_dpow_pop {s : List LB} (hst : CStack s) (hv : 2 * n + 4 ≤ cval s)
    (ih : Ready (dpow (2 * n + 4) s)) : Ready (dpow n (.W :: dpow 2 s)) := by
  rw [dpow_W, ← dpow_add]
  refine Ready.pop ?_ ?_
  · rw [cval_dpow hst _ (by omega)]
    omega
  · rw [show cdec (cdec (dpow (2 * n + 2) s)) = dpow 2 (dpow (2 * n + 2) s) from rfl,
      ← dpow_add]
    simpa [show 2 + (2 * n + 2) = 2 * n + 4 by ring] using ih

/-! ## The scan of a word -/

/-- The reverse scan, on the *reversed* word. -/
def scanRev : List RB → ℕ → ℤ → (ℕ → Prop) → Prop
  | [], n, _, Q => Q n
  | RB.Y :: t, n, a, Q => n % 2 = 0 ∨ (n % 2 = 1 ∧ scanRev t ((n - 1) / 2) a Q)
  | RB.V :: t, n, a, Q => n % 2 = 1 ∨ (n % 2 = 0 ∧ scanRev t (n / 2) a Q)
  | RB.X :: t, n, a, Q => ((2 * n + 4 : ℕ) : ℤ) ≤ rrun t.reverse a ∧ scanRev t (2 * n + 4) a Q
  | _ :: _, _, _, _ => False

/-- **The reverse two-decrement scan of the reset word `w`**, read from the
right, starting from the debt `n` over a base whose counter is `a`.  If the
scan stops inside `w` the predicate holds outright; otherwise `Q` receives the
debt the scan carries into the base. -/
def Scan (w : List RB) (n : ℕ) (a : ℤ) (Q : ℕ → Prop) : Prop := scanRev w.reverse n a Q

variable {a : ℤ} {Q : ℕ → Prop}

@[simp] theorem Scan_nil : Scan [] n a Q ↔ Q n := Iff.rfl

theorem Scan_snoc_Y : Scan (u ++ [.Y]) n a Q ↔
    (n % 2 = 0 ∨ (n % 2 = 1 ∧ Scan u ((n - 1) / 2) a Q)) := by
  simp only [Scan, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rfl

theorem Scan_snoc_V : Scan (u ++ [.V]) n a Q ↔
    (n % 2 = 1 ∨ (n % 2 = 0 ∧ Scan u (n / 2) a Q)) := by
  simp only [Scan, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rfl

theorem Scan_snoc_X : Scan (u ++ [.X]) n a Q ↔
    (((2 * n + 4 : ℕ) : ℤ) ≤ rrun u a ∧ Scan u (2 * n + 4) a Q) := by
  simp only [Scan, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rw [show scanRev (RB.X :: u.reverse) n a Q
    = (((2 * n + 4 : ℕ) : ℤ) ≤ rrun u.reverse.reverse a ∧ scanRev u.reverse (2 * n + 4) a Q)
    from rfl, List.reverse_reverse]

/-- The scan only ever weakens its exit predicate. -/
theorem scanRev_mono : ∀ (t : List RB) (n : ℕ) (a : ℤ) {Q Q' : ℕ → Prop},
    (∀ m, Q m → Q' m) → scanRev t n a Q → scanRev t n a Q' := by
  intro t
  induction t with
  | nil => intro n a Q Q' hQ h; exact hQ n h
  | cons b t ih =>
      intro n a Q Q' hQ h
      match b with
      | .Y =>
          rcases h with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, ih _ _ hQ h2⟩
      | .V =>
          rcases h with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, ih _ _ hQ h2⟩
      | .X => exact ⟨h.1, ih _ _ hQ h.2⟩
      | .R => exact absurd h (by simp [scanRev])
      | .R1 => exact absurd h (by simp [scanRev])
      | .R2 => exact absurd h (by simp [scanRev])
      | .P1 => exact absurd h (by simp [scanRev])
      | .P2 => exact absurd h (by simp [scanRev])
      | .U => exact absurd h (by simp [scanRev])
      | .F => exact absurd h (by simp [scanRev])
      | .G => exact absurd h (by simp [scanRev])

theorem Scan.mono {w : List RB} {Q' : ℕ → Prop} (hQ : ∀ m, Q m → Q' m)
    (h : Scan w n a Q) : Scan w n a Q' :=
  scanRev_mono w.reverse n a hQ h

/-- A scan that stops inside the word implies any other exit condition. -/
theorem Scan.of_stops {w : List RB} (h : Scan w n a (fun _ => False)) : Scan w n a Q :=
  h.mono (fun _ hf => hf.elim)

/-! ## From the scan to readiness -/

/-- **The reverse scan computes readiness of a paid reset stack.** -/
theorem ready_scan : ∀ (w : List RB), Digs w → ∀ {σ : List LB} {n : ℕ} {Q : ℕ → Prop},
    CStack σ → Adm σ → Good σ → 0 ≤ rrun w (cval σ) →
    Scan w n (cval σ) Q → (∀ n', Q n' → Ready (dpow n' σ)) →
    Ready (dpow n (tfold σ w)) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro _ σ n Q _ _ _ _ hs hQ
      exact hQ n hs
  | append_singleton u b ih =>
      intro hw σ n Q hst hadm hg hcl hs hQ
      obtain ⟨hwu, hb1⟩ := hw.of_append
      have hb : Dig b := hb1 b (by simp)
      have hclu : 0 ≤ rrun u (cval σ) := rrun_nonneg_of_nonneg hb1 hcl
      obtain ⟨hstu, hadmu, hgu, hcvu, -, -⟩ := tfold_props u hwu hst hadm hg hclu
      rcases hb with rfl | rfl | rfl
      · -- a one bit
        rw [tfoldS_Y]
        rcases Scan_snoc_Y.mp hs with h | ⟨h1, h2⟩
        · exact ready_dpow_consZ_even h
        · exact ready_dpow_consZ_odd h1 (ih hwu hst hadm hg hclu h2 hQ)
      · -- a zero bit
        rw [tfoldS_V]
        rcases Scan_snoc_V.mp hs with h | ⟨h1, h2⟩
        · exact ready_dpow_consX_odd h
        · exact ready_dpow_consX_even h1 (ih hwu hst hadm hg hclu h2 hQ)
      · -- a pop
        rw [tfoldS_X]
        obtain ⟨hsup, h2⟩ := Scan_snoc_X.mp hs
        refine ready_dpow_pop hstu ?_ (ih hwu hst hadm hg hclu h2 hQ)
        have : ((2 * n + 4 : ℕ) : ℤ) ≤ (cval (tfold σ u) : ℤ) := by rw [hcvu]; exact hsup
        exact_mod_cast this

/-- The form in which the scan is used: a scan that stops inside the word makes
the paid stack ready. -/
theorem ready_tfold_of_stops {w : List RB} (hw : Digs w) {σ : List LB}
    (hst : CStack σ) (hadm : Adm σ) (hg : Good σ) (hcl : 0 ≤ rrun w (cval σ))
    (hs : Scan w 0 (cval σ) (fun _ => False)) : Ready (tfold σ w) :=
  ready_scan w hw hst hadm hg hcl hs (fun _ hf => hf.elim)

end BB25.Prefix
