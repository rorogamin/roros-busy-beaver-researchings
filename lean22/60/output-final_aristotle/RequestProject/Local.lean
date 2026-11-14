import RequestProject.Excursion

/-!
# A reusable framework for *local* macro rules

A **local rule** is a statement of the form

> if the tape carries the word `l` on the cells `a, …, a + l.length - 1`, and the head is
> at `a + k` in state `q`, then after exactly `n` steps the head is at `a + k'` in state
> `q'`, the window carries `l'`, no cell outside the window has been read or written, and
> `l'.length = l.length`.

Such a rule is a purely finite computation, so it can be *evaluated* rather than proved by
hand: this file defines a list-level simulator `lstep` which refuses to leave the window,
proves that it faithfully simulates `step` (`lstep_sound`), and packages the result in the
predicate `Win`.  Concrete local rules are then discharged by `decide`.
-/

namespace BB25

open Function

/-! ### The window tape -/

/-- The tape that carries `l` on `[a, a + l.length)` and agrees with `T` elsewhere. -/
def Tape (T : ℤ → Sym) (a : ℤ) (l : List Sym) : ℤ → Sym := fun i =>
  if a ≤ i ∧ i < a + (l.length : ℤ) then l.getD (i - a).toNat 0 else T i

lemma Tape_in {T : ℤ → Sym} {a : ℤ} {l : List Sym} {k : ℕ} (hk : k < l.length) :
    Tape T a l (a + (k : ℤ)) = l.getD k 0 := by
  have hk' : (k : ℤ) < (l.length : ℤ) := by exact_mod_cast hk
  have : (a + (k : ℤ) - a).toNat = k := by omega
  simp only [Tape]
  rw [if_pos (And.intro (by omega) (by omega)), this]

lemma Tape_out {T : ℤ → Sym} {a : ℤ} {l : List Sym} {i : ℤ}
    (h : i < a ∨ a + (l.length : ℤ) ≤ i) : Tape T a l i = T i := by
  simp only [Tape]
  rw [if_neg (by rcases h with h | h <;> omega)]

lemma Seg_Tape (T : ℤ → Sym) (a : ℤ) (l : List Sym) : Seg (Tape T a l) a l := by
  intro i hi; exact Tape_in hi

/-- If the tape already carries `l` on the window, the window tape *is* the tape. -/
lemma Tape_eq_of_Seg {T : ℤ → Sym} {a : ℤ} {l : List Sym} (h : Seg T a l) :
    Tape T a l = T := by
  funext i
  by_cases hi : a ≤ i ∧ i < a + (l.length : ℤ)
  · obtain ⟨h1, h2⟩ := hi
    have hk : (i - a).toNat < l.length := by omega
    have he : a + (((i - a).toNat : ℕ) : ℤ) = i := by omega
    have := Tape_in (T := T) (a := a) (l := l) hk
    rw [he] at this
    rw [this, ← h _ hk, he]
  · exact Tape_out (by omega)

lemma wr_Tape (T : ℤ → Sym) (a : ℤ) (l : List Sym) (k : ℕ) (v : Sym) (hk : k < l.length) :
    wr (Tape T a l) (a + (k : ℤ)) v = Tape T a (l.set k v) := by
  have hkset : k < (l.set k v).length := by simpa using hk
  funext i
  by_cases hik : i = a + (k : ℤ)
  · subst hik
    rw [wr_self, Tape_in hkset]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by simpa using hk)]
    simp
  · rw [wr_of_ne _ _ _ hik]
    by_cases hi : a ≤ i ∧ i < a + (l.length : ℤ)
    · obtain ⟨h1, h2⟩ := hi
      have hj : (i - a).toNat < l.length := by omega
      have hjset : (i - a).toNat < (l.set k v).length := by simpa using hj
      have he : a + (((i - a).toNat : ℕ) : ℤ) = i := by omega
      have e1 := Tape_in (T := T) (a := a) (l := l) hj
      have e2 := Tape_in (T := T) (a := a) (l := l.set k v) hjset
      rw [he] at e1 e2
      rw [e1, e2]
      have hjne : (i - a).toNat ≠ k := by intro hh; apply hik; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne hjne.symm]
    · rw [Tape_out (by omega), Tape_out (by simp only [List.length_set]; omega)]

/-! ### The list-level simulator -/

lemma cfg_eq {q q' : St} {p p' : ℤ} {T T' : ℤ → Sym}
    (hq : q = q') (hp : p = p') (hT : T = T') : (⟨q, p, T⟩ : Cfg) = ⟨q', p', T'⟩ := by
  subst hq; subst hp; subst hT; rfl

/-- One step of the machine, computed on the window.  It returns `none` whenever the head
would leave the window (or the machine halts), so a successful run certifies that the rule
really is local. -/
def lstep (q : St) (k : ℕ) (l : List Sym) : Option (St × ℕ × List Sym) :=
  if k < l.length then
    match q with
    | .H => none
    | .A =>
        if l.getD k 0 = 0 then (if k + 1 < l.length then some (.B, k + 1, l.set k 1) else none)
        else if l.getD k 0 = 1 then (if 0 < k then some (.A, k - 1, l.set k 2) else none)
        else if l.getD k 0 = 2 then (if 0 < k then some (.B, k - 1, l.set k 3) else none)
        else if l.getD k 0 = 3 then (if 0 < k then some (.B, k - 1, l.set k 4) else none)
        else none
    | .B =>
        if l.getD k 0 = 0 then (if 0 < k then some (.A, k - 1, l) else none)
        else if l.getD k 0 = 1 then (if 0 < k then some (.B, k - 1, l.set k 4) else none)
        else if l.getD k 0 = 2 then (if k + 1 < l.length then some (.A, k + 1, l.set k 3) else none)
        else if l.getD k 0 = 3 then (if 0 < k then some (.A, k - 1, l.set k 4) else none)
        else if l.getD k 0 = 4 then (if k + 1 < l.length then some (.B, k + 1, l.set k 0) else none)
        else none
  else none

/-- `n` steps of the window simulator. -/
def lrun : ℕ → St → ℕ → List Sym → Option (St × ℕ × List Sym)
  | 0, q, k, l => some (q, k, l)
  | n + 1, q, k, l =>
      match lstep q k l with
      | none => none
      | some (q', k', l') => lrun n q' k' l'

lemma lstep_sound {q q' : St} {k k' : ℕ} {l l' : List Sym}
    (h : lstep q k l = some (q', k', l')) (T : ℤ → Sym) (a : ℤ) :
    step ⟨q, a + (k : ℤ), Tape T a l⟩ = ⟨q', a + (k' : ℤ), Tape T a l'⟩ ∧
      l'.length = l.length := by
  unfold lstep at h
  split at h
  swap
  · exact absurd h (by simp)
  rename_i hk
  have hv : Tape T a l (a + (k : ℤ)) = l.getD k 0 := Tape_in hk
  cases q
  case H => exact absurd h (by simp)
  all_goals
    split_ifs at h <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h <;>
      refine ⟨?_, by simp⟩ <;>
      first
        | exact (step_A0 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) (wr_Tape _ _ _ _ _ hk))
        | exact (step_A1 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) (wr_Tape _ _ _ _ _ hk))
        | exact (step_A2 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) (wr_Tape _ _ _ _ _ hk))
        | exact (step_A3 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) (wr_Tape _ _ _ _ _ hk))
        | exact (step_B0 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) rfl)
        | exact (step_B1 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) (wr_Tape _ _ _ _ _ hk))
        | exact (step_B2 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) (wr_Tape _ _ _ _ _ hk))
        | exact (step_B3 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) (wr_Tape _ _ _ _ _ hk))
        | exact (step_B4 _ _ (by rw [hv]; assumption)).trans
            (cfg_eq rfl (by omega) (wr_Tape _ _ _ _ _ hk))

lemma lrun_sound : ∀ (n : ℕ) {q q' : St} {k k' : ℕ} {l l' : List Sym},
    lrun n q k l = some (q', k', l') → ∀ (T : ℤ → Sym) (a : ℤ),
      step^[n] ⟨q, a + (k : ℤ), Tape T a l⟩ = ⟨q', a + (k' : ℤ), Tape T a l'⟩ ∧
        l'.length = l.length := by
  intro n
  induction n with
  | zero =>
      intro q q' k k' l l' h T a
      simp only [lrun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro q q' k k' l l' h T a
      rw [lrun] at h
      rcases hs : lstep q k l with _ | ⟨q1, k1, l1⟩
      · rw [hs] at h; exact absurd h (by simp)
      · rw [hs] at h
        obtain ⟨hstep, hlen⟩ := lstep_sound hs T a
        obtain ⟨hrun, hlen'⟩ := ih h T a
        exact ⟨by rw [iterate_succ_apply, hstep, hrun], by omega⟩

/-! ### The `Win` predicate -/

/-- `Win q q' k k' l l' n`: the head enters the window carrying `l` at offset `k` in state
`q`, and after exactly `n` steps it is at offset `k'` in state `q'`, the window carries
`l'`, and no cell outside the window was read or written. -/
def Win (q q' : St) (k k' : ℕ) (l l' : List Sym) (n : ℕ) : Prop :=
  ∀ (T : ℤ → Sym) (a : ℤ), Seg T a l →
    ∃ T' : ℤ → Sym,
      step^[n] ⟨q, a + (k : ℤ), T⟩ = ⟨q', a + (k' : ℤ), T'⟩ ∧
      Seg T' a l' ∧
      (∀ i : ℤ, i < a ∨ a + (l.length : ℤ) ≤ i → T' i = T i)

theorem Win.of_lrun {q q' : St} {k k' : ℕ} {l l' : List Sym} {n : ℕ}
    (h : lrun n q k l = some (q', k', l')) : Win q q' k k' l l' n := by
  intro T a hs
  refine ⟨Tape T a l', ?_, Seg_Tape _ _ _, ?_⟩
  · have := (lrun_sound n h T a).1
    rwa [Tape_eq_of_Seg hs] at this
  · intro i hi
    have hlen := (lrun_sound n h T a).2
    exact Tape_out (by rw [hlen]; exact hi)

/-- A local rule certifies that the machine does not halt during the steps it covers. -/
theorem Win.no_halt {q q' : St} {k k' : ℕ} {l l' : List Sym} {n : ℕ}
    (h : Win q q' k k' l l' n) (hq : q' ≠ St.H) (T : ℤ → Sym) (a : ℤ) (hs : Seg T a l) :
    ∀ m ≤ n, ¬ Halted (step^[m] ⟨q, a + (k : ℤ), T⟩) := by
  obtain ⟨T', hs', -, -⟩ := h T a hs
  exact not_halted_within (by rw [Halted, hs']; exact hq)

end BB25
