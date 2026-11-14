/-
# The excursion calculus

`RequestProject/Transits.lean` proves the individual passages of the head
through a token.  To talk about *counter dynamics* we must be able to compose
them: a token passes the signal on to its right neighbour, waits for it to come
back, possibly passes it on again, and only then returns the signal to its own
left neighbour.  This file sets up the notion that makes such composition legal,
and restates every rule of the table in it.

The central definition is `Exc p t u`:

> the head, arriving at cell `p` in state `A` and moving right, eventually
> leaves the half-tape `[p, ∞)` again, arriving at cell `p - 1` in state `A`;
> while doing so it changes no cell to the left of `p`, and it leaves the cells
> from `p` rightwards as prescribed by `u`.

Two points make `Exc` composable:

* it is quantified over *all* tapes agreeing with `t` from `p` rightwards, so an
  `Exc` fact may be used inside any left context, and
* both arguments only matter from `p` rightwards (`Exc_congr`).

`ExcN k p t u` is the `k`-fold iteration: `k` successive signals arrive at `p`
from the left, and `u` is the state of the half-tape after the `k`-th one has
been returned.
-/
import RequestProject.Transits

namespace ShiftOverflow

/-! ## Reachability -/

/-- `Reaches c c'`: the machine started in `c` runs (without halting) to `c'`. -/
def Reaches (c c' : Cfg) : Prop := ∃ n, steps n c = some c'

theorem steps_add (m n : ℕ) (c : Cfg) : steps (m + n) c = (steps m c).bind (steps n) := by
  induction m generalizing c with
  | zero => simp [steps]
  | succ k ih =>
      have e : k + 1 + n = (k + n) + 1 := by omega
      rw [e]
      cases h : step c with
      | none => simp [steps, h]
      | some c' => simp [steps, h, ih]

theorem Reaches.of_steps {n : ℕ} {c c' : Cfg} (h : steps n c = some c') : Reaches c c' :=
  ⟨n, h⟩

theorem Reaches.trans {c c' c'' : Cfg} (h : Reaches c c') (h' : Reaches c' c'') :
    Reaches c c'' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨n, hn⟩ := h'
  exact ⟨m + n, by rw [steps_add, hm]; simpa using hn⟩

/-! ## The blank tape -/

/-- The blank tape. -/
def blank : ℤ → ℕ := fun _ => 0

/-- The machine's initial configuration: blank tape, head at `0`, state `A`. -/
def init : Cfg := ⟨blank, 0, .A⟩

/-- If the machine has not halted after `n` steps, it has not halted after any
smaller number of steps. -/
theorem steps_ne_none_of_le {c : Cfg} {j n : ℕ} (hj : j ≤ n) (h : steps n c ≠ none) :
    steps j c ≠ none := by
  intro hjn
  apply h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [steps_add, hjn]
  rfl

/-! ## Excursions -/

/-- `patch p s u` is the tape that agrees with `u` from `p` rightwards and with
`s` strictly to the left of `p`. -/
def patch (p : ℤ) (s u : ℤ → ℕ) : ℤ → ℕ := fun i => if p ≤ i then u i else s i

/-- **One excursion.**  The head arrives at cell `p` in state `A` moving right,
and eventually leaves to the left of `p`, arriving at `p - 1` in state `A`,
having changed only cells `≥ p`, which it leaves as in `u`.  The statement is
quantified over the left context, which is therefore irrelevant. -/
def Exc (p : ℤ) (t u : ℤ → ℕ) : Prop :=
  ∀ s : ℤ → ℕ, (∀ i, p ≤ i → s i = t i) →
    Reaches ⟨s, p, .A⟩ ⟨patch p s u, p - 1, .A⟩

theorem Exc_congr {p : ℤ} {t t' u u' : ℤ → ℕ} (ht : ∀ i, p ≤ i → t' i = t i)
    (hu : ∀ i, p ≤ i → u' i = u i) (h : Exc p t u) : Exc p t' u' := by
  intro s hs
  have hs' : ∀ i, p ≤ i → s i = t i := fun i hi => (hs i hi).trans (ht i hi)
  have := h s hs'
  have e : patch p s u = patch p s u' := by
    funext i
    by_cases hi : p ≤ i
    · simp [patch, hi, hu i hi]
    · simp [patch, hi]
  rwa [← e]

/-- `ExcN k p t u`: `k` successive signals arrive at `p`, the last one leaving
the half-tape in the state `u`. -/
def ExcN : ℕ → ℤ → (ℤ → ℕ) → (ℤ → ℕ) → Prop
  | 0, p, t, u => ∀ i, p ≤ i → u i = t i
  | (k + 1), p, t, u => ∃ w, Exc p t w ∧ ExcN k p w u

theorem ExcN_congr : ∀ {k : ℕ} {p : ℤ} {t t' u u' : ℤ → ℕ}, (∀ i, p ≤ i → t' i = t i) →
    (∀ i, p ≤ i → u' i = u i) → ExcN k p t u → ExcN k p t' u'
  | 0, p, t, t', u, u', ht, hu, h => by
      intro i hi
      rw [hu i hi, h i hi, ht i hi]
  | (k + 1), p, t, t', u, u', ht, hu, h => by
      obtain ⟨w, h1, h2⟩ := h
      exact ⟨w, Exc_congr ht (fun _ _ => rfl) h1, ExcN_congr (fun _ _ => rfl) hu h2⟩

theorem ExcN_split : ∀ (a b : ℕ) {p : ℤ} {t u : ℤ → ℕ}, ExcN (a + b) p t u →
    ∃ w, ExcN a p t w ∧ ExcN b p w u
  | 0, b, p, t, u, h => ⟨t, fun _ _ => rfl, by simpa using h⟩
  | (a + 1), b, p, t, u, h => by
      obtain ⟨z, h1, h2⟩ := (by simpa [Nat.succ_add] using h : ExcN ((a + b) + 1) p t u)
      obtain ⟨w, hw1, hw2⟩ := ExcN_split a b h2
      exact ⟨w, ⟨z, h1, hw1⟩, hw2⟩

/-! ## The rules of the table, as excursion facts

Each theorem below is the corresponding entry of row `A` of the longitudinal
table, in composable form.  The hypotheses `Exc (p+2) t u` say what the token to
the right does with the signals that this token sends it. -/

theorem patch_eq_upd2 {p : ℤ} {s u : ℤ → ℕ} (a b : ℕ)
    (h : ∀ i, p + 2 ≤ i → u i = s i) :
    patch p s (upd2 u p a b) = upd2 s p a b := by
  funext i
  unfold patch upd2 Function.update
  by_cases h0 : i = p
  · subst h0; simp
  · by_cases h1 : i = p + 1
    · subst h1; simp
    · have : ¬ (i = p + 1) := h1
      by_cases hp : p ≤ i
      · have : p + 2 ≤ i := by omega
        simp [h0, h1, hp, h i this]
      · simp [h0, h1, hp]

theorem patch_eq_upd1 {p : ℤ} {s u : ℤ → ℕ} (a : ℕ)
    (h : ∀ i, p + 1 ≤ i → u i = s i) :
    patch p s (upd1 u p a) = upd1 s p a := by
  funext i
  unfold patch upd1 Function.update
  by_cases h0 : i = p
  · subst h0; simp
  · by_cases hp : p ≤ i
    · have : p + 1 ≤ i := by omega
      simp [h0, hp, h i this]
    · simp [h0, hp]

theorem upd2_patch_eq {p : ℤ} {s w v : ℤ → ℕ} (a b : ℕ)
    (hl : ∀ i, i < p → w i = s i) (hr : ∀ i, p + 2 ≤ i → w i = v i) :
    upd2 w p a b = patch p s (upd2 v p a b) := by
  funext i
  unfold patch upd2 Function.update
  by_cases h0 : i = p
  · subst h0; simp
  · by_cases h1 : i = p + 1
    · subst h1; simp
    · by_cases hp : p ≤ i
      · have h2 : p + 2 ≤ i := by omega
        simp [h0, h1, hp, hr i h2]
      · simp [h0, h1, hp, hl i (by omega)]

theorem upd2_apply {p : ℤ} {s : ℤ → ℕ} {a b : ℕ} (i : ℤ) :
    upd2 s p a b i = if i = p + 1 then b else if i = p then a else s i := by
  unfold upd2 Function.update
  by_cases h1 : i = p + 1 <;> by_cases h0 : i = p <;> simp [h0, h1]

theorem upd2_right {p : ℤ} {s : ℤ → ℕ} {a b : ℕ} {i : ℤ} (hi : p + 2 ≤ i) :
    upd2 s p a b i = s i := by
  rw [upd2_apply]
  rw [if_neg (by omega), if_neg (by omega)]

theorem upd2_left {p : ℤ} {s : ℤ → ℕ} {a b : ℕ} {i : ℤ} (hi : i < p) :
    upd2 s p a b i = s i := by
  rw [upd2_apply]
  rw [if_neg (by omega), if_neg (by omega)]

theorem upd2_fst {p : ℤ} {s : ℤ → ℕ} {a b : ℕ} : upd2 s p a b p = a := by
  rw [upd2_apply]; rw [if_neg (by omega), if_pos rfl]

theorem upd2_snd {p : ℤ} {s : ℤ → ℕ} {a b : ℕ} : upd2 s p a b (p + 1) = b := by
  rw [upd2_apply]; rw [if_pos rfl]

theorem patch_right {p : ℤ} {s u : ℤ → ℕ} {i : ℤ} (hi : p ≤ i) :
    patch p s u i = u i := by simp [patch, hi]

theorem patch_left {p : ℤ} {s u : ℤ → ℕ} {i : ℤ} (hi : i < p) :
    patch p s u i = s i := by
  have : ¬ p ≤ i := by omega
  simp [patch, this]

theorem patch_eq_upd3 {p : ℤ} {s u : ℤ → ℕ} (a b c : ℕ)
    (h : ∀ i, p + 3 ≤ i → u i = s i) :
    patch p s (upd3 u p a b c) = upd3 s p a b c := by
  funext i
  unfold patch upd3 Function.update
  by_cases h0 : i = p
  · subst h0; simp
  · by_cases h1 : i = p + 1
    · subst h1; simp
    · by_cases h2 : i = p + 2
      · subst h2; simp
      · by_cases hp : p ≤ i
        · have : p + 3 ≤ i := by omega
          simp [h0, h1, h2, hp, h i this]
        · simp [h0, h1, h2, hp]

/-- `A · 2 0 = 2 3`: the signal is absorbed; the block becomes `2 3`. -/
theorem exc_20 {p : ℤ} {t : ℤ → ℕ} (h0 : t p = 2) (h1 : t (p + 1) = 0) :
    Exc p t (upd2 t p 2 3) := by
  intro s hs
  refine Reaches.of_steps (n := 5) ?_
  have e := transitL_20 s p (by rw [hs p (le_refl p)]; exact h0)
      (by rw [hs (p + 1) (by omega)]; exact h1)
  rw [e]
  have : patch p s (upd2 t p 2 3) = upd2 s p 2 3 :=
    patch_eq_upd2 2 3 (fun i hi => (hs i (by omega)).symm)
  simp [this]

/-- `A · 0 0 = 2 1`: the signal is absorbed; the block becomes `2 1`. -/
theorem exc_00 {p : ℤ} {t : ℤ → ℕ} (h0 : t p = 0) (h1 : t (p + 1) = 0) :
    Exc p t (upd2 t p 2 1) := by
  intro s hs
  refine Reaches.of_steps (n := 3) ?_
  have e := transitL_00 s p (by rw [hs p (le_refl p)]; exact h0)
      (by rw [hs (p + 1) (by omega)]; exact h1)
  rw [e]
  have : patch p s (upd2 t p 2 1) = upd2 s p 2 1 :=
    patch_eq_upd2 2 1 (fun i hi => (hs i (by omega)).symm)
  simp [this]

/-- `A · 1 = 2`: a loose `1` absorbs the signal and becomes `2`. -/
theorem exc_1 {p : ℤ} {t : ℤ → ℕ} (h0 : t p = 1) : Exc p t (upd1 t p 2) := by
  intro s hs
  refine Reaches.of_steps (n := 1) ?_
  have e := transitL_1 s p (by rw [hs p (le_refl p)]; exact h0)
  rw [e]
  have : patch p s (upd1 t p 2) = upd1 s p 2 :=
    patch_eq_upd1 2 (fun i hi => (hs i (by omega)).symm)
  simp [this]

/-- `A · 4 = 0`: a loose `4` absorbs the signal and becomes `0`. -/
theorem exc_4 {p : ℤ} {t : ℤ → ℕ} (h0 : t p = 4) : Exc p t (upd1 t p 0) := by
  intro s hs
  refine Reaches.of_steps (n := 1) ?_
  have e := transitL_4 s p (by rw [hs p (le_refl p)]; exact h0)
  rw [e]
  have : patch p s (upd1 t p 0) = upd1 s p 0 :=
    patch_eq_upd1 0 (fun i hi => (hs i (by omega)).symm)
  simp [this]

/-! ### The tokens that pass the signal on -/

/-- `A · 2 2 = 2 2 A A`: the block passes the signal on **twice** — the second
copy is sent only after the first one has come all the way back — and is left
unchanged.  This is the doubling step of the binary counter. -/
theorem exc_22 {p : ℤ} {t u v : ℤ → ℕ} (h0 : t p = 2) (h1 : t (p + 1) = 2)
    (H1 : Exc (p + 2) t u) (H2 : Exc (p + 2) u v) :
    Exc p t (upd2 v p 2 2) := by
  intro s hs
  have hsp : s p = 2 := by rw [hs p (le_refl p)]; exact h0
  have hsp1 : s (p + 1) = 2 := by rw [hs (p + 1) (by omega)]; exact h1
  have e1 : steps 2 ⟨s, p, .A⟩ = some ⟨upd2 s p 0 1, p + 2, .A⟩ := transitL_22 s p hsp hsp1
  have hs1 : ∀ i, p + 2 ≤ i → (upd2 s p 0 1) i = t i := by
    intro i hi; rw [upd2_right hi]; exact hs i (by omega)
  have r1 := H1 _ hs1
  rw [show p + 2 - 1 = p + 1 from by ring] at r1
  set s2 := patch (p + 2) (upd2 s p 0 1) u with hs2
  have hs2p : s2 p = 0 := by
    rw [hs2, patch_left (by omega), upd2_fst]
  have hs2p1 : s2 (p + 1) = 1 := by
    rw [hs2, patch_left (by omega), upd2_snd]
  have e2 : steps 3 ⟨s2, p + 1, .A⟩ = some ⟨upd2 s2 p 1 1, p + 2, .A⟩ :=
    transitR_01 s2 p hs2p hs2p1
  have hs3 : ∀ i, p + 2 ≤ i → (upd2 s2 p 1 1) i = u i := by
    intro i hi; rw [upd2_right hi, hs2, patch_right (by omega)]
  have r2 := H2 _ hs3
  rw [show p + 2 - 1 = p + 1 from by ring] at r2
  set s4 := patch (p + 2) (upd2 s2 p 1 1) v with hs4
  have hs4p : s4 p = 1 := by
    rw [hs4, patch_left (by omega), upd2_fst]
  have hs4p1 : s4 (p + 1) = 1 := by
    rw [hs4, patch_left (by omega), upd2_snd]
  have e3 : steps 2 ⟨s4, p + 1, .A⟩ = some ⟨upd2 s4 p 2 2, p - 1, .A⟩ :=
    transitR_11 s4 p hs4p hs4p1
  have hfin : upd2 s4 p 2 2 = patch p s (upd2 v p 2 2) := by
    refine upd2_patch_eq 2 2 (fun i hi => ?_) (fun i hi => ?_)
    · rw [hs4, patch_left (by omega), upd2_left hi, hs2, patch_left (by omega), upd2_left hi]
    · rw [hs4, patch_right (by omega)]
  rw [hfin] at e3
  exact ((Reaches.of_steps e1).trans r1).trans ((Reaches.of_steps e2).trans
    (r2.trans (Reaches.of_steps e3)))

/-- `A · 2 1 = 2 0 A`: the block passes the signal on once and becomes `2 0`. -/
theorem exc_21 {p : ℤ} {t u : ℤ → ℕ} (h0 : t p = 2) (h1 : t (p + 1) = 1)
    (H : Exc (p + 2) t u) : Exc p t (upd2 u p 2 0) := by
  intro s hs
  have hsp : s p = 2 := by rw [hs p (le_refl p)]; exact h0
  have hsp1 : s (p + 1) = 1 := by rw [hs (p + 1) (by omega)]; exact h1
  have e1 : steps 4 ⟨s, p, .A⟩ = some ⟨upd2 s p 1 4, p + 2, .A⟩ := transitL_21 s p hsp hsp1
  have hs1 : ∀ i, p + 2 ≤ i → (upd2 s p 1 4) i = t i := by
    intro i hi; rw [upd2_right hi]; exact hs i (by omega)
  have r1 := H _ hs1
  rw [show p + 2 - 1 = p + 1 from by ring] at r1
  set s2 := patch (p + 2) (upd2 s p 1 4) u with hs2
  have hs2p : s2 p = 1 := by
    rw [hs2, patch_left (by omega), upd2_fst]
  have hs2p1 : s2 (p + 1) = 4 := by
    rw [hs2, patch_left (by omega), upd2_snd]
  have e2 : steps 2 ⟨s2, p + 1, .A⟩ = some ⟨upd2 s2 p 2 0, p - 1, .A⟩ :=
    transitR_14 s2 p hs2p hs2p1
  have hfin : upd2 s2 p 2 0 = patch p s (upd2 u p 2 0) := by
    refine upd2_patch_eq 2 0 (fun i hi => ?_) (fun i hi => ?_)
    · rw [hs2, patch_left (by omega), upd2_left hi]
    · rw [hs2, patch_right (by omega)]
  rw [hfin] at e2
  exact ((Reaches.of_steps e1).trans r1).trans (Reaches.of_steps e2)

/-- `A · 2 3 = 2 1 A`: the block passes the signal on once and becomes `2 1`. -/
theorem exc_23 {p : ℤ} {t u : ℤ → ℕ} (h0 : t p = 2) (h1 : t (p + 1) = 3)
    (H : Exc (p + 2) t u) : Exc p t (upd2 u p 2 1) := by
  intro s hs
  have hsp : s p = 2 := by rw [hs p (le_refl p)]; exact h0
  have hsp1 : s (p + 1) = 3 := by rw [hs (p + 1) (by omega)]; exact h1
  have e1 : steps 2 ⟨s, p, .A⟩ = some ⟨upd2 s p 0 4, p + 2, .A⟩ := transitL_23 s p hsp hsp1
  have hs1 : ∀ i, p + 2 ≤ i → (upd2 s p 0 4) i = t i := by
    intro i hi; rw [upd2_right hi]; exact hs i (by omega)
  have r1 := H _ hs1
  rw [show p + 2 - 1 = p + 1 from by ring] at r1
  set s2 := patch (p + 2) (upd2 s p 0 4) u with hs2
  have hs2p : s2 p = 0 := by
    rw [hs2, patch_left (by omega), upd2_fst]
  have hs2p1 : s2 (p + 1) = 4 := by
    rw [hs2, patch_left (by omega), upd2_snd]
  have e2 : steps 4 ⟨s2, p + 1, .A⟩ = some ⟨upd2 s2 p 2 1, p - 1, .A⟩ :=
    transitR_04 s2 p hs2p hs2p1
  have hfin : upd2 s2 p 2 1 = patch p s (upd2 u p 2 1) := by
    refine upd2_patch_eq 2 1 (fun i hi => ?_) (fun i hi => ?_)
    · rw [hs2, patch_left (by omega), upd2_left hi]
    · rw [hs2, patch_right (by omega)]
  rw [hfin] at e2
  exact ((Reaches.of_steps e1).trans r1).trans (Reaches.of_steps e2)

/-- `A · 0 2 = 2 2 A`: the block passes the signal on once and becomes `2 2`,
i.e. a fresh block joins the binary counter. -/
theorem exc_02 {p : ℤ} {t u : ℤ → ℕ} (h0 : t p = 0) (h1 : t (p + 1) = 2)
    (H : Exc (p + 2) t u) : Exc p t (upd2 u p 2 2) := by
  intro s hs
  have hsp : s p = 0 := by rw [hs p (le_refl p)]; exact h0
  have hsp1 : s (p + 1) = 2 := by rw [hs (p + 1) (by omega)]; exact h1
  have e1 : steps 2 ⟨s, p, .A⟩ = some ⟨upd2 s p 1 1, p + 2, .A⟩ := transitL_02 s p hsp hsp1
  have hs1 : ∀ i, p + 2 ≤ i → (upd2 s p 1 1) i = t i := by
    intro i hi; rw [upd2_right hi]; exact hs i (by omega)
  have r1 := H _ hs1
  rw [show p + 2 - 1 = p + 1 from by ring] at r1
  set s2 := patch (p + 2) (upd2 s p 1 1) u with hs2
  have hs2p : s2 p = 1 := by
    rw [hs2, patch_left (by omega), upd2_fst]
  have hs2p1 : s2 (p + 1) = 1 := by
    rw [hs2, patch_left (by omega), upd2_snd]
  have e2 : steps 2 ⟨s2, p + 1, .A⟩ = some ⟨upd2 s2 p 2 2, p - 1, .A⟩ :=
    transitR_11 s2 p hs2p hs2p1
  have hfin : upd2 s2 p 2 2 = patch p s (upd2 u p 2 2) := by
    refine upd2_patch_eq 2 2 (fun i hi => ?_) (fun i hi => ?_)
    · rw [hs2, patch_left (by omega), upd2_left hi]
    · rw [hs2, patch_right (by omega)]
  rw [hfin] at e2
  exact ((Reaches.of_steps e1).trans r1).trans (Reaches.of_steps e2)

/-- `A · 2 2 3 = 2 0 0`: the three-cell token `2 2 3` absorbs the signal and
settles to the cells `2 0 0`. -/
theorem exc_223 {p : ℤ} {t : ℤ → ℕ} (h0 : t p = 2) (h1 : t (p + 1) = 2) (h2 : t (p + 2) = 3) :
    Exc p t (upd3 t p 2 0 0) := by
  intro s hs
  refine Reaches.of_steps (n := 9) ?_
  have e := transitL_223 s p (by rw [hs p (le_refl p)]; exact h0)
      (by rw [hs (p + 1) (by omega)]; exact h1) (by rw [hs (p + 2) (by omega)]; exact h2)
  rw [e]
  have : patch p s (upd3 t p 2 0 0) = upd3 s p 2 0 0 :=
    patch_eq_upd3 2 0 0 (fun i hi => (hs i (by omega)).symm)
  simp [this]

/-- `A · 0 2 3 = 2 3 4`: the three-cell token `0 2 3` absorbs the signal and
settles to the cells `2 3 4` — the only way a loose `4` is ever created. -/
theorem exc_023 {p : ℤ} {t : ℤ → ℕ} (h0 : t p = 0) (h1 : t (p + 1) = 2) (h2 : t (p + 2) = 3) :
    Exc p t (upd3 t p 2 3 4) := by
  intro s hs
  refine Reaches.of_steps (n := 5) ?_
  have e := transitL_023 s p (by rw [hs p (le_refl p)]; exact h0)
      (by rw [hs (p + 1) (by omega)]; exact h1) (by rw [hs (p + 2) (by omega)]; exact h2)
  rw [e]
  have : patch p s (upd3 t p 2 3 4) = upd3 s p 2 3 4 :=
    patch_eq_upd3 2 3 4 (fun i hi => (hs i (by omega)).symm)
  simp [this]

end ShiftOverflow
