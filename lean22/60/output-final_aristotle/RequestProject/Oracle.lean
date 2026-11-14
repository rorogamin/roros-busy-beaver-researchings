module

public import RequestProject.Rect

/-!
# Soundness of finite rectangles for the actual machine

We compare the machine with an *oracle machine* `ostep lo`: it behaves exactly like `step`,
except that when the head arrives on cell `lo - 1` (just left of a window whose left end is
`lo`), it consults a list of letters: the next letter must have the current state as its entry
state, and the head is put back on `lo` in the letter's exit state.  (Otherwise, or if the
list is exhausted, the oracle machine goes to the absorbing state `H`.)

The main theorem `rect_sound` says that a rectangle `Rect S [r] L T` is realised by the oracle
machine: started on the rightmost cell of a window carrying `S`, in state `r.ent`, with the
oracle list starting with `L`, it leaves the window on the right, in state `r.ext`, with the
window now carrying `T`, having consumed exactly `L`.
-/

@[expose] public section

namespace BB25
namespace LR

/-! ### Iteration and tape writes -/

/-- `iter f k x` applies `f` to `x` exactly `k` times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => iter f k (f x)

@[inherit_doc] scoped notation:max f "^[" n "]" => iter f n

theorem iter_succ {α : Type} (f : α → α) (k : Nat) (x : α) : f^[k + 1] x = f^[k] (f x) := rfl

theorem iter_one {α : Type} (f : α → α) (x : α) : f^[1] x = f x := rfl

theorem iter_add {α : Type} (f : α → α) (m n : Nat) (x : α) :
    f^[m + n] x = f^[m] (f^[n] x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

theorem iter_succ' {α : Type} (f : α → α) (k : Nat) (x : α) : f^[k + 1] x = f (f^[k] x) := by
  rw [Nat.add_comm]; exact iter_add f 1 k x

@[simp] theorem wr_self (T : Int → Sym) (p : Int) (v : Sym) : wr T p v p = v := by
  simp [wr]

@[simp] theorem wr_of_ne (T : Int → Sym) (p : Int) (v : Sym) {i : Int} (h : i ≠ p) :
    wr T p v i = T i := by
  simp [wr, h]

/-! ### The oracle machine -/

/-- A configuration of the oracle machine: a configuration and the remaining oracle word. -/
abbrev OCfg := Cfg × List Letter

/-- One step of the oracle machine with left window end `lo`. -/
def ostep (lo : Int) (x : OCfg) : OCfg :=
  if x.1.pos = lo - 1 then
    match x.2 with
    | [] => (⟨St.H, x.1.pos, x.1.tape⟩, [])
    | m :: O => if x.1.st = m.ent then (⟨m.ext, lo, x.1.tape⟩, O)
                else (⟨St.H, x.1.pos, x.1.tape⟩, m :: O)
  else (step x.1, x.2)

theorem ostep_of_ne {lo : Int} {x : OCfg} (h : x.1.pos ≠ lo - 1) : ostep lo x = (step x.1, x.2) := by
  simp [ostep, h]

theorem ostep_oracle {lo : Int} (m : Letter) (τ : Int → Sym) (O : List Letter) :
    ostep lo (⟨m.ent, lo - 1, τ⟩, m :: O) = (⟨m.ext, lo, τ⟩, O) := by
  simp [ostep]

theorem Letter.ent_ne_H (m : Letter) : m.ent ≠ St.H := by cases m <;> simp [Letter.ent]

/-- The halting state is absorbing for the oracle machine too. -/
theorem ostep_H {lo : Int} {x : OCfg} (h : x.1.st = St.H) : (ostep lo x).1.st = St.H := by
  obtain ⟨⟨st, p, τ⟩, O⟩ := x
  simp only at h
  subst h
  unfold ostep
  split
  · rcases O with _ | ⟨m, O⟩
    · rfl
    · have := Letter.ent_ne_H m
      simp [Ne.symm this]
  · rfl

theorem ostep_iterate_H {lo : Int} {x : OCfg} (h : x.1.st = St.H) (k : Nat) :
    ((ostep lo)^[k] x).1.st = St.H := by
  induction k generalizing x with
  | zero => exact h
  | succ k ih => rw [iter_succ]; exact ih (ostep_H h)

/-! ### Agreement of `step` with the table `tr` -/

theorem wr_same {τ : Int → Sym} {p : Int} {v : Sym} (h : τ p = v) : wr τ p v = τ := by
  funext i
  by_cases hi : i = p
  · subst hi; simp [h]
  · simp [hi]

theorem step_right {X : St} {s w : Sym} {Y : St} {τ : Int → Sym} {p : Int}
    (h : tr X s = some (w, true, Y)) (hs : τ p = s) :
    step ⟨X, p, τ⟩ = ⟨Y, p + 1, wr τ p w⟩ := by
  obtain ⟨v, hv⟩ := s
  unfold step; simp only [hs]
  cases X <;> rcases v with _|_|_|_|_|v <;> simp [tr] at h <;>
    (try omega) <;> obtain ⟨rfl, rfl⟩ := h <;> rfl

theorem step_left {X : St} {s w : Sym} {Y : St} {τ : Int → Sym} {p : Int}
    (h : tr X s = some (w, false, Y)) (hs : τ p = s) :
    step ⟨X, p, τ⟩ = ⟨Y, p - 1, wr τ p w⟩ := by
  obtain ⟨v, hv⟩ := s
  unfold step; simp only [hs]
  cases X <;> rcases v with _|_|_|_|_|v <;> simp [tr] at h <;>
    (try omega) <;> obtain ⟨rfl, rfl⟩ := h
  all_goals first
    | rfl
    | (show (⟨St.A, p - 1, τ⟩ : Cfg) = _; congr 1; funext i; unfold wr; split <;> simp_all)

/-! ### Tape windows (listed right to left) -/

/-- `Holds τ p S`: the cells `p, p-1, …` of `τ` carry the list `S`. -/
def Holds (τ : Int → Sym) : Int → List Sym → Prop
  | _, [] => True
  | p, s :: S => τ p = s ∧ Holds τ (p - 1) S

/-- `wl τ p T`: overwrite the cells `p, p-1, …` of `τ` with the list `T`. -/
def wl : (Int → Sym) → Int → List Sym → (Int → Sym)
  | τ, _, [] => τ
  | τ, p, t :: T => wl (wr τ p t) (p - 1) T

theorem wr_wr (τ : Int → Sym) (p : Int) (u v : Sym) : wr (wr τ p u) p v = wr τ p v := by
  funext i; by_cases hi : i = p <;> simp [wr, hi]

theorem wr_comm (τ : Int → Sym) {p q : Int} (h : p ≠ q) (u v : Sym) :
    wr (wr τ p u) q v = wr (wr τ q v) p u := by
  funext i
  by_cases hp : i = p
  · subst hp; simp [wr, h]
  · by_cases hq : i = q
    · subst hq; simp [wr, hp]
    · simp [wr, hp, hq]

theorem wl_gt {τ : Int → Sym} {p i : Int} (T : List Sym) (h : p < i) : wl τ p T i = τ i := by
  induction T generalizing τ p with
  | nil => rfl
  | cons t T ih => rw [wl, ih (by omega), wr_of_ne _ _ _ (by omega)]

theorem Holds_wl (τ : Int → Sym) (p : Int) (T : List Sym) : Holds (wl τ p T) p T := by
  induction T generalizing τ p with
  | nil => trivial
  | cons t T ih => exact ⟨by rw [wl, wl_gt _ (by omega), wr_self], ih _ _⟩

theorem Holds_congr {τ τ' : Int → Sym} {p : Int} {S : List Sym} (h : Holds τ p S)
    (h' : ∀ i, p - S.length < i → i ≤ p → τ' i = τ i) : Holds τ' p S := by
  induction S generalizing p with
  | nil => trivial
  | cons s S ih =>
    obtain ⟨h1, h2⟩ := h
    simp only [List.length_cons] at h'
    exact ⟨by rw [h' p (by omega) (Int.le_refl _), h1], ih h2 (fun i hi hi' => h' i (by omega) (by omega))⟩

theorem wl_self {τ : Int → Sym} {p : Int} {S : List Sym} (h : Holds τ p S) : wl τ p S = τ := by
  induction S generalizing p with
  | nil => rfl
  | cons s S ih => rw [wl, wr_same h.1, ih h.2]

theorem wr_wl {σ : Int → Sym} {p q : Int} (T : List Sym) (h : q < p) (t : Sym) :
    wr (wl σ q T) p t = wl (wr σ p t) q T := by
  induction T generalizing σ q with
  | nil => rfl
  | cons x T ih => rw [wl, wl, ih (by omega), wr_comm _ (by omega)]

theorem wl_wl (τ : Int → Sym) (p : Int) {T T' : List Sym} (h : T.length = T'.length) :
    wl (wl τ p T) p T' = wl τ p T' := by
  induction T generalizing τ p T' with
  | nil => cases T' with
    | nil => rfl
    | cons _ _ => exact absurd h (Nat.succ_ne_zero _).symm
  | cons t T ih =>
    cases T' with
    | nil => exact absurd h (Nat.succ_ne_zero _)
    | cons t' T'' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [wl, wl, wl, wr_wl _ (by omega), wr_wr, ih _ _ h]

/-! ### Soundness -/

theorem Rect.nilR {S T : List Sym} {L : List Letter} (h : Rect S [] L T) : L = [] ∧ T = S := by
  induction S generalizing T with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons s S ih =>
    cases h with
    | cons hc hr =>
      cases hc
      obtain ⟨rfl, rfl⟩ := ih hr
      exact ⟨rfl, rfl⟩

theorem Cell.single_inv {s t : Sym} {r : Letter} {M : List Letter} (h : Cell s [r] M t) :
    Visit s r.ent M r.ext t := by
  cases h with
  | cons hv hc => cases hc; simpa using hv

/-- The oracle machine realises one visit to a window with left end `lo` carrying `S`. -/
def OVisit (lo : Int) (S : List Sym) (X : St) (L : List Letter) (Y : St) (T : List Sym) :
    Prop :=
  ∀ (τ : Int → Sym) (O : List Letter), Holds τ (lo + S.length - 1) S →
    ∃ k, (ostep lo)^[k] (⟨X, lo + S.length - 1, τ⟩, L ++ O) =
      (⟨Y, lo + S.length, wl τ (lo + S.length - 1) T⟩, O)

theorem visit_sound (lo : Int) (n : Nat)
    (IH : ∀ (S : List Sym) (r : Letter) (L : List Letter) (T : List Sym), S.length = n →
      Rect S [r] L T → OVisit lo S r.ent L r.ext T) :
    ∀ {s : Sym} {X : St} {M : List Letter} {Y : St} {t : Sym}, Visit s X M Y t →
    ∀ (S1 : List Sym) (L : List Letter) (T1 : List Sym) (τ : Int → Sym) (O : List Letter),
      S1.length = n → Rect S1 M L T1 → τ (lo + n) = s → Holds τ (lo + n - 1) S1 →
      ∃ k, (ostep lo)^[k] (⟨X, lo + n, τ⟩, L ++ O) =
        (⟨Y, lo + n + 1, wl τ (lo + n) (t :: T1)⟩, O) := by
  intro s X M Y t hv
  induction hv with
  | right htr =>
    intro S1 L T1 τ O _ hR hs hH
    obtain ⟨rfl, rfl⟩ := Rect.nilR hR
    refine ⟨1, ?_⟩
    rw [iter_one, ostep_of_ne (by dsimp only; omega), step_right htr hs]
    simp only [List.nil_append, wl]
    rw [wl_self (Holds_congr hH (fun i _ hi => wr_of_ne _ _ _ (by omega)))]
  | @left s X w M Y t m htr _ ih =>
    intro S1 L T1 τ O hl hR hs hH
    have hR' : Rect S1 ([m] ++ M) L T1 := hR
    obtain ⟨L1, L2, S2, rfl, h1, h2⟩ := hR'.split
    have hstep : ostep lo (⟨X, lo + n, τ⟩, (L1 ++ L2) ++ O) =
        (⟨m.ent, lo + n - 1, wr τ (lo + n) w⟩, L1 ++ (L2 ++ O)) := by
      rw [ostep_of_ne (by dsimp only; omega), step_left htr hs, List.append_assoc]
    have hH1 : Holds (wr τ (lo + n) w) (lo + S1.length - 1) S1 := by
      rw [hl]; exact Holds_congr hH (fun i _ hi => wr_of_ne _ _ _ (by omega))
    obtain ⟨k1, hk1⟩ := IH S1 m L1 S2 hl h1 (wr τ (lo + n) w) (L2 ++ O) hH1
    rw [hl] at hk1
    have hl2 : S2.length = n := (Rect.length_eq h1).trans hl
    obtain ⟨k2, hk2⟩ := ih S2 L2 T1 (wl (wr τ (lo + n) w) (lo + n - 1) S2) O hl2 h2
      (by rw [wl_gt _ (by omega), wr_self]) (Holds_wl _ _ _)
    refine ⟨k2 + k1 + 1, ?_⟩
    rw [iter_add, iter_add, iter_one, hstep, hk1,
      hk2]
    have hlT : S2.length = T1.length := (Rect.length_eq h2).symm
    simp only [wl]
    rw [wr_wl _ (by omega), wr_wr, wl_wl _ _ hlT]

/-- **Soundness of rectangles.** -/
theorem rect_sound (lo : Int) : ∀ (n : Nat) (S : List Sym) (r : Letter) (L : List Letter)
    (T : List Sym), S.length = n → Rect S [r] L T → OVisit lo S r.ent L r.ext T
  | 0, S, r, L, T, hl, hR => by
    rw [List.length_eq_zero_iff] at hl
    subst hl
    cases hR
    intro τ O _
    refine ⟨1, ?_⟩
    simp only [List.length_nil, Int.cast_ofNat_Int, Int.add_zero, iter_one,
      List.cons_append, List.nil_append, wl]
    exact ostep_oracle r τ O
  | n + 1, S, r, L, T, hl, hR => by
    obtain ⟨s, S1, rfl⟩ : ∃ s S1, S = s :: S1 := by
      cases S with
      | nil => exact absurd hl (Nat.succ_ne_zero _).symm
      | cons s S1 => exact ⟨s, S1, rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    cases hR with
    | @cons _ _ M t _ _ T1 hc hR1 =>
      have hv := Cell.single_inv hc
      intro τ O hH
      have hp : lo + ((s :: S1).length : Int) - 1 = lo + n := by
        rw [List.length_cons, hl]; omega
      have hp' : lo + ((s :: S1).length : Int) = lo + n + 1 := by
        rw [List.length_cons, hl]; omega
      rw [hp] at hH ⊢
      rw [hp']
      obtain ⟨h1, h2⟩ := hH
      exact visit_sound lo n (rect_sound lo n) hv S1 L T1 τ O hl hR1 h1 h2

end LR
end BB25
