module

public import RequestProject.Oracle

/-!
# The right-hand driver

Right of the window, the blank-tape machine builds the word `(042)^m`.  The three rules
below (each proved for every `m`) show that, whenever the head leaves the window to the right,
the right half sends it back in the state required by the boundary word `a (cab)^ω`.
-/

@[expose] public section

namespace BB25
namespace LR

/-- `RightIs τ p W`: from cell `p` rightwards the tape reads `W`, followed by blanks. -/
def RightIs (τ : Int → Sym) (p : Int) (W : List Sym) : Prop := ∀ i : Nat, τ (p + i) = W.getD i 0

theorem RightIs_cons {τ : Int → Sym} {p : Int} {x : Sym} {W : List Sym} :
    RightIs τ p (x :: W) ↔ τ p = x ∧ RightIs τ (p + 1) W := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun i => ?_⟩
    have := h (i + 1)
    rw [show p + ((i + 1 : Nat) : Int) = p + 1 + i by omega] at this
    simpa using this
  · rintro ⟨h0, h⟩ i
    cases i with
    | zero => simpa using h0
    | succ i =>
      rw [show p + ((i + 1 : Nat) : Int) = p + 1 + i by omega]
      simpa using h i

theorem RightIs_congr {τ τ' : Int → Sym} {p : Int} {W : List Sym} (h : RightIs τ p W)
    (h' : ∀ i, p ≤ i → τ' i = τ i) : RightIs τ' p W := fun i => by
  rw [h' _ (by omega)]; exact h i

/-- The token word `(042)^m`. -/
def U : Nat → List Sym
  | 0 => []
  | m + 1 => 0 :: 4 :: 2 :: U m

/-! ### Stepping helpers -/

theorem osR {lo : Int} {X Y : St} {s w : Sym} {p q : Int} {τ : Int → Sym} {O : List Letter}
    {y : OCfg} {k : Nat} (hne : p ≠ lo - 1) (htr : tr X s = some (w, true, Y)) (hs : τ p = s)
    (hq : q = p + 1) (hk : (ostep lo)^[k] (⟨Y, q, wr τ p w⟩, O) = y) :
    (ostep lo)^[k + 1] (⟨X, p, τ⟩, O) = y := by
  rw [iter_succ, ostep_of_ne hne]
  simp only
  rw [step_right htr hs, ← hq]; exact hk

theorem osL {lo : Int} {X Y : St} {s w : Sym} {p q : Int} {τ : Int → Sym} {O : List Letter}
    {y : OCfg} {k : Nat} (hne : p ≠ lo - 1) (htr : tr X s = some (w, false, Y)) (hs : τ p = s)
    (hq : q = p - 1) (hk : (ostep lo)^[k] (⟨Y, q, wr τ p w⟩, O) = y) :
    (ostep lo)^[k + 1] (⟨X, p, τ⟩, O) = y := by
  rw [iter_succ, ostep_of_ne hne]
  simp only
  rw [step_left htr hs, ← hq]; exact hk

theorem osDone {lo : Int} {x : OCfg} : (ostep lo)^[0] x = x := rfl

/-! ### The three rules -/

/-- Rule 1: entering `(042)^m` in state `A` returns in state `A`, leaving `2 (042)^m`. -/
theorem rule1 (lo : Int) : ∀ (m : Nat) (p : Int) (τ : Int → Sym) (O : List Letter), lo ≤ p →
    RightIs τ p (U m) →
    ∃ k τ', (ostep lo)^[k] (⟨St.A, p, τ⟩, O) = (⟨St.A, p - 1, τ'⟩, O) ∧
      RightIs τ' p (2 :: U m) ∧ (∀ i < p, τ' i = τ i) ∧ 1 ≤ k
  | 0, p, τ, O, hp, hR => by
    have h0 : τ p = 0 := by simpa using hR 0
    have h1 : τ (p + 1) = 0 := by simpa using hR 1
    refine ⟨3, wr (wr τ p 1) p 2, ?_, ?_, ?_, by omega⟩
    · refine osR (s := 0) (by omega) rfl h0 rfl ?_
      refine osL (s := 0) (by omega) rfl (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)
        (show p = p + 1 - 1 by omega) ?_
      refine osL (s := 1) (by omega) rfl (by rw [wr_of_ne _ _ _ (by omega), wr_self]) rfl ?_
      rw [wr_same (show wr τ p 1 (p + 1) = 0 by rw [wr_of_ne _ _ _ (by omega)]; exact h1), osDone]
    · intro i
      cases i with
      | zero => simp
      | succ i =>
        rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]
        simpa [U] using hR (i + 1)
    · intro i hi
      rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]
  | m + 1, p, τ, O, hp, hR => by
    obtain ⟨h0, hR⟩ := RightIs_cons.1 hR
    obtain ⟨h1, hR⟩ := RightIs_cons.1 hR
    obtain ⟨h2, hR⟩ := RightIs_cons.1 hR
    obtain ⟨τ3, hτ3⟩ : ∃ x, x = wr (wr (wr τ p 1) (p + 1) 0) (p + 1 + 1) 3 := ⟨_, rfl⟩
    have e1 : (ostep lo)^[3] (⟨St.A, p, τ⟩, O) = (⟨St.A, p + 1 + 1 + 1, τ3⟩, O) := by
      refine osR (s := 0) (by omega) rfl h0 rfl ?_
      refine osR (s := 4) (by omega) rfl (by rw [wr_of_ne _ _ _ (by omega)]; exact h1) rfl ?_
      refine osR (s := 2) (by omega) rfl
        (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h2) rfl ?_
      rw [hτ3]; rfl
    have hR3 : RightIs τ3 (p + 1 + 1 + 1) (U m) := RightIs_congr hR (fun i hi => by
      rw [hτ3, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)])
    obtain ⟨k0, τ4, hk0, hR4, hin4, -⟩ := rule1 lo m (p + 1 + 1 + 1) τ3 O (by omega) hR3
    have v2 : τ4 (p + 1 + 1) = 3 := by rw [hin4 _ (by omega), hτ3, wr_self]
    have v1 : τ4 (p + 1) = 0 := by
      rw [hin4 _ (by omega), hτ3, wr_of_ne _ _ _ (by omega), wr_self]
    have v0 : τ4 p = 1 := by
      rw [hin4 _ (by omega), hτ3, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
    obtain ⟨τ7, hτ7⟩ : ∃ x, x = wr (wr (wr τ4 (p + 1 + 1) 4) (p + 1) 0) p 2 := ⟨_, rfl⟩
    have e3 : (ostep lo)^[3] (⟨St.A, p + 1 + 1, τ4⟩, O) = (⟨St.A, p - 1, τ7⟩, O) := by
      refine osL (s := 3) (by omega) rfl v2 (show p + 1 = p + 1 + 1 - 1 by omega) ?_
      refine osL (s := 0) (by omega) rfl (by rw [wr_of_ne _ _ _ (by omega)]; exact v1)
        (show p = p + 1 - 1 by omega) ?_
      refine osL (s := 1) (by omega) rfl
        (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact v0) rfl ?_
      rw [hτ7]; rfl
    refine ⟨3 + k0 + 3, τ7, ?_, ?_, ?_, by omega⟩
    · rw [iter_add, iter_add, e1, hk0,
        show p + 1 + 1 + 1 - 1 = p + 1 + 1 by omega, e3]
    · refine RightIs_cons.2 ⟨by simp [hτ7], RightIs_cons.2 ⟨?_, RightIs_cons.2 ⟨?_,
        RightIs_cons.2 ⟨?_, ?_⟩⟩⟩⟩
      · rw [hτ7, wr_of_ne _ _ _ (by omega), wr_self]
      · rw [hτ7, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
      · have := (RightIs_cons.1 hR4).1
        rw [hτ7, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
          wr_of_ne _ _ _ (by omega), this]
      · refine RightIs_congr (RightIs_cons.1 hR4).2 (fun i hi => ?_)
        rw [hτ7, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
          wr_of_ne _ _ _ (by omega)]
    · intro i hi
      rw [hτ7, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
        wr_of_ne _ _ _ (by omega), hin4 _ (by omega), hτ3, wr_of_ne _ _ _ (by omega),
        wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]

/-- Rule 2: entering `2 (042)^m` in state `B` returns in state `B`, leaving `4 2 (042)^m`. -/
theorem rule2 (lo : Int) (m : Nat) (p : Int) (τ : Int → Sym) (O : List Letter) (hp : lo ≤ p)
    (hR : RightIs τ p (2 :: U m)) :
    ∃ k τ', (ostep lo)^[k] (⟨St.B, p, τ⟩, O) = (⟨St.B, p - 1, τ'⟩, O) ∧
      RightIs τ' p (4 :: 2 :: U m) ∧ (∀ i < p, τ' i = τ i) ∧ 1 ≤ k := by
  obtain ⟨h2, hR⟩ := RightIs_cons.1 hR
  have e1 : (ostep lo)^[1] (⟨St.B, p, τ⟩, O) = (⟨St.A, p + 1, wr τ p 3⟩, O) :=
    osR (s := 2) (by omega) rfl h2 rfl rfl
  have hR1 : RightIs (wr τ p 3) (p + 1) (U m) :=
    RightIs_congr hR (fun i hi => wr_of_ne _ _ _ (by omega))
  obtain ⟨k0, τ2, hk0, hR2, hin2, -⟩ := rule1 lo m (p + 1) (wr τ p 3) O (by omega) hR1
  have v3 : τ2 p = 3 := by rw [hin2 _ (by omega), wr_self]
  have e3 : (ostep lo)^[1] (⟨St.A, p, τ2⟩, O) = (⟨St.B, p - 1, wr τ2 p 4⟩, O) :=
    osL (s := 3) (by omega) rfl v3 rfl rfl
  refine ⟨1 + k0 + 1, wr τ2 p 4, ?_, ?_, ?_, by omega⟩
  · rw [iter_add, iter_add, e1, hk0,
      show p + 1 - 1 = p by omega, e3]
  · exact RightIs_cons.2 ⟨by simp, RightIs_congr hR2 (fun i hi => wr_of_ne _ _ _ (by omega))⟩
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), hin2 _ (by omega), wr_of_ne _ _ _ (by omega)]

/-- Rule 3: entering `4 2 (042)^m` in state `B` returns in state `A`, leaving `(042)^(m+1)`. -/
theorem rule3 (lo : Int) (m : Nat) (p : Int) (τ : Int → Sym) (O : List Letter) (hp : lo ≤ p)
    (hR : RightIs τ p (4 :: 2 :: U m)) :
    ∃ k τ', (ostep lo)^[k] (⟨St.B, p, τ⟩, O) = (⟨St.A, p - 1, τ'⟩, O) ∧
      RightIs τ' p (U (m + 1)) ∧ (∀ i < p, τ' i = τ i) ∧ 1 ≤ k := by
  obtain ⟨h4, hR⟩ := RightIs_cons.1 hR
  have e1 : (ostep lo)^[1] (⟨St.B, p, τ⟩, O) = (⟨St.B, p + 1, wr τ p 0⟩, O) :=
    osR (s := 4) (by omega) rfl h4 rfl rfl
  have hR1 : RightIs (wr τ p 0) (p + 1) (2 :: U m) :=
    RightIs_congr hR (fun i hi => wr_of_ne _ _ _ (by omega))
  obtain ⟨k0, τ2, hk0, hR2, hin2, -⟩ := rule2 lo m (p + 1) (wr τ p 0) O (by omega) hR1
  have v0 : τ2 p = 0 := by rw [hin2 _ (by omega), wr_self]
  have e3 : (ostep lo)^[1] (⟨St.B, p, τ2⟩, O) = (⟨St.A, p - 1, wr τ2 p 0⟩, O) :=
    osL (s := 0) (by omega) rfl v0 rfl rfl
  refine ⟨1 + k0 + 1, wr τ2 p 0, ?_, ?_, ?_, by omega⟩
  · rw [iter_add, iter_add, e1, hk0,
      show p + 1 - 1 = p by omega, e3]
  · exact RightIs_cons.2 ⟨by simp, RightIs_congr hR2 (fun i hi => wr_of_ne _ _ _ (by omega))⟩
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), hin2 _ (by omega), wr_of_ne _ _ _ (by omega)]

end LR
end BB25
