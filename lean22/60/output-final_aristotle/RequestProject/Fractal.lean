module

public import RequestProject.Rect

/-!
# The all-rank rectangle induction

With `n = 3^r`, `d = 2^r`, `w = n - d`, `M = d/2` (carried here recursively as
`(n,d,w,M) ↦ (3n, 2d, 2w+n, 2M)` starting from `(3,2,1,1)`), we prove that for every rank
there is a finite word `P` for which both the *reset* rectangles and the *triangle*
rectangles exist for all parameters `m, q, k`.  The next word is obtained by cutting the
derived *echo* rectangle.
-/

@[expose] public section

namespace BB25
namespace LR

open Letter

/-- `Z ℓ R L`: a rectangle of width `ℓ` turning `0^ℓ` into `1^ℓ`. -/
def Z (ℓ : Nat) (R L : List Letter) : Prop :=
  Rect (List.replicate ℓ 0) R L (List.replicate ℓ 1)

/-- (B): a run of `1`s passes a `b` straight through and resets to `0`s. -/
theorem rect_ones_b (ℓ : Nat) : Rect (List.replicate ℓ 1) [b] [b] (List.replicate ℓ 0) := by
  induction ℓ with
  | zero => exact Rect.nil _
  | succ ℓ ih => exact Rect.cons cell1b ih

/-- One pair of `1`-cells in the odd wall. -/
theorem rect_pair (j m s : Nat) :
    Rect [1, 1] (pw E j ++ pw D (m + 1) ++ pw E (s + 1))
      (pw E (j + 1) ++ pw D (m + 1) ++ pw E s) [1, 1] := by
  have h1 := cell1_C j m (s + 1) 0
  -- second cell
  have h2 : Cell 1 (A (2 * j + 1) ++ [b] ++ A 0 ++ pw D m ++ [c] ++ A (2 * (s + 1)))
      (pw E (j + 1) ++ pw D (m + 1) ++ pw E s) 1 := by
    have g := ((((((((cell1_A2 j).append cell1a).append (cell0b 0)).append
      (cell1_D0 m)).append cell1c).append cell3a).append cell0a).append (cell1_A2 s))
    have eR : A (2 * j + 1) ++ [b] ++ A 0 ++ pw D m ++ [c] ++ A (2 * (s + 1)) =
        A (2 * j) ++ [a] ++ [b] ++ pw D m ++ [c] ++ [a] ++ [a] ++ A (2 * s) := by
      rw [show 2 * (s + 1) = 1 + 1 + 2 * s by omega, A_add, A_add, A_add]
      simp
    have eL : pw E (j + 1) ++ pw D (m + 1) ++ pw E s =
        pw E j ++ [c, b, a] ++ (A 0 ++ [c]) ++ pw [a, b, c] m ++ [a] ++ [b] ++ [] ++ pw E s := by
      rw [pw_succ', pw_succ']
      have := c_abc m
      simp only [E, D, A, List.replicate_zero, List.nil_append, List.append_nil,
        List.append_assoc] at this ⊢
      rw [← List.append_assoc [c] (pw [a, b, c] m), this]
      simp
    rw [eR, eL]; exact g
  exact Rect.cons h1 (Rect.one h2)

/-- Iterated pairs. -/
theorem rect_pairs (m : Nat) : ∀ i s : Nat,
    Rect (List.replicate (2 * i) 1) (pw D (m + 1) ++ pw E (i + s))
      (pw E i ++ pw D (m + 1) ++ pw E s) (List.replicate (2 * i) 1)
  | 0, s => by simpa using Rect.nil (pw D (m + 1) ++ pw E s)
  | i + 1, s => by
    have ih := rect_pairs m i (s + 1)
    have hp := rect_pair i m s
    have h := ih.space hp
    have e : List.replicate (2 * (i + 1)) (1 : Sym) = List.replicate (2 * i) 1 ++ [1, 1] := by
      rw [show 2 * (i + 1) = 2 * i + 2 by omega, rep_add]; rfl
    rw [e, show i + 1 + s = i + (s + 1) by omega]
    exact h

/-- (U): the odd all-ones wall. -/
theorem rect_wall (h m e k : Nat) :
    Rect (List.replicate (2 * h + 1) 1) (pw D (m + 1) ++ pw E (h + e))
      (A (2 * h + 1) ++ [b] ++ A k ++ pw D m ++ [c] ++ A (2 * e))
      (List.replicate (2 * h + 1) 1) := by
  have h1 := rect_pairs m h e
  have h2 := Rect.one (cell1_C h m e k)
  have := h1.space h2
  rw [rep_add]
  exact this

/-- The triangle's exposed word. -/
def theta (m k : Nat) : List Letter := if m = 0 then [] else A k ++ pw D m

/-- The two rectangle families at one rank. -/
def Good (d w M : Nat) (P : List Letter) : Prop :=
  (∀ m q k : Nat, Z d (P ++ pw F m ++ A (d + 1 + 2 * q))
      (A k ++ pw D (M - 1 + m) ++ [c] ++ A (2 * q + 2))) ∧
  (∀ m q k : Nat, Z w (a :: (pw D (M - 1 + m) ++ [c] ++ A (w + 1 + 2 * q)))
      (P ++ theta m k ++ pw E q))

/-! ### Base rank -/

theorem good_base : Good 2 1 1 [a, b] := by
  refine ⟨fun m q k => ?_, fun m q k => ?_⟩
  · -- two cells, middle boundary `b D^m E^(q+1)`
    have c1 : Cell 0 ([a, b] ++ pw F m ++ A (2 + 1 + 2 * q)) ([b] ++ pw D m ++ pw E (q + 1)) 1 := by
      have g := (cell0ab.append (cell0_F m)).append (cell0_odd (q + 1))
      rw [show 2 + 1 + 2 * q = 2 * (q + 1) + 1 by omega]
      simpa using g
    have c2 : Cell 0 ([b] ++ pw D m ++ pw E (q + 1))
        (A k ++ pw D (1 - 1 + m) ++ [c] ++ A (2 * q + 2)) 1 := by
      have g := ((cell0b k).append (cell1_D0 m)).append (cell1_E (q + 1))
      have e : A k ++ pw D (1 - 1 + m) ++ [c] ++ A (2 * q + 2) =
          A k ++ [c] ++ pw [a, b, c] m ++ A (2 * (q + 1)) := by
        rw [show 1 - 1 + m = m by omega, show 2 * q + 2 = 2 * (q + 1) by omega,
          List.append_assoc (A k) [c], c_abc]
        simp
      rw [e]; exact g
    exact Rect.cons c1 (Rect.one c2)
  · show Rect [0] _ _ [1]
    apply Rect.one
    rw [show 1 - 1 + m = m by omega, show 1 + 1 + 2 * q = 1 + 1 + 2 * q from rfl]
    rcases m with _ | m
    · -- `a c a a a^(2q)`
      have g := ((((cell0a.append cell1c).append cell3a).append cell0a).append (cell1_A2 q))
      have eR : a :: (pw D 0 ++ [c] ++ A (1 + 1 + 2 * q)) =
          [a] ++ [c] ++ [a] ++ [a] ++ A (2 * q) := by
        rw [A_add, A_add]; simp
      have eL : [a, b] ++ theta 0 k ++ pw E q = [] ++ [a] ++ [b] ++ [] ++ pw E q := by
        simp [theta]
      rw [eR, eL]; exact g
    · have g := ((((((cell0a.append (cell1D k)).append (cell1_D0 m)).append cell1c).append
        cell3a).append cell0a).append (cell1_A2 q))
      have eR : a :: (pw D (m + 1) ++ [c] ++ A (1 + 1 + 2 * q)) =
          [a] ++ D ++ pw D m ++ [c] ++ [a] ++ [a] ++ A (2 * q) := by
        rw [A_add, A_add, pw_succ]; simp
      have eL : [a, b] ++ theta (m + 1) k ++ pw E q =
          [] ++ ([a, b] ++ A k ++ [c]) ++ pw [a, b, c] m ++ [a] ++ [b] ++ [] ++ pw E q := by
        have h1 : theta (m + 1) k = A k ++ pw D (m + 1) := by simp [theta]
        rw [h1, pw_succ']
        rw [show ([] ++ ([a, b] ++ A k ++ [c]) ++ pw [a, b, c] m ++ [a] ++ [b] ++ [] ++ pw E q)
            = [a, b] ++ A k ++ ([c] ++ pw [a, b, c] m) ++ [a, b] ++ pw E q by simp, c_abc]
        simp [D]
      rw [eR, eL]; exact g

/-! ### The induction step -/

theorem replicate_split {x : Sym} {p q : Nat} {U1 U2 : List Sym}
    (h : List.replicate (p + q) x = U1 ++ U2) (hl : U1.length = p) :
    U1 = List.replicate p x ∧ U2 = List.replicate q x := by
  rw [rep_add] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
  exact ⟨h1.symm, h2.symm⟩

theorem Z.space {ℓ₁ ℓ₂ : Nat} {R M L : List Letter} (h1 : Z ℓ₁ R M) (h2 : Z ℓ₂ M L) :
    Z (ℓ₁ + ℓ₂) R L := by
  unfold Z at *
  rw [rep_add, rep_add]
  exact h1.space h2

/-- `b D^j c a^(e+1) = F^(j+1) a^e`. -/
theorem bDca (j e : Nat) : [b] ++ pw D j ++ [c] ++ A (e + 1) = pw F (j + 1) ++ A e := by
  have h := pw_conj [b] [c, a] j
  have hD : pw ([c, a] ++ [b]) j = pw D j := rfl
  have hF : pw ([b] ++ [c, a]) j = pw F j := rfl
  rw [hD, hF] at h
  rw [h, pw_succ', A_succ]
  simp [F]

/-- The echo rectangle `Z_n (P a^n) P`. -/
theorem echo {d w M h : Nat} {P : List Letter} (hG : Good d w M P) (hw : w = 2 * h + 1) :
    Z (d + w) (P ++ A (d + w)) P := by
  have r := hG.1 0 h 1
  have t := hG.2 0 0 0
  have e1 : P ++ pw F 0 ++ A (d + 1 + 2 * h) = P ++ A (d + w) := by
    rw [hw, show d + 1 + 2 * h = d + (2 * h + 1) by omega]; simp
  have e2 : A 1 ++ pw D (M - 1 + 0) ++ [c] ++ A (2 * h + 2) =
      a :: (pw D (M - 1 + 0) ++ [c] ++ A (w + 1 + 2 * 0)) := by
    rw [hw, show 2 * h + 1 + 1 + 2 * 0 = 2 * h + 2 by omega]; simp
  have e3 : P ++ theta 0 0 ++ pw E 0 = P := by simp [theta]
  rw [e1, e2] at r
  rw [e3] at t
  exact Z.space r t

theorem good_step {d w M : Nat} {P : List Letter} (hG : Good d w M P) (hM : 1 ≤ M)
    (hd : d = 2 * M) (hw : w % 2 = 1) :
    ∃ P', Good (2 * d) (2 * w + (d + w)) (2 * M) P' := by
  obtain ⟨h, hh⟩ : ∃ h, w = 2 * h + 1 := ⟨w / 2, by omega⟩
  have E0 := echo hG hh
  -- cut the echo after its first `w` cells
  have E0' : Rect (List.replicate w 0 ++ List.replicate d 0) (P ++ A (d + w)) P
      (List.replicate (w + d) 1) := by
    rw [← rep_add, show w + d = d + w by omega]; exact E0
  obtain ⟨H, U1, U2, hU, hl, X, Y⟩ := Rect.cut E0'
  obtain ⟨rfl, rfl⟩ := replicate_split hU (by simpa using hl)
  refine ⟨H ++ [b] ++ P, fun m q k => ?_, fun m q k => ?_⟩
  · -- reset
    have B1 := (Y.append (rect_ones_b d)).append (hG.1 m (q + M) 0)
    have B2 := hG.1 (M + m) q k
    have eMid : P ++ [b] ++ (A 0 ++ pw D (M - 1 + m) ++ [c] ++ A (2 * (q + M) + 2)) =
        P ++ pw F (M + m) ++ A (d + 1 + 2 * q) := by
      have := bDca (M - 1 + m) (d + 1 + 2 * q)
      rw [show M - 1 + m + 1 = M + m by omega] at this
      rw [show 2 * (q + M) + 2 = d + 1 + 2 * q + 1 by omega,
        List.append_assoc P (pw F (M + m)), ← this]
      simp
    rw [eMid] at B1
    have B := Z.space B1 B2
    unfold Z at B ⊢
    refine B.cast (by rw [show d + d = 2 * d by omega]) ?_ ?_ (by rw [show d + d = 2 * d by omega])
    · rw [show d + 1 + 2 * (q + M) = 2 * d + 1 + 2 * q by omega]; simp
    · rw [show M - 1 + (M + m) = 2 * M - 1 + m by omega]
  · -- triangle
    have T1 := hG.2 (M + m) (d + w - M + q) (d + w)
    have hth : theta (M + m) (d + w) = A (d + w) ++ pw D (M + m) := by
      simp [theta]; omega
    rw [hth] at T1
    have W := rect_wall (h + M) (M + m - 1) (h + 1 + q) 1
    have W' : Rect (List.replicate (d + w) 1) (pw D (M + m) ++ pw E (d + w - M + q))
        (A (d + w) ++ [b] ++ (a :: (pw D (M - 1 + m) ++ [c] ++ A (w + 1 + 2 * q))))
        (List.replicate (d + w) 1) := by
      refine W.cast (by congr 1; omega) ?_ ?_ (by congr 1; omega)
      · rw [show M + m - 1 + 1 = M + m by omega, show h + M + (h + 1 + q) = d + w - M + q by omega]
      · rw [show 2 * (h + M) + 1 = d + w by omega, show M + m - 1 = M - 1 + m by omega,
          show 2 * (h + 1 + q) = w + 1 + 2 * q by omega]
        simp
    have B2 := Rect.append E0 W'
    have B3 := (X.append (rect_ones_b w)).append (hG.2 m q k)
    have B12 := Z.space T1 (show Z (d + w) _ _ from B2.cast rfl (by simp) rfl rfl)
    have B123 := Z.space B12 (show Z w _ _ from B3.cast rfl (by simp) rfl rfl)
    unfold Z at B123 ⊢
    refine B123.cast (by congr 1; omega) ?_ ?_ (by congr 1; omega)
    · rw [show M - 1 + (M + m) = 2 * M - 1 + m by omega,
        show w + 1 + 2 * (d + w - M + q) = 2 * w + (d + w) + 1 + 2 * q by omega]
    · simp

/-- **All ranks.**  For every bound `r` there is a rank whose triangle width `w` and
half-width `M` both exceed `r`. -/
theorem all_ranks (r : Nat) : ∃ d w M P, 1 ≤ M ∧ d = 2 * M ∧ w % 2 = 1 ∧ r < w ∧ r < M ∧
    Good d w M P := by
  induction r with
  | zero => exact ⟨2, 1, 1, [a, b], Nat.le_refl _, rfl, rfl, Nat.zero_lt_one, Nat.zero_lt_one, good_base⟩
  | succ r ih =>
    obtain ⟨d, w, M, P, hM, hd, hw, hrw, hrM, hG⟩ := ih
    obtain ⟨P', hG'⟩ := good_step hG hM hd hw
    exact ⟨2 * d, 2 * w + (d + w), 2 * M, P', by omega, by omega, by omega, by omega, by omega, hG'⟩

end LR
end BB25
