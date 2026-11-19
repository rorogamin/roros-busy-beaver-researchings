/-
  BB/Fwp2_7.lean
  Shared 7-state `fwp21_7` reload (`sym = 2`) and halt (`[5]`) layer on top of `Fwp2Core`.
  Powers BB(7, 7), BB(7, 8), and BB(7, 9).
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2

namespace BB

/-- The 7-state `fwp21_7` extension of `Fwp2Core`. -/
structure Fwp2_7Core (tm : TM) : Prop where
  fp : Fwp2Core tm
  A2 : tm 0 2 = some ⟨6, Dir.L, some 0⟩
  A5 : tm 0 5 = some ⟨5, Dir.R, some 2⟩
  A6 : tm 0 6 = some ⟨5, Dir.L, some 0⟩
  B0 : tm 1 0 = some ⟨1, Dir.R, none⟩
  B6 : tm 1 6 = some ⟨6, Dir.L, some 3⟩
  C6 : tm 2 6 = some ⟨5, Dir.R, some 1⟩
  D6 : tm 3 6 = some ⟨1, Dir.L, some 0⟩

/-- Growth function `H2 m = Pempty (2 * m + 1) > f_{ω^2}(m)`. -/
def H2_7 (m : Nat) : Nat := Pempty (2 * m + 1)

theorem H2_7_mono {x y : Nat} (hxy : x ≤ y) : H2_7 x ≤ H2_7 y :=
  Pempty_mono (by omega)

theorem H2_7_0_ge : 17 ≤ H2_7 0 := by
  have hgen : ∀ r, Pfn (r + 1) 1 0 = Pfn (r + 1) 0 (Pfn (r + 1) 0 0) := fun _ => rfl
  have h1 : Pfn 1 1 0 = Pfn 1 0 (Pfn 1 0 0) := hgen 0
  have h2 : Pfn 1 0 0 + 1 ≤ Pfn 1 0 (Pfn 1 0 0) := Pfn_ge_succ 1 0 (Pfn 1 0 0)
  have h0 : Pfn 1 0 0 = 15 := rfl
  have h3 : 16 ≤ Pfn 1 1 0 := by rw [h1]; omega
  have hpe : ∀ r, Pempty r = Pfn r 1 0 + 1 := fun _ => rfl
  have h1eq : 2 * 0 + 1 = 1 := rfl
  rw [H2_7, h1eq, hpe]
  omega

theorem H2_7_inc (m : Nat) (_hm : 1 ≤ m) : m + 1 ≤ H2_7 m := by
  have h := Pempty_ge (2 * m + 1); unfold H2_7; omega

theorem H2_7_gt (m : Nat) (_hm : 1 ≤ m) : f_omega2 m < H2_7 m := by
  have h1 := Pempty_gt_f_omega2 m
  have h2 : Pempty m ≤ Pempty (2 * m + 1) := Pempty_mono (by omega)
  exact Nat.lt_of_lt_of_le h1 h2

section Fwp2_7Lemmas

variable {tm : TM} (h7 : Fwp2_7Core tm)
include h7

private theorem loop_B5_7 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) L (rep n 5 R)) (mkCfgR (some 1) (rep n 5 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 1) L (5 :: rep k 5 R)) =
              some (mkCfgR (some 1) (5 :: L) (rep k 5 R)) :=
      step_mkCfgR_R h7.fp.B5
    have h2 := ih (5 :: L); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

private theorem loop_A_3to5 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 0) (rep n 3 L) (2 :: R))
               (mkCfgR (some 0) L (2 :: rep n 5 R)) (3 * n) := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 0) (3 :: rep k 3 L) (2 :: R)) =
              some (mkCfgR (some 0) (rep k 3 L) (3 :: 6 :: R)) :=
      step_mkCfgR_L_cons h7.A2
    have h2 : step tm (mkCfgR (some 0) (rep k 3 L) (3 :: 6 :: R)) =
              some (mkCfgR (some 0) (2 :: rep k 3 L) (6 :: R)) :=
      step_mkCfgR_R h7.fp.kc.A3
    have h3 : step tm (mkCfgR (some 0) (2 :: rep k 3 L) (6 :: R)) =
              some (mkCfgR (some 0) (rep k 3 L) (2 :: 5 :: R)) :=
      step_mkCfgR_L_cons h7.A6
    have h4 := ih (5 :: R)
    rw [rep_snoc_one] at h4
    have hall := steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 (steps_succ tm _ _ _ _ h3 h4))
    have ht : 3 * k + 1 + 1 + 1 = 3 * (k + 1) := by omega
    rw [ht] at hall
    exact hall

theorem reload_2_7 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (Scfg (r + 1) 0 m (2 :: R))
                    (mkCfgR (some 0) (2 :: rep (r + 2 * m + 2) 5 []) (1 :: R)) t := by
  have h1 : step tm (Scfg (r + 1) 0 m (2 :: R)) =
            some (mkCfgR (some 0) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons h7.A2
  have h2 := loop_A_3to5 h7 (2 * m + 1) (rep (r + 1) 5 []) (6 :: R)
  have h3 : step tm (mkCfgR (some 0) (5 :: rep r 5 []) (2 :: rep (2 * m + 1) 5 (6 :: R))) =
            some (mkCfgR (some 0) (rep r 5 []) (5 :: 6 :: rep (2 * m + 1) 5 (6 :: R))) :=
    step_mkCfgR_L_cons h7.A2
  have h4 : step tm (mkCfgR (some 0) (rep r 5 []) (5 :: 6 :: rep (2 * m + 1) 5 (6 :: R))) =
            some (mkCfgR (some 2) (5 :: rep r 5 []) (6 :: rep (2 * m + 1) 5 (6 :: R))) :=
    step_mkCfgR_R h7.A5
  have h5 : step tm (mkCfgR (some 2) (5 :: rep r 5 []) (6 :: rep (2 * m + 1) 5 (6 :: R))) =
            some (mkCfgR (some 1) (5 :: 5 :: rep r 5 []) (rep (2 * m + 1) 5 (6 :: R))) :=
    step_mkCfgR_R h7.C6
  have h6 := loop_B5_7 h7 (2 * m + 1) (5 :: 5 :: rep r 5 []) (6 :: R)
  have hrep5 : rep (2 * m + 1) 5 (5 :: 5 :: rep r 5 []) = rep (r + 2 * m + 3) 5 [] := by
    have hadd : ∀ a b L, rep a 5 (rep b 5 L) = rep (a + b) 5 L := by
      intro a
      induction a with
      | zero => intro b L; simp [rep]
      | succ p ihp => intro b L; rw [Nat.succ_add]; simp only [rep, ihp]
    have h1' : 5 :: 5 :: rep r 5 [] = rep (r + 2) 5 [] := rfl
    rw [h1', hadd]
    have ha : 2 * m + 1 + (r + 2) = r + 2 * m + 3 := by omega
    rw [ha]
  rw [hrep5] at h6
  have h7s : step tm (mkCfgR (some 1) (5 :: rep (r + 2 * m + 2) 5 []) (6 :: R)) =
             some (mkCfgR (some 3) (rep (r + 2 * m + 2) 5 []) (5 :: 6 :: R)) :=
    step_mkCfgR_L_cons h7.B6
  have h8 : step tm (mkCfgR (some 3) (rep (r + 2 * m + 2) 5 []) (5 :: 6 :: R)) =
            some (mkCfgR (some 3) (3 :: rep (r + 2 * m + 2) 5 []) (6 :: R)) :=
    step_mkCfgR_R h7.fp.D5
  have h9 : step tm (mkCfgR (some 3) (3 :: rep (r + 2 * m + 2) 5 []) (6 :: R)) =
            some (mkCfgR (some 0) (rep (r + 2 * m + 2) 5 []) (3 :: 1 :: R)) :=
    step_mkCfgR_L_cons h7.D6
  have h10 : step tm (mkCfgR (some 0) (rep (r + 2 * m + 2) 5 []) (3 :: 1 :: R)) =
             some (mkCfgR (some 0) (2 :: rep (r + 2 * m + 2) 5 []) (1 :: R)) :=
    step_mkCfgR_R h7.fp.kc.A3
  have ha := steps_succ tm _ _ _ _ h1 (reaches_trans h2
    (steps_succ tm _ _ _ _ h3 (steps_succ tm _ _ _ _ h4 (steps_succ tm _ _ _ _ h5 h6))))
  have hb := steps_succ tm _ _ _ _ h7s (steps_succ tm _ _ _ _ h8
    (steps_succ tm _ _ _ _ h9 (steps_one tm _ _ h10)))
  exact ⟨_, reaches_trans ha hb⟩

theorem rule_2_7 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches tm (Scfg (r + 1) 0 m (2 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H2_7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2_7 h7 r m R
  obtain ⟨t2, h2, hle2⟩ := fwp2_empty3 h7.fp (r + 2 * m + 1) R
  have hmono : H2_7 m ≤ Pempty (r + 2 * m + 1) := Pempty_mono (by omega)
  exact ⟨r + 2 * m + 1, Pempty (r + 2 * m + 1), t1 + t2, reaches_trans h1 h2, hmono,
    Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

theorem rule_2_7_rep (n : Nat) :
    ∀ r m R, ∃ r' m' t, Reaches tm (Scfg (r + 1) 0 m (rep n 2 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H2_7 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero tm _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_2_7 h7 r m R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_2_7 h7 r m (rep (p' + 1) 2 R)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R
      have hcomm : iter H2_7 (p' + 1) (H2_7 m) = iter H2_7 (p' + 2) m := (iter_add H2_7 (p' + 1) 1 m).symm
      have hmb : iter H2_7 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H2_7 (fun _ _ h => H2_7_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem rule_halt_5_7 (r m : Nat) :
    ∃ cf, Reaches tm (Scfg (r + 1) 0 m [5]) cf 3 ∧ cf.st = none := by
  have h1 : step tm (Scfg (r + 1) 0 m [5]) =
            some (mkCfgR (some 2) (5 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) []) :=
    step_mkCfgR_R h7.A5
  have h2 : step tm (mkCfgR (some 2) (5 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) []) =
            some (mkCfgR (some 1) (3 :: 5 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) []) :=
    step_mkCfgR_R_nil h7.fp.kc.C0
  have h3 : step tm (mkCfgR (some 1) (3 :: 5 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) []) =
            some (mkCfgR none (1 :: 3 :: 5 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) []) :=
    step_mkCfgR_R_nil h7.B0
  exact ⟨_, steps_succ tm 2 _ _ _ h1 (steps_succ tm 1 _ _ _ h2 (steps_one tm _ _ h3)), rfl⟩

end Fwp2_7Lemmas
end BB
