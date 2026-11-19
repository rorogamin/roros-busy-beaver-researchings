/-
  BB/Fwp2_H8.lean
  Shared higher-symbol & cursor-5 layers on top of `Fwp2_HCore`:
    - `Fwp2_H6Core`: symbol `6` (`H_plus2 > f_{ω^2+1}`)
    - `Fwp2_H7Core`: symbol `7` (`H7_H > f_{ω^2+2}`)
    - `Fwp2_H8Core`: symbol `8` (`H8_H > f_{ω^2+3}`)
    - Generic climbing combinators: `climb_2m_plus_1`, `iter_H_ge_17`
    - Generic cursor-5 combinators: `halt_cursor_5`, `iter_cursor_rep`, `iter_cursor_rep0`,
      `reload_51_4step`, `reload_5mark_empty`, `reload_5top_zero`
  Powers ALL 12 new `BB(9..11, 6..9)` champions!
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H

namespace BB

/-! ### Growth Functions `H7_H` and `H8_H` + Generic Climbing Helpers -/

def H7_H (m : Nat) : Nat := iter H_plus2 (2 * m) 1
def H8_H (m : Nat) : Nat := iter H7_H (2 * m - 1) 1

theorem H7_H_mono {x y : Nat} (hxy : x ≤ y) : H7_H x ≤ H7_H y :=
  iter_mono_steps H_plus2 (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z' => exact Nat.le_trans (Nat.le_succ _) (H_plus2_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H7_H_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H7_H m :=
  climb_double H_plus2 (f_omega2_plus 1) 1 (by omega) (fun _ _ h => H_plus2_mono h) H_plus2_inc H_plus2_gt
    (fOmega2_props 1 0 1) m hm

theorem H7_H_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H7_H m := by
  have h1 := H7_H_gt m hm
  have h2 : m ≤ f_omega2_plus 2 m := (fOmega2_props 1 0 2).ge_self m
  omega

theorem H7_H_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H7_H m := by
  cases h2m : 2 * m with
  | zero => omega
  | succ q => unfold H7_H; rw [h2m, iter_succ]; exact H_plus2_ge_17 _

theorem H8_H_mono {x y : Nat} (hxy : x ≤ y) : H8_H x ≤ H8_H y :=
  iter_mono_steps H7_H (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z' => exact Nat.le_trans (Nat.le_succ _) (H7_H_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H8_H_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 3 m < H8_H m :=
  climb_2m_minus_1 H7_H (f_omega2_plus 2) 1 (by omega) (fun _ _ h => H7_H_mono h) H7_H_inc H7_H_gt
    (fOmega2_props 1 0 2) m hm

theorem H8_H_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H8_H m := by
  have h1 := H8_H_gt m hm
  have h2 : m ≤ f_omega2_plus 3 m := (fOmega2_props 1 0 3).ge_self m
  omega

theorem H8_H_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H8_H m := by
  cases h2m : 2 * m - 1 with
  | zero => omega
  | succ q =>
    unfold H8_H; rw [h2m, iter_succ]
    have hpos : 1 ≤ iter H7_H q 1 := iter_ge_self H7_H (fun z => by
      cases z with
      | zero => exact Nat.zero_le _
      | succ z' => exact Nat.le_trans (Nat.le_succ _) (H7_H_inc (z' + 1) (Nat.succ_pos z'))) q 1
    exact H7_H_ge_17 _ hpos

/-- Climbing with `2*m + 1` iterations (dominates `2*m - 1`). -/
theorem climb_2m_plus_1 (H f : Nat → Nat) (c : Nat) (hc : 1 ≤ c)
    (hmono : ∀ x y, x ≤ y → H x ≤ H y)
    (hinc : ∀ x, 1 ≤ x → x + 1 ≤ H x)
    (hdom : ∀ x, 1 ≤ x → f x < H x)
    (hf : FGHProps f) :
    ∀ m, 1 ≤ m → fNext f m < iter H (2 * m + 1) c := by
  intro m hm
  have h1 := climb_2m_minus_1 H f c hc hmono hinc hdom hf m hm
  have hge : ∀ z, z ≤ H z := fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z' => exact Nat.le_trans (Nat.le_succ _) (hinc (z' + 1) (Nat.succ_pos z'))
  exact Nat.lt_of_lt_of_le h1 (iter_mono_steps H hge (by omega) c)

/-- Generic `≥ 17` lower bound for `iter H k c` when `k ≥ 1`, `c ≥ 1`, `H x ≥ 17` for `x ≥ 1`. -/
theorem iter_H_ge_17 (H : Nat → Nat) (k c : Nat) (hk : 1 ≤ k) (hc : 1 ≤ c)
    (hinc : ∀ x, 1 ≤ x → x + 1 ≤ H x)
    (h17 : ∀ x, 1 ≤ x → 17 ≤ H x) :
    17 ≤ iter H k c := by
  cases k with
  | zero => omega
  | succ q =>
    rw [iter_succ]
    have hge : ∀ z, z ≤ H z := fun z => by
      cases z with
      | zero => exact Nat.zero_le _
      | succ z' => exact Nat.le_trans (Nat.le_succ _) (hinc (z' + 1) (Nat.succ_pos z'))
    exact h17 _ (Nat.le_trans hc (iter_ge_self H hge q c))

/-! ### Shared Cores `Fwp2_H6Core`, `Fwp2_H7Core`, `Fwp2_H8Core` -/

structure Fwp2_H6Core (tm : TM) : Prop where
  fh : Fwp2_HCore tm
  A6 : tm 0 6 = some ⟨6, Dir.L, some 7⟩
  G6 : tm 6 6 = some ⟨2, Dir.L, some 7⟩
  H4 : tm 7 4 = some ⟨2, Dir.L, some 7⟩

structure Fwp2_H7Core (tm : TM) : Prop where
  h6 : Fwp2_H6Core tm
  A7 : tm 0 7 = some ⟨7, Dir.L, some 7⟩
  G7 : tm 6 7 = some ⟨6, Dir.L, some 3⟩
  D4 : tm 3 4 = some ⟨6, Dir.L, some 3⟩
  D6 : tm 3 6 = some ⟨3, Dir.R, some 1⟩
  B6 : tm 1 6 = some ⟨3, Dir.R, some 2⟩
  C6 : tm 2 6 = some ⟨2, Dir.R, some 0⟩

structure Fwp2_H8Core (tm : TM) : Prop where
  h7 : Fwp2_H7Core tm
  A8 : tm 0 8 = some ⟨8, Dir.L, some 7⟩
  G8 : tm 6 8 = some ⟨7, Dir.L, some 6⟩
  G4 : tm 6 4 = some ⟨7, Dir.L, some 6⟩
  B7 : tm 1 7 = some ⟨3, Dir.R, some 2⟩
  C7 : tm 2 7 = some ⟨3, Dir.R, some 4⟩
  E7 : tm 4 7 = some ⟨3, Dir.R, some 5⟩
  F7 : tm 5 7 = some ⟨2, Dir.R, some 0⟩

/-! ### Shared `rule_6_H`, `rule_7_H`, `rule_8_H` -/

private theorem loop_H4_H6 {tm : TM} (h6 : Fwp2_H6Core tm) (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 7) (rep n 4 L) (4 :: R))
               (mkCfgR (some 7) L (4 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 7) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 7) (rep k 4 L) (4 :: 2 :: R)) :=
      step_mkCfgR_L_cons h6.H4
    have h2 := ih (2 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

theorem rule_6_H {tm : TM} (h6 : Fwp2_H6Core tm) (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches tm (Scfg (r + 1) 0 m (6 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have h1 : step tm (Scfg (r + 1) 0 m (6 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons h6.A6
  obtain ⟨ts, hs⟩ := sweep_HG h6.fh r m 6 R
  have h2 : step tm (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (6 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: 2 :: R)) :=
    step_mkCfgR_L_cons h6.G6
  have h3 := loop_H4_H6 h6 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step tm (mkCfgR (some 7) (5 :: rep r 5 []) (4 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_L_cons h6.H4
  have h5 : step tm (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_R h6.fh.H5
  obtain ⟨r', m', te, he, hme, hte⟩ := exec_G2_2s h6.fh r m hm R
  have hpre := steps_succ tm _ _ _ _ h1 (reaches_trans hs
    (steps_succ tm _ _ _ _ h2 (reaches_trans h3 (steps_succ tm _ _ _ _ h4 (steps_one tm _ _ h5)))))
  exact ⟨r', m', _, reaches_trans hpre he, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

theorem rule_6_H_rep {tm : TM} (h6 : Fwp2_H6Core tm) (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches tm (Scfg (r + 1) 0 m (rep n 6 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H_plus2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t ∧ 1 ≤ r') := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero tm _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_6_H h6 r m hm R
      exact ⟨r1 + 1, m1, t1, h1, hm1, fun _ => ⟨ht1, by omega⟩⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_6_H h6 r m hm (rep (p' + 1) 6 R)
      have hm1p : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H_plus2_ge_17 m) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih (r1 + 1) m1 R hm1p
      have hcomm : iter H_plus2 (p' + 1) (H_plus2 m) = iter H_plus2 (p' + 2) m :=
        (iter_add H_plus2 (p' + 1) 1 m).symm
      have hmb : iter H_plus2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        ⟨Nat.le_trans (ht2 (Nat.succ_pos p')).1 (Nat.le_add_left _ _), (ht2 (Nat.succ_pos p')).2⟩⟩

private theorem loop_D4_H7 {tm : TM} (h7 : Fwp2_H7Core tm) (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 3) (rep n 4 L) (4 :: R))
               (mkCfgR (some 3) L (4 :: rep n 6 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 3) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 3) (rep k 4 L) (4 :: 6 :: R)) :=
      step_mkCfgR_L_cons h7.D4
    have h2 := ih (6 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

theorem reload_7_H {tm : TM} (h7 : Fwp2_H7Core tm) (r m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (Scfg (r + 2) 0 m (7 :: R)) (Scfg (r + 1) 0 1 (rep (2 * m) 6 R)) t := by
  have h1 : step tm (Scfg (r + 2) 0 m (7 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 2) 5 [])) (2 :: 7 :: R)) :=
    step_mkCfgR_L_cons h7.A7
  obtain ⟨ts, hs⟩ := sweep_HG h7.h6.fh (r + 1) m 7 R
  have h2 : step tm (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 2) 5 [])) (7 :: R)) =
            some (mkCfgR (some 3) (rep (2 * m + 1) 4 (rep (r + 2) 5 [])) (4 :: 6 :: R)) :=
    step_mkCfgR_L_cons h7.G7
  have h3 := loop_D4_H7 h7 (2 * m + 1) (rep (r + 2) 5 []) (6 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step tm (mkCfgR (some 3) (5 :: rep (r + 1) 5 []) (4 :: rep (2 * m + 2) 6 R)) =
            some (mkCfgR (some 3) (rep (r + 1) 5 []) (5 :: rep (2 * m + 3) 6 R)) :=
    step_mkCfgR_L_cons h7.D4
  have h5 : step tm (mkCfgR (some 3) (rep (r + 1) 5 []) (5 :: rep (2 * m + 3) 6 R)) =
            some (mkCfgR (some 3) (3 :: rep (r + 1) 5 []) (rep (2 * m + 3) 6 R)) :=
    step_mkCfgR_R h7.h6.fh.fp.D5
  have h6 : step tm (mkCfgR (some 3) (3 :: rep (r + 1) 5 []) (6 :: rep (2 * m + 2) 6 R)) =
            some (mkCfgR (some 1) (3 :: 3 :: rep (r + 1) 5 []) (rep (2 * m + 2) 6 R)) :=
    step_mkCfgR_R h7.D6
  have h7s : step tm (mkCfgR (some 1) (3 :: 3 :: rep (r + 1) 5 []) (6 :: rep (2 * m + 1) 6 R)) =
             some (mkCfgR (some 2) (3 :: 3 :: 3 :: rep (r + 1) 5 []) (rep (2 * m + 1) 6 R)) :=
    step_mkCfgR_R h7.B6
  have h8 : step tm (mkCfgR (some 2) (3 :: 3 :: 3 :: rep (r + 1) 5 []) (6 :: rep (2 * m) 6 R)) =
            some (Scfg (r + 1) 0 1 (rep (2 * m) 6 R)) :=
    step_mkCfgR_R h7.C6
  exact ⟨_, reaches_trans (steps_succ tm _ _ _ _ h1 (reaches_trans hs (steps_succ tm _ _ _ _ h2 h3)))
    (steps_succ tm _ _ _ _ h4 (steps_succ tm _ _ _ _ h5
      (steps_succ tm _ _ _ _ h6 (steps_succ tm _ _ _ _ h7s (steps_one tm _ _ h8)))))⟩

theorem rule_7_H {tm : TM} (h7 : Fwp2_H7Core tm) (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches tm (Scfg (r + 2) 0 m (7 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H7_H m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_7_H h7 r m R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_6_H_rep h7.h6 (2 * m) r 1 R (by omega)
  obtain ⟨ht2_le, hr2_pos⟩ := ht2 (by omega)
  cases r2 with
  | zero => omega
  | succ r2' =>
    exact ⟨r2', m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans ht2_le (Nat.le_add_left _ _)⟩

theorem rule_7_H_rep {tm : TM} (h7 : Fwp2_H7Core tm) (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches tm (Scfg (r + 2) 0 m (rep n 7 R)) (Scfg (r' + 2) 0 m' R) t ∧
      iter H7_H n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero tm _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_7_H h7 r m hm R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_7_H h7 r m hm (rep (p' + 1) 7 R)
      have hm1p : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H7_H_ge_17 m hm) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R hm1p
      have hcomm : iter H7_H (p' + 1) (H7_H m) = iter H7_H (p' + 2) m := (iter_add H7_H (p' + 1) 1 m).symm
      have hmb : iter H7_H (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H7_H (fun _ _ h => H7_H_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

private theorem loop_G4_H8 {tm : TM} (h8 : Fwp2_H8Core tm) (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 6) (rep n 4 L) (4 :: R))
               (mkCfgR (some 6) L (4 :: rep n 7 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 6) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 6) (rep k 4 L) (4 :: 7 :: R)) :=
      step_mkCfgR_L_cons h8.G4
    have h2 := ih (7 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

private theorem loop_G5_H8 {tm : TM} (h8 : Fwp2_H8Core tm) (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 6) (rep n 5 L) (5 :: R))
               (mkCfgR (some 6) L (5 :: rep n 5 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 6) (5 :: rep k 5 L) (5 :: R)) =
              some (mkCfgR (some 6) (rep k 5 L) (5 :: 5 :: R)) :=
      step_mkCfgR_L_cons h8.h7.h6.fh.fp.G5
    have h2 := ih (5 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

theorem reload_8_H {tm : TM} (h8 : Fwp2_H8Core tm) (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ t, Reaches tm (Scfg (r + 1) 0 m (8 :: R)) (Scfg (r + 3) 0 1 (rep (2 * m - 1) 7 R)) t := by
  cases m with
  | zero => cases hm
  | succ m' =>
    have h1 : step tm (Scfg (r + 1) 0 (m' + 1) (8 :: R)) =
              some (mkCfgR (some 7) (rep (2 * (m' + 1) + 1) 3 (rep (r + 1) 5 [])) (2 :: 8 :: R)) :=
      step_mkCfgR_L_cons h8.A8
    obtain ⟨ts, hs⟩ := sweep_HG h8.h7.h6.fh r (m' + 1) 8 R
    have h2 : step tm (mkCfgR (some 6) (4 :: rep (2 * (m' + 1) + 1) 4 (rep (r + 1) 5 [])) (8 :: R)) =
              some (mkCfgR (some 6) (rep (2 * (m' + 1) + 1) 4 (rep (r + 1) 5 [])) (4 :: 7 :: R)) :=
      step_mkCfgR_L_cons h8.G8
    have h3 := loop_G4_H8 h8 (2 * (m' + 1) + 1) (rep (r + 1) 5 []) (7 :: R)
    rw [rep_snoc_one] at h3
    have h4 : step tm (mkCfgR (some 6) (5 :: rep r 5 []) (4 :: rep (2 * (m' + 1) + 2) 7 R)) =
              some (mkCfgR (some 6) (rep r 5 []) (5 :: rep (2 * (m' + 1) + 3) 7 R)) :=
      step_mkCfgR_L_cons h8.G4
    have h5 := loop_G5_H8 h8 r [] (rep (2 * (m' + 1) + 3) 7 R)
    have h6 : step tm (mkCfgR (some 6) [] (5 :: rep r 5 (rep (2 * (m' + 1) + 3) 7 R))) =
              some (mkCfgR (some 6) [] (0 :: rep (r + 1) 5 (rep (2 * (m' + 1) + 3) 7 R))) :=
      step_mkCfgR_L_nil h8.h7.h6.fh.fp.G5
    have h7s : step tm (mkCfgR (some 6) [] (0 :: rep (r + 1) 5 (rep (2 * (m' + 1) + 3) 7 R))) =
               some (mkCfgR (some 5) [] (0 :: rep (r + 2) 5 (rep (2 * (m' + 1) + 3) 7 R))) :=
      step_mkCfgR_L_nil h8.h7.h6.fh.fp.G0
    have h8s : step tm (mkCfgR (some 5) [] (0 :: rep (r + 2) 5 (rep (2 * (m' + 1) + 3) 7 R))) =
               some (mkCfgR (some 1) [5] (rep (r + 2) 5 (rep (2 * (m' + 1) + 3) 7 R))) :=
      step_mkCfgR_R h8.h7.h6.fh.fp.F0
    have h9 := loop_B5_H h8.h7.h6.fh (r + 2) [5] (rep (2 * (m' + 1) + 3) 7 R)
    have hrep5 : rep (r + 2) 5 [5] = rep (r + 3) 5 [] := by rw [rep_snoc_one]; rfl
    rw [hrep5] at h9
    have h7eq : rep (2 * (m' + 1) + 3) 7 R = 7 :: 7 :: 7 :: 7 :: rep (2 * (m' + 1) - 1) 7 R := by
      have ha : 2 * (m' + 1) + 3 = (2 * (m' + 1) - 1) + 4 := by omega
      rw [ha]; rfl
    rw [h7eq] at h9
    have h10 : Reaches tm
        (mkCfgR (some 1) (rep (r + 3) 5 []) (7 :: 7 :: 7 :: 7 :: rep (2 * (m' + 1) - 1) 7 R))
        (Scfg (r + 3) 0 1 (rep (2 * (m' + 1) - 1) 7 R)) 4 := by
      refine steps_succ tm 3 _ _ _ (step_mkCfgR_R h8.B7) ?_
      refine steps_succ tm 2 _ _ _ (step_mkCfgR_R h8.C7) ?_
      refine steps_succ tm 1 _ _ _ (step_mkCfgR_R h8.E7) ?_
      exact steps_one tm _ _ (step_mkCfgR_R h8.F7)
    have ha := steps_succ tm _ _ _ _ h1 (reaches_trans hs (steps_succ tm _ _ _ _ h2 h3))
    have hb := steps_succ tm _ _ _ _ h4 (reaches_trans h5 (steps_succ tm _ _ _ _ h6
      (steps_succ tm _ _ _ _ h7s (steps_succ tm _ _ _ _ h8s (reaches_trans h9 h10)))))
    exact ⟨_, reaches_trans ha hb⟩

theorem rule_8_H {tm : TM} (h8 : Fwp2_H8Core tm) (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches tm (Scfg (r + 1) 0 m (8 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H8_H m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_8_H h8 r m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_7_H_rep h8.h7 (2 * m - 1) (r + 1) 1 R (by omega)
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem rule_8_H_rep {tm : TM} (h8 : Fwp2_H8Core tm) (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches tm (Scfg (r + 2) 0 m (rep n 8 R)) (Scfg (r' + 2) 0 m' R) t ∧
      iter H8_H n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero tm _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_8_H h8 (r + 1) m hm R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_8_H h8 (r + 1) m hm (rep (p' + 1) 8 R)
      have hm1p : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H8_H_ge_17 m hm) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R hm1p
      have hcomm : iter H8_H (p' + 1) (H8_H m) = iter H8_H (p' + 2) m := (iter_add H8_H (p' + 1) 1 m).symm
      have hmb : iter H8_H (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H8_H (fun _ _ h => H8_H_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

/-! ### Generic Cursor-5 Combinators -/

/-- 2-step halt on `5 0` (`A5 = (mark'+1) R I`, `I0 = 1 R Z`). -/
theorem halt_cursor_5 {tm : TM} {mark' : Nat}
    (hA5 : tm 0 5 = some ⟨mark' + 1, Dir.R, some 8⟩)
    (hI0 : tm 8 0 = some ⟨1, Dir.R, none⟩)
    (r m : Nat) :
    ∃ cf, Reaches tm (Scfg r 0 m [5]) cf 2 ∧ cf.st = none := by
  have h1 : step tm (Scfg r 0 m [5]) =
            some (mkCfgR (some 8) ((mark' + 1) :: 2 :: rep (2 * m + 1) 3 (rep r 5 [])) []) :=
    step_mkCfgR_R hA5
  have h2 : step tm (mkCfgR (some 8) ((mark' + 1) :: 2 :: rep (2 * m + 1) 3 (rep r 5 [])) []) =
            some (mkCfgR none (1 :: (mark' + 1) :: 2 :: rep (2 * m + 1) 3 (rep r 5 [])) []) :=
    step_mkCfgR_R_nil hI0
  exact ⟨_, steps_succ tm 1 _ _ _ h1 (steps_one tm _ _ h2), rfl⟩

/-- Generic repetition of any cursor-5 macro rule requiring `1 ≤ m`. -/
theorem iter_cursor_rep {tm : TM} (minR sym : Nat) (H : Nat → Nat)
    (hmono : ∀ x y, x ≤ y → H x ≤ H y)
    (hpos : ∀ x, 1 ≤ x → 1 ≤ H x)
    (hstep : ∀ r m R, 1 ≤ m →
      ∃ r' m' t, Reaches tm (Scfg (r + minR) 0 m (5 :: sym :: R))
                            (Scfg (r' + minR) 0 m' (5 :: R)) t ∧ H m ≤ m' ∧ m' ≤ t)
    (n : Nat) :
    ∀ r m R, 1 ≤ m →
      ∃ r' m' t, Reaches tm (Scfg (r + minR) 0 m (5 :: rep n sym R))
                            (Scfg (r' + minR) 0 m' (5 :: R)) t ∧
        iter H n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero tm _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := hstep r m R hm
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := hstep r m (rep (p' + 1) sym R) hm
      have hm1p : 1 ≤ m1 := Nat.le_trans (hpos m hm) hm1
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R hm1p
      have hcomm : iter H (p' + 1) (H m) = iter H (p' + 2) m := (iter_add H (p' + 1) 1 m).symm
      have hmb : iter H (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H hmono (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

/-- Generic repetition of any cursor-5 macro rule that works for ALL `m : Nat` (including `m = 0`). -/
theorem iter_cursor_rep0 {tm : TM} (minR sym : Nat) (H : Nat → Nat)
    (hmono : ∀ x y, x ≤ y → H x ≤ H y)
    (hstep : ∀ r m R,
      ∃ r' m' t, Reaches tm (Scfg (r + minR) 0 m (5 :: sym :: R))
                            (Scfg (r' + minR) 0 m' (5 :: R)) t ∧ H m ≤ m' ∧ m' ≤ t)
    (n : Nat) :
    ∀ r m R,
      ∃ r' m' t, Reaches tm (Scfg (r + minR) 0 m (5 :: rep n sym R))
                            (Scfg (r' + minR) 0 m' (5 :: R)) t ∧
        iter H n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero tm _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := hstep r m R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := hstep r m (rep (p' + 1) sym R)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R
      have hcomm : iter H (p' + 1) (H m) = iter H (p' + 2) m := (iter_add H (p' + 1) 1 m).symm
      have hmb : iter H (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H hmono (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

/-- Generic left sweep turning `3`s into `w' + 1` in state `q`. -/
theorem loop_L3 {tm : TM} {q w' : Nat}
    (hq3 : tm q 3 = some ⟨w' + 1, Dir.L, some q⟩)
    (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some q) (rep n 3 L) (3 :: R))
               (mkCfgR (some q) L (3 :: rep n (w' + 1) R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some q) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some q) (rep k 3 L) (3 :: (w' + 1) :: R)) :=
      step_mkCfgR_L_cons hq3
    have h2 := ih ((w' + 1) :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

/-- Shared `5 1` reload for ALL 9 cores in `BB(9..11, 7..9)`:
    `Scfg (r+1) 0 m (5 :: 1 :: R) --> Scfg (r+1) 0 1 (rep (2*m - 1) (low'+1) (5 :: R))` (`m ≥ 1`). -/
theorem reload_51_4step {tm : TM} {sw mark' low' s1 s2 s3 : Nat}
    (hA5 : tm 0 5 = some ⟨mark' + 1, Dir.R, some 8⟩)
    (hI1 : tm 8 1 = some ⟨5, Dir.L, some sw⟩)
    (hswM : tm sw (mark' + 1) = some ⟨low' + 1, Dir.L, some sw⟩)
    (hsw2 : tm sw 2 = some ⟨low' + 1, Dir.L, some sw⟩)
    (hsw3 : tm sw 3 = some ⟨low' + 1, Dir.L, some sw⟩)
    (hsw5 : tm sw 5 = some ⟨5, Dir.R, some 1⟩)
    (hB : tm 1 (low' + 1) = some ⟨3, Dir.R, some s1⟩)
    (h1 : tm s1 (low' + 1) = some ⟨3, Dir.R, some s2⟩)
    (h2 : tm s2 (low' + 1) = some ⟨3, Dir.R, some s3⟩)
    (h3 : tm s3 (low' + 1) = some ⟨2, Dir.R, some 0⟩)
    (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ t, Reaches tm (Scfg (r + 1) 0 m (5 :: 1 :: R))
                    (Scfg (r + 1) 0 1 (rep (2 * m - 1) (low' + 1) (5 :: R))) t := by
  cases m with
  | zero => cases hm
  | succ m' =>
    have ha : step tm (Scfg (r + 1) 0 (m' + 1) (5 :: 1 :: R)) =
              some (mkCfgR (some 8) ((mark' + 1) :: 2 :: rep (2 * (m' + 1) + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) :=
      step_mkCfgR_R hA5
    have hb : step tm (mkCfgR (some 8) ((mark' + 1) :: 2 :: rep (2 * (m' + 1) + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) =
              some (mkCfgR (some sw) (2 :: rep (2 * (m' + 1) + 1) 3 (rep (r + 1) 5 [])) ((mark' + 1) :: 5 :: R)) :=
      step_mkCfgR_L_cons hI1
    have hc : step tm (mkCfgR (some sw) (2 :: rep (2 * (m' + 1) + 1) 3 (rep (r + 1) 5 [])) ((mark' + 1) :: 5 :: R)) =
              some (mkCfgR (some sw) (rep (2 * (m' + 1) + 1) 3 (rep (r + 1) 5 [])) (2 :: (low' + 1) :: 5 :: R)) :=
      step_mkCfgR_L_cons hswM
    have hd : step tm (mkCfgR (some sw) (3 :: rep (2 * (m' + 1)) 3 (rep (r + 1) 5 [])) (2 :: (low' + 1) :: 5 :: R)) =
              some (mkCfgR (some sw) (rep (2 * (m' + 1)) 3 (rep (r + 1) 5 [])) (3 :: (low' + 1) :: (low' + 1) :: 5 :: R)) :=
      step_mkCfgR_L_cons hsw2
    have he := loop_L3 hsw3 (2 * (m' + 1)) (rep (r + 1) 5 []) ((low' + 1) :: (low' + 1) :: 5 :: R)
    rw [rep_snoc_one, rep_snoc_one] at he
    have hf : step tm (mkCfgR (some sw) (5 :: rep r 5 []) (3 :: rep (2 * (m' + 1) + 2) (low' + 1) (5 :: R))) =
              some (mkCfgR (some sw) (rep r 5 []) (5 :: rep (2 * (m' + 1) + 3) (low' + 1) (5 :: R))) :=
      step_mkCfgR_L_cons hsw3
    have hg : step tm (mkCfgR (some sw) (rep r 5 []) (5 :: rep (2 * (m' + 1) + 3) (low' + 1) (5 :: R))) =
              some (mkCfgR (some 1) (rep (r + 1) 5 []) (rep (2 * (m' + 1) + 3) (low' + 1) (5 :: R))) :=
      step_mkCfgR_R hsw5
    have hsplit : rep (2 * (m' + 1) + 3) (low' + 1) (5 :: R) =
                  (low' + 1) :: (low' + 1) :: (low' + 1) :: (low' + 1) :: rep (2 * (m' + 1) - 1) (low' + 1) (5 :: R) := by
      have heq : 2 * (m' + 1) + 3 = (2 * (m' + 1) - 1) + 4 := by omega
      rw [heq]; rfl
    rw [hsplit] at hg
    have hh : Reaches tm
        (mkCfgR (some 1) (rep (r + 1) 5 []) ((low' + 1) :: (low' + 1) :: (low' + 1) :: (low' + 1) :: rep (2 * (m' + 1) - 1) (low' + 1) (5 :: R)))
        (Scfg (r + 1) 0 1 (rep (2 * (m' + 1) - 1) (low' + 1) (5 :: R))) 4 := by
      refine steps_succ tm 3 _ _ _ (step_mkCfgR_R hB) ?_
      refine steps_succ tm 2 _ _ _ (step_mkCfgR_R h1) ?_
      refine steps_succ tm 1 _ _ _ (step_mkCfgR_R h2) ?_
      exact steps_one tm _ _ (step_mkCfgR_R h3)
    have hp1 := steps_succ tm _ _ _ _ ha (steps_succ tm _ _ _ _ hb
      (steps_succ tm _ _ _ _ hc (steps_succ tm _ _ _ _ hd he)))
    have hp2 := steps_succ tm _ _ _ _ hf (steps_succ tm _ _ _ _ hg hh)
    exact ⟨_, reaches_trans hp1 hp2⟩

/-- Shared `5 mark` reload for ALL 6 cores in `BB(10..11, 7..9)`:
    `Scfg (r+1) 0 m (5 :: (mark'+1) :: R) --> Scfg (r+1) 0 (Pempty r) (5 :: rep (2*m + 1) 1 R)` (works for ALL `m`!). -/
theorem reload_5mark_empty {tm : TM} {mark' : Nat} (fp : Fwp2Core tm)
    (hA5 : tm 0 5 = some ⟨mark' + 1, Dir.R, some 8⟩)
    (hIM : tm 8 (mark' + 1) = some ⟨1, Dir.L, some 8⟩)
    (hI2 : tm 8 2 = some ⟨1, Dir.L, some 8⟩)
    (hI3 : tm 8 3 = some ⟨1, Dir.L, some 8⟩)
    (hI5 : tm 8 5 = some ⟨5, Dir.R, some 7⟩)
    (hH1 : tm 7 1 = some ⟨2, Dir.R, some 5⟩)
    (hF1 : tm 5 1 = some ⟨1, Dir.R, some 9⟩)
    (hJ1 : tm 9 1 = some ⟨5, Dir.L, some 0⟩)
    (r m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (Scfg (r + 1) 0 m (5 :: (mark' + 1) :: R))
                    (Scfg (r + 1) 0 (Pempty r) (5 :: rep (2 * m + 1) 1 R)) t := by
  have ha : step tm (Scfg (r + 1) 0 m (5 :: (mark' + 1) :: R)) =
            some (mkCfgR (some 8) ((mark' + 1) :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) ((mark' + 1) :: R)) :=
    step_mkCfgR_R hA5
  have hb : step tm (mkCfgR (some 8) ((mark' + 1) :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) ((mark' + 1) :: R)) =
            some (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) ((mark' + 1) :: 1 :: R)) :=
    step_mkCfgR_L_cons hIM
  have hc : step tm (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) ((mark' + 1) :: 1 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 1 :: 1 :: R)) :=
    step_mkCfgR_L_cons hIM
  have hd : step tm (mkCfgR (some 8) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 1 :: 1 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 1 :: 1 :: 1 :: R)) :=
    step_mkCfgR_L_cons hI2
  have he := loop_L3 hI3 (2 * m) (rep (r + 1) 5 []) (1 :: 1 :: 1 :: R)
  rw [rep_snoc_one, rep_snoc_one, rep_snoc_one] at he
  have hf : step tm (mkCfgR (some 8) (5 :: rep r 5 []) (3 :: rep (2 * m + 3) 1 R)) =
            some (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 4) 1 R)) :=
    step_mkCfgR_L_cons hI3
  have hg : step tm (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 4) 1 R)) =
            some (mkCfgR (some 7) (rep (r + 1) 5 []) (rep (2 * m + 4) 1 R)) :=
    step_mkCfgR_R hI5
  have hsplit : rep (2 * m + 4) 1 R = 1 :: 1 :: 1 :: rep (2 * m + 1) 1 R := by
    have heq : 2 * m + 4 = (2 * m + 1) + 3 := by omega
    rw [heq]; rfl
  rw [hsplit] at hg
  have hh : Reaches tm
      (mkCfgR (some 7) (rep (r + 1) 5 []) (1 :: 1 :: 1 :: rep (2 * m + 1) 1 R))
      (mkCfgR (some 0) (2 :: rep (r + 1) 5 []) (1 :: 5 :: rep (2 * m + 1) 1 R)) 3 := by
    refine steps_succ tm 2 _ _ _ (step_mkCfgR_R hH1) ?_
    refine steps_succ tm 1 _ _ _ (step_mkCfgR_R hF1) ?_
    exact steps_one tm _ _ (step_mkCfgR_L_cons hJ1)
  obtain ⟨te, hempty, _⟩ := fwp2_empty3 fp r (5 :: rep (2 * m + 1) 1 R)
  have hp1 := steps_succ tm _ _ _ _ ha (steps_succ tm _ _ _ _ hb
    (steps_succ tm _ _ _ _ hc (steps_succ tm _ _ _ _ hd he)))
  have hp2 := steps_succ tm _ _ _ _ hf (steps_succ tm _ _ _ _ hg (reaches_trans hh hempty))
  exact ⟨_, reaches_trans hp1 hp2⟩

/-- Shared `5 top` reload for ALL 3 cores in `BB(11, 7..9)`:
    `Scfg (r+1) 0 m (5 :: top :: R) --> Scfg (r+1) 0 0 (5 :: rep (2*m + 1) (mark'+1) R)` (works for ALL `m`!). -/
theorem reload_5top_zero {tm : TM} {mark' top e1 e2 e3 : Nat}
    (hA5 : tm 0 5 = some ⟨mark' + 1, Dir.R, some 8⟩)
    (hIt : tm 8 top = some ⟨mark' + 1, Dir.L, some 10⟩)
    (hKM : tm 10 (mark' + 1) = some ⟨mark' + 1, Dir.L, some 10⟩)
    (hK2 : tm 10 2 = some ⟨mark' + 1, Dir.L, some 10⟩)
    (hK3 : tm 10 3 = some ⟨mark' + 1, Dir.L, some 10⟩)
    (hK5 : tm 10 5 = some ⟨5, Dir.R, some e1⟩)
    (he1 : tm e1 (mark' + 1) = some ⟨3, Dir.R, some e2⟩)
    (he2 : tm e2 (mark' + 1) = some ⟨2, Dir.R, some e3⟩)
    (he3 : tm e3 (mark' + 1) = some ⟨5, Dir.L, some 5⟩)
    (hF2 : tm 5 2 = some ⟨2, Dir.R, some 0⟩)
    (r m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (Scfg (r + 1) 0 m (5 :: top :: R))
                    (Scfg (r + 1) 0 0 (5 :: rep (2 * m + 1) (mark' + 1) R)) t := by
  have ha : step tm (Scfg (r + 1) 0 m (5 :: top :: R)) =
            some (mkCfgR (some 8) ((mark' + 1) :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (top :: R)) :=
    step_mkCfgR_R hA5
  have hb : step tm (mkCfgR (some 8) ((mark' + 1) :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (top :: R)) =
            some (mkCfgR (some 10) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) ((mark' + 1) :: (mark' + 1) :: R)) :=
    step_mkCfgR_L_cons hIt
  have hc : step tm (mkCfgR (some 10) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) ((mark' + 1) :: (mark' + 1) :: R)) =
            some (mkCfgR (some 10) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: (mark' + 1) :: (mark' + 1) :: R)) :=
    step_mkCfgR_L_cons hKM
  have hd : step tm (mkCfgR (some 10) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: (mark' + 1) :: (mark' + 1) :: R)) =
            some (mkCfgR (some 10) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: (mark' + 1) :: (mark' + 1) :: (mark' + 1) :: R)) :=
    step_mkCfgR_L_cons hK2
  have he := loop_L3 hK3 (2 * m) (rep (r + 1) 5 []) ((mark' + 1) :: (mark' + 1) :: (mark' + 1) :: R)
  rw [rep_snoc_one, rep_snoc_one, rep_snoc_one] at he
  have hf : step tm (mkCfgR (some 10) (5 :: rep r 5 []) (3 :: rep (2 * m + 3) (mark' + 1) R)) =
            some (mkCfgR (some 10) (rep r 5 []) (5 :: rep (2 * m + 4) (mark' + 1) R)) :=
    step_mkCfgR_L_cons hK3
  have hg : step tm (mkCfgR (some 10) (rep r 5 []) (5 :: rep (2 * m + 4) (mark' + 1) R)) =
            some (mkCfgR (some e1) (rep (r + 1) 5 []) (rep (2 * m + 4) (mark' + 1) R)) :=
    step_mkCfgR_R hK5
  have hsplit : rep (2 * m + 4) (mark' + 1) R =
                (mark' + 1) :: (mark' + 1) :: (mark' + 1) :: rep (2 * m + 1) (mark' + 1) R := by
    have heq : 2 * m + 4 = (2 * m + 1) + 3 := by omega
    rw [heq]; rfl
  rw [hsplit] at hg
  have hh : Reaches tm
      (mkCfgR (some e1) (rep (r + 1) 5 []) ((mark' + 1) :: (mark' + 1) :: (mark' + 1) :: rep (2 * m + 1) (mark' + 1) R))
      (Scfg (r + 1) 0 0 (5 :: rep (2 * m + 1) (mark' + 1) R)) 4 := by
    refine steps_succ tm 3 _ _ _ (step_mkCfgR_R he1) ?_
    refine steps_succ tm 2 _ _ _ (step_mkCfgR_R he2) ?_
    refine steps_succ tm 1 _ _ _ (step_mkCfgR_L_cons he3) ?_
    exact steps_one tm _ _ (step_mkCfgR_R hF2)
  have hp1 := steps_succ tm _ _ _ _ ha (steps_succ tm _ _ _ _ hb
    (steps_succ tm _ _ _ _ hc (steps_succ tm _ _ _ _ hd he)))
  have hp2 := steps_succ tm _ _ _ _ hf (steps_succ tm _ _ _ _ hg hh)
  exact ⟨_, reaches_trans hp1 hp2⟩

end BB
