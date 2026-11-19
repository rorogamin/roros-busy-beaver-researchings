/-
  BB/BB8_8.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(8, 8):
    TM: 6LB3LB2LH2RA4LB1RZ6LH7LH_7RG3RB1LD2RA3LF5RB3RC7LC_3RB1LB3LC2RC4LC1LE2RA4RB_3RB3RE3LC2RC6LD3RD3RB7LG_5RB3RE4RG4LC3LG5LE1RZ7LD_5RB5RB0RD1LF5LF5LF2LG7LD_5LF4RG1LB1LG7RH5LG2LH6LD_7LA7LA1LH1LH2LH5RG1RZ7RF
    Domain: BB(8, 8) (8 states, 8 symbols)
    Previous best dominated bounds: BB(8, 7) > f_{ω^2+2}(8), BB(7, 8) > f_{ω^2+2}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+3}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H

namespace BB
namespace BB8_8

def bb88 : TM
  -- State A (0): 6LB 3LB 2LH 2RA 4LB 1RZ 6LH 7LH
  | 0, 0 => some ⟨6, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨1, Dir.R, none⟩
  | 0, 6 => some ⟨6, Dir.L, some 7⟩
  | 0, 7 => some ⟨7, Dir.L, some 7⟩
  -- State B (1): 7RG 3RB 1LD 2RA 3LF 5RB 3RC 7LC
  | 1, 0 => some ⟨7, Dir.R, some 6⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨3, Dir.R, some 2⟩
  | 1, 7 => some ⟨7, Dir.L, some 2⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 2RA 4RB
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨2, Dir.R, some 0⟩
  | 2, 7 => some ⟨4, Dir.R, some 1⟩
  -- State D (3): 3RB 3RE 3LC 2RC 6LD 3RD 3RB 7LG
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨6, Dir.L, some 3⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨3, Dir.R, some 1⟩
  | 3, 7 => some ⟨7, Dir.L, some 6⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 1RZ 7LD
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨1, Dir.R, none⟩
  | 4, 7 => some ⟨7, Dir.L, some 3⟩
  -- State F (5): 5RB 5RB 0RD 1LF 5LF 5LF 2LG 7LD
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨0, Dir.R, some 3⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨2, Dir.L, some 6⟩
  | 5, 7 => some ⟨7, Dir.L, some 3⟩
  -- State G (6): 5LF 4RG 1LB 1LG 7RH 5LG 2LH 6LD
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨7, Dir.R, some 7⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨2, Dir.L, some 7⟩
  | 6, 7 => some ⟨6, Dir.L, some 3⟩
  -- State H (7): 7LA 7LA 1LH 1LH 2LH 5RG 1RZ 7RF
  | 7, 0 => some ⟨7, Dir.L, some 0⟩
  | 7, 1 => some ⟨7, Dir.L, some 0⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | 7, 6 => some ⟨1, Dir.R, none⟩
  | 7, 7 => some ⟨7, Dir.R, some 5⟩
  | _, _ => none

theorem bb88_valid : ValidTM 8 8 bb88 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 6 | 7 => exact ⟨by decide, by decide⟩ | 5 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | _ + 8 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 8 => rfl

theorem bb88_core : Fwp2_HCore bb88 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_H4 (n : Nat) (L R : List Nat) :
    Reaches bb88 (mkCfgR (some 7) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 7) L (4 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb88 _
  | succ k ih =>
    have h1 : step bb88 (mkCfgR (some 7) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 7) (rep k 4 L) (4 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb88) (q := 7) (w := 1) (cur := 4) rfl
    have h2 := ih (2 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb88 k _ _ _ h1 h2

private theorem loop_D4 (n : Nat) (L R : List Nat) :
    Reaches bb88 (mkCfgR (some 3) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 3) L (4 :: rep n 6 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb88 _
  | succ k ih =>
    have h1 : step bb88 (mkCfgR (some 3) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 3) (rep k 4 L) (4 :: 6 :: R)) :=
      step_mkCfgR_L_cons (tm := bb88) (q := 3) (w := 5) (cur := 4) rfl
    have h2 := ih (6 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb88 k _ _ _ h1 h2

theorem rule_6 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb88 (Scfg (r + 1) 0 m (6 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have h1 : step bb88 (Scfg (r + 1) 0 m (6 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb88) (q := 0) (w := 5) (cur := 6) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb88_core r m 6 R
  have h2 : step bb88 (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (6 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb88) (q := 6) (w := 1) (cur := 6) rfl
  have h3 := loop_H4 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb88 (mkCfgR (some 7) (5 :: rep r 5 []) (4 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb88) (q := 7) (w := 1) (cur := 4) rfl
  have h5 : step bb88 (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_R (tm := bb88) (q := 7) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he, hme, hte⟩ := exec_G2_2s bb88_core r m hm R
  have hpre := steps_succ bb88 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb88 _ _ _ _ h2 (reaches_trans h3 (steps_succ bb88 _ _ _ _ h4 (steps_one bb88 _ _ h5)))))
  exact ⟨r', m', _, reaches_trans hpre he, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

theorem rule_6_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb88 (Scfg (r + 1) 0 m (rep n 6 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H_plus2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t ∧ 1 ≤ r') := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb88 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_6 r m hm R
      exact ⟨r1 + 1, m1, t1, h1, hm1, fun _ => ⟨ht1, by omega⟩⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_6 r m hm (rep (p' + 1) 6 R)
      have hm1p : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H_plus2_ge_17 m) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih (r1 + 1) m1 R hm1p
      have hcomm : iter H_plus2 (p' + 1) (H_plus2 m) = iter H_plus2 (p' + 2) m :=
        (iter_add H_plus2 (p' + 1) 1 m).symm
      have hmb : iter H_plus2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        ⟨Nat.le_trans (ht2 (Nat.succ_pos p')).1 (Nat.le_add_left _ _), (ht2 (Nat.succ_pos p')).2⟩⟩

def H7 (m : Nat) : Nat := iter H_plus2 (2 * m) 1

theorem H7_mono {x y : Nat} (hxy : x ≤ y) : H7 x ≤ H7 y :=
  iter_mono_steps H_plus2 (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z' => exact Nat.le_trans (Nat.le_succ _) (H_plus2_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H7_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H7 m :=
  climb_double H_plus2 (f_omega2_plus 1) 1 (by omega) (fun _ _ h => H_plus2_mono h) H_plus2_inc H_plus2_gt
    (fOmega2_props 1 0 1) m hm

theorem H7_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H7 m := by
  have h1 : 1 ≤ 2 * m := by omega
  cases h2m : 2 * m with
  | zero => omega
  | succ q =>
    unfold H7; rw [h2m, iter_succ]; exact H_plus2_ge_17 _

theorem reload_7 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb88 (Scfg (r + 2) 0 m (7 :: R)) (Scfg (r + 1) 0 1 (rep (2 * m) 6 R)) t := by
  have h1 : step bb88 (Scfg (r + 2) 0 m (7 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 2) 5 [])) (2 :: 7 :: R)) :=
    step_mkCfgR_L_cons (tm := bb88) (q := 0) (w := 6) (cur := 7) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb88_core (r + 1) m 7 R
  have h2 : step bb88 (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 2) 5 [])) (7 :: R)) =
            some (mkCfgR (some 3) (rep (2 * m + 1) 4 (rep (r + 2) 5 [])) (4 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb88) (q := 6) (w := 5) (cur := 7) rfl
  have h3 := loop_D4 (2 * m + 1) (rep (r + 2) 5 []) (6 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb88 (mkCfgR (some 3) (5 :: rep (r + 1) 5 []) (4 :: rep (2 * m + 2) 6 R)) =
            some (mkCfgR (some 3) (rep (r + 1) 5 []) (5 :: rep (2 * m + 3) 6 R)) :=
    step_mkCfgR_L_cons (tm := bb88) (q := 3) (w := 5) (cur := 4) rfl
  have h5 : step bb88 (mkCfgR (some 3) (rep (r + 1) 5 []) (5 :: rep (2 * m + 3) 6 R)) =
            some (mkCfgR (some 3) (3 :: rep (r + 1) 5 []) (rep (2 * m + 3) 6 R)) :=
    step_mkCfgR_R (tm := bb88) (q := 3) (w := 2) (cur := 5) rfl
  have h6 : step bb88 (mkCfgR (some 3) (3 :: rep (r + 1) 5 []) (6 :: rep (2 * m + 2) 6 R)) =
            some (mkCfgR (some 1) (3 :: 3 :: rep (r + 1) 5 []) (rep (2 * m + 2) 6 R)) :=
    step_mkCfgR_R (tm := bb88) (q := 3) (w := 2) (cur := 6) rfl
  have h7 : step bb88 (mkCfgR (some 1) (3 :: 3 :: rep (r + 1) 5 []) (6 :: rep (2 * m + 1) 6 R)) =
            some (mkCfgR (some 2) (3 :: 3 :: 3 :: rep (r + 1) 5 []) (rep (2 * m + 1) 6 R)) :=
    step_mkCfgR_R (tm := bb88) (q := 1) (w := 2) (cur := 6) rfl
  have h8 : step bb88 (mkCfgR (some 2) (3 :: 3 :: 3 :: rep (r + 1) 5 []) (6 :: rep (2 * m) 6 R)) =
            some (Scfg (r + 1) 0 1 (rep (2 * m) 6 R)) :=
    step_mkCfgR_R (tm := bb88) (q := 2) (w := 1) (cur := 6) rfl
  have ha := steps_succ bb88 _ _ _ _ h1 (reaches_trans hs (steps_succ bb88 _ _ _ _ h2 h3))
  have hb := steps_succ bb88 _ _ _ _ h4 (steps_succ bb88 _ _ _ _ h5
    (steps_succ bb88 _ _ _ _ h6 (steps_succ bb88 _ _ _ _ h7 (steps_one bb88 _ _ h8))))
  exact ⟨_, reaches_trans ha hb⟩

theorem rule_7 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb88 (Scfg (r + 2) 0 m (7 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_7 r m R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_6_rep (2 * m) r 1 R (by omega)
  obtain ⟨ht2_le, hr2_pos⟩ := ht2 (by omega)
  cases r2 with
  | zero => omega
  | succ r2' =>
    exact ⟨r2', m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans ht2_le (Nat.le_add_left _ _)⟩

theorem rule_7_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb88 (Scfg (r + 2) 0 m (rep n 7 R)) (Scfg (r' + 2) 0 m' R) t ∧
      iter H7 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb88 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_7 r m hm R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_7 r m hm (rep (p' + 1) 7 R)
      have hm1p : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H7_ge_17 m hm) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R hm1p
      have hcomm : iter H7 (p' + 1) (H7 m) = iter H7 (p' + 2) m := (iter_add H7 (p' + 1) 1 m).symm
      have hmb : iter H7 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H7 (fun _ _ h => H7_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem bb88_bootstrap :
    Reaches bb88 initConfig (Scfg 3 0 1 [7, 7, 1, 7, 7, 7, 1, 7, 7, 7, 5]) 93 := rfl

theorem bb88_halts_gt_f_omega2_plus_3_7 :
    ValidTM 8 8 bb88 ∧ ∃ t, HaltsIn bb88 initConfig t ∧ f_omega2_plus 3 7 < t := by
  refine ⟨bb88_valid, ?_⟩
  have hboot := bb88_bootstrap
  -- 1st `7`: m1 ≥ 17 ≥ 7
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_7 1 1 (by omega) [7, 1, 7, 7, 7, 1, 7, 7, 7, 5]
  have hm1_7 : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H7_ge_17 1 (by omega)) hm1)
  -- 2nd `7`: ≥ iter H7 1 7
  obtain ⟨r2, m2, t2, h2, hm2, _⟩ := rule_7 r1 m1 (by omega) [1, 7, 7, 7, 1, 7, 7, 7, 5]
  have h2b : iter H7 1 7 ≤ m2 := by rw [iter_succ, iter_zero]; exact Nat.le_trans (H7_mono hm1_7) hm2
  -- `1`: preserves r ≥ 2 and increases m
  obtain ⟨t3, h3, _⟩ := fwp2_step bb88_core.fp (r2 + 2) 0 m2 [7, 7, 7, 1, 7, 7, 7, 5]
  have hm3 : m2 ≤ Pfn (r2 + 2) 0 m2 := Nat.le_trans (Nat.le_succ m2) (Pfn_ge_succ _ 0 m2)
  have hm3p : 1 ≤ Pfn (r2 + 2) 0 m2 := by have := Pfn_ge_succ (r2 + 2) 0 m2; omega
  -- `7^3`: ≥ iter H7 4 7
  obtain ⟨r4, m4, t4, h4, hm4, _⟩ := rule_7_rep 3 r2 (Pfn (r2 + 2) 0 m2) [1, 7, 7, 7, 5] hm3p
  have h4b : iter H7 4 7 ≤ m4 := by
    have hsplit : iter H7 4 7 = iter H7 3 (iter H7 1 7) := iter_add H7 3 1 7
    rw [hsplit]; exact Nat.le_trans (iter_mono_arg H7 (fun _ _ h => H7_mono h) 3 (Nat.le_trans h2b hm3)) hm4
  -- `1`: preserves r ≥ 2 and increases m
  obtain ⟨t5, h5, _⟩ := fwp2_step bb88_core.fp (r4 + 2) 0 m4 [7, 7, 7, 5]
  have hm5 : m4 ≤ Pfn (r4 + 2) 0 m4 := Nat.le_trans (Nat.le_succ m4) (Pfn_ge_succ _ 0 m4)
  have hm5p : 1 ≤ Pfn (r4 + 2) 0 m4 := by have := Pfn_ge_succ (r4 + 2) 0 m4; omega
  -- `7^3`: ≥ iter H7 7 7 AND m6 ≤ t6
  obtain ⟨r6, m6, t6, h6, hm6, ht6⟩ := rule_7_rep 3 r4 (Pfn (r4 + 2) 0 m4) [5] hm5p
  have h6b : iter H7 7 7 ≤ m6 := by
    have hsplit : iter H7 7 7 = iter H7 3 (iter H7 4 7) := iter_add H7 3 4 7
    rw [hsplit]; exact Nat.le_trans (iter_mono_arg H7 (fun _ _ h => H7_mono h) 3 (Nat.le_trans h4b hm5)) hm6
  have hhalt : step bb88 (Scfg (r6 + 2) 0 m6 [5]) =
               some (mkCfgR none (1 :: 2 :: rep (2 * m6 + 1) 3 (rep (r6 + 2) 5 [])) []) :=
    step_mkCfgR_R (tm := bb88) (q := 0) (w := 0) (cur := 5) rfl
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans
    (reaches_trans (reaches_trans (reaches_trans hboot h1) h2) h3) h4) h5) h6) (steps_one bb88 _ _ hhalt)
  have hlt : f_omega2_plus 3 7 < iter H7 7 7 :=
    iter_strict_dom H7 (f_omega2_plus 2) 1 H7_gt (fOmega2_props 1 0 2) 7 7 (by omega) (by omega)
  have hlt_m6 : f_omega2_plus 3 7 < m6 := Nat.lt_of_lt_of_le hlt h6b
  have hle_t : m6 ≤ t6 := ht6 (by omega)
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m6 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb88_halts_gt_f_omega2_plus_3_7

end BB8_8
end BB
