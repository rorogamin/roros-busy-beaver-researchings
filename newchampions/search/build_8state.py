"""Generate exact, axiom-free Lean 4 and Rocq 9.1 proofs for BB(8,7), BB(8,8), BB(8,9)."""
from search.gen_tm import gen_lean_tm, gen_rocq_tm

TM87 = '6LC3LB2LH2RA4LB6LH1RZ_5RA3RB1LD2RA3LF5RB0RH_3RB1LB3LC2RC4LC1LE4LH_3RB3RE3LC2RC5RF3RD1RZ_5RB3RE4RG4LC3LG5LE1RZ_5RB5RB1RZ1LF5LF5LF1RH_5LF4RG1LB1LG5LD5LG2LH_5LA0LH1LH1LH2LH5RG1RZ'
TM88 = '6LB3LB2LH2RA4LB1RZ6LH7LH_7RG3RB1LD2RA3LF5RB3RC7LC_3RB1LB3LC2RC4LC1LE2RA4RB_3RB3RE3LC2RC6LD3RD3RB7LG_5RB3RE4RG4LC3LG5LE1RZ7LD_5RB5RB0RD1LF5LF5LF2LG7LD_5LF4RG1LB1LG7RH5LG2LH6LD_7LA7LA1LH1LH2LH5RG1RZ7RF'
TM89 = '3LF3LB2LH2RA4LB1RZ6LH7LH8LH_6LF3RB1LD2RA3LF5RB3RC3RC8LC_3RB1LB3LC2RC4LC1LE2RA3RE8LF_3RB3RE3LC2RC6LD3RD3RB8RC8RH_5RB3RE4RG4LC3LG5LE8RF3RF8LA_5RB5RB7LD1LF5LF5LF7RG2RA2LE_5LF4RG1LB1LG7LG5LG2LH6LD7LG_8RB8LE1LH1LH2LH5RG8RG8RH1RH'

# ===================== BB(8, 7) =====================
bb87_lean = f"""/-
  BB/BB8_7.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(8, 7):
    TM: {TM87}
    Domain: BB(8, 7) (8 states, 7 symbols)
    Previous best dominated bounds: BB(8, 6) > f_{{ω^2+1}}(f_ω(31)), BB(7, 7) > f_{{ω^2+1}}(3)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+2}}(8)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H

namespace BB
namespace BB8_7

{gen_lean_tm('bb87', TM87)}

theorem bb87_core : Fwp2_HCore bb87 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_H4 (n : Nat) (L R : List Nat) :
    Reaches bb87 (mkCfgR (some 7) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 7) L (4 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb87 _
  | succ k ih =>
    have h1 : step bb87 (mkCfgR (some 7) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 7) (rep k 4 L) (4 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb87) (q := 7) (w := 1) (cur := 4) rfl
    have h2 := ih (2 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb87 k _ _ _ h1 h2

theorem rule_5 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb87 (Scfg (r + 1) 0 m (5 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have h1 : step bb87 (Scfg (r + 1) 0 m (5 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb87) (q := 0) (w := 5) (cur := 5) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb87_core r m 6 R
  have h2 : step bb87 (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (6 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb87) (q := 6) (w := 1) (cur := 6) rfl
  have h3 := loop_H4 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb87 (mkCfgR (some 7) (5 :: rep r 5 []) (4 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb87) (q := 7) (w := 1) (cur := 4) rfl
  have h5 : step bb87 (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_R (tm := bb87) (q := 7) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he, hme, hte⟩ := exec_G2_2s bb87_core r m hm R
  have hpre := steps_succ bb87 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb87 _ _ _ _ h2 (reaches_trans h3 (steps_succ bb87 _ _ _ _ h4 (steps_one bb87 _ _ h5)))))
  exact ⟨r', m', _, reaches_trans hpre he, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

theorem rule_5_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb87 (Scfg (r + 1) 0 m (rep n 5 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H_plus2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb87 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_5 r m hm R
      exact ⟨r1 + 1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5 r m hm (rep (p' + 1) 5 R)
      have hm1_pos : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H_plus2_ge_17 m) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih (r1 + 1) m1 R hm1_pos
      have hcomm : iter H_plus2 (p' + 1) (H_plus2 m) = iter H_plus2 (p' + 2) m :=
        (iter_add H_plus2 (p' + 1) 1 m).symm
      have hmb : iter H_plus2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb87_bootstrap :
    Reaches bb87 initConfig (Scfg 3 0 1 (rep 9 5 [1, 6])) 160 := rfl

theorem bb87_halts_gt_f_omega2_plus_2_8 :
    ValidTM 8 7 bb87 ∧ ∃ t, HaltsIn bb87 initConfig t ∧ f_omega2_plus 2 8 < t := by
  refine ⟨bb87_valid, ?_⟩
  have hboot := bb87_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5 2 1 (by omega) (rep 8 5 [1, 6])
  have hm1_8 : 8 ≤ m1 := Nat.le_trans (by omega : 8 ≤ 17) (Nat.le_trans (H_plus2_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_5_rep 8 (r1 + 1) m1 [1, 6] (by omega)
  obtain ⟨t3, h3, _⟩ := fwp2_step bb87_core.fp (r2 + 1) 0 m2 [6]
  have hhalt : step bb87 (Scfg (r2 + 1) 0 (Pfn (r2 + 1) 0 m2) [6]) =
               some (mkCfgR none (1 :: 2 :: rep (2 * Pfn (r2 + 1) 0 m2 + 1) 3 (rep (r2 + 1) 5 [])) []) :=
    step_mkCfgR_R (tm := bb87) (q := 0) (w := 0) (cur := 6) rfl
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans hboot h1) h2) h3)
    (steps_one bb87 _ _ hhalt)
  have hlt1 : f_omega2_plus 2 8 < iter H_plus2 8 8 :=
    iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 8 8 (by omega) (by omega)
  have hlt2 : iter H_plus2 8 8 ≤ iter H_plus2 8 m1 := iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) 8 hm1_8
  have hlt_m2 : f_omega2_plus 2 8 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb87_halts_gt_f_omega2_plus_2_8

end BB8_7
end BB
"""

bb87_v = f"""(*
  rocq/BB8_7.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(8, 7):
    TM: {TM87}
    Domain: BB(8, 7) (8 states, 7 symbols)
    Previous best dominated bounds: BB(8, 6) > f_{{ω^2+1}}(f_ω(31)), BB(7, 7) > f_{{ω^2+1}}(3)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+2}}(8)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H.
Import ListNotations.

{gen_rocq_tm('bb87', TM87)}

Lemma bb87_core : Fwp2_HCore bb87.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_H4 : forall n L R,
  Reaches bb87 (mkCfgR (Some 7) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 7) L (4 :: rep n 2 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 4 4 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rule_5 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb87 (Scfg (S r) 0 m (5 :: R)) (Scfg (S (S r')) 0 m' R) t /\\
    H_plus2 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (sweep_HG bb87 bb87_core r m 6 R) as [ts Hs].
  destruct (exec_G2_2s bb87 bb87_core r m R Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists r', m'. eexists. split.
  - eapply reaches_trans; [| exact He].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 2 5 _ _ R eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 1 4 6 _ _ R eq_refl) |].
    eapply reaches_trans; [apply (loop_H4 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
    rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 5 4 _ _ _ eq_refl) |].
    replace (2 :: 2 :: rep (2 * m + 1) 2 R) with (rep (2 * m + 3) 2 R)
      by (replace (2 * m + 3) with (S (S (2 * m + 1))) by lia; reflexivity).
    apply steps_one. apply (step_mkCfgR_R _ 7 4 _ _ 5 _ eq_refl).
  - split; [exact Hme | lia].
Qed.

Lemma rule_5_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb87 (Scfg (S r) 0 m (rep n 5 R)) (Scfg (S r') 0 m' R) t /\\
    iter H_plus2 n m <= m' /\\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_5 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists (S r1), m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_5 r m (rep (S p') 5 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H_plus2_ge_17 m); lia).
      destruct (IH (S r1) m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H_plus2 (S (S p')) m) with (iter H_plus2 (S p') (H_plus2 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H_plus2_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb87_bootstrap :
  Reaches bb87 initConfig (Scfg 3 0 1 (rep 9 5 [1; 6])) 160.
Proof. vm_compute. reflexivity. Qed.

Theorem bb87_halts_gt_f_omega2_plus_2_8 :
  ValidTM 8 7 bb87 /\\ exists t, HaltsIn bb87 initConfig t /\\ f_omega2_plus 2 8 < t.
Proof.
  split; [exact bb87_valid |].
  pose proof bb87_bootstrap as Hboot.
  destruct (rule_5 2 1 (rep 8 5 [1; 6]) ltac:(lia)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_8 : 8 <= m1) by (pose proof (H_plus2_ge_17 1); lia).
  destruct (rule_5_rep 8 (S r1) m1 [1; 6] ltac:(lia)) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  destruct (fwp2_step bb87 (fh_fp _ bb87_core) (S r2) 0 m2 [6]) as [t3 [H3 _]].
  assert (Hhalt : step bb87 (Scfg (S r2) 0 (Pfn (S r2) 0 m2) [6]) =
    Some (mkCfgR None (1 :: 2 :: rep (2 * Pfn (S r2) 0 m2 + 1) 3 (rep (S r2) 5 [])) [])).
  {{ apply (step_mkCfgR_R _ 0 0 _ _ 6 [] eq_refl). }}
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r) H3)
    (steps_one _ _ _ Hhalt)) as Hreach.
  pose proof (iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 8 8 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H_plus2 H_plus2_mono 8 8 m1 Hm1_8) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (f_omega2_plus 2 8) with (iter (f_omega2_plus 1) 8 8). lia.
Qed.

Print Assumptions bb87_halts_gt_f_omega2_plus_2_8.
"""

# ===================== BB(8, 8) =====================
bb88_lean = f"""/-
  BB/BB8_8.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(8, 8):
    TM: {TM88}
    Domain: BB(8, 8) (8 states, 8 symbols)
    Previous best dominated bounds: BB(8, 7) > f_{{ω^2+2}}(8), BB(7, 8) > f_{{ω^2+2}}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+3}}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H

namespace BB
namespace BB8_8

{gen_lean_tm('bb88', TM88)}

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

theorem H7_mono {{x y : Nat}} (hxy : x ≤ y) : H7 x ≤ H7 y :=
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
"""

bb88_v = f"""(*
  rocq/BB8_8.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(8, 8):
    TM: {TM88}
    Domain: BB(8, 8) (8 states, 8 symbols)
    Previous best dominated bounds: BB(8, 7) > f_{{ω^2+2}}(8), BB(7, 8) > f_{{ω^2+2}}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+3}}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H.
Import ListNotations.

{gen_rocq_tm('bb88', TM88)}

Lemma bb88_core : Fwp2_HCore bb88.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_H4 : forall n L R,
  Reaches bb88 (mkCfgR (Some 7) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 7) L (4 :: rep n 2 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 4 4 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_D4 : forall n L R,
  Reaches bb88 (mkCfgR (Some 3) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 3) L (4 :: rep n 6 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 5 4 4 _ _ R eq_refl) |].
  specialize (IH L (6 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rule_6 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb88 (Scfg (S r) 0 m (6 :: R)) (Scfg (S (S r')) 0 m' R) t /\\
    H_plus2 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (sweep_HG bb88 bb88_core r m 6 R) as [ts Hs].
  destruct (exec_G2_2s bb88 bb88_core r m R Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists r', m'. eexists. split.
  - eapply reaches_trans; [| exact He].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 2 6 _ _ R eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 1 4 6 _ _ R eq_refl) |].
    eapply reaches_trans; [apply (loop_H4 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
    rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 5 4 _ _ _ eq_refl) |].
    replace (2 :: 2 :: rep (2 * m + 1) 2 R) with (rep (2 * m + 3) 2 R)
      by (replace (2 * m + 3) with (S (S (2 * m + 1))) by lia; reflexivity).
    apply steps_one. apply (step_mkCfgR_R _ 7 4 _ _ 5 _ eq_refl).
  - split; [exact Hme | lia].
Qed.

Lemma rule_6_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb88 (Scfg (S r) 0 m (rep n 6 R)) (Scfg (S r') 0 m' R) t /\\
    iter H_plus2 n m <= m' /\\ (1 <= n -> m' <= t /\\ 1 <= r').
Proof.
  induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_6 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists (S r1), m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; split; [exact Ht1 | lia]]].
    + destruct (rule_6 r m (rep (S p') 6 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H_plus2_ge_17 m); lia).
      destruct (IH (S r1) m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H_plus2 (S (S p')) m) with (iter H_plus2 (S p') (H_plus2 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H_plus2_mono | exact Hm1] | exact Hm2].
      * intros _. destruct (Ht2 ltac:(lia)) as [Ht2a Hr2a]. lia.
Qed.

Definition H7 (m : nat) : nat := iter H_plus2 (2 * m) 1.

Lemma H7_mono : forall x y, x <= y -> H7 x <= H7 y.
Proof.
  intros x y Hxy. unfold H7.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H_plus2_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H7_gt : forall m, 1 <= m -> f_omega2_plus 2 m < H7 m.
Proof.
  intros m Hm. unfold H7.
  apply (climb_double H_plus2 (f_omega2_plus 1) 1 ltac:(lia) H_plus2_mono H_plus2_inc H_plus2_gt (fOmega2_props 1 0 1) m Hm).
Qed.

Lemma H7_ge_17 : forall m, 1 <= m -> 17 <= H7 m.
Proof.
  intros m Hm. unfold H7.
  destruct (2 * m) as [| q] eqn:E; [lia |].
  rewrite iter_succ. apply H_plus2_ge_17.
Qed.

Lemma reload_7 : forall r m R,
  exists t, Reaches bb88 (Scfg (S (S r)) 0 m (7 :: R)) (Scfg (S r) 0 1 (rep (2 * m) 6 R)) t.
Proof.
  intros r m R. destruct (sweep_HG bb88 bb88_core (S r) m 7 R) as [ts Hs].
  eexists. eapply reaches_trans.
  - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 6 2 7 _ _ R eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 5 4 7 _ _ R eq_refl) |].
    apply (loop_D4 (2 * m + 1) (rep (S (S r)) 5 []) (6 :: R)).
  - rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 5 5 4 _ _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 5 _ eq_refl) |].
    replace (6 :: 6 :: rep (2 * m + 1) 6 R) with (6 :: 6 :: 6 :: rep (2 * m) 6 R)
      by (replace (2 * m + 1) with (S (2 * m)) by lia; reflexivity).
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 6 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 6 _ eq_refl) |].
    apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 2 1 _ _ 6 _ eq_refl).
Qed.

Lemma rule_7 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb88 (Scfg (S (S r)) 0 m (7 :: R)) (Scfg (S (S r')) 0 m' R) t /\\
    H7 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_7 r m R) as [t0 H0].
  destruct (rule_6_rep (2 * m) r 1 R ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (Ht2 ltac:(lia)) as [Ht2_le Hr2_pos].
  destruct r2 as [| r2']; [lia |].
  exists r2', m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split; [exact Hm2 | lia]].
Qed.

Lemma rule_7_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb88 (Scfg (S (S r)) 0 m (rep n 7 R)) (Scfg (S (S r')) 0 m' R) t /\\
    iter H7 n m <= m' /\\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_7 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_7 r m (rep (S p') 7 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H7_ge_17 m Hm); lia).
      destruct (IH r1 m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H7 (S (S p')) m) with (iter H7 (S p') (H7 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H7_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb88_bootstrap :
  Reaches bb88 initConfig (Scfg 3 0 1 [7; 7; 1; 7; 7; 7; 1; 7; 7; 7; 5]) 93.
Proof. vm_compute. reflexivity. Qed.

Theorem bb88_halts_gt_f_omega2_plus_3_7 :
  ValidTM 8 8 bb88 /\\ exists t, HaltsIn bb88 initConfig t /\\ f_omega2_plus 3 7 < t.
Proof.
  split; [exact bb88_valid |].
  pose proof bb88_bootstrap as Hboot.
  destruct (rule_7 1 1 [7; 1; 7; 7; 7; 1; 7; 7; 7; 5] ltac:(lia)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_7 : 7 <= m1) by (pose proof (H7_ge_17 1 ltac:(lia)); lia).
  destruct (rule_7 r1 m1 [1; 7; 7; 7; 1; 7; 7; 7; 5] ltac:(lia)) as [r2 [m2 [t2 [H2s [Hm2 _]]]]].
  assert (H2b : iter H7 1 7 <= m2) by (rewrite iter_succ, iter_zero; pose proof (H7_mono 7 m1 Hm1_7); lia).
  destruct (fwp2_step bb88 (fh_fp _ bb88_core) (S (S r2)) 0 m2 [7; 7; 7; 1; 7; 7; 7; 5]) as [t3 [H3 _]].
  assert (Hm3 : S m2 <= Pfn (S (S r2)) 0 m2) by apply Pfn_ge_succ.
  destruct (rule_7_rep 3 r2 (Pfn (S (S r2)) 0 m2) [1; 7; 7; 7; 5] ltac:(lia)) as [r4 [m4 [t4 [H4 [Hm4 _]]]]].
  assert (H4b : iter H7 4 7 <= m4).
  {{ eapply Nat.le_trans; [| exact Hm4].
     change (iter H7 4 7) with (iter H7 (3 + 1) 7). rewrite iter_add.
     apply iter_mono_arg; [apply H7_mono | lia]. }}
  destruct (fwp2_step bb88 (fh_fp _ bb88_core) (S (S r4)) 0 m4 [7; 7; 7; 5]) as [t5 [H5 _]].
  assert (Hm5 : S m4 <= Pfn (S (S r4)) 0 m4) by apply Pfn_ge_succ.
  destruct (rule_7_rep 3 r4 (Pfn (S (S r4)) 0 m4) [5] ltac:(lia)) as [r6 [m6 [t6 [H6 [Hm6 Ht6]]]]].
  assert (H6b : iter H7 7 7 <= m6).
  {{ eapply Nat.le_trans; [| exact Hm6].
     change (iter H7 7 7) with (iter H7 (3 + 4) 7). rewrite iter_add.
     apply iter_mono_arg; [apply H7_mono | lia]. }}
  assert (Hhalt : step bb88 (Scfg (S (S r6)) 0 m6 [5]) =
    Some (mkCfgR None (1 :: 2 :: rep (2 * m6 + 1) 3 (rep (S (S r6)) 5 [])) [])).
  {{ apply (step_mkCfgR_R _ 0 0 _ _ 5 [] eq_refl). }}
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _
      (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _
        Hboot H1) H2s) H3) H4) H5) H6) (steps_one _ _ _ Hhalt)) as Hreach.
  pose proof (iter_strict_dom H7 (f_omega2_plus 2) 1 H7_gt (fOmega2_props 1 0 2) 7 7 ltac:(lia) ltac:(lia)) as Hlt.
  pose proof (Ht6 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (f_omega2_plus 3 7) with (iter (f_omega2_plus 2) 7 7). lia.
Qed.

Print Assumptions bb88_halts_gt_f_omega2_plus_3_7.
"""

# ===================== BB(8, 9) =====================
bb89_lean = f"""/-
  BB/BB8_9.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(8, 9):
    TM: {TM89}
    Domain: BB(8, 9) (8 states, 9 symbols)
    Previous best dominated bounds: BB(8, 8) > f_{{ω^2+3}}(7), BB(7, 9) > f_{{ω^2+3}}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+4}}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H

namespace BB
namespace BB8_9

{gen_lean_tm('bb89', TM89)}

theorem bb89_core : Fwp2_HCore bb89 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_H4 (n : Nat) (L R : List Nat) :
    Reaches bb89 (mkCfgR (some 7) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 7) L (4 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb89 _
  | succ k ih =>
    have h1 : step bb89 (mkCfgR (some 7) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 7) (rep k 4 L) (4 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb89) (q := 7) (w := 1) (cur := 4) rfl
    have h2 := ih (2 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb89 k _ _ _ h1 h2

private theorem loop_D4 (n : Nat) (L R : List Nat) :
    Reaches bb89 (mkCfgR (some 3) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 3) L (4 :: rep n 6 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb89 _
  | succ k ih =>
    have h1 : step bb89 (mkCfgR (some 3) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 3) (rep k 4 L) (4 :: 6 :: R)) :=
      step_mkCfgR_L_cons (tm := bb89) (q := 3) (w := 5) (cur := 4) rfl
    have h2 := ih (6 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb89 k _ _ _ h1 h2

private theorem loop_G4 (n : Nat) (L R : List Nat) :
    Reaches bb89 (mkCfgR (some 6) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 6) L (4 :: rep n 7 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb89 _
  | succ k ih =>
    have h1 : step bb89 (mkCfgR (some 6) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 6) (rep k 4 L) (4 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb89) (q := 6) (w := 6) (cur := 4) rfl
    have h2 := ih (7 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb89 k _ _ _ h1 h2

private theorem loop_G5 (n : Nat) (L R : List Nat) :
    Reaches bb89 (mkCfgR (some 6) (rep n 5 L) (5 :: R))
                 (mkCfgR (some 6) L (5 :: rep n 5 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb89 _
  | succ k ih =>
    have h1 : step bb89 (mkCfgR (some 6) (5 :: rep k 5 L) (5 :: R)) =
              some (mkCfgR (some 6) (rep k 5 L) (5 :: 5 :: R)) :=
      step_mkCfgR_L_cons (tm := bb89) (q := 6) (w := 4) (cur := 5) rfl
    have h2 := ih (5 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb89 k _ _ _ h1 h2

theorem rule_6 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb89 (Scfg (r + 1) 0 m (6 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have h1 : step bb89 (Scfg (r + 1) 0 m (6 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb89) (q := 0) (w := 5) (cur := 6) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb89_core r m 6 R
  have h2 : step bb89 (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (6 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb89) (q := 6) (w := 1) (cur := 6) rfl
  have h3 := loop_H4 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb89 (mkCfgR (some 7) (5 :: rep r 5 []) (4 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb89) (q := 7) (w := 1) (cur := 4) rfl
  have h5 : step bb89 (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_R (tm := bb89) (q := 7) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he, hme, hte⟩ := exec_G2_2s bb89_core r m hm R
  have hpre := steps_succ bb89 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb89 _ _ _ _ h2 (reaches_trans h3 (steps_succ bb89 _ _ _ _ h4 (steps_one bb89 _ _ h5)))))
  exact ⟨r', m', _, reaches_trans hpre he, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

theorem rule_6_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb89 (Scfg (r + 1) 0 m (rep n 6 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H_plus2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t ∧ 1 ≤ r') := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb89 _, Nat.le_refl m, fun h => by cases h⟩
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
def H8 (m : Nat) : Nat := iter H7 (2 * m - 1) 1

theorem H7_mono {{x y : Nat}} (hxy : x ≤ y) : H7 x ≤ H7 y :=
  iter_mono_steps H_plus2 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H_plus2_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1
theorem H7_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H7 m :=
  climb_double H_plus2 (f_omega2_plus 1) 1 (by omega) (fun _ _ h => H_plus2_mono h) H_plus2_inc H_plus2_gt
    (fOmega2_props 1 0 1) m hm
theorem H7_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H7 m := by
  have h1 := H7_gt m hm; have h2 : m ≤ f_omega2_plus 2 m := (fOmega2_props 1 0 2).ge_self m; omega
theorem H7_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H7 m := by
  cases h2m : 2 * m with | zero => omega | succ q => unfold H7; rw [h2m, iter_succ]; exact H_plus2_ge_17 _

theorem H8_mono {{x y : Nat}} (hxy : x ≤ y) : H8 x ≤ H8 y :=
  iter_mono_steps H7 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H7_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1
theorem H8_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 3 m < H8 m :=
  climb_2m_minus_1 H7 (f_omega2_plus 2) 1 (by omega) (fun _ _ h => H7_mono h) H7_inc H7_gt
    (fOmega2_props 1 0 2) m hm
theorem H8_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H8 m := by
  cases h2m : 2 * m - 1 with
  | zero => omega
  | succ q =>
    unfold H8; rw [h2m, iter_succ]
    have hpos : 1 ≤ iter H7 q 1 := iter_ge_self H7 (fun z => by
      cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H7_inc (z' + 1) (Nat.succ_pos z'))) q 1
    exact H7_ge_17 _ hpos

theorem reload_7 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb89 (Scfg (r + 2) 0 m (7 :: R)) (Scfg (r + 1) 0 1 (rep (2 * m) 6 R)) t := by
  have h1 : step bb89 (Scfg (r + 2) 0 m (7 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 2) 5 [])) (2 :: 7 :: R)) :=
    step_mkCfgR_L_cons (tm := bb89) (q := 0) (w := 6) (cur := 7) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb89_core (r + 1) m 7 R
  have h2 : step bb89 (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 2) 5 [])) (7 :: R)) =
            some (mkCfgR (some 3) (rep (2 * m + 1) 4 (rep (r + 2) 5 [])) (4 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb89) (q := 6) (w := 5) (cur := 7) rfl
  have h3 := loop_D4 (2 * m + 1) (rep (r + 2) 5 []) (6 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb89 (mkCfgR (some 3) (5 :: rep (r + 1) 5 []) (4 :: rep (2 * m + 2) 6 R)) =
            some (mkCfgR (some 3) (rep (r + 1) 5 []) (5 :: rep (2 * m + 3) 6 R)) :=
    step_mkCfgR_L_cons (tm := bb89) (q := 3) (w := 5) (cur := 4) rfl
  have h5 : step bb89 (mkCfgR (some 3) (rep (r + 1) 5 []) (5 :: rep (2 * m + 3) 6 R)) =
            some (mkCfgR (some 3) (3 :: rep (r + 1) 5 []) (rep (2 * m + 3) 6 R)) :=
    step_mkCfgR_R (tm := bb89) (q := 3) (w := 2) (cur := 5) rfl
  have h6 : step bb89 (mkCfgR (some 3) (3 :: rep (r + 1) 5 []) (6 :: rep (2 * m + 2) 6 R)) =
            some (mkCfgR (some 1) (3 :: 3 :: rep (r + 1) 5 []) (rep (2 * m + 2) 6 R)) :=
    step_mkCfgR_R (tm := bb89) (q := 3) (w := 2) (cur := 6) rfl
  have h7 : step bb89 (mkCfgR (some 1) (3 :: 3 :: rep (r + 1) 5 []) (6 :: rep (2 * m + 1) 6 R)) =
            some (mkCfgR (some 2) (3 :: 3 :: 3 :: rep (r + 1) 5 []) (rep (2 * m + 1) 6 R)) :=
    step_mkCfgR_R (tm := bb89) (q := 1) (w := 2) (cur := 6) rfl
  have h8 : step bb89 (mkCfgR (some 2) (3 :: 3 :: 3 :: rep (r + 1) 5 []) (6 :: rep (2 * m) 6 R)) =
            some (Scfg (r + 1) 0 1 (rep (2 * m) 6 R)) :=
    step_mkCfgR_R (tm := bb89) (q := 2) (w := 1) (cur := 6) rfl
  exact ⟨_, reaches_trans (steps_succ bb89 _ _ _ _ h1 (reaches_trans hs (steps_succ bb89 _ _ _ _ h2 h3)))
    (steps_succ bb89 _ _ _ _ h4 (steps_succ bb89 _ _ _ _ h5
      (steps_succ bb89 _ _ _ _ h6 (steps_succ bb89 _ _ _ _ h7 (steps_one bb89 _ _ h8)))))⟩

theorem rule_7 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb89 (Scfg (r + 2) 0 m (7 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_7 r m R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_6_rep (2 * m) r 1 R (by omega)
  obtain ⟨ht2_le, hr2_pos⟩ := ht2 (by omega)
  cases r2 with | zero => omega | succ r2' =>
    exact ⟨r2', m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans ht2_le (Nat.le_add_left _ _)⟩

theorem rule_7_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb89 (Scfg (r + 2) 0 m (rep n 7 R)) (Scfg (r' + 2) 0 m' R) t ∧
      iter H7 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb89 _, Nat.le_refl m, fun h => by cases h⟩
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

theorem reload_8 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ t, Reaches bb89 (Scfg (r + 1) 0 m (8 :: R)) (Scfg (r + 3) 0 1 (rep (2 * m - 1) 7 R)) t := by
  cases m with
  | zero => cases hm
  | succ m' =>
    have h1 : step bb89 (Scfg (r + 1) 0 (m' + 1) (8 :: R)) =
              some (mkCfgR (some 7) (rep (2 * (m' + 1) + 1) 3 (rep (r + 1) 5 [])) (2 :: 8 :: R)) :=
      step_mkCfgR_L_cons (tm := bb89) (q := 0) (w := 7) (cur := 8) rfl
    obtain ⟨ts, hs⟩ := sweep_HG bb89_core r (m' + 1) 8 R
    have h2 : step bb89 (mkCfgR (some 6) (4 :: rep (2 * (m' + 1) + 1) 4 (rep (r + 1) 5 [])) (8 :: R)) =
              some (mkCfgR (some 6) (rep (2 * (m' + 1) + 1) 4 (rep (r + 1) 5 [])) (4 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb89) (q := 6) (w := 6) (cur := 8) rfl
    have h3 := loop_G4 (2 * (m' + 1) + 1) (rep (r + 1) 5 []) (7 :: R)
    rw [rep_snoc_one] at h3
    have h4 : step bb89 (mkCfgR (some 6) (5 :: rep r 5 []) (4 :: rep (2 * (m' + 1) + 2) 7 R)) =
              some (mkCfgR (some 6) (rep r 5 []) (5 :: rep (2 * (m' + 1) + 3) 7 R)) :=
      step_mkCfgR_L_cons (tm := bb89) (q := 6) (w := 6) (cur := 4) rfl
    have h5 := loop_G5 r [] (rep (2 * (m' + 1) + 3) 7 R)
    have h6 : step bb89 (mkCfgR (some 6) [] (5 :: rep r 5 (rep (2 * (m' + 1) + 3) 7 R))) =
              some (mkCfgR (some 6) [] (0 :: rep (r + 1) 5 (rep (2 * (m' + 1) + 3) 7 R))) :=
      step_mkCfgR_L_nil (tm := bb89) (q := 6) (w := 4) (cur := 5) rfl
    have h7 : step bb89 (mkCfgR (some 6) [] (0 :: rep (r + 1) 5 (rep (2 * (m' + 1) + 3) 7 R))) =
              some (mkCfgR (some 5) [] (0 :: rep (r + 2) 5 (rep (2 * (m' + 1) + 3) 7 R))) :=
      step_mkCfgR_L_nil (tm := bb89) (q := 6) (w := 4) (cur := 0) rfl
    have h8 : step bb89 (mkCfgR (some 5) [] (0 :: rep (r + 2) 5 (rep (2 * (m' + 1) + 3) 7 R))) =
              some (mkCfgR (some 1) [5] (rep (r + 2) 5 (rep (2 * (m' + 1) + 3) 7 R))) :=
      step_mkCfgR_R (tm := bb89) (q := 5) (w := 4) (cur := 0) rfl
    have h9 := loop_B5_H bb89_core (r + 2) [5] (rep (2 * (m' + 1) + 3) 7 R)
    have hrep5 : rep (r + 2) 5 [5] = rep (r + 3) 5 [] := by rw [rep_snoc_one]; rfl
    rw [hrep5] at h9
    have h7s : rep (2 * (m' + 1) + 3) 7 R = 7 :: 7 :: 7 :: 7 :: rep (2 * (m' + 1) - 1) 7 R := by
      have ha : 2 * (m' + 1) + 3 = (2 * (m' + 1) - 1) + 4 := by omega
      rw [ha]; rfl
    rw [h7s] at h9
    have h10 : Reaches bb89
        (mkCfgR (some 1) (rep (r + 3) 5 []) (7 :: 7 :: 7 :: 7 :: rep (2 * (m' + 1) - 1) 7 R))
        (Scfg (r + 3) 0 1 (rep (2 * (m' + 1) - 1) 7 R)) 4 := by
      refine steps_succ bb89 3 _ _ _ (step_mkCfgR_R (tm := bb89) (q := 1) (w := 2) (cur := 7) rfl) ?_
      refine steps_succ bb89 2 _ _ _ (step_mkCfgR_R (tm := bb89) (q := 2) (w := 2) (cur := 7) rfl) ?_
      refine steps_succ bb89 1 _ _ _ (step_mkCfgR_R (tm := bb89) (q := 4) (w := 2) (cur := 7) rfl) ?_
      exact steps_one bb89 _ _ (step_mkCfgR_R (tm := bb89) (q := 5) (w := 1) (cur := 7) rfl)
    have ha := steps_succ bb89 _ _ _ _ h1 (reaches_trans hs (steps_succ bb89 _ _ _ _ h2 h3))
    have hb := steps_succ bb89 _ _ _ _ h4 (reaches_trans h5 (steps_succ bb89 _ _ _ _ h6
      (steps_succ bb89 _ _ _ _ h7 (steps_succ bb89 _ _ _ _ h8 (reaches_trans h9 h10)))))
    exact ⟨_, reaches_trans ha hb⟩

theorem rule_8 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb89 (Scfg (r + 1) 0 m (8 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H8 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_8 r m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_7_rep (2 * m - 1) (r + 1) 1 R (by omega)
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem rule_8_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb89 (Scfg (r + 1) 0 m (rep n 8 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H8 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb89 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_8 r m hm R
      exact ⟨r1 + 1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_8 r m hm (rep (p' + 1) 8 R)
      have hm1p : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H8_ge_17 m hm) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih (r1 + 1) m1 R hm1p
      have hcomm : iter H8 (p' + 1) (H8 m) = iter H8 (p' + 2) m := (iter_add H8 (p' + 1) 1 m).symm
      have hmb : iter H8 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H8 (fun _ _ h => H8_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem bb89_bootstrap :
    Reaches bb89 initConfig (Scfg 1 0 0 [2, 8, 8, 8, 8, 1, 8, 8, 8, 5]) 119 := rfl

theorem bb89_halts_gt_f_omega2_plus_4_7 :
    ValidTM 8 9 bb89 ∧ ∃ t, HaltsIn bb89 initConfig t ∧ f_omega2_plus 4 7 < t := by
  refine ⟨bb89_valid, ?_⟩
  have hboot := bb89_bootstrap
  -- `2`: sets m1 ≥ 17 ≥ 7
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_2_H bb89_core 0 0 [8, 8, 8, 8, 1, 8, 8, 8, 5]
  have hm1_7 : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans H2_H_0_ge hm1)
  -- `8^4`: ≥ iter H8 4 7
  obtain ⟨r2, m2, t2, h2, hm2, _⟩ := rule_8_rep 4 (r1 + 1) m1 [1, 8, 8, 8, 5] (by omega)
  have h2b : iter H8 4 7 ≤ m2 := Nat.le_trans (iter_mono_arg H8 (fun _ _ h => H8_mono h) 4 hm1_7) hm2
  -- `1`: increases m
  obtain ⟨t3, h3, _⟩ := fwp2_step bb89_core.fp (r2 + 1) 0 m2 [8, 8, 8, 5]
  have hm3 : m2 ≤ Pfn (r2 + 1) 0 m2 := Nat.le_trans (Nat.le_succ m2) (Pfn_ge_succ _ 0 m2)
  have hm3p : 1 ≤ Pfn (r2 + 1) 0 m2 := by have := Pfn_ge_succ (r2 + 1) 0 m2; omega
  -- `8^3`: ≥ iter H8 7 7 AND m4 ≤ t4
  obtain ⟨r4, m4, t4, h4, hm4, ht4⟩ := rule_8_rep 3 r2 (Pfn (r2 + 1) 0 m2) [5] hm3p
  have h4b : iter H8 7 7 ≤ m4 := by
    have hsplit : iter H8 7 7 = iter H8 3 (iter H8 4 7) := iter_add H8 3 4 7
    rw [hsplit]; exact Nat.le_trans (iter_mono_arg H8 (fun _ _ h => H8_mono h) 3 (Nat.le_trans h2b hm3)) hm4
  have hhalt : step bb89 (Scfg (r4 + 1) 0 m4 [5]) =
               some (mkCfgR none (1 :: 2 :: rep (2 * m4 + 1) 3 (rep (r4 + 1) 5 [])) []) :=
    step_mkCfgR_R (tm := bb89) (q := 0) (w := 0) (cur := 5) rfl
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans
    (reaches_trans hboot h1) h2) h3) h4) (steps_one bb89 _ _ hhalt)
  have hlt : f_omega2_plus 4 7 < iter H8 7 7 :=
    iter_strict_dom H8 (f_omega2_plus 3) 1 H8_gt (fOmega2_props 1 0 3) 7 7 (by omega) (by omega)
  have hlt_m4 : f_omega2_plus 4 7 < m4 := Nat.lt_of_lt_of_le hlt h4b
  have hle_t : m4 ≤ t4 := ht4 (by omega)
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m4 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb89_halts_gt_f_omega2_plus_4_7

end BB8_9
end BB
"""

bb89_v = f"""(*
  rocq/BB8_9.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(8, 9):
    TM: {TM89}
    Domain: BB(8, 9) (8 states, 9 symbols)
    Previous best dominated bounds: BB(8, 8) > f_{{ω^2+3}}(7), BB(7, 9) > f_{{ω^2+3}}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+4}}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H.
Import ListNotations.

{gen_rocq_tm('bb89', TM89)}

Lemma bb89_core : Fwp2_HCore bb89.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_H4 : forall n L R,
  Reaches bb89 (mkCfgR (Some 7) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 7) L (4 :: rep n 2 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 4 4 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_D4 : forall n L R,
  Reaches bb89 (mkCfgR (Some 3) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 3) L (4 :: rep n 6 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 5 4 4 _ _ R eq_refl) |].
  specialize (IH L (6 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_G4 : forall n L R,
  Reaches bb89 (mkCfgR (Some 6) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 6) L (4 :: rep n 7 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 4 4 _ _ R eq_refl) |].
  specialize (IH L (7 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_G5 : forall n L R,
  Reaches bb89 (mkCfgR (Some 6) (rep n 5 L) (5 :: R))
               (mkCfgR (Some 6) L (5 :: rep n 5 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 4 5 5 _ _ R eq_refl) |].
  specialize (IH L (5 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rule_6 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb89 (Scfg (S r) 0 m (6 :: R)) (Scfg (S (S r')) 0 m' R) t /\\
    H_plus2 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (sweep_HG bb89 bb89_core r m 6 R) as [ts Hs].
  destruct (exec_G2_2s bb89 bb89_core r m R Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists r', m'. eexists. split.
  - eapply reaches_trans; [| exact He].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 2 6 _ _ R eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 1 4 6 _ _ R eq_refl) |].
    eapply reaches_trans; [apply (loop_H4 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
    rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 5 4 _ _ _ eq_refl) |].
    replace (2 :: 2 :: rep (2 * m + 1) 2 R) with (rep (2 * m + 3) 2 R)
      by (replace (2 * m + 3) with (S (S (2 * m + 1))) by lia; reflexivity).
    apply steps_one. apply (step_mkCfgR_R _ 7 4 _ _ 5 _ eq_refl).
  - split; [exact Hme | lia].
Qed.

Lemma rule_6_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb89 (Scfg (S r) 0 m (rep n 6 R)) (Scfg (S r') 0 m' R) t /\\
    iter H_plus2 n m <= m' /\\ (1 <= n -> m' <= t /\\ 1 <= r').
Proof.
  induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_6 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists (S r1), m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; split; [exact Ht1 | lia]]].
    + destruct (rule_6 r m (rep (S p') 6 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H_plus2_ge_17 m); lia).
      destruct (IH (S r1) m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H_plus2 (S (S p')) m) with (iter H_plus2 (S p') (H_plus2 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H_plus2_mono | exact Hm1] | exact Hm2].
      * intros _. destruct (Ht2 ltac:(lia)) as [Ht2a Hr2a]. lia.
Qed.

Definition H7 (m : nat) : nat := iter H_plus2 (2 * m) 1.
Definition H8 (m : nat) : nat := iter H7 (2 * m - 1) 1.

Lemma H7_mono : forall x y, x <= y -> H7 x <= H7 y.
Proof.
  intros x y Hxy. unfold H7.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H_plus2_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H7_gt : forall m, 1 <= m -> f_omega2_plus 2 m < H7 m.
Proof.
  intros m Hm. unfold H7.
  apply (climb_double H_plus2 (f_omega2_plus 1) 1 ltac:(lia) H_plus2_mono H_plus2_inc H_plus2_gt (fOmega2_props 1 0 1) m Hm).
Qed.

Lemma H7_inc : forall m, 1 <= m -> S m <= H7 m.
Proof.
  intros m Hm. pose proof (H7_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 2) m).
  change (f_omega2_plus 2 m) with (fOmega2 1 0 2 m) in *. lia.
Qed.

Lemma H7_ge_17 : forall m, 1 <= m -> 17 <= H7 m.
Proof.
  intros m Hm. unfold H7.
  destruct (2 * m) as [| q] eqn:E; [lia |].
  rewrite iter_succ. apply H_plus2_ge_17.
Qed.

Lemma H8_mono : forall x y, x <= y -> H8 x <= H8 y.
Proof.
  intros x y Hxy. unfold H8.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H7_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H8_gt : forall m, 1 <= m -> f_omega2_plus 3 m < H8 m.
Proof.
  intros m Hm. unfold H8.
  apply (climb_2m_minus_1 H7 (f_omega2_plus 2) 1 ltac:(lia) H7_mono H7_inc H7_gt (fOmega2_props 1 0 2) m Hm).
Qed.

Lemma H8_ge_17 : forall m, 1 <= m -> 17 <= H8 m.
Proof.
  intros m Hm. unfold H8.
  destruct (2 * m - 1) as [| q] eqn:E; [lia |].
  rewrite iter_succ. apply H7_ge_17.
  apply iter_ge_self; intro z; destruct z; [lia | pose proof (H7_inc (S z) ltac:(lia)); lia].
Qed.

Lemma reload_7 : forall r m R,
  exists t, Reaches bb89 (Scfg (S (S r)) 0 m (7 :: R)) (Scfg (S r) 0 1 (rep (2 * m) 6 R)) t.
Proof.
  intros r m R. destruct (sweep_HG bb89 bb89_core (S r) m 7 R) as [ts Hs].
  eexists. eapply reaches_trans.
  - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 6 2 7 _ _ R eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 5 4 7 _ _ R eq_refl) |].
    apply (loop_D4 (2 * m + 1) (rep (S (S r)) 5 []) (6 :: R)).
  - rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 5 5 4 _ _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 5 _ eq_refl) |].
    replace (6 :: 6 :: rep (2 * m + 1) 6 R) with (6 :: 6 :: 6 :: rep (2 * m) 6 R)
      by (replace (2 * m + 1) with (S (2 * m)) by lia; reflexivity).
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 6 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 6 _ eq_refl) |].
    apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 2 1 _ _ 6 _ eq_refl).
Qed.

Lemma rule_7 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb89 (Scfg (S (S r)) 0 m (7 :: R)) (Scfg (S (S r')) 0 m' R) t /\\
    H7 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_7 r m R) as [t0 H0].
  destruct (rule_6_rep (2 * m) r 1 R ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (Ht2 ltac:(lia)) as [Ht2_le Hr2_pos].
  destruct r2 as [| r2']; [lia |].
  exists r2', m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split; [exact Hm2 | lia]].
Qed.

Lemma rule_7_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb89 (Scfg (S (S r)) 0 m (rep n 7 R)) (Scfg (S (S r')) 0 m' R) t /\\
    iter H7 n m <= m' /\\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_7 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_7 r m (rep (S p') 7 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H7_ge_17 m Hm); lia).
      destruct (IH r1 m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H7 (S (S p')) m) with (iter H7 (S p') (H7 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H7_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma reload_8 : forall r m R, 1 <= m ->
  exists t, Reaches bb89 (Scfg (S r) 0 m (8 :: R)) (Scfg (S (S (S r))) 0 1 (rep (2 * m - 1) 7 R)) t.
Proof.
  intros r m R Hm. destruct m as [| m']; [lia |].
  destruct (sweep_HG bb89 bb89_core r (S m') 8 R) as [ts Hs].
  eexists. eapply reaches_trans.
  - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 7 2 8 _ _ R eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * S m' + 2) with (S (2 * S m' + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 4 8 _ _ R eq_refl) |].
    apply (loop_G4 (2 * S m' + 1) (rep (S r) 5 []) (7 :: R)).
  - rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 5 4 _ _ _ eq_refl) |].
    replace (7 :: 7 :: rep (2 * S m' + 1) 7 R) with (rep (2 * S m' + 3) 7 R)
      by (replace (2 * S m' + 3) with (S (S (2 * S m' + 1))) by lia; reflexivity).
    eapply reaches_trans; [apply (loop_G5 r [] (rep (2 * S m' + 3) 7 R)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil _ 6 4 5 _ _ eq_refl) |].
    change (5 :: rep r 5 (rep (2 * S m' + 3) 7 R)) with (rep (S r) 5 (rep (2 * S m' + 3) 7 R)).
    eapply steps_succ; [apply (step_mkCfgR_L_nil _ 6 4 0 _ _ eq_refl) |].
    change (5 :: rep (S r) 5 (rep (2 * S m' + 3) 7 R)) with (rep (S (S r)) 5 (rep (2 * S m' + 3) 7 R)).
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ eq_refl) |].
    eapply reaches_trans; [apply (loop_B5_H bb89 bb89_core (S (S r)) [5] (rep (2 * S m' + 3) 7 R)) |].
    rewrite rep_snoc_one.
    replace (rep (2 * S m' + 3) 7 R) with (7 :: 7 :: 7 :: 7 :: rep (2 * S m' - 1) 7 R)
      by (replace (2 * S m' + 3) with (S (S (S (S (2 * S m' - 1))))) by lia; reflexivity).
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 7 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ _ 7 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 4 2 _ _ 7 _ eq_refl) |].
    apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 5 1 _ _ 7 _ eq_refl).
Qed.

Lemma rule_8 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb89 (Scfg (S r) 0 m (8 :: R)) (Scfg (S (S r')) 0 m' R) t /\\
    H8 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_8 r m R Hm) as [t0 H0].
  destruct (rule_7_rep (2 * m - 1) (S r) 1 R ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split; [exact Hm2 | pose proof (Ht2 ltac:(lia)); lia]].
Qed.

Lemma rule_8_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb89 (Scfg (S r) 0 m (rep n 8 R)) (Scfg (S r') 0 m' R) t /\\
    iter H8 n m <= m' /\\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_8 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists (S r1), m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_8 r m (rep (S p') 8 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H8_ge_17 m Hm); lia).
      destruct (IH (S r1) m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H8 (S (S p')) m) with (iter H8 (S p') (H8 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H8_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb89_bootstrap :
  Reaches bb89 initConfig (Scfg 1 0 0 [2; 8; 8; 8; 8; 1; 8; 8; 8; 5]) 119.
Proof. vm_compute. reflexivity. Qed.

Theorem bb89_halts_gt_f_omega2_plus_4_7 :
  ValidTM 8 9 bb89 /\\ exists t, HaltsIn bb89 initConfig t /\\ f_omega2_plus 4 7 < t.
Proof.
  split; [exact bb89_valid |].
  pose proof bb89_bootstrap as Hboot.
  destruct (rule_2_H bb89 bb89_core 0 0 [8; 8; 8; 8; 1; 8; 8; 8; 5]) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_7 : 7 <= m1) by (pose proof H2_H_0_ge; lia).
  destruct (rule_8_rep 4 (S r1) m1 [1; 8; 8; 8; 5] ltac:(lia)) as [r2 [m2 [t2 [H2s [Hm2 _]]]]].
  assert (H2b : iter H8 4 7 <= m2) by (pose proof (iter_mono_arg H8 H8_mono 4 7 m1 Hm1_7); lia).
  destruct (fwp2_step bb89 (fh_fp _ bb89_core) (S r2) 0 m2 [8; 8; 8; 5]) as [t3 [H3 _]].
  assert (Hm3 : S m2 <= Pfn (S r2) 0 m2) by apply Pfn_ge_succ.
  destruct (rule_8_rep 3 r2 (Pfn (S r2) 0 m2) [5] ltac:(lia)) as [r4 [m4 [t4 [H4 [Hm4 Ht4]]]]].
  assert (H4b : iter H8 7 7 <= m4).
  {{ eapply Nat.le_trans; [| exact Hm4].
     change (iter H8 7 7) with (iter H8 (3 + 4) 7). rewrite iter_add.
     apply iter_mono_arg; [apply H8_mono | lia]. }}
  assert (Hhalt : step bb89 (Scfg (S r4) 0 m4 [5]) =
    Some (mkCfgR None (1 :: 2 :: rep (2 * m4 + 1) 3 (rep (S r4) 5 [])) [])).
  {{ apply (step_mkCfgR_R _ 0 0 _ _ 5 [] eq_refl). }}
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _
      (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2s) H3) H4)
    (steps_one _ _ _ Hhalt)) as Hreach.
  pose proof (iter_strict_dom H8 (f_omega2_plus 3) 1 H8_gt (fOmega2_props 1 0 3) 7 7 ltac:(lia) ltac:(lia)) as Hlt.
  pose proof (Ht4 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (f_omega2_plus 4 7) with (iter (f_omega2_plus 3) 7 7). lia.
Qed.

Print Assumptions bb89_halts_gt_f_omega2_plus_4_7.
"""

for path, content in [
    ('lean/BB/BB8_7.lean', bb87_lean),
    ('rocq/BB8_7.v', bb87_v),
    ('lean/BB/BB8_8.lean', bb88_lean),
    ('rocq/BB8_8.v', bb88_v),
    ('lean/BB/BB8_9.lean', bb89_lean),
    ('rocq/BB8_9.v', bb89_v),
]:
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(content)
print("Generated all 6 files for BB(8,7), BB(8,8), BB(8,9)!")
