"""Generate exact, axiom-free Lean 4 and Rocq 9.1 proofs for BB(7,7), BB(7,8), BB(7,9)."""
from search.gen_tm import gen_lean_tm, gen_rocq_tm

TM77 = '6LF3LB6LA2RA4LB5RC5LA_1RZ3RB1LD2RA3LF5RB6LD_3RB1LB3LC2RC4LC1LE5RB_3RB3RE3LC2RC0LE3RD1LA_5RB3RE2LE4LC3LG5LE1RZ_5RB5RB4RF1LF2LD5LF4RG_5LF1RZ5LB1LG2RG5LG1RZ'
TM78 = '7LD3LB6LA2RA4LB5RC5LA2LG_1RZ3RB1LD2RA3LF5RB6LD4RG_3RB1LB3LC2RC4LC1LE5RB3RF_3RB3RE3LC2RC7RB3RD1LA7LD_5RB3RE7RD4LC3LG5LE0LA1LG_5RB5RB2RA1LF2LA5LF5RD7LF_5LF3LA7LA1LG7LA5LG7RD0RG'
TM79 = '8RG3LB6LA2RA4LB5RC5LA2LG7LE_1RZ3RB1LD2RA3LF5RB6LD1RZ5LD_3RB1LB3LC2RC4LC1LE5RB3RF3RD_3RB3RE3LC2RC7LF3RD1LA2RA8LE_5RB3RE8LA4LC3LG5LE1RZ1RZ3LA_5RB5RB2RA1LF8LF5LF1RZ1RF8LC_5LF4RG7LA1LG8RC5LG1LC4RF8RG'

# ===================== BB(7, 7) =====================
bb77_lean = f"""/-
  BB/BB7_7.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(7, 7):
    TM: {TM77}
    Domain: BB(7, 7) (7 states, 7 symbols)
    Previous best dominated bounds: BB(7, 6) > f_{{ω^2}}(110), BB(6, 7) > f_{{ω×2+1}}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+1}}(3)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_7

namespace BB
namespace BB7_7

{gen_lean_tm('bb77', TM77)}

theorem bb77_core : Fwp2_7Core bb77 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bb77_bootstrap :
    Reaches bb77 initConfig (Scfg 2 0 0 [2, 2, 2, 2, 1, 5]) 69 := rfl

theorem bb77_halts_gt_f_omega2_plus_1_3 :
    ValidTM 7 7 bb77 ∧ ∃ t, HaltsIn bb77 initConfig t ∧ f_omega2_plus 1 3 < t := by
  refine ⟨bb77_valid, ?_⟩
  have hboot := bb77_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_2_7 bb77_core 1 0 [2, 2, 2, 1, 5]
  have hm1_3 : 3 ≤ m1 := Nat.le_trans (by omega : 3 ≤ 17) (Nat.le_trans H2_7_0_ge hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2_7_rep bb77_core 3 r1 m1 [1, 5]
  obtain ⟨t3, h3, _⟩ := fwp2_step bb77_core.fp (r2 + 1) 0 m2 [5]
  obtain ⟨cf, hhalt, hst⟩ := rule_halt_5_7 bb77_core r2 (Pfn (r2 + 1) 0 m2)
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans hboot h1) h2) h3) hhalt
  have hlt1 : f_omega2_plus 1 3 < iter H2_7 3 3 :=
    iter_strict_dom H2_7 f_omega2 1 H2_7_gt (fOmega2_props 1 0 0) 3 3 (by omega) (by omega)
  have hlt2 : iter H2_7 3 3 ≤ iter H2_7 3 m1 := iter_mono_arg H2_7 (fun _ _ h => H2_7_mono h) 3 hm1_3
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  have hlt_m2 : f_omega2_plus 1 3 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb77_halts_gt_f_omega2_plus_1_3

end BB7_7
end BB
"""

bb77_v = f"""(*
  rocq/BB7_7.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 7):
    TM: {TM77}
    Domain: BB(7, 7) (7 states, 7 symbols)
    Previous best dominated bounds: BB(7, 6) > f_{{ω^2}}(110), BB(6, 7) > f_{{ω×2+1}}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+1}}(3)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_7.
Import ListNotations.

{gen_rocq_tm('bb77', TM77)}

Lemma bb77_core : Fwp2_7Core bb77.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Lemma bb77_bootstrap :
  Reaches bb77 initConfig (Scfg 2 0 0 [2; 2; 2; 2; 1; 5]) 69.
Proof. vm_compute. reflexivity. Qed.

Theorem bb77_halts_gt_f_omega2_plus_1_3 :
  ValidTM 7 7 bb77 /\\ exists t, HaltsIn bb77 initConfig t /\\ f_omega2_plus 1 3 < t.
Proof.
  split; [exact bb77_valid |].
  pose proof bb77_bootstrap as Hboot.
  destruct (rule_2_7 bb77 bb77_core 1 0 [2; 2; 2; 1; 5]) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_3 : 3 <= m1) by (pose proof H2_7_0_ge; lia).
  destruct (rule_2_7_rep bb77 bb77_core 3 r1 m1 [1; 5]) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  destruct (fwp2_step bb77 (f7_fp _ bb77_core) (S r2) 0 m2 [5]) as [t3 [H3 _]].
  destruct (rule_halt_5_7 bb77 bb77_core r2 (Pfn (S r2) 0 m2)) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r) H3) Hhalt) as Hreach.
  pose proof (iter_strict_dom H2_7 f_omega2 1 H2_7_gt (fOmega2_props 1 0 0) 3 3 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H2_7 H2_7_mono 3 3 m1 Hm1_3) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 1 3) with (iter f_omega2 3 3). lia.
Qed.

Print Assumptions bb77_halts_gt_f_omega2_plus_1_3.
"""

# ===================== BB(7, 8) =====================
bb78_lean = f"""/-
  BB/BB7_8.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(7, 8):
    TM: {TM78}
    Domain: BB(7, 8) (7 states, 8 symbols)
    Previous best dominated bounds: BB(7, 7) > f_{{ω^2+1}}(3), BB(6, 8) > f_{{ω×2+2}}(11)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+2}}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_7

namespace BB
namespace BB7_8

{gen_lean_tm('bb78', TM78)}

theorem bb78_core : Fwp2_7Core bb78 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Symbol `7` Reload: `Scfg (r+1) 0 m (7 :: R) --> Scfg (r+1) 0 0 (rep (2*m + 1) 2 R)` -/

private theorem loop_G_7 (n : Nat) (L R : List Nat) :
    Reaches bb78 (mkCfgR (some 6) (rep n 3 L) (2 :: R))
                 (mkCfgR (some 6) L (2 :: rep n 2 R)) (3 * n) := by
  induction n generalizing R with
  | zero => exact reaches_zero bb78 _
  | succ k ih =>
    have h1 : step bb78 (mkCfgR (some 6) (3 :: rep k 3 L) (2 :: R)) =
              some (mkCfgR (some 0) (rep k 3 L) (3 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb78) (q := 6) (w := 6) (cur := 2) rfl
    have h2 : step bb78 (mkCfgR (some 0) (rep k 3 L) (3 :: 7 :: R)) =
              some (mkCfgR (some 0) (2 :: rep k 3 L) (7 :: R)) :=
      step_mkCfgR_R (tm := bb78) (q := 0) (w := 1) (cur := 3) rfl
    have h3 : step bb78 (mkCfgR (some 0) (2 :: rep k 3 L) (7 :: R)) =
              some (mkCfgR (some 6) (rep k 3 L) (2 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb78) (q := 0) (w := 1) (cur := 7) rfl
    have h4 := ih (2 :: R); rw [rep_snoc_one] at h4
    have hall := steps_succ bb78 _ _ _ _ h1 (steps_succ bb78 _ _ _ _ h2 (steps_succ bb78 _ _ _ _ h3 h4))
    have ht : 3 * k + 1 + 1 + 1 = 3 * (k + 1) := by omega
    rw [ht] at hall; exact hall

theorem reload_7 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb78 (Scfg (r + 1) 0 m (7 :: R)) (Scfg (r + 1) 0 0 (rep (2 * m + 1) 2 R)) t := by
  have h1 : step bb78 (Scfg (r + 1) 0 m (7 :: R)) =
            some (mkCfgR (some 6) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb78) (q := 0) (w := 1) (cur := 7) rfl
  have h2 := loop_G_7 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h2
  have h3 : step bb78 (mkCfgR (some 6) (5 :: rep r 5 []) (2 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 0) (rep r 5 []) (5 :: 7 :: rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb78) (q := 6) (w := 6) (cur := 2) rfl
  have h4 : step bb78 (mkCfgR (some 0) (rep r 5 []) (5 :: 7 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 2) (5 :: rep r 5 []) (7 :: rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb78) (q := 0) (w := 4) (cur := 5) rfl
  have h5 : step bb78 (mkCfgR (some 2) (5 :: rep r 5 []) (7 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 5) (3 :: 5 :: rep r 5 []) (rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb78) (q := 2) (w := 2) (cur := 7) rfl
  have h6 : step bb78 (mkCfgR (some 5) (3 :: 5 :: rep r 5 []) (2 :: rep (2 * m + 1) 2 R)) =
            some (Scfg (r + 1) 0 0 (rep (2 * m + 1) 2 R)) :=
    step_mkCfgR_R (tm := bb78) (q := 5) (w := 1) (cur := 2) rfl
  exact ⟨_, steps_succ bb78 _ _ _ _ h1 (reaches_trans h2
    (steps_succ bb78 _ _ _ _ h3 (steps_succ bb78 _ _ _ _ h4
      (steps_succ bb78 _ _ _ _ h5 (steps_one bb78 _ _ h6)))))⟩

def H7 (m : Nat) : Nat := iter H2_7 (2 * m) 17

theorem H7_mono {{x y : Nat}} (hxy : x ≤ y) : H7 x ≤ H7 y :=
  iter_mono_steps H2_7 (fun z => by have := Pempty_ge (2 * z + 1); unfold H2_7; omega) (by omega) 17

theorem H7_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 1 m < H7 m :=
  climb_double H2_7 f_omega2 17 (by omega) (fun _ _ h => H2_7_mono h) H2_7_inc H2_7_gt
    (fOmega2_props 1 0 0) m hm

theorem rule_7 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb78 (Scfg (r + 1) 0 m (7 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_7 r m R
  obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_2_7 bb78_core r 0 (rep (2 * m) 2 R)
  have hm1_17 : 17 ≤ m1 := Nat.le_trans H2_7_0_ge hm1
  cases m with
  | zero =>
    have hH7 : H7 0 = 17 := rfl
    exact ⟨r1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ m' =>
    obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2_7_rep bb78_core (2 * (m' + 1)) r1 m1 R
    have harg : iter H2_7 (2 * (m' + 1)) 17 ≤ iter H2_7 (2 * (m' + 1)) m1 :=
      iter_mono_arg H2_7 (fun _ _ h => H2_7_mono h) (2 * (m' + 1)) hm1_17
    exact ⟨r2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans harg hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem rule_7_rep (n : Nat) :
    ∀ r m R, ∃ r' m' t, Reaches bb78 (Scfg (r + 1) 0 m (rep n 7 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H7 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero bb78 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_7 r m R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_7 r m (rep (p' + 1) 7 R)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R
      have hcomm : iter H7 (p' + 1) (H7 m) = iter H7 (p' + 2) m := (iter_add H7 (p' + 1) 1 m).symm
      have hmb : iter H7 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H7 (fun _ _ h => H7_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb78_bootstrap :
    Reaches bb78 initConfig (Scfg 1 0 0 (7 :: 2 :: rep 7 7 [2, 1, 5])) 268 := rfl

theorem bb78_halts_gt_f_omega2_plus_2_7 :
    ValidTM 7 8 bb78 ∧ ∃ t, HaltsIn bb78 initConfig t ∧ f_omega2_plus 2 7 < t := by
  refine ⟨bb78_valid, ?_⟩
  have hboot := bb78_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_7 0 0 (2 :: rep 7 7 [2, 1, 5])
  obtain ⟨r2, m2, t2, h2, hm2, _⟩ := rule_2_7 bb78_core r1 m1 (rep 7 7 [2, 1, 5])
  have hm2_7 : 7 ≤ m2 := by
    have h17 : 17 ≤ m1 := by have : H7 0 = 17 := rfl; omega
    have hinc := Pempty_ge (2 * m1 + 1)
    unfold H2_7 at hm2; omega
  obtain ⟨r3, m3, t3, h3, hm3, ht3⟩ := rule_7_rep 7 r2 m2 [2, 1, 5]
  obtain ⟨r4, m4, t4, h4, _, _⟩ := rule_2_7 bb78_core r3 m3 [1, 5]
  obtain ⟨t5, h5, _⟩ := fwp2_step bb78_core.fp (r4 + 1) 0 m4 [5]
  obtain ⟨cf, hhalt, hst⟩ := rule_halt_5_7 bb78_core r4 (Pfn (r4 + 1) 0 m4)
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans
    (reaches_trans (reaches_trans hboot h1) h2) h3) h4) h5) hhalt
  have hlt1 : f_omega2_plus 2 7 < iter H7 7 7 :=
    iter_strict_dom H7 (f_omega2_plus 1) 1 H7_gt (fOmega2_props 1 0 1) 7 7 (by omega) (by omega)
  have hlt2 : iter H7 7 7 ≤ iter H7 7 m2 := iter_mono_arg H7 (fun _ _ h => H7_mono h) 7 hm2_7
  have hlt_m3 : f_omega2_plus 2 7 < m3 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm3
  have hle_t : m3 ≤ t3 := ht3 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m3 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb78_halts_gt_f_omega2_plus_2_7

end BB7_8
end BB
"""

bb78_v = f"""(*
  rocq/BB7_8.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 8):
    TM: {TM78}
    Domain: BB(7, 8) (7 states, 8 symbols)
    Previous best dominated bounds: BB(7, 7) > f_{{ω^2+1}}(3), BB(6, 8) > f_{{ω×2+2}}(11)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+2}}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_7.
Import ListNotations.

{gen_rocq_tm('bb78', TM78)}

Lemma bb78_core : Fwp2_7Core bb78.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_G_7 : forall n L R,
  Reaches bb78 (mkCfgR (Some 6) (rep n 3 L) (2 :: R))
               (mkCfgR (Some 6) L (2 :: rep n 2 R)) (3 * n).
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  replace (3 * S k) with (S (S (S (3 * k)))) by lia.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 3 2 _ _ R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 3 (7 :: R) eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 1 2 7 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma reload_7 : forall r m R,
  exists t, Reaches bb78 (Scfg (S r) 0 m (7 :: R)) (Scfg (S r) 0 0 (rep (2 * m + 1) 2 R)) t.
Proof.
  intros r m R. eexists.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 1 2 7 _ _ R eq_refl) |].
  eapply reaches_trans; [apply (loop_G_7 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
  rewrite rep_snoc_one.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 5 2 _ _ _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 4 _ _ 5 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ _ 7 _ eq_refl) |].
  apply steps_one. unfold Scfg.
  apply (step_mkCfgR_R _ 5 1 _ _ 2 _ eq_refl).
Qed.

Definition H7 (m : nat) : nat := iter H2_7 (2 * m) 17.

Lemma H7_mono : forall x y, x <= y -> H7 x <= H7 y.
Proof.
  intros x y Hxy. unfold H7.
  apply iter_mono_steps; [intro z; unfold H2_7; pose proof (Pempty_ge (2 * z + 1)); lia | lia].
Qed.

Lemma H7_gt : forall m, 1 <= m -> f_omega2_plus 1 m < H7 m.
Proof.
  intros m Hm. unfold H7.
  apply (climb_double H2_7 f_omega2 17 ltac:(lia) H2_7_mono H2_7_inc H2_7_gt (fOmega2_props 1 0 0) m Hm).
Qed.

Lemma rule_7 : forall r m R,
  exists r' m' t, Reaches bb78 (Scfg (S r) 0 m (7 :: R)) (Scfg (S r') 0 m' R) t /\\
    H7 m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_7 r m R) as [t0 H0].
  replace (2 * m + 1) with (S (2 * m)) in H0 by lia.
  destruct (rule_2_7 bb78 bb78_core r 0 (rep (2 * m) 2 R)) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
  assert (Hm1_17 : 17 <= m1) by (pose proof H2_7_0_ge; lia).
  destruct m as [| m'].
  - exists r1, m1, (t0 + t1). split; [eapply reaches_trans; eassumption | split; [change (H7 0) with 17; lia | lia]].
  - destruct (rule_2_7_rep bb78 bb78_core (2 * S m') r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
    exists r2, m2, ((t0 + t1) + t2). split; [eapply reaches_trans; [eapply reaches_trans; eassumption | exact H2r] | split].
    + unfold H7. eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_7_mono | exact Hm1_17] | exact Hm2].
    + pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_7_rep : forall n r m R,
  exists r' m' t, Reaches bb78 (Scfg (S r) 0 m (rep n 7 R)) (Scfg (S r') 0 m' R) t /\\
    iter H7 n m <= m' /\\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_7 r m R) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_7 r m (rep (S p') 7 R)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H7 (S (S p')) m) with (iter H7 (S p') (H7 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H7_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb78_bootstrap :
  Reaches bb78 initConfig (Scfg 1 0 0 (7 :: 2 :: rep 7 7 [2; 1; 5])) 268.
Proof. vm_compute. reflexivity. Qed.

Theorem bb78_halts_gt_f_omega2_plus_2_7 :
  ValidTM 7 8 bb78 /\\ exists t, HaltsIn bb78 initConfig t /\\ f_omega2_plus 2 7 < t.
Proof.
  split; [exact bb78_valid |].
  pose proof bb78_bootstrap as Hboot.
  destruct (rule_7 0 0 (2 :: rep 7 7 [2; 1; 5])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  destruct (rule_2_7 bb78 bb78_core r1 m1 (rep 7 7 [2; 1; 5])) as [r2 [m2 [t2 [H2s [Hm2 _]]]]].
  assert (Hm2_7 : 7 <= m2).
  {{ change (H7 0) with 17 in Hm1. unfold H2_7 in Hm2. pose proof (Pempty_ge (2 * m1 + 1)). lia. }}
  destruct (rule_7_rep 7 r2 m2 [2; 1; 5]) as [r3 [m3 [t3 [H3 [Hm3 Ht3]]]]].
  destruct (rule_2_7 bb78 bb78_core r3 m3 [1; 5]) as [r4 [m4 [t4 [H4 _]]]].
  destruct (fwp2_step bb78 (f7_fp _ bb78_core) (S r4) 0 m4 [5]) as [t5 [H5 _]].
  destruct (rule_halt_5_7 bb78 bb78_core r4 (Pfn (S r4) 0 m4)) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _
      (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2s) H3) H4) H5) Hhalt) as Hreach.
  pose proof (iter_strict_dom H7 (f_omega2_plus 1) 1 H7_gt (fOmega2_props 1 0 1) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H7 H7_mono 7 7 m2 Hm2_7) as Hlt2.
  pose proof (Ht3 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 2 7) with (iter (f_omega2_plus 1) 7 7). lia.
Qed.

Print Assumptions bb78_halts_gt_f_omega2_plus_2_7.
"""

# ===================== BB(7, 9) =====================
bb79_lean = f"""/-
  BB/BB7_9.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(7, 9):
    TM: {TM79}
    Domain: BB(7, 9) (7 states, 9 symbols)
    Previous best dominated bounds: BB(7, 8) > f_{{ω^2+2}}(7), BB(6, 9) > f_{{ω×2+3}}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+3}}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_7

namespace BB
namespace BB7_9

{gen_lean_tm('bb79', TM79)}

theorem bb79_core : Fwp2_7Core bb79 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_G_7 (n : Nat) (L R : List Nat) :
    Reaches bb79 (mkCfgR (some 6) (rep n 3 L) (2 :: R))
                 (mkCfgR (some 6) L (2 :: rep n 2 R)) (3 * n) := by
  induction n generalizing R with
  | zero => exact reaches_zero bb79 _
  | succ k ih =>
    have h1 : step bb79 (mkCfgR (some 6) (3 :: rep k 3 L) (2 :: R)) =
              some (mkCfgR (some 0) (rep k 3 L) (3 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb79) (q := 6) (w := 6) (cur := 2) rfl
    have h2 : step bb79 (mkCfgR (some 0) (rep k 3 L) (3 :: 7 :: R)) =
              some (mkCfgR (some 0) (2 :: rep k 3 L) (7 :: R)) :=
      step_mkCfgR_R (tm := bb79) (q := 0) (w := 1) (cur := 3) rfl
    have h3 : step bb79 (mkCfgR (some 0) (2 :: rep k 3 L) (7 :: R)) =
              some (mkCfgR (some 6) (rep k 3 L) (2 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb79) (q := 0) (w := 1) (cur := 7) rfl
    have h4 := ih (2 :: R); rw [rep_snoc_one] at h4
    have hall := steps_succ bb79 _ _ _ _ h1 (steps_succ bb79 _ _ _ _ h2 (steps_succ bb79 _ _ _ _ h3 h4))
    have ht : 3 * k + 1 + 1 + 1 = 3 * (k + 1) := by omega
    rw [ht] at hall; exact hall

private theorem loop_E_8 (n : Nat) (L R : List Nat) :
    Reaches bb79 (mkCfgR (some 4) (rep n 3 L) (2 :: R))
                 (mkCfgR (some 4) L (2 :: rep n 7 R)) (3 * n) := by
  induction n generalizing R with
  | zero => exact reaches_zero bb79 _
  | succ k ih =>
    have h1 : step bb79 (mkCfgR (some 4) (3 :: rep k 3 L) (2 :: R)) =
              some (mkCfgR (some 0) (rep k 3 L) (3 :: 8 :: R)) :=
      step_mkCfgR_L_cons (tm := bb79) (q := 4) (w := 7) (cur := 2) rfl
    have h2 : step bb79 (mkCfgR (some 0) (rep k 3 L) (3 :: 8 :: R)) =
              some (mkCfgR (some 0) (2 :: rep k 3 L) (8 :: R)) :=
      step_mkCfgR_R (tm := bb79) (q := 0) (w := 1) (cur := 3) rfl
    have h3 : step bb79 (mkCfgR (some 0) (2 :: rep k 3 L) (8 :: R)) =
              some (mkCfgR (some 4) (rep k 3 L) (2 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb79) (q := 0) (w := 6) (cur := 8) rfl
    have h4 := ih (7 :: R); rw [rep_snoc_one] at h4
    have hall := steps_succ bb79 _ _ _ _ h1 (steps_succ bb79 _ _ _ _ h2 (steps_succ bb79 _ _ _ _ h3 h4))
    have ht : 3 * k + 1 + 1 + 1 = 3 * (k + 1) := by omega
    rw [ht] at hall; exact hall

theorem reload_7 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb79 (Scfg (r + 1) 0 m (7 :: R)) (Scfg (r + 1) 0 0 (rep (2 * m + 1) 2 R)) t := by
  have h1 : step bb79 (Scfg (r + 1) 0 m (7 :: R)) =
            some (mkCfgR (some 6) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb79) (q := 0) (w := 1) (cur := 7) rfl
  have h2 := loop_G_7 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h2
  have h3 : step bb79 (mkCfgR (some 6) (5 :: rep r 5 []) (2 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 0) (rep r 5 []) (5 :: 7 :: rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb79) (q := 6) (w := 6) (cur := 2) rfl
  have h4 : step bb79 (mkCfgR (some 0) (rep r 5 []) (5 :: 7 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 2) (5 :: rep r 5 []) (7 :: rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 0) (w := 4) (cur := 5) rfl
  have h5 : step bb79 (mkCfgR (some 2) (5 :: rep r 5 []) (7 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 5) (3 :: 5 :: rep r 5 []) (rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 2) (w := 2) (cur := 7) rfl
  have h6 : step bb79 (mkCfgR (some 5) (3 :: 5 :: rep r 5 []) (2 :: rep (2 * m + 1) 2 R)) =
            some (Scfg (r + 1) 0 0 (rep (2 * m + 1) 2 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 5) (w := 1) (cur := 2) rfl
  exact ⟨_, steps_succ bb79 _ _ _ _ h1 (reaches_trans h2
    (steps_succ bb79 _ _ _ _ h3 (steps_succ bb79 _ _ _ _ h4
      (steps_succ bb79 _ _ _ _ h5 (steps_one bb79 _ _ h6)))))⟩

theorem reload_8 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb79 (Scfg (r + 1) 0 m (8 :: R)) (Scfg (r + 1) 0 0 (rep (2 * m + 1) 7 R)) t := by
  have h1 : step bb79 (Scfg (r + 1) 0 m (8 :: R)) =
            some (mkCfgR (some 4) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 7 :: R)) :=
    step_mkCfgR_L_cons (tm := bb79) (q := 0) (w := 6) (cur := 8) rfl
  have h2 := loop_E_8 (2 * m + 1) (rep (r + 1) 5 []) (7 :: R)
  rw [rep_snoc_one] at h2
  have h3 : step bb79 (mkCfgR (some 4) (5 :: rep r 5 []) (2 :: rep (2 * m + 2) 7 R)) =
            some (mkCfgR (some 0) (rep r 5 []) (5 :: 8 :: rep (2 * m + 2) 7 R)) :=
    step_mkCfgR_L_cons (tm := bb79) (q := 4) (w := 7) (cur := 2) rfl
  have h4 : step bb79 (mkCfgR (some 0) (rep r 5 []) (5 :: 8 :: rep (2 * m + 2) 7 R)) =
            some (mkCfgR (some 2) (5 :: rep r 5 []) (8 :: rep (2 * m + 2) 7 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 0) (w := 4) (cur := 5) rfl
  have h5 : step bb79 (mkCfgR (some 2) (5 :: rep r 5 []) (8 :: rep (2 * m + 2) 7 R)) =
            some (mkCfgR (some 3) (3 :: 5 :: rep r 5 []) (rep (2 * m + 2) 7 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 2) (w := 2) (cur := 8) rfl
  have h6 : step bb79 (mkCfgR (some 3) (3 :: 5 :: rep r 5 []) (7 :: rep (2 * m + 1) 7 R)) =
            some (Scfg (r + 1) 0 0 (rep (2 * m + 1) 7 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 3) (w := 1) (cur := 7) rfl
  exact ⟨_, steps_succ bb79 _ _ _ _ h1 (reaches_trans h2
    (steps_succ bb79 _ _ _ _ h3 (steps_succ bb79 _ _ _ _ h4
      (steps_succ bb79 _ _ _ _ h5 (steps_one bb79 _ _ h6)))))⟩

def H7 (m : Nat) : Nat := iter H2_7 (2 * m) 17
def H8 (m : Nat) : Nat := iter H7 (2 * m) 17

theorem H7_mono {{x y : Nat}} (hxy : x ≤ y) : H7 x ≤ H7 y :=
  iter_mono_steps H2_7 (fun z => by have := Pempty_ge (2 * z + 1); unfold H2_7; omega) (by omega) 17
theorem H7_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 1 m < H7 m :=
  climb_double H2_7 f_omega2 17 (by omega) (fun _ _ h => H2_7_mono h) H2_7_inc H2_7_gt
    (fOmega2_props 1 0 0) m hm
theorem H7_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H7 m := by
  have h1 := H7_gt m hm; have h2 : m ≤ f_omega2_plus 1 m := (fOmega2_props 1 0 1).ge_self m; omega

theorem H8_mono {{x y : Nat}} (hxy : x ≤ y) : H8 x ≤ H8 y :=
  iter_mono_steps H7 (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z' => exact Nat.le_trans (Nat.le_succ _) (H7_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 17
theorem H8_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H8 m :=
  climb_double H7 (f_omega2_plus 1) 17 (by omega) (fun _ _ h => H7_mono h) H7_inc H7_gt
    (fOmega2_props 1 0 1) m hm

theorem rule_7 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb79 (Scfg (r + 1) 0 m (7 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_7 r m R
  obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_2_7 bb79_core r 0 (rep (2 * m) 2 R)
  have hm1_17 : 17 ≤ m1 := Nat.le_trans H2_7_0_ge hm1
  cases m with
  | zero =>
    have hH7 : H7 0 = 17 := rfl
    exact ⟨r1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ m' =>
    obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2_7_rep bb79_core (2 * (m' + 1)) r1 m1 R
    have harg := iter_mono_arg H2_7 (fun _ _ h => H2_7_mono h) (2 * (m' + 1)) hm1_17
    exact ⟨r2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans harg hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem rule_7_rep (n : Nat) :
    ∀ r m R, ∃ r' m' t, Reaches bb79 (Scfg (r + 1) 0 m (rep n 7 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H7 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero bb79 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_7 r m R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_7 r m (rep (p' + 1) 7 R)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R
      have hcomm : iter H7 (p' + 1) (H7 m) = iter H7 (p' + 2) m := (iter_add H7 (p' + 1) 1 m).symm
      have hmb : iter H7 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H7 (fun _ _ h => H7_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem rule_8 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb79 (Scfg (r + 1) 0 m (8 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H8 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_8 r m R
  obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_7 r 0 (rep (2 * m) 7 R)
  have hm1_17 : 17 ≤ m1 := by have : H7 0 = 17 := rfl; omega
  cases m with
  | zero =>
    have hH8 : H8 0 = 17 := rfl
    exact ⟨r1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ m' =>
    obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_7_rep (2 * (m' + 1)) r1 m1 R
    have harg := iter_mono_arg H7 (fun _ _ h => H7_mono h) (2 * (m' + 1)) hm1_17
    exact ⟨r2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans harg hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem rule_8_rep (n : Nat) :
    ∀ r m R, ∃ r' m' t, Reaches bb79 (Scfg (r + 1) 0 m (rep n 8 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H8 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero bb79 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_8 r m R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_8 r m (rep (p' + 1) 8 R)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R
      have hcomm : iter H8 (p' + 1) (H8 m) = iter H8 (p' + 2) m := (iter_add H8 (p' + 1) 1 m).symm
      have hmb : iter H8 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H8 (fun _ _ h => H8_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem bb79_bootstrap :
    Reaches bb79 initConfig (Scfg 1 0 0 (rep 8 8 [5])) 74 := rfl

theorem bb79_halts_gt_f_omega2_plus_3_7 :
    ValidTM 7 9 bb79 ∧ ∃ t, HaltsIn bb79 initConfig t ∧ f_omega2_plus 3 7 < t := by
  refine ⟨bb79_valid, ?_⟩
  have hboot := bb79_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_8 0 0 (rep 7 8 [5])
  have hm1_7 : 7 ≤ m1 := by have : H8 0 = 17 := rfl; omega
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_8_rep 7 r1 m1 [5]
  obtain ⟨cf, hhalt, hst⟩ := rule_halt_5_7 bb79_core r2 m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 3 7 < iter H8 7 7 :=
    iter_strict_dom H8 (f_omega2_plus 2) 1 H8_gt (fOmega2_props 1 0 2) 7 7 (by omega) (by omega)
  have hlt2 : iter H8 7 7 ≤ iter H8 7 m1 := iter_mono_arg H8 (fun _ _ h => H8_mono h) 7 hm1_7
  have hlt_m2 : f_omega2_plus 3 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb79_halts_gt_f_omega2_plus_3_7

end BB7_9
end BB
"""

bb79_v = f"""(*
  rocq/BB7_9.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 9):
    TM: {TM79}
    Domain: BB(7, 9) (7 states, 9 symbols)
    Previous best dominated bounds: BB(7, 8) > f_{{ω^2+2}}(7), BB(6, 9) > f_{{ω×2+3}}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+3}}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_7.
Import ListNotations.

{gen_rocq_tm('bb79', TM79)}

Lemma bb79_core : Fwp2_7Core bb79.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_G_7 : forall n L R,
  Reaches bb79 (mkCfgR (Some 6) (rep n 3 L) (2 :: R))
               (mkCfgR (Some 6) L (2 :: rep n 2 R)) (3 * n).
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  replace (3 * S k) with (S (S (S (3 * k)))) by lia.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 3 2 _ _ R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 3 (7 :: R) eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 1 2 7 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_E_8 : forall n L R,
  Reaches bb79 (mkCfgR (Some 4) (rep n 3 L) (2 :: R))
               (mkCfgR (Some 4) L (2 :: rep n 7 R)) (3 * n).
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  replace (3 * S k) with (S (S (S (3 * k)))) by lia.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 7 3 2 _ _ R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 3 (8 :: R) eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 6 2 8 _ _ R eq_refl) |].
  specialize (IH L (7 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma reload_7 : forall r m R,
  exists t, Reaches bb79 (Scfg (S r) 0 m (7 :: R)) (Scfg (S r) 0 0 (rep (2 * m + 1) 2 R)) t.
Proof.
  intros r m R. eexists.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 1 2 7 _ _ R eq_refl) |].
  eapply reaches_trans; [apply (loop_G_7 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
  rewrite rep_snoc_one.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 5 2 _ _ _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 4 _ _ 5 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ _ 7 _ eq_refl) |].
  apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 5 1 _ _ 2 _ eq_refl).
Qed.

Lemma reload_8 : forall r m R,
  exists t, Reaches bb79 (Scfg (S r) 0 m (8 :: R)) (Scfg (S r) 0 0 (rep (2 * m + 1) 7 R)) t.
Proof.
  intros r m R. eexists.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 6 2 8 _ _ R eq_refl) |].
  eapply reaches_trans; [apply (loop_E_8 (2 * m + 1) (rep (S r) 5 []) (7 :: R)) |].
  rewrite rep_snoc_one.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 7 5 2 _ _ _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 4 _ _ 5 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ _ 8 _ eq_refl) |].
  apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 3 1 _ _ 7 _ eq_refl).
Qed.

Definition H7 (m : nat) : nat := iter H2_7 (2 * m) 17.
Definition H8 (m : nat) : nat := iter H7 (2 * m) 17.

Lemma H7_mono : forall x y, x <= y -> H7 x <= H7 y.
Proof.
  intros x y Hxy. unfold H7.
  apply iter_mono_steps; [intro z; unfold H2_7; pose proof (Pempty_ge (2 * z + 1)); lia | lia].
Qed.

Lemma H7_gt : forall m, 1 <= m -> f_omega2_plus 1 m < H7 m.
Proof.
  intros m Hm. unfold H7.
  apply (climb_double H2_7 f_omega2 17 ltac:(lia) H2_7_mono H2_7_inc H2_7_gt (fOmega2_props 1 0 0) m Hm).
Qed.

Lemma H7_inc : forall m, 1 <= m -> S m <= H7 m.
Proof.
  intros m Hm. pose proof (H7_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 1) m).
  change (f_omega2_plus 1 m) with (fOmega2 1 0 1 m) in *. lia.
Qed.

Lemma H8_mono : forall x y, x <= y -> H8 x <= H8 y.
Proof.
  intros x y Hxy. unfold H8.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H7_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H8_gt : forall m, 1 <= m -> f_omega2_plus 2 m < H8 m.
Proof.
  intros m Hm. unfold H8.
  apply (climb_double H7 (f_omega2_plus 1) 17 ltac:(lia) H7_mono H7_inc H7_gt (fOmega2_props 1 0 1) m Hm).
Qed.

Lemma rule_7 : forall r m R,
  exists r' m' t, Reaches bb79 (Scfg (S r) 0 m (7 :: R)) (Scfg (S r') 0 m' R) t /\\
    H7 m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_7 r m R) as [t0 H0].
  replace (2 * m + 1) with (S (2 * m)) in H0 by lia.
  destruct (rule_2_7 bb79 bb79_core r 0 (rep (2 * m) 2 R)) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
  assert (Hm1_17 : 17 <= m1) by (pose proof H2_7_0_ge; lia).
  destruct m as [| m'].
  - exists r1, m1, (t0 + t1). split; [eapply reaches_trans; eassumption | split; [change (H7 0) with 17; lia | lia]].
  - destruct (rule_2_7_rep bb79 bb79_core (2 * S m') r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
    exists r2, m2, ((t0 + t1) + t2). split; [eapply reaches_trans; [eapply reaches_trans; eassumption | exact H2r] | split].
    + unfold H7. eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_7_mono | exact Hm1_17] | exact Hm2].
    + pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_7_rep : forall n r m R,
  exists r' m' t, Reaches bb79 (Scfg (S r) 0 m (rep n 7 R)) (Scfg (S r') 0 m' R) t /\\
    iter H7 n m <= m' /\\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_7 r m R) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_7 r m (rep (S p') 7 R)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H7 (S (S p')) m) with (iter H7 (S p') (H7 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H7_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_8 : forall r m R,
  exists r' m' t, Reaches bb79 (Scfg (S r) 0 m (8 :: R)) (Scfg (S r') 0 m' R) t /\\
    H8 m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_8 r m R) as [t0 H0].
  replace (2 * m + 1) with (S (2 * m)) in H0 by lia.
  destruct (rule_7 r 0 (rep (2 * m) 7 R)) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
  assert (Hm1_17 : 17 <= m1) by (change (H7 0) with 17 in Hm1; lia).
  destruct m as [| m'].
  - exists r1, m1, (t0 + t1). split; [eapply reaches_trans; eassumption | split; [change (H8 0) with 17; lia | lia]].
  - destruct (rule_7_rep (2 * S m') r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
    exists r2, m2, ((t0 + t1) + t2). split; [eapply reaches_trans; [eapply reaches_trans; eassumption | exact H2r] | split].
    + unfold H8. eapply Nat.le_trans; [apply iter_mono_arg; [apply H7_mono | exact Hm1_17] | exact Hm2].
    + pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_8_rep : forall n r m R,
  exists r' m' t, Reaches bb79 (Scfg (S r) 0 m (rep n 8 R)) (Scfg (S r') 0 m' R) t /\\
    iter H8 n m <= m' /\\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_8 r m R) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_8 r m (rep (S p') 8 R)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H8 (S (S p')) m) with (iter H8 (S p') (H8 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H8_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb79_bootstrap :
  Reaches bb79 initConfig (Scfg 1 0 0 (rep 8 8 [5])) 74.
Proof. vm_compute. reflexivity. Qed.

Theorem bb79_halts_gt_f_omega2_plus_3_7 :
  ValidTM 7 9 bb79 /\\ exists t, HaltsIn bb79 initConfig t /\\ f_omega2_plus 3 7 < t.
Proof.
  split; [exact bb79_valid |].
  pose proof bb79_bootstrap as Hboot.
  destruct (rule_8 0 0 (rep 7 8 [5])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_7 : 7 <= m1) by (change (H8 0) with 17 in Hm1; lia).
  destruct (rule_8_rep 7 r1 m1 [5]) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  destruct (rule_halt_5_7 bb79 bb79_core r2 m2) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r) Hhalt) as Hreach.
  pose proof (iter_strict_dom H8 (f_omega2_plus 2) 1 H8_gt (fOmega2_props 1 0 2) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H8 H8_mono 7 7 m1 Hm1_7) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 3 7) with (iter (f_omega2_plus 2) 7 7). lia.
Qed.

Print Assumptions bb79_halts_gt_f_omega2_plus_3_7.
"""

for path, content in [
    ('lean/BB/BB7_7.lean', bb77_lean),
    ('rocq/BB7_7.v', bb77_v),
    ('lean/BB/BB7_8.lean', bb78_lean),
    ('rocq/BB7_8.v', bb78_v),
    ('lean/BB/BB7_9.lean', bb79_lean),
    ('rocq/BB7_9.v', bb79_v),
]:
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(content)
print("Generated all 6 files for BB(7,7), BB(7,8), BB(7,9)!")
