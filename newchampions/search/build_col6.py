"""Generate exact, axiom-free Lean 4 and Rocq 9.1 proofs for Column m=6: BB(9,6), BB(10,6), BB(11,6)."""
import json
from search.gen_tm import gen_lean_tm, gen_rocq_tm

with open('search/boots_9to11.json') as f:
    BOOTS = json.load(f)

TM96  = BOOTS['BB9_6']['tm']
TM106 = BOOTS['BB10_6']['tm']
TM116 = BOOTS['BB11_6']['tm']

# ===================== BB(9, 6) =====================
bb96_lean = f"""/-
  BB/BB9_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(9, 6):
    TM: {TM96}
    Domain: BB(9, 6) (9 states, 6 symbols)
    Previous best dominated bounds: BB(8, 6) > f_{{ω^2+1}}(f_ω(31)), BB(9, 5) > f_{{ω^2+1}}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+2}}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB9_6

{gen_lean_tm('bb96', TM96)}

theorem bb96_core : Fwp2_HCore bb96 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rule_51 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches bb96 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have ha : step bb96 (Scfg (r + 1) 0 m (5 :: 1 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) :=
    step_mkCfgR_R (tm := bb96) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb96 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) =
            some (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb96) (q := 8) (w := 4) (cur := 1) rfl
  have hc : step bb96 (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb96) (q := 8) (w := 1) (cur := 2) rfl
  have hd : step bb96 (mkCfgR (some 8) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb96) (q := 8) (w := 1) (cur := 2) rfl
  have he := loop_L3 (tm := bb96) (q := 8) (w' := 1) rfl (2 * m) (rep (r + 1) 5 []) (2 :: 2 :: 5 :: R)
  rw [rep_snoc_one, rep_snoc_one] at he
  have hf : step bb96 (mkCfgR (some 8) (5 :: rep r 5 []) (3 :: rep (2 * m + 2) 2 (5 :: R))) =
            some (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_L_cons (tm := bb96) (q := 8) (w := 1) (cur := 3) rfl
  have hg : step bb96 (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_R (tm := bb96) (q := 8) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he2, hme, hte⟩ := exec_G2_2s bb96_core r m hm (5 :: R)
  have hpre := reaches_trans
    (steps_succ bb96 _ _ _ _ ha (steps_succ bb96 _ _ _ _ hb
      (steps_succ bb96 _ _ _ _ hc (steps_succ bb96 _ _ _ _ hd he))))
    (steps_succ bb96 _ _ _ _ hf (steps_one bb96 _ _ hg))
  exact ⟨r' + 1, m', _, reaches_trans hpre he2, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb96_bootstrap :
    Reaches bb96 initConfig (Scfg 3 0 1 (5 :: rep 8 1 [])) 112 := rfl

theorem bb96_halts_gt_f_omega2_plus_2_7 :
    ValidTM 9 6 bb96 ∧ ∃ t, HaltsIn bb96 initConfig t ∧ f_omega2_plus 2 7 < t := by
  refine ⟨bb96_valid, ?_⟩
  have hboot := bb96_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_51 2 1 (rep 7 1 []) (by omega)
  have hm1_7 : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H_plus2_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 1 1 H_plus2
    (fun _ _ h => H_plus2_mono h) (fun z _ => Nat.le_trans (by omega : 1 ≤ 17) (H_plus2_ge_17 z))
    rule_51 7 r1 m1 [] (by omega)
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb96) (mark' := 1) rfl rfl (r2 + 1) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 2 7 < iter H_plus2 7 7 :=
    iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 7 7 (by omega) (by omega)
  have hlt2 : iter H_plus2 7 7 ≤ iter H_plus2 7 m1 := iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) 7 hm1_7
  have hlt_m2 : f_omega2_plus 2 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb96_halts_gt_f_omega2_plus_2_7

end BB9_6
end BB
"""

bb96_v = f"""(*
  rocq/BB9_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(9, 6):
    TM: {TM96}
    Domain: BB(9, 6) (9 states, 6 symbols)
    Previous best dominated bounds: BB(8, 6) > f_{{ω^2+1}}(f_ω(31)), BB(9, 5) > f_{{ω^2+1}}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+2}}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

{gen_rocq_tm('bb96', TM96)}

Lemma bb96_core : Fwp2_HCore bb96.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Lemma rule_51 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb96 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\\
    H_plus2 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (exec_G2_2s bb96 bb96_core r m (5 :: R) Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists (S r'), m'. eexists. split.
  - eapply reaches_trans; [| replace (S r' + 1) with (S (S r')) by lia; exact He].
    eapply reaches_trans.
    + replace (r + 1) with (S r) by lia. unfold Scfg.
      eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 5 _ eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 4 2 1 _ _ R eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 1 2 2 _ _ _ eq_refl) |].
      replace (2 * m + 1) with (S (2 * m)) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 1 3 2 _ _ _ eq_refl) |].
      apply (loop_L3 bb96 8 1 (2 * m) (rep (S r) 5 []) (2 :: 2 :: 5 :: R) eq_refl).
    + rewrite rep_snoc_one, rep_snoc_one.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 1 5 3 _ _ _ eq_refl) |].
      replace (2 :: 2 :: 2 :: rep (2 * m) 2 (5 :: R)) with (rep (2 * m + 3) 2 (5 :: R))
        by (replace (2 * m + 3) with (S (S (S (2 * m)))) by lia; reflexivity).
      apply steps_one. apply (step_mkCfgR_R _ 8 4 _ _ 5 _ eq_refl).
  - split; [exact Hme | lia].
Qed.

Lemma bb96_bootstrap :
  Reaches bb96 initConfig (Scfg 3 0 1 (5 :: rep 8 1 [])) 112.
Proof. vm_compute. reflexivity. Qed.

Theorem bb96_halts_gt_f_omega2_plus_2_7 :
  ValidTM 9 6 bb96 /\\ exists t, HaltsIn bb96 initConfig t /\\ f_omega2_plus 2 7 < t.
Proof.
  split; [exact bb96_valid |].
  pose proof bb96_bootstrap as Hboot.
  destruct (rule_51 2 1 (rep 7 1 []) ltac:(lia)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_7 : 7 <= m1) by (pose proof (H_plus2_ge_17 1); lia).
  assert (Hpos : forall x, 1 <= x -> 1 <= H_plus2 x) by (intros x _; pose proof (H_plus2_ge_17 x); lia).
  destruct (iter_cursor_rep bb96 1 1 H_plus2 H_plus2_mono Hpos rule_51 7 r1 m1 [] ltac:(lia))
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (halt_cursor_5 bb96 1 (r2 + 1) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H_plus2 H_plus2_mono 7 7 m1 Hm1_7) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 2 7) with (iter (f_omega2_plus 1) 7 7). lia.
Qed.

Print Assumptions bb96_halts_gt_f_omega2_plus_2_7.
"""

# ===================== BB(10, 6) =====================
bb106_lean = f"""/-
  BB/BB10_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(10, 6):
    TM: {TM106}
    Domain: BB(10, 6) (10 states, 6 symbols)
    Previous best dominated bounds: BB(9, 6) > f_{{ω^2+2}}(7), BB(10, 5) > f_{{ω^2+2}}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+3}}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB10_6

{gen_lean_tm('bb106', TM106)}

theorem bb106_core : Fwp2_HCore bb106 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_J4 (n : Nat) (L R : List Nat) :
    Reaches bb106 (mkCfgR (some 9) (rep n 4 L) (4 :: R))
                  (mkCfgR (some 9) L (4 :: rep n 4 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb106 _
  | succ k ih =>
    have h1 : step bb106 (mkCfgR (some 9) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 9) (rep k 4 L) (4 :: 4 :: R)) :=
      step_mkCfgR_L_cons (tm := bb106) (q := 9) (w := 3) (cur := 4) rfl
    have h2 := ih (4 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb106 k _ _ _ h1 h2

theorem rule_54 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have ha : step bb106 (Scfg (r + 1) 0 m (5 :: 4 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (4 :: R)) :=
    step_mkCfgR_R (tm := bb106) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb106 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (4 :: R)) =
            some (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 4) (cur := 4) rfl
  have hc : step bb106 (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 1) (cur := 2) rfl
  have hd : step bb106 (mkCfgR (some 8) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 1) (cur := 2) rfl
  have he := loop_L3 (tm := bb106) (q := 8) (w' := 1) rfl (2 * m) (rep (r + 1) 5 []) (2 :: 2 :: 5 :: R)
  rw [rep_snoc_one, rep_snoc_one] at he
  have hf : step bb106 (mkCfgR (some 8) (5 :: rep r 5 []) (3 :: rep (2 * m + 2) 2 (5 :: R))) =
            some (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 1) (cur := 3) rfl
  have hg : step bb106 (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_R (tm := bb106) (q := 8) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he2, hme, hte⟩ := exec_G2_2s bb106_core r m hm (5 :: R)
  have hpre := reaches_trans
    (steps_succ bb106 _ _ _ _ ha (steps_succ bb106 _ _ _ _ hb
      (steps_succ bb106 _ _ _ _ hc (steps_succ bb106 _ _ _ _ hd he))))
    (steps_succ bb106 _ _ _ _ hf (steps_one bb106 _ _ hg))
  exact ⟨r' + 1, m', _, reaches_trans hpre he2, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

def H51 (m : Nat) : Nat := iter H_plus2 (2 * m + 1) 1

theorem H51_mono {{x y : Nat}} (hxy : x ≤ y) : H51 x ≤ H51 y :=
  iter_mono_steps H_plus2 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H_plus2_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H51_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H51 m :=
  climb_2m_plus_1 H_plus2 (f_omega2_plus 1) 1 (by omega) (fun _ _ h => H_plus2_mono h) H_plus2_inc H_plus2_gt
    (fOmega2_props 1 0 1) m hm

theorem H51_ge_17 (m : Nat) : 17 ≤ H51 m :=
  iter_H_ge_17 H_plus2 (2 * m + 1) 1 (by omega) (by omega) H_plus2_inc (fun z _ => H_plus2_ge_17 z)

theorem reload_51 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R))
                       (Scfg (r + 1) 0 (Pempty r) (5 :: rep (2 * m + 1) 4 R)) t := by
  have ha : step bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) :=
    step_mkCfgR_R (tm := bb106) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb106 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) =
            some (mkCfgR (some 7) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 3) (cur := 1) rfl
  have hc : step bb106 (mkCfgR (some 7) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 4 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 1 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 7) (w := 0) (cur := 2) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb106_core r m 1 (4 :: R)
  have hd : step bb106 (mkCfgR (some 6) (rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (1 :: 4 :: R)) =
            some (mkCfgR (some 6) (4 :: rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: R)) :=
    step_mkCfgR_R (tm := bb106) (q := 6) (w := 3) (cur := 1) rfl
  have he : step bb106 (mkCfgR (some 6) (4 :: rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: R)) =
            some (mkCfgR (some 9) (rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 6) (w := 3) (cur := 4) rfl
  have hf := loop_J4 (2 * m + 2) (rep (r + 1) 5 []) (4 :: R)
  rw [rep_snoc_one] at hf
  have hg : step bb106 (mkCfgR (some 9) (5 :: rep r 5 []) (4 :: rep (2 * m + 3) 4 R)) =
            some (mkCfgR (some 9) (rep r 5 []) (5 :: rep (2 * m + 4) 4 R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 9) (w := 3) (cur := 4) rfl
  have hh : step bb106 (mkCfgR (some 9) (rep r 5 []) (5 :: rep (2 * m + 4) 4 R)) =
            some (mkCfgR (some 7) (rep (r + 1) 5 []) (rep (2 * m + 4) 4 R)) :=
    step_mkCfgR_R (tm := bb106) (q := 9) (w := 4) (cur := 5) rfl
  have hsplit : rep (2 * m + 4) 4 R = 4 :: 4 :: 4 :: rep (2 * m + 1) 4 R := by
    have heq : 2 * m + 4 = (2 * m + 1) + 3 := by omega
    rw [heq]; rfl
  rw [hsplit] at hh
  have hi : Reaches bb106
      (mkCfgR (some 7) (rep (r + 1) 5 []) (4 :: 4 :: 4 :: rep (2 * m + 1) 4 R))
      (mkCfgR (some 0) (2 :: rep (r + 1) 5 []) (1 :: 5 :: rep (2 * m + 1) 4 R)) 5 := by
    refine steps_succ bb106 4 _ _ _ (step_mkCfgR_R (tm := bb106) (q := 7) (w := 2) (cur := 4) rfl) ?_
    refine steps_succ bb106 3 _ _ _ (step_mkCfgR_R (tm := bb106) (q := 3) (w := 1) (cur := 4) rfl) ?_
    refine steps_succ bb106 2 _ _ _ (step_mkCfgR_L_cons (tm := bb106) (q := 5) (w := 4) (cur := 4) rfl) ?_
    refine steps_succ bb106 1 _ _ _ (step_mkCfgR_L_cons (tm := bb106) (q := 5) (w := 0) (cur := 2) rfl) ?_
    exact steps_one bb106 _ _ (step_mkCfgR_R (tm := bb106) (q := 0) (w := 1) (cur := 3) rfl)
  obtain ⟨te, hempty, _⟩ := fwp2_empty3 bb106_core.fp r (5 :: rep (2 * m + 1) 4 R)
  have hp1 := steps_succ bb106 _ _ _ _ ha (steps_succ bb106 _ _ _ _ hb (steps_succ bb106 _ _ _ _ hc
    (reaches_trans hs (steps_succ bb106 _ _ _ _ hd (steps_succ bb106 _ _ _ _ he hf)))))
  have hp2 := steps_succ bb106 _ _ _ _ hg (steps_succ bb106 _ _ _ _ hh (reaches_trans hi hempty))
  exact ⟨_, reaches_trans hp1 hp2⟩

theorem rule_51 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51 r m R
  have hpe : 1 ≤ Pempty r := Nat.le_trans (by omega : 1 ≤ r + 2) (Pempty_ge r)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 1 4 H_plus2
    (fun _ _ h => H_plus2_mono h) (fun z _ => Nat.le_trans (by omega : 1 ≤ 17) (H_plus2_ge_17 z))
    rule_54 (2 * m + 1) r (Pempty r) R hpe
  have harg : H51 m ≤ iter H_plus2 (2 * m + 1) (Pempty r) :=
    iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb106_bootstrap :
    Reaches bb106 initConfig (Scfg 1 0 1 (5 :: rep 8 1 [])) 131 := rfl

theorem bb106_halts_gt_f_omega2_plus_3_7 :
    ValidTM 10 6 bb106 ∧ ∃ t, HaltsIn bb106 initConfig t ∧ f_omega2_plus 3 7 < t := by
  refine ⟨bb106_valid, ?_⟩
  have hboot := bb106_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_51 0 1 (rep 7 1 [])
  have hm1_7 : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H51_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 1 1 H51
    (fun _ _ h => H51_mono h) rule_51 7 r1 m1 []
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb106) (mark' := 1) rfl rfl (r2 + 1) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 3 7 < iter H51 7 7 :=
    iter_strict_dom H51 (f_omega2_plus 2) 1 H51_gt (fOmega2_props 1 0 2) 7 7 (by omega) (by omega)
  have hlt2 : iter H51 7 7 ≤ iter H51 7 m1 := iter_mono_arg H51 (fun _ _ h => H51_mono h) 7 hm1_7
  have hlt_m2 : f_omega2_plus 3 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb106_halts_gt_f_omega2_plus_3_7

end BB10_6
end BB
"""

bb106_v = f"""(*
  rocq/BB10_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(10, 6):
    TM: {TM106}
    Domain: BB(10, 6) (10 states, 6 symbols)
    Previous best dominated bounds: BB(9, 6) > f_{{ω^2+2}}(7), BB(10, 5) > f_{{ω^2+2}}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+3}}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

{gen_rocq_tm('bb106', TM106)}

Lemma bb106_core : Fwp2_HCore bb106.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_J4 : forall n L R,
  Reaches bb106 (mkCfgR (Some 9) (rep n 4 L) (4 :: R))
                (mkCfgR (Some 9) L (4 :: rep n 4 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 9 3 4 4 _ _ R eq_refl) |].
  specialize (IH L (4 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rule_54 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\\
    H_plus2 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (exec_G2_2s bb106 bb106_core r m (5 :: R) Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists (S r'), m'. eexists. split.
  - eapply reaches_trans; [| replace (S r' + 1) with (S (S r')) by lia; exact He].
    eapply reaches_trans.
    + replace (r + 1) with (S r) by lia. unfold Scfg.
      eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 5 _ eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 4 2 4 _ _ R eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 1 2 2 _ _ _ eq_refl) |].
      replace (2 * m + 1) with (S (2 * m)) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 1 3 2 _ _ _ eq_refl) |].
      apply (loop_L3 bb106 8 1 (2 * m) (rep (S r) 5 []) (2 :: 2 :: 5 :: R) eq_refl).
    + rewrite rep_snoc_one, rep_snoc_one.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 1 5 3 _ _ _ eq_refl) |].
      replace (2 :: 2 :: 2 :: rep (2 * m) 2 (5 :: R)) with (rep (2 * m + 3) 2 (5 :: R))
        by (replace (2 * m + 3) with (S (S (S (2 * m)))) by lia; reflexivity).
      apply steps_one. apply (step_mkCfgR_R _ 8 4 _ _ 5 _ eq_refl).
  - split; [exact Hme | lia].
Qed.

Definition H51 (m : nat) : nat := iter H_plus2 (2 * m + 1) 1.

Lemma H51_mono : forall x y, x <= y -> H51 x <= H51 y.
Proof.
  intros x y Hxy. unfold H51.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H_plus2_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H51_gt : forall m, 1 <= m -> f_omega2_plus 2 m < H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (climb_2m_plus_1 H_plus2 (f_omega2_plus 1) 1 ltac:(lia) H_plus2_mono H_plus2_inc H_plus2_gt (fOmega2_props 1 0 1) m Hm).
Qed.

Lemma H51_ge_17 : forall m, 17 <= H51 m.
Proof.
  intro m. unfold H51.
  apply (iter_H_ge_17 H_plus2 (2 * m + 1) 1 ltac:(lia) ltac:(lia) H_plus2_inc (fun z _ => H_plus2_ge_17 z)).
Qed.

Lemma reload_51 : forall r m R,
  exists t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R))
                          (Scfg (r + 1) 0 (Pempty r) (5 :: rep (2 * m + 1) 4 R)) t.
Proof.
  intros r m R.
  destruct (sweep_HG bb106 bb106_core r m 1 (4 :: R)) as [ts Hs].
  destruct (fwp2_empty3 bb106 (fh_fp _ bb106_core) r (5 :: rep (2 * m + 1) 4 R)) as [te [Hempty _]].
  eexists. replace (r + 1) with (S r) by lia.
  eapply reaches_trans; [| exact Hempty].
  eapply reaches_trans.
  - unfold Scfg.
    eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 5 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 3 2 1 _ _ R eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 0 2 2 _ _ _ eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 6 3 _ _ 1 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 3 4 4 _ _ R eq_refl) |].
    apply (loop_J4 (2 * m + 2) (rep (S r) 5 []) (4 :: R)).
  - rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 9 3 5 4 _ _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 9 4 _ _ 5 _ eq_refl) |].
    replace (4 :: 4 :: rep (2 * m + 2) 4 R) with (4 :: 4 :: 4 :: rep (2 * m + 1) 4 R)
      by (replace (2 * m + 2) with (S (2 * m + 1)) by lia; reflexivity).
    eapply steps_succ; [apply (step_mkCfgR_R _ 7 2 _ _ 4 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 1 _ _ 4 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 4 2 4 _ _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 2 _ _ _ eq_refl) |].
    apply steps_one. apply (step_mkCfgR_R _ 0 1 _ _ 3 _ eq_refl).
Qed.

Lemma rule_51 : forall r m R,
  exists r' m' t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\\
    H51 m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_51 r m R) as [t0 H0].
  assert (Hpe : 1 <= Pempty r) by (pose proof (Pempty_ge r); lia).
  assert (Hpos : forall x, 1 <= x -> 1 <= H_plus2 x) by (intros x _; pose proof (H_plus2_ge_17 x); lia).
  destruct (iter_cursor_rep bb106 1 4 H_plus2 H_plus2_mono Hpos rule_54 (2 * m + 1) r (Pempty r) R Hpe)
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split].
  - unfold H51. eapply Nat.le_trans; [apply iter_mono_arg; [apply H_plus2_mono | exact Hpe] | exact Hm2].
  - pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb106_bootstrap :
  Reaches bb106 initConfig (Scfg 1 0 1 (5 :: rep 8 1 [])) 131.
Proof. vm_compute. reflexivity. Qed.

Theorem bb106_halts_gt_f_omega2_plus_3_7 :
  ValidTM 10 6 bb106 /\\ exists t, HaltsIn bb106 initConfig t /\\ f_omega2_plus 3 7 < t.
Proof.
  split; [exact bb106_valid |].
  pose proof bb106_bootstrap as Hboot.
  destruct (rule_51 0 1 (rep 7 1 [])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_7 : 7 <= m1) by (pose proof (H51_ge_17 1); lia).
  destruct (iter_cursor_rep0 bb106 1 1 H51 H51_mono rule_51 7 r1 m1 [])
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (halt_cursor_5 bb106 1 (r2 + 1) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom H51 (f_omega2_plus 2) 1 H51_gt (fOmega2_props 1 0 2) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H51 H51_mono 7 7 m1 Hm1_7) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 3 7) with (iter (f_omega2_plus 2) 7 7). lia.
Qed.

Print Assumptions bb106_halts_gt_f_omega2_plus_3_7.
"""

# ===================== BB(11, 6) =====================
bb116_lean = f"""/-
  BB/BB11_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(11, 6):
    TM: {TM116}
    Domain: BB(11, 6) (11 states, 6 symbols)
    Previous best dominated bounds: BB(10, 6) > f_{{ω^2+3}}(7), BB(11, 4) > f_{{ω^2+1}}, BB(10, 5) > f_{{ω^2+2}}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+4}}(8)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB11_6

{gen_lean_tm('bb116', TM116)}

theorem bb116_core : Fwp2_HCore bb116 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_J4 (n : Nat) (L R : List Nat) :
    Reaches bb116 (mkCfgR (some 9) (rep n 4 L) (4 :: R))
                  (mkCfgR (some 9) L (4 :: rep n 4 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb116 _
  | succ k ih =>
    have h1 : step bb116 (mkCfgR (some 9) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 9) (rep k 4 L) (4 :: 4 :: R)) :=
      step_mkCfgR_L_cons (tm := bb116) (q := 9) (w := 3) (cur := 4) rfl
    have h2 := ih (4 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb116 k _ _ _ h1 h2

theorem rule_54 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have ha : step bb116 (Scfg (r + 1) 0 m (5 :: 4 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (4 :: R)) :=
    step_mkCfgR_R (tm := bb116) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb116 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (4 :: R)) =
            some (mkCfgR (some 10) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 8) (w := 4) (cur := 4) rfl
  have hc : step bb116 (mkCfgR (some 10) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) =
            some (mkCfgR (some 10) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 10) (w := 1) (cur := 2) rfl
  have hd : step bb116 (mkCfgR (some 10) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) =
            some (mkCfgR (some 10) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 10) (w := 1) (cur := 2) rfl
  have he := loop_L3 (tm := bb116) (q := 10) (w' := 1) rfl (2 * m) (rep (r + 1) 5 []) (2 :: 2 :: 5 :: R)
  rw [rep_snoc_one, rep_snoc_one] at he
  have hf : step bb116 (mkCfgR (some 10) (5 :: rep r 5 []) (3 :: rep (2 * m + 2) 2 (5 :: R))) =
            some (mkCfgR (some 10) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 10) (w := 1) (cur := 3) rfl
  have hg : step bb116 (mkCfgR (some 10) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_R (tm := bb116) (q := 10) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he2, hme, hte⟩ := exec_G2_2s bb116_core r m hm (5 :: R)
  have hpre := reaches_trans
    (steps_succ bb116 _ _ _ _ ha (steps_succ bb116 _ _ _ _ hb
      (steps_succ bb116 _ _ _ _ hc (steps_succ bb116 _ _ _ _ hd he))))
    (steps_succ bb116 _ _ _ _ hf (steps_one bb116 _ _ hg))
  exact ⟨r' + 1, m', _, reaches_trans hpre he2, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

def H51 (m : Nat) : Nat := iter H_plus2 (2 * m + 1) 1
def H52 (m : Nat) : Nat := iter H51 (2 * m + 1) 1

theorem H51_mono {{x y : Nat}} (hxy : x ≤ y) : H51 x ≤ H51 y :=
  iter_mono_steps H_plus2 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H_plus2_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H51_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H51 m :=
  climb_2m_plus_1 H_plus2 (f_omega2_plus 1) 1 (by omega) (fun _ _ h => H_plus2_mono h) H_plus2_inc H_plus2_gt
    (fOmega2_props 1 0 1) m hm

theorem H51_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H51 m := by
  have h1 := H51_gt m hm; have h2 : m ≤ f_omega2_plus 2 m := (fOmega2_props 1 0 2).ge_self m; omega

theorem H51_ge_17 (m : Nat) : 17 ≤ H51 m :=
  iter_H_ge_17 H_plus2 (2 * m + 1) 1 (by omega) (by omega) H_plus2_inc (fun z _ => H_plus2_ge_17 z)

theorem H52_mono {{x y : Nat}} (hxy : x ≤ y) : H52 x ≤ H52 y :=
  iter_mono_steps H51 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H51_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H52_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 3 m < H52 m :=
  climb_2m_plus_1 H51 (f_omega2_plus 2) 1 (by omega) (fun _ _ h => H51_mono h) H51_inc H51_gt
    (fOmega2_props 1 0 2) m hm

theorem reload_51 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 1 :: R))
                       (Scfg (r + 1) 0 (Pempty r) (5 :: rep (2 * m + 1) 4 R)) t := by
  have ha : step bb116 (Scfg (r + 1) 0 m (5 :: 1 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) :=
    step_mkCfgR_R (tm := bb116) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb116 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) =
            some (mkCfgR (some 7) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 8) (w := 3) (cur := 1) rfl
  have hc : step bb116 (mkCfgR (some 7) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 4 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 1 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 7) (w := 0) (cur := 2) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb116_core r m 1 (4 :: R)
  have hd : step bb116 (mkCfgR (some 6) (rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (1 :: 4 :: R)) =
            some (mkCfgR (some 6) (4 :: rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: R)) :=
    step_mkCfgR_R (tm := bb116) (q := 6) (w := 3) (cur := 1) rfl
  have he : step bb116 (mkCfgR (some 6) (4 :: rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: R)) =
            some (mkCfgR (some 9) (rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 6) (w := 3) (cur := 4) rfl
  have hf := loop_J4 (2 * m + 2) (rep (r + 1) 5 []) (4 :: R)
  rw [rep_snoc_one] at hf
  have hg : step bb116 (mkCfgR (some 9) (5 :: rep r 5 []) (4 :: rep (2 * m + 3) 4 R)) =
            some (mkCfgR (some 9) (rep r 5 []) (5 :: rep (2 * m + 4) 4 R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 9) (w := 3) (cur := 4) rfl
  have hh : step bb116 (mkCfgR (some 9) (rep r 5 []) (5 :: rep (2 * m + 4) 4 R)) =
            some (mkCfgR (some 7) (rep (r + 1) 5 []) (rep (2 * m + 4) 4 R)) :=
    step_mkCfgR_R (tm := bb116) (q := 9) (w := 4) (cur := 5) rfl
  have hsplit : rep (2 * m + 4) 4 R = 4 :: 4 :: 4 :: rep (2 * m + 1) 4 R := by
    have heq : 2 * m + 4 = (2 * m + 1) + 3 := by omega
    rw [heq]; rfl
  rw [hsplit] at hh
  have hi : Reaches bb116
      (mkCfgR (some 7) (rep (r + 1) 5 []) (4 :: 4 :: 4 :: rep (2 * m + 1) 4 R))
      (mkCfgR (some 0) (2 :: rep (r + 1) 5 []) (1 :: 5 :: rep (2 * m + 1) 4 R)) 5 := by
    refine steps_succ bb116 4 _ _ _ (step_mkCfgR_R (tm := bb116) (q := 7) (w := 2) (cur := 4) rfl) ?_
    refine steps_succ bb116 3 _ _ _ (step_mkCfgR_R (tm := bb116) (q := 3) (w := 1) (cur := 4) rfl) ?_
    refine steps_succ bb116 2 _ _ _ (step_mkCfgR_L_cons (tm := bb116) (q := 5) (w := 4) (cur := 4) rfl) ?_
    refine steps_succ bb116 1 _ _ _ (step_mkCfgR_L_cons (tm := bb116) (q := 5) (w := 0) (cur := 2) rfl) ?_
    exact steps_one bb116 _ _ (step_mkCfgR_R (tm := bb116) (q := 0) (w := 1) (cur := 3) rfl)
  obtain ⟨te, hempty, _⟩ := fwp2_empty3 bb116_core.fp r (5 :: rep (2 * m + 1) 4 R)
  have hp1 := steps_succ bb116 _ _ _ _ ha (steps_succ bb116 _ _ _ _ hb (steps_succ bb116 _ _ _ _ hc
    (reaches_trans hs (steps_succ bb116 _ _ _ _ hd (steps_succ bb116 _ _ _ _ he hf)))))
  have hp2 := steps_succ bb116 _ _ _ _ hg (steps_succ bb116 _ _ _ _ hh (reaches_trans hi hempty))
  exact ⟨_, reaches_trans hp1 hp2⟩

theorem rule_51 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51 r m R
  have hpe : 1 ≤ Pempty r := Nat.le_trans (by omega : 1 ≤ r + 2) (Pempty_ge r)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 1 4 H_plus2
    (fun _ _ h => H_plus2_mono h) (fun z _ => Nat.le_trans (by omega : 1 ≤ 17) (H_plus2_ge_17 z))
    rule_54 (2 * m + 1) r (Pempty r) R hpe
  have harg : H51 m ≤ iter H_plus2 (2 * m + 1) (Pempty r) :=
    iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem reload_52 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 2 :: R))
                       (Scfg (r + 1) 0 (Pempty r) (5 :: rep (2 * m + 1) 1 R)) t := by
  have ha : step bb116 (Scfg (r + 1) 0 m (5 :: 2 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: R)) :=
    step_mkCfgR_R (tm := bb116) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb116 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: R)) =
            some (mkCfgR (some 9) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 8) (w := 0) (cur := 2) rfl
  have hc : step bb116 (mkCfgR (some 9) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 1 :: R)) =
            some (mkCfgR (some 9) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 1 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 9) (w := 0) (cur := 2) rfl
  have hd : step bb116 (mkCfgR (some 9) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 1 :: 1 :: R)) =
            some (mkCfgR (some 9) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 1 :: 1 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 9) (w := 0) (cur := 2) rfl
  have he := loop_L3 (tm := bb116) (q := 9) (w' := 0) rfl (2 * m) (rep (r + 1) 5 []) (1 :: 1 :: 1 :: R)
  rw [rep_snoc_one, rep_snoc_one, rep_snoc_one] at he
  have hf : step bb116 (mkCfgR (some 9) (5 :: rep r 5 []) (3 :: rep (2 * m + 3) 1 R)) =
            some (mkCfgR (some 9) (rep r 5 []) (5 :: rep (2 * m + 4) 1 R)) :=
    step_mkCfgR_L_cons (tm := bb116) (q := 9) (w := 0) (cur := 3) rfl
  have hg : step bb116 (mkCfgR (some 9) (rep r 5 []) (5 :: rep (2 * m + 4) 1 R)) =
            some (mkCfgR (some 7) (rep (r + 1) 5 []) (rep (2 * m + 4) 1 R)) :=
    step_mkCfgR_R (tm := bb116) (q := 9) (w := 4) (cur := 5) rfl
  have hsplit : rep (2 * m + 4) 1 R = 1 :: 1 :: 1 :: rep (2 * m + 1) 1 R := by
    have heq : 2 * m + 4 = (2 * m + 1) + 3 := by omega
    rw [heq]; rfl
  rw [hsplit] at hg
  have hh : Reaches bb116
      (mkCfgR (some 7) (rep (r + 1) 5 []) (1 :: 1 :: 1 :: rep (2 * m + 1) 1 R))
      (mkCfgR (some 0) (2 :: rep (r + 1) 5 []) (1 :: 5 :: rep (2 * m + 1) 1 R)) 3 := by
    refine steps_succ bb116 2 _ _ _ (step_mkCfgR_R (tm := bb116) (q := 7) (w := 1) (cur := 1) rfl) ?_
    refine steps_succ bb116 1 _ _ _ (step_mkCfgR_R (tm := bb116) (q := 5) (w := 0) (cur := 1) rfl) ?_
    exact steps_one bb116 _ _ (step_mkCfgR_L_cons (tm := bb116) (q := 9) (w := 4) (cur := 1) rfl)
  obtain ⟨te, hempty, _⟩ := fwp2_empty3 bb116_core.fp r (5 :: rep (2 * m + 1) 1 R)
  have hp1 := steps_succ bb116 _ _ _ _ ha (steps_succ bb116 _ _ _ _ hb
    (steps_succ bb116 _ _ _ _ hc (steps_succ bb116 _ _ _ _ hd he)))
  have hp2 := steps_succ bb116 _ _ _ _ hf (steps_succ bb116 _ _ _ _ hg (reaches_trans hh hempty))
  exact ⟨_, reaches_trans hp1 hp2⟩

theorem rule_52 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 2 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H52 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_52 r m R
  have hpe : 1 ≤ Pempty r := Nat.le_trans (by omega : 1 ≤ r + 2) (Pempty_ge r)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 1 1 H51
    (fun _ _ h => H51_mono h) rule_51 (2 * m + 1) r (Pempty r) R
  have harg : H52 m ≤ iter H51 (2 * m + 1) (Pempty r) :=
    iter_mono_arg H51 (fun _ _ h => H51_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb116_bootstrap :
    Reaches bb116 initConfig (Scfg 1 0 1 (5 :: 1 :: rep 8 2 [])) 83 := rfl

theorem bb116_halts_gt_f_omega2_plus_4_8 :
    ValidTM 11 6 bb116 ∧ ∃ t, HaltsIn bb116 initConfig t ∧ f_omega2_plus 4 8 < t := by
  refine ⟨bb116_valid, ?_⟩
  have hboot := bb116_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_51 0 1 (rep 8 2 [])
  have hm1_8 : 8 ≤ m1 := Nat.le_trans (by omega : 8 ≤ 17) (Nat.le_trans (H51_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 1 2 H52
    (fun _ _ h => H52_mono h) rule_52 8 r1 m1 []
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb116) (mark' := 1) rfl rfl (r2 + 1) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 4 8 < iter H52 8 8 :=
    iter_strict_dom H52 (f_omega2_plus 3) 1 H52_gt (fOmega2_props 1 0 3) 8 8 (by omega) (by omega)
  have hlt2 : iter H52 8 8 ≤ iter H52 8 m1 := iter_mono_arg H52 (fun _ _ h => H52_mono h) 8 hm1_8
  have hlt_m2 : f_omega2_plus 4 8 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb116_halts_gt_f_omega2_plus_4_8

end BB11_6
end BB
"""

bb116_v = f"""(*
  rocq/BB11_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(11, 6):
    TM: {TM116}
    Domain: BB(11, 6) (11 states, 6 symbols)
    Previous best dominated bounds: BB(10, 6) > f_{{ω^2+3}}(7), BB(11, 4) > f_{{ω^2+1}}, BB(10, 5) > f_{{ω^2+2}}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+4}}(8)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

{gen_rocq_tm('bb116', TM116)}

Lemma bb116_core : Fwp2_HCore bb116.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_J4 : forall n L R,
  Reaches bb116 (mkCfgR (Some 9) (rep n 4 L) (4 :: R))
                (mkCfgR (Some 9) L (4 :: rep n 4 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 9 3 4 4 _ _ R eq_refl) |].
  specialize (IH L (4 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rule_54 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\\
    H_plus2 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (exec_G2_2s bb116 bb116_core r m (5 :: R) Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists (S r'), m'. eexists. split.
  - eapply reaches_trans; [| replace (S r' + 1) with (S (S r')) by lia; exact He].
    eapply reaches_trans.
    + replace (r + 1) with (S r) by lia. unfold Scfg.
      eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 5 _ eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 4 2 4 _ _ R eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 10 1 2 2 _ _ _ eq_refl) |].
      replace (2 * m + 1) with (S (2 * m)) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 10 1 3 2 _ _ _ eq_refl) |].
      apply (loop_L3 bb116 10 1 (2 * m) (rep (S r) 5 []) (2 :: 2 :: 5 :: R) eq_refl).
    + rewrite rep_snoc_one, rep_snoc_one.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 10 1 5 3 _ _ _ eq_refl) |].
      replace (2 :: 2 :: 2 :: rep (2 * m) 2 (5 :: R)) with (rep (2 * m + 3) 2 (5 :: R))
        by (replace (2 * m + 3) with (S (S (S (2 * m)))) by lia; reflexivity).
      apply steps_one. apply (step_mkCfgR_R _ 10 4 _ _ 5 _ eq_refl).
  - split; [exact Hme | lia].
Qed.

Definition H51 (m : nat) : nat := iter H_plus2 (2 * m + 1) 1.
Definition H52 (m : nat) : nat := iter H51 (2 * m + 1) 1.

Lemma H51_mono : forall x y, x <= y -> H51 x <= H51 y.
Proof.
  intros x y Hxy. unfold H51.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H_plus2_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H51_gt : forall m, 1 <= m -> f_omega2_plus 2 m < H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (climb_2m_plus_1 H_plus2 (f_omega2_plus 1) 1 ltac:(lia) H_plus2_mono H_plus2_inc H_plus2_gt (fOmega2_props 1 0 1) m Hm).
Qed.

Lemma H51_inc : forall m, 1 <= m -> S m <= H51 m.
Proof.
  intros m Hm. pose proof (H51_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 2) m).
  change (f_omega2_plus 2 m) with (fOmega2 1 0 2 m) in *. lia.
Qed.

Lemma H51_ge_17 : forall m, 17 <= H51 m.
Proof.
  intro m. unfold H51.
  apply (iter_H_ge_17 H_plus2 (2 * m + 1) 1 ltac:(lia) ltac:(lia) H_plus2_inc (fun z _ => H_plus2_ge_17 z)).
Qed.

Lemma H52_mono : forall x y, x <= y -> H52 x <= H52 y.
Proof.
  intros x y Hxy. unfold H52.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H51_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H52_gt : forall m, 1 <= m -> f_omega2_plus 3 m < H52 m.
Proof.
  intros m Hm. unfold H52.
  apply (climb_2m_plus_1 H51 (f_omega2_plus 2) 1 ltac:(lia) H51_mono H51_inc H51_gt (fOmega2_props 1 0 2) m Hm).
Qed.

Lemma reload_51 : forall r m R,
  exists t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 1 :: R))
                          (Scfg (r + 1) 0 (Pempty r) (5 :: rep (2 * m + 1) 4 R)) t.
Proof.
  intros r m R.
  destruct (sweep_HG bb116 bb116_core r m 1 (4 :: R)) as [ts Hs].
  destruct (fwp2_empty3 bb116 (fh_fp _ bb116_core) r (5 :: rep (2 * m + 1) 4 R)) as [te [Hempty _]].
  eexists. replace (r + 1) with (S r) by lia.
  eapply reaches_trans; [| exact Hempty].
  eapply reaches_trans.
  - unfold Scfg.
    eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 5 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 3 2 1 _ _ R eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 0 2 2 _ _ _ eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 6 3 _ _ 1 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 3 4 4 _ _ R eq_refl) |].
    apply (loop_J4 (2 * m + 2) (rep (S r) 5 []) (4 :: R)).
  - rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 9 3 5 4 _ _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 9 4 _ _ 5 _ eq_refl) |].
    replace (4 :: 4 :: rep (2 * m + 2) 4 R) with (4 :: 4 :: 4 :: rep (2 * m + 1) 4 R)
      by (replace (2 * m + 2) with (S (2 * m + 1)) by lia; reflexivity).
    eapply steps_succ; [apply (step_mkCfgR_R _ 7 2 _ _ 4 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 1 _ _ 4 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 4 2 4 _ _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 2 _ _ _ eq_refl) |].
    apply steps_one. apply (step_mkCfgR_R _ 0 1 _ _ 3 _ eq_refl).
Qed.

Lemma rule_51 : forall r m R,
  exists r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\\
    H51 m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_51 r m R) as [t0 H0].
  assert (Hpe : 1 <= Pempty r) by (pose proof (Pempty_ge r); lia).
  assert (Hpos : forall x, 1 <= x -> 1 <= H_plus2 x) by (intros x _; pose proof (H_plus2_ge_17 x); lia).
  destruct (iter_cursor_rep bb116 1 4 H_plus2 H_plus2_mono Hpos rule_54 (2 * m + 1) r (Pempty r) R Hpe)
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split].
  - unfold H51. eapply Nat.le_trans; [apply iter_mono_arg; [apply H_plus2_mono | exact Hpe] | exact Hm2].
  - pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma reload_52 : forall r m R,
  exists t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 2 :: R))
                          (Scfg (r + 1) 0 (Pempty r) (5 :: rep (2 * m + 1) 1 R)) t.
Proof.
  intros r m R.
  destruct (fwp2_empty3 bb116 (fh_fp _ bb116_core) r (5 :: rep (2 * m + 1) 1 R)) as [te [Hempty _]].
  eexists. replace (r + 1) with (S r) by lia.
  eapply reaches_trans; [| exact Hempty].
  eapply reaches_trans.
  - unfold Scfg.
    eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 5 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 0 2 2 _ _ R eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 9 0 2 2 _ _ _ eq_refl) |].
    replace (2 * m + 1) with (S (2 * m)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 9 0 3 2 _ _ _ eq_refl) |].
    apply (loop_L3 bb116 9 0 (2 * m) (rep (S r) 5 []) (1 :: 1 :: 1 :: R) eq_refl).
  - rewrite rep_snoc_one, rep_snoc_one, rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 9 0 5 3 _ _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 9 4 _ _ 5 _ eq_refl) |].
    change (1 :: 1 :: 1 :: 1 :: rep (2 * m) 1 R) with (1 :: 1 :: 1 :: rep (S (2 * m)) 1 R).
    replace (S (2 * m)) with (2 * m + 1) by lia.
    eapply steps_succ; [apply (step_mkCfgR_R _ 7 1 _ _ 1 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 0 _ _ 1 _ eq_refl) |].
    apply steps_one. apply (step_mkCfgR_L_cons _ 9 4 1 1 _ _ _ eq_refl).
Qed.

Lemma rule_52 : forall r m R,
  exists r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 2 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\\
    H52 m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_52 r m R) as [t0 H0].
  assert (Hpe : 1 <= Pempty r) by (pose proof (Pempty_ge r); lia).
  destruct (iter_cursor_rep0 bb116 1 1 H51 H51_mono rule_51 (2 * m + 1) r (Pempty r) R)
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split].
  - unfold H52. eapply Nat.le_trans; [apply iter_mono_arg; [apply H51_mono | exact Hpe] | exact Hm2].
  - pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb116_bootstrap :
  Reaches bb116 initConfig (Scfg 1 0 1 (5 :: 1 :: rep 8 2 [])) 83.
Proof. vm_compute. reflexivity. Qed.

Theorem bb116_halts_gt_f_omega2_plus_4_8 :
  ValidTM 11 6 bb116 /\\ exists t, HaltsIn bb116 initConfig t /\\ f_omega2_plus 4 8 < t.
Proof.
  split; [exact bb116_valid |].
  pose proof bb116_bootstrap as Hboot.
  destruct (rule_51 0 1 (rep 8 2 [])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_8 : 8 <= m1) by (pose proof (H51_ge_17 1); lia).
  destruct (iter_cursor_rep0 bb116 1 2 H52 H52_mono rule_52 8 r1 m1 [])
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (halt_cursor_5 bb116 1 (r2 + 1) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom H52 (f_omega2_plus 3) 1 H52_gt (fOmega2_props 1 0 3) 8 8 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H52 H52_mono 8 8 m1 Hm1_8) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 4 8) with (iter (f_omega2_plus 3) 8 8). lia.
Qed.

Print Assumptions bb116_halts_gt_f_omega2_plus_4_8.
"""

for path, content in [
    ('lean/BB/BB9_6.lean',  bb96_lean),
    ('rocq/BB9_6.v',        bb96_v),
    ('lean/BB/BB10_6.lean', bb106_lean),
    ('rocq/BB10_6.v',       bb106_v),
    ('lean/BB/BB11_6.lean', bb116_lean),
    ('rocq/BB11_6.v',       bb116_v),
]:
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    print(f"Wrote {path}")
