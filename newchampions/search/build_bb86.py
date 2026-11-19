"""Verify and generate exact, axiom-free Lean 4 & Rocq 9.1 proofs for BB(8, 6) > f_{ω^2+2}(4)."""
from search.sim import parse_tm, run, fmt_cfg, mk_cfg
from search.gen_tm import gen_lean_tm, gen_rocq_tm

TM86 = '2LF3LB2LH2RA4LB4LH_1RH3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC1RZ3RD_5RB3RE4RG4LC3LG5LE_5RB5RE1RZ1LF5LF5LF_5LF4RG1LB1LG2LH5LG_1RA1RZ1LH1LH2LH5RG'

ns, ms, tab = parse_tm(TM86)
assert (ns, ms) == (8, 6)
t, tp, p, s = run(tab, {}, 0, 0, 41)
assert t == 41 and fmt_cfg(tp, p, s) == '53332 A> 55555', fmt_cfg(tp, p, s)
# Verify halt on blank right tape from Scfg r 0 m []
tp2, p2, s2 = mk_cfg('53332', '', 0)
th, tp3, p3, s3 = run(tab, tp2, p2, s2, 10)
assert th == 2 and s3 is None, (th, s3)
print("BB(8, 6) Python check PASSED! boot@41: 53332 A> 55555, halt in 2 steps.")

bb86_lean = f"""/-
  BB/BB8_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(8, 6):
    TM: {TM86}
    Domain: BB(8, 6) (8 states, 6 symbols)
    Previous wiki champion: BB(8, 6) > f_{{ω^2+1}}(f_ω(31)) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+2}}(4)
    (strictly beats previous BB(8, 6) by a full FGH ordinal level, and strictly < our BB(9, 6) & BB(8, 7))
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H

namespace BB
namespace BB8_6

{gen_lean_tm('bb86', TM86)}

theorem bb86_core : Fwp2_HCore bb86 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_H4 (n : Nat) (L R : List Nat) :
    Reaches bb86 (mkCfgR (some 7) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 7) L (4 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb86 _
  | succ k ih =>
    have h1 : step bb86 (mkCfgR (some 7) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 7) (rep k 4 L) (4 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb86) (q := 7) (w := 1) (cur := 4) rfl
    have h2 := ih (2 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb86 k _ _ _ h1 h2

theorem rule_5 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb86 (Scfg (r + 1) 0 m (5 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have h1 : step bb86 (Scfg (r + 1) 0 m (5 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb86) (q := 0) (w := 3) (cur := 5) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb86_core r m 4 R
  have h2 : step bb86 (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb86) (q := 6) (w := 1) (cur := 4) rfl
  have h3 := loop_H4 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb86 (mkCfgR (some 7) (5 :: rep r 5 []) (4 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb86) (q := 7) (w := 1) (cur := 4) rfl
  have h5 : step bb86 (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_R (tm := bb86) (q := 7) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he, hme, hte⟩ := exec_G2_2s bb86_core r m hm R
  have hpre := steps_succ bb86 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb86 _ _ _ _ h2 (reaches_trans h3 (steps_succ bb86 _ _ _ _ h4 (steps_one bb86 _ _ h5)))))
  exact ⟨r', m', _, reaches_trans hpre he, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

theorem rule_5_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb86 (Scfg (r + 1) 0 m (rep n 5 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H_plus2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb86 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_5 r m hm R
      exact ⟨r1 + 1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5 r m hm (rep (p' + 1) 5 R)
      have hm1p : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H_plus2_ge_17 m) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih (r1 + 1) m1 R hm1p
      have hcomm : iter H_plus2 (p' + 1) (H_plus2 m) = iter H_plus2 (p' + 2) m :=
        (iter_add H_plus2 (p' + 1) 1 m).symm
      have hmb : iter H_plus2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem bb86_bootstrap :
    Reaches bb86 initConfig (Scfg 1 0 1 (rep 5 5 [])) 41 := rfl

theorem bb86_halts_gt_f_omega2_plus_2_4 :
    ValidTM 8 6 bb86 ∧ ∃ t, HaltsIn bb86 initConfig t ∧ f_omega2_plus 2 4 < t := by
  refine ⟨bb86_valid, ?_⟩
  have hboot := bb86_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5 0 1 (by omega) (rep 4 5 [])
  have hm1_4 : 4 ≤ m1 := Nat.le_trans (by omega : 4 ≤ 17) (Nat.le_trans (H_plus2_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_5_rep 4 (r1 + 1) m1 [] (by omega)
  have hh1 : step bb86 (Scfg (r2 + 1) 0 m2 []) =
             some (mkCfgR (some 5) (rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2, 2]) := rfl
  have hh2 : step bb86 (mkCfgR (some 5) (rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2, 2]) =
             some (mkCfgR none (1 :: rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2]) :=
    step_mkCfgR_R (tm := bb86) (q := 5) (w := 0) (cur := 2) rfl
  have hhalt : Reaches bb86 (Scfg (r2 + 1) 0 m2 [])
      (mkCfgR none (1 :: rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2]) 2 :=
    steps_succ bb86 1 _ _ _ hh1 (steps_one bb86 _ _ hh2)
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 2 4 < iter H_plus2 4 4 :=
    iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 4 4 (by omega) (by omega)
  have hlt2 : iter H_plus2 4 4 ≤ iter H_plus2 4 m1 := iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) 4 hm1_4
  have hlt_m2 : f_omega2_plus 2 4 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb86_halts_gt_f_omega2_plus_2_4

end BB8_6
end BB
"""

bb86_v = f"""(*
  rocq/BB8_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(8, 6):
    TM: {TM86}
    Domain: BB(8, 6) (8 states, 6 symbols)
    Previous wiki champion: BB(8, 6) > f_{{ω^2+1}}(f_ω(31)) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+2}}(4)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H.
Import ListNotations.

{gen_rocq_tm('bb86', TM86)}

Lemma bb86_core : Fwp2_HCore bb86.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_H4 : forall n L R,
  Reaches bb86 (mkCfgR (Some 7) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 7) L (4 :: rep n 2 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 4 4 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rule_5 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb86 (Scfg (S r) 0 m (5 :: R)) (Scfg (S (S r')) 0 m' R) t /\\
    H_plus2 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (sweep_HG bb86 bb86_core r m 4 R) as [ts Hs].
  destruct (exec_G2_2s bb86 bb86_core r m R Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists r', m'. eexists. split.
  - eapply reaches_trans; [| exact He].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 3 2 5 _ _ R eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 1 4 4 _ _ R eq_refl) |].
    eapply reaches_trans; [apply (loop_H4 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
    rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 5 4 _ _ _ eq_refl) |].
    replace (2 :: 2 :: rep (2 * m + 1) 2 R) with (rep (2 * m + 3) 2 R)
      by (replace (2 * m + 3) with (S (S (2 * m + 1))) by lia; reflexivity).
    apply steps_one. apply (step_mkCfgR_R _ 7 4 _ _ 5 _ eq_refl).
  - split; [exact Hme | lia].
Qed.

Lemma rule_5_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb86 (Scfg (S r) 0 m (rep n 5 R)) (Scfg (S r') 0 m' R) t /\\
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

Lemma bb86_bootstrap :
  Reaches bb86 initConfig (Scfg 1 0 1 (rep 5 5 [])) 41.
Proof. vm_compute. reflexivity. Qed.

Theorem bb86_halts_gt_f_omega2_plus_2_4 :
  ValidTM 8 6 bb86 /\\ exists t, HaltsIn bb86 initConfig t /\\ f_omega2_plus 2 4 < t.
Proof.
  split; [exact bb86_valid |].
  pose proof bb86_bootstrap as Hboot.
  destruct (rule_5 0 1 (rep 4 5 []) ltac:(lia)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_4 : 4 <= m1) by (pose proof (H_plus2_ge_17 1); lia).
  destruct (rule_5_rep 4 (S r1) m1 [] ltac:(lia)) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  assert (Hh1 : step bb86 (Scfg (S r2) 0 m2 []) =
    Some (mkCfgR (Some 5) (rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [2; 2])).
  {{ unfold Scfg, mkCfgR, step. simpl. reflexivity. }}
  assert (Hh2 : step bb86 (mkCfgR (Some 5) (rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [2; 2]) =
    Some (mkCfgR None (1 :: rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [2])).
  {{ apply (step_mkCfgR_R _ 5 0 _ _ 2 [2] eq_refl). }}
  assert (Hhalt : Reaches bb86 (Scfg (S r2) 0 m2 [])
    (mkCfgR None (1 :: rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [2]) 2)
    by (eapply steps_succ; [exact Hh1 | apply steps_one; exact Hh2]).
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r) Hhalt) as Hreach.
  pose proof (iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 4 4 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H_plus2 H_plus2_mono 4 4 m1 Hm1_4) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (f_omega2_plus 2 4) with (iter (f_omega2_plus 1) 4 4). lia.
Qed.

Print Assumptions bb86_halts_gt_f_omega2_plus_2_4.
"""

with open('lean/BB/BB8_6.lean', 'w', encoding='utf-8') as f:
    f.write(bb86_lean)
with open('rocq/BB8_6.v', 'w', encoding='utf-8') as f:
    f.write(bb86_v)
print("Wrote lean/BB/BB8_6.lean and rocq/BB8_6.v")
