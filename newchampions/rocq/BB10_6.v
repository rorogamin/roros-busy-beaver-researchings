(*
  rocq/BB10_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(10, 6):
    TM: 1LJ3LB2LH2RA4LB2RI_1LA3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC2RF3RD_5RB3RE4RG4LC3LG5LE_5RB5RB1LA1LF5LF5LF_5LF4RG1LB1LG4LJ5LG_1RJ3LD1LH1LH3RD5RG_1RZ4LH2LI2LI5LI5RG_1RD1RI0LB3RB4LJ5RH
    Domain: BB(10, 6) (10 states, 6 symbols)
    Previous best dominated bounds: BB(9, 6) > f_{ω^2+2}(7), BB(10, 5) > f_{ω^2+2}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+3}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

Definition bb106 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 1LJ 3LB 2LH 2RA 4LB 2RI *)
  | 0, 0 => Some (mkAction 1 DL (Some 9))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 2 DR (Some 8))
  (* State B (1): 1LA 3RB 1LD 2RA 3LF 5RB *)
  | 1, 0 => Some (mkAction 1 DL (Some 0))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  (* State D (3): 3RB 3RE 3LC 2RC 2RF 3RD *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 2 DR (Some 5))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  (* State E (4): 5RB 3RE 4RG 4LC 3LG 5LE *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 4 DR (Some 6))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  (* State F (5): 5RB 5RB 1LA 1LF 5LF 5LF *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 1 DL (Some 0))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  (* State G (6): 5LF 4RG 1LB 1LG 4LJ 5LG *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 4 DL (Some 9))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  (* State H (7): 1RJ 3LD 1LH 1LH 3RD 5RG *)
  | 7, 0 => Some (mkAction 1 DR (Some 9))
  | 7, 1 => Some (mkAction 3 DL (Some 3))
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 3 DR (Some 3))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  (* State I (8): 1RZ 4LH 2LI 2LI 5LI 5RG *)
  | 8, 0 => Some (mkAction 1 DR None)
  | 8, 1 => Some (mkAction 4 DL (Some 7))
  | 8, 2 => Some (mkAction 2 DL (Some 8))
  | 8, 3 => Some (mkAction 2 DL (Some 8))
  | 8, 4 => Some (mkAction 5 DL (Some 8))
  | 8, 5 => Some (mkAction 5 DR (Some 6))
  (* State J (9): 1RD 1RI 0LB 3RB 4LJ 5RH *)
  | 9, 0 => Some (mkAction 1 DR (Some 3))
  | 9, 1 => Some (mkAction 1 DR (Some 8))
  | 9, 2 => Some (mkAction 0 DL (Some 1))
  | 9, 3 => Some (mkAction 3 DR (Some 1))
  | 9, 4 => Some (mkAction 4 DL (Some 9))
  | 9, 5 => Some (mkAction 5 DR (Some 7))
  | _, _ => None
  end.

Lemma bb106_valid : ValidTM 10 6 bb106.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 10 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 10 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

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
  exists r' m' t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H_plus2 m <= m' /\ m' <= t.
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
  exists r' m' t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H51 m <= m' /\ m' <= t.
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
  ValidTM 10 6 bb106 /\ exists t, HaltsIn bb106 initConfig t /\ f_omega2_plus 3 7 < t.
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
