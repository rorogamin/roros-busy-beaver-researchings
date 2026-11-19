(*
  rocq/BB11_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(11, 6):
    TM: 2RK3LB2LH2RA4LB2RI_0LK3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC2RF3RD_5RB3RE4RG4LC3LG5LE_5RB1RJ1LA1LF5LF5LF_5LF4RG1LB1LG4LJ5LG_2LE2RF1LH1LH3RD5RG_1RZ4LH1LJ5LJ5LK0RC_3RB5LA1LJ1LJ4LJ5RH_1RH4RA2LK2LK0LD5RG
    Domain: BB(11, 6) (11 states, 6 symbols)
    Previous best dominated bounds: BB(10, 6) > f_{ω^2+3}(7), BB(11, 4) > f_{ω^2+1}, BB(10, 5) > f_{ω^2+2}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+4}(8)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

Definition bb116 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 2RK 3LB 2LH 2RA 4LB 2RI *)
  | 0, 0 => Some (mkAction 2 DR (Some 10))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 2 DR (Some 8))
  (* State B (1): 0LK 3RB 1LD 2RA 3LF 5RB *)
  | 1, 0 => Some (mkAction 0 DL (Some 10))
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
  (* State F (5): 5RB 1RJ 1LA 1LF 5LF 5LF *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 1 DR (Some 9))
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
  (* State H (7): 2LE 2RF 1LH 1LH 3RD 5RG *)
  | 7, 0 => Some (mkAction 2 DL (Some 4))
  | 7, 1 => Some (mkAction 2 DR (Some 5))
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 3 DR (Some 3))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  (* State I (8): 1RZ 4LH 1LJ 5LJ 5LK 0RC *)
  | 8, 0 => Some (mkAction 1 DR None)
  | 8, 1 => Some (mkAction 4 DL (Some 7))
  | 8, 2 => Some (mkAction 1 DL (Some 9))
  | 8, 3 => Some (mkAction 5 DL (Some 9))
  | 8, 4 => Some (mkAction 5 DL (Some 10))
  | 8, 5 => Some (mkAction 0 DR (Some 2))
  (* State J (9): 3RB 5LA 1LJ 1LJ 4LJ 5RH *)
  | 9, 0 => Some (mkAction 3 DR (Some 1))
  | 9, 1 => Some (mkAction 5 DL (Some 0))
  | 9, 2 => Some (mkAction 1 DL (Some 9))
  | 9, 3 => Some (mkAction 1 DL (Some 9))
  | 9, 4 => Some (mkAction 4 DL (Some 9))
  | 9, 5 => Some (mkAction 5 DR (Some 7))
  (* State K (10): 1RH 4RA 2LK 2LK 0LD 5RG *)
  | 10, 0 => Some (mkAction 1 DR (Some 7))
  | 10, 1 => Some (mkAction 4 DR (Some 0))
  | 10, 2 => Some (mkAction 2 DL (Some 10))
  | 10, 3 => Some (mkAction 2 DL (Some 10))
  | 10, 4 => Some (mkAction 0 DL (Some 3))
  | 10, 5 => Some (mkAction 5 DR (Some 6))
  | _, _ => None
  end.

Lemma bb116_valid : ValidTM 11 6 bb116.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 11 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 11 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

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
  exists r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H_plus2 m <= m' /\ m' <= t.
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
  exists r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H51 m <= m' /\ m' <= t.
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
  exists r' m' t, Reaches bb116 (Scfg (r + 1) 0 m (5 :: 2 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H52 m <= m' /\ m' <= t.
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
  ValidTM 11 6 bb116 /\ exists t, HaltsIn bb116 initConfig t /\ f_omega2_plus 4 8 < t.
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
