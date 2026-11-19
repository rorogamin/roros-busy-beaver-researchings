(*
  rocq/BB9_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(9, 6):
    TM: 4LH3LB2LH2RA4LB2RI_4LA3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC5LC3RD_5RB3RE4RG4LC3LG5LE_5RB5RB1RH1LF5LF5LF_5LF4RG1LB1LG2RG5LG_1LC1RD1LH1LH5RC5RG_1RZ5LI2LI2LI1LB5RG
    Domain: BB(9, 6) (9 states, 6 symbols)
    Previous best dominated bounds: BB(8, 6) > f_{ω^2+1}(f_ω(31)), BB(9, 5) > f_{ω^2+1}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+2}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

Definition bb96 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 4LH 3LB 2LH 2RA 4LB 2RI *)
  | 0, 0 => Some (mkAction 4 DL (Some 7))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 2 DR (Some 8))
  (* State B (1): 4LA 3RB 1LD 2RA 3LF 5RB *)
  | 1, 0 => Some (mkAction 4 DL (Some 0))
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
  (* State D (3): 3RB 3RE 3LC 2RC 5LC 3RD *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 5 DL (Some 2))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  (* State E (4): 5RB 3RE 4RG 4LC 3LG 5LE *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 4 DR (Some 6))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  (* State F (5): 5RB 5RB 1RH 1LF 5LF 5LF *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 1 DR (Some 7))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  (* State G (6): 5LF 4RG 1LB 1LG 2RG 5LG *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 2 DR (Some 6))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  (* State H (7): 1LC 1RD 1LH 1LH 5RC 5RG *)
  | 7, 0 => Some (mkAction 1 DL (Some 2))
  | 7, 1 => Some (mkAction 1 DR (Some 3))
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 5 DR (Some 2))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  (* State I (8): 1RZ 5LI 2LI 2LI 1LB 5RG *)
  | 8, 0 => Some (mkAction 1 DR None)
  | 8, 1 => Some (mkAction 5 DL (Some 8))
  | 8, 2 => Some (mkAction 2 DL (Some 8))
  | 8, 3 => Some (mkAction 2 DL (Some 8))
  | 8, 4 => Some (mkAction 1 DL (Some 1))
  | 8, 5 => Some (mkAction 5 DR (Some 6))
  | _, _ => None
  end.

Lemma bb96_valid : ValidTM 9 6 bb96.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 9 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 9 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb96_core : Fwp2_HCore bb96.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Lemma rule_51 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb96 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H_plus2 m <= m' /\ m' <= t.
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
  ValidTM 9 6 bb96 /\ exists t, HaltsIn bb96 initConfig t /\ f_omega2_plus 2 7 < t.
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
