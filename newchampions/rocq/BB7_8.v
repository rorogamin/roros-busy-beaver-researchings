(*
  rocq/BB7_8.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 8):
    TM: 7LD3LB6LA2RA4LB5RC5LA2LG_1RZ3RB1LD2RA3LF5RB6LD4RG_3RB1LB3LC2RC4LC1LE5RB3RF_3RB3RE3LC2RC7RB3RD1LA7LD_5RB3RE7RD4LC3LG5LE0LA1LG_5RB5RB2RA1LF2LA5LF5RD7LF_5LF3LA7LA1LG7LA5LG7RD0RG
    Domain: BB(7, 8) (7 states, 8 symbols)
    Previous best dominated bounds: BB(7, 7) > f_{ω^2+1}(3), BB(6, 8) > f_{ω×2+2}(11)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+2}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_7.
Import ListNotations.

Definition bb78 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 7LD 3LB 6LA 2RA 4LB 5RC 5LA 2LG *)
  | 0, 0 => Some (mkAction 7 DL (Some 3))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 6 DL (Some 0))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 5 DR (Some 2))
  | 0, 6 => Some (mkAction 5 DL (Some 0))
  | 0, 7 => Some (mkAction 2 DL (Some 6))
  (* State B (1): 1RZ 3RB 1LD 2RA 3LF 5RB 6LD 4RG *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  | 1, 6 => Some (mkAction 6 DL (Some 3))
  | 1, 7 => Some (mkAction 4 DR (Some 6))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 5RB 3RF *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  | 2, 6 => Some (mkAction 5 DR (Some 1))
  | 2, 7 => Some (mkAction 3 DR (Some 5))
  (* State D (3): 3RB 3RE 3LC 2RC 7RB 3RD 1LA 7LD *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 7 DR (Some 1))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  | 3, 6 => Some (mkAction 1 DL (Some 0))
  | 3, 7 => Some (mkAction 7 DL (Some 3))
  (* State E (4): 5RB 3RE 7RD 4LC 3LG 5LE 0LA 1LG *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 7 DR (Some 3))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 6 => Some (mkAction 0 DL (Some 0))
  | 4, 7 => Some (mkAction 1 DL (Some 6))
  (* State F (5): 5RB 5RB 2RA 1LF 2LA 5LF 5RD 7LF *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 2 DR (Some 0))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 2 DL (Some 0))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 5 DR (Some 3))
  | 5, 7 => Some (mkAction 7 DL (Some 5))
  (* State G (6): 5LF 3LA 7LA 1LG 7LA 5LG 7RD 0RG *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 3 DL (Some 0))
  | 6, 2 => Some (mkAction 7 DL (Some 0))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 7 DL (Some 0))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 7 DR (Some 3))
  | 6, 7 => Some (mkAction 0 DR (Some 6))
  | _, _ => None
  end.

Lemma bb78_valid : ValidTM 7 8 bb78.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 7 (destruct s as [| s]; [
      do 8 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 7 (destruct s as [| s]; [
      do 8 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

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
  exists r' m' t, Reaches bb78 (Scfg (S r) 0 m (7 :: R)) (Scfg (S r') 0 m' R) t /\
    H7 m <= m' /\ m' <= t.
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
  exists r' m' t, Reaches bb78 (Scfg (S r) 0 m (rep n 7 R)) (Scfg (S r') 0 m' R) t /\
    iter H7 n m <= m' /\ (1 <= n -> m' <= t).
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
  ValidTM 7 8 bb78 /\ exists t, HaltsIn bb78 initConfig t /\ f_omega2_plus 2 7 < t.
Proof.
  split; [exact bb78_valid |].
  pose proof bb78_bootstrap as Hboot.
  destruct (rule_7 0 0 (2 :: rep 7 7 [2; 1; 5])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  destruct (rule_2_7 bb78 bb78_core r1 m1 (rep 7 7 [2; 1; 5])) as [r2 [m2 [t2 [H2s [Hm2 _]]]]].
  assert (Hm2_7 : 7 <= m2).
  { change (H7 0) with 17 in Hm1. unfold H2_7 in Hm2. pose proof (Pempty_ge (2 * m1 + 1)). lia. }
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
