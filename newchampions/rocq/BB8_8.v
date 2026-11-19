(*
  rocq/BB8_8.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(8, 8):
    TM: 6LB3LB2LH2RA4LB1RZ6LH7LH_7RG3RB1LD2RA3LF5RB3RC7LC_3RB1LB3LC2RC4LC1LE2RA4RB_3RB3RE3LC2RC6LD3RD3RB7LG_5RB3RE4RG4LC3LG5LE1RZ7LD_5RB5RB0RD1LF5LF5LF2LG7LD_5LF4RG1LB1LG7RH5LG2LH6LD_7LA7LA1LH1LH2LH5RG1RZ7RF
    Domain: BB(8, 8) (8 states, 8 symbols)
    Previous best dominated bounds: BB(8, 7) > f_{ω^2+2}(8), BB(7, 8) > f_{ω^2+2}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+3}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H.
Import ListNotations.

Definition bb88 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 6LB 3LB 2LH 2RA 4LB 1RZ 6LH 7LH *)
  | 0, 0 => Some (mkAction 6 DL (Some 1))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 1 DR None)
  | 0, 6 => Some (mkAction 6 DL (Some 7))
  | 0, 7 => Some (mkAction 7 DL (Some 7))
  (* State B (1): 7RG 3RB 1LD 2RA 3LF 5RB 3RC 7LC *)
  | 1, 0 => Some (mkAction 7 DR (Some 6))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  | 1, 6 => Some (mkAction 3 DR (Some 2))
  | 1, 7 => Some (mkAction 7 DL (Some 2))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 2RA 4RB *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  | 2, 6 => Some (mkAction 2 DR (Some 0))
  | 2, 7 => Some (mkAction 4 DR (Some 1))
  (* State D (3): 3RB 3RE 3LC 2RC 6LD 3RD 3RB 7LG *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 6 DL (Some 3))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  | 3, 6 => Some (mkAction 3 DR (Some 1))
  | 3, 7 => Some (mkAction 7 DL (Some 6))
  (* State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 1RZ 7LD *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 4 DR (Some 6))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 6 => Some (mkAction 1 DR None)
  | 4, 7 => Some (mkAction 7 DL (Some 3))
  (* State F (5): 5RB 5RB 0RD 1LF 5LF 5LF 2LG 7LD *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 0 DR (Some 3))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 2 DL (Some 6))
  | 5, 7 => Some (mkAction 7 DL (Some 3))
  (* State G (6): 5LF 4RG 1LB 1LG 7RH 5LG 2LH 6LD *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 7 DR (Some 7))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 2 DL (Some 7))
  | 6, 7 => Some (mkAction 6 DL (Some 3))
  (* State H (7): 7LA 7LA 1LH 1LH 2LH 5RG 1RZ 7RF *)
  | 7, 0 => Some (mkAction 7 DL (Some 0))
  | 7, 1 => Some (mkAction 7 DL (Some 0))
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 2 DL (Some 7))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  | 7, 6 => Some (mkAction 1 DR None)
  | 7, 7 => Some (mkAction 7 DR (Some 5))
  | _, _ => None
  end.

Lemma bb88_valid : ValidTM 8 8 bb88.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 8 (destruct s as [| s]; [
      do 8 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 8 (destruct s as [| s]; [
      do 8 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

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
  exists r' m' t, Reaches bb88 (Scfg (S r) 0 m (6 :: R)) (Scfg (S (S r')) 0 m' R) t /\
    H_plus2 m <= m' /\ m' <= t.
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
  exists r' m' t, Reaches bb88 (Scfg (S r) 0 m (rep n 6 R)) (Scfg (S r') 0 m' R) t /\
    iter H_plus2 n m <= m' /\ (1 <= n -> m' <= t /\ 1 <= r').
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
  exists r' m' t, Reaches bb88 (Scfg (S (S r)) 0 m (7 :: R)) (Scfg (S (S r')) 0 m' R) t /\
    H7 m <= m' /\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_7 r m R) as [t0 H0].
  destruct (rule_6_rep (2 * m) r 1 R ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (Ht2 ltac:(lia)) as [Ht2_le Hr2_pos].
  destruct r2 as [| r2']; [lia |].
  exists r2', m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split; [exact Hm2 | lia]].
Qed.

Lemma rule_7_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb88 (Scfg (S (S r)) 0 m (rep n 7 R)) (Scfg (S (S r')) 0 m' R) t /\
    iter H7 n m <= m' /\ (1 <= n -> m' <= t).
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
  ValidTM 8 8 bb88 /\ exists t, HaltsIn bb88 initConfig t /\ f_omega2_plus 3 7 < t.
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
  { eapply Nat.le_trans; [| exact Hm4].
     change (iter H7 4 7) with (iter H7 (3 + 1) 7). rewrite iter_add.
     apply iter_mono_arg; [apply H7_mono | lia]. }
  destruct (fwp2_step bb88 (fh_fp _ bb88_core) (S (S r4)) 0 m4 [7; 7; 7; 5]) as [t5 [H5 _]].
  assert (Hm5 : S m4 <= Pfn (S (S r4)) 0 m4) by apply Pfn_ge_succ.
  destruct (rule_7_rep 3 r4 (Pfn (S (S r4)) 0 m4) [5] ltac:(lia)) as [r6 [m6 [t6 [H6 [Hm6 Ht6]]]]].
  assert (H6b : iter H7 7 7 <= m6).
  { eapply Nat.le_trans; [| exact Hm6].
     change (iter H7 7 7) with (iter H7 (3 + 4) 7). rewrite iter_add.
     apply iter_mono_arg; [apply H7_mono | lia]. }
  assert (Hhalt : step bb88 (Scfg (S (S r6)) 0 m6 [5]) =
    Some (mkCfgR None (1 :: 2 :: rep (2 * m6 + 1) 3 (rep (S (S r6)) 5 [])) [])).
  { apply (step_mkCfgR_R _ 0 0 _ _ 5 [] eq_refl). }
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
