(*
  rocq/Fwp2_H8.v
  Shared higher-symbol & cursor-5 layers on top of Fwp2_HCore:
    - Fwp2_H6Core, Fwp2_H7Core, Fwp2_H8Core
    - H7_H > f_{ω^2+2}, H8_H > f_{ω^2+3}, climb_2m_plus_1, iter_H_ge_17
    - halt_cursor_5, iter_cursor_rep, iter_cursor_rep0
    - reload_51_4step, reload_5mark_empty, reload_5top_zero
  Powers ALL 12 new BB(9..11, 6..9) champions!
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H.
Import ListNotations.

(* Growth Functions H7_H and H8_H + Generic Climbing Helpers *)

Definition H7_H (m : nat) : nat := iter H_plus2 (2 * m) 1.
Definition H8_H (m : nat) : nat := iter H7_H (2 * m - 1) 1.

Lemma H7_H_mono : forall x y, x <= y -> H7_H x <= H7_H y.
Proof.
  intros x y Hxy. unfold H7_H.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H_plus2_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H7_H_gt : forall m, 1 <= m -> f_omega2_plus 2 m < H7_H m.
Proof.
  intros m Hm. unfold H7_H.
  apply (climb_double H_plus2 (f_omega2_plus 1) 1 ltac:(lia) H_plus2_mono H_plus2_inc H_plus2_gt (fOmega2_props 1 0 1) m Hm).
Qed.

Lemma H7_H_inc : forall m, 1 <= m -> S m <= H7_H m.
Proof.
  intros m Hm. pose proof (H7_H_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 2) m).
  change (f_omega2_plus 2 m) with (fOmega2 1 0 2 m) in *. lia.
Qed.

Lemma H7_H_ge_17 : forall m, 1 <= m -> 17 <= H7_H m.
Proof.
  intros m Hm. unfold H7_H.
  destruct (2 * m) as [| q] eqn:E; [lia |].
  rewrite iter_succ. apply H_plus2_ge_17.
Qed.

Lemma H8_H_mono : forall x y, x <= y -> H8_H x <= H8_H y.
Proof.
  intros x y Hxy. unfold H8_H.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H7_H_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H8_H_gt : forall m, 1 <= m -> f_omega2_plus 3 m < H8_H m.
Proof.
  intros m Hm. unfold H8_H.
  apply (climb_2m_minus_1 H7_H (f_omega2_plus 2) 1 ltac:(lia) H7_H_mono H7_H_inc H7_H_gt (fOmega2_props 1 0 2) m Hm).
Qed.

Lemma H8_H_inc : forall m, 1 <= m -> S m <= H8_H m.
Proof.
  intros m Hm. pose proof (H8_H_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 3) m).
  change (f_omega2_plus 3 m) with (fOmega2 1 0 3 m) in *. lia.
Qed.

Lemma H8_H_ge_17 : forall m, 1 <= m -> 17 <= H8_H m.
Proof.
  intros m Hm. unfold H8_H.
  destruct (2 * m - 1) as [| q] eqn:E; [lia |].
  rewrite iter_succ.
  assert (Hpos : 1 <= iter H7_H q 1).
  { apply iter_ge_self. intro z. destruct z; [lia | pose proof (H7_H_inc (S z) ltac:(lia)); lia]. }
  apply H7_H_ge_17; lia.
Qed.

Lemma climb_2m_plus_1 :
  forall (H f : nat -> nat) (c : nat),
    1 <= c ->
    (forall x y, x <= y -> H x <= H y) ->
    (forall x, 1 <= x -> S x <= H x) ->
    (forall x, 1 <= x -> f x < H x) ->
    FGHProps f ->
    forall m, 1 <= m -> fNext f m < iter H (2 * m + 1) c.
Proof.
  intros H f c Hc Hmono Hinc Hdom Hf m Hm.
  pose proof (climb_2m_minus_1 H f c Hc Hmono Hinc Hdom Hf m Hm) as H1.
  assert (Hge : forall z, z <= H z) by (intro z; destruct z; [lia | pose proof (Hinc (S z) ltac:(lia)); lia]).
  eapply Nat.lt_le_trans; [exact H1 | apply iter_mono_steps; [exact Hge | lia]].
Qed.

Lemma iter_H_ge_17 :
  forall (H : nat -> nat) (k c : nat),
    1 <= k -> 1 <= c ->
    (forall x, 1 <= x -> S x <= H x) ->
    (forall x, 1 <= x -> 17 <= H x) ->
    17 <= iter H k c.
Proof.
  intros H k c Hk Hc Hinc H17. destruct k as [| q]; [lia |].
  rewrite iter_succ.
  assert (Hge : forall z, z <= H z) by (intro z; destruct z; [lia | pose proof (Hinc (S z) ltac:(lia)); lia]).
  pose proof (iter_ge_self H Hge q c). apply H17; lia.
Qed.

(* Shared Cores Fwp2_H6Core, Fwp2_H7Core, Fwp2_H8Core *)

Record Fwp2_H6Core (tm : TM) : Prop := mkFwp2_H6Core {
  h6_fh : Fwp2_HCore tm;
  h6_A6 : tm 0 6 = Some (mkAction 6 DL (Some 7));
  h6_G6 : tm 6 6 = Some (mkAction 2 DL (Some 7));
  h6_H4 : tm 7 4 = Some (mkAction 2 DL (Some 7))
}.

Record Fwp2_H7Core (tm : TM) : Prop := mkFwp2_H7Core {
  h7_h6 : Fwp2_H6Core tm;
  h7_A7 : tm 0 7 = Some (mkAction 7 DL (Some 7));
  h7_G7 : tm 6 7 = Some (mkAction 6 DL (Some 3));
  h7_D4 : tm 3 4 = Some (mkAction 6 DL (Some 3));
  h7_D6 : tm 3 6 = Some (mkAction 3 DR (Some 1));
  h7_B6 : tm 1 6 = Some (mkAction 3 DR (Some 2));
  h7_C6 : tm 2 6 = Some (mkAction 2 DR (Some 0))
}.

Record Fwp2_H8Core (tm : TM) : Prop := mkFwp2_H8Core {
  h8_h7 : Fwp2_H7Core tm;
  h8_A8 : tm 0 8 = Some (mkAction 8 DL (Some 7));
  h8_G8 : tm 6 8 = Some (mkAction 7 DL (Some 6));
  h8_G4 : tm 6 4 = Some (mkAction 7 DL (Some 6));
  h8_B7 : tm 1 7 = Some (mkAction 3 DR (Some 2));
  h8_C7 : tm 2 7 = Some (mkAction 3 DR (Some 4));
  h8_E7 : tm 4 7 = Some (mkAction 3 DR (Some 5));
  h8_F7 : tm 5 7 = Some (mkAction 2 DR (Some 0))
}.

(* Shared rule_6_H, rule_7_H, rule_8_H *)

Local Lemma loop_H4_H6 : forall tm (h6 : Fwp2_H6Core tm) n L R,
  Reaches tm (mkCfgR (Some 7) (rep n 4 L) (4 :: R))
             (mkCfgR (Some 7) L (4 :: rep n 2 R)) n.
Proof.
  intros tm h6. induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 4 4 _ _ R (h6_H4 _ h6)) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Theorem rule_6_H : forall tm (h6 : Fwp2_H6Core tm) r m R, 1 <= m ->
  exists r' m' t, Reaches tm (Scfg (S r) 0 m (6 :: R)) (Scfg (S (S r')) 0 m' R) t /\
    H_plus2 m <= m' /\ m' <= t.
Proof.
  intros tm h6 r m R Hm.
  destruct (sweep_HG tm (h6_fh _ h6) r m 6 R) as [ts Hs].
  destruct (exec_G2_2s tm (h6_fh _ h6) r m R Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists r', m'. eexists. split.
  - eapply reaches_trans; [| exact He].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 2 6 _ _ R (h6_A6 _ h6)) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 1 4 6 _ _ R (h6_G6 _ h6)) |].
    eapply reaches_trans; [apply (loop_H4_H6 tm h6 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
    rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 5 4 _ _ _ (h6_H4 _ h6)) |].
    replace (2 :: 2 :: rep (2 * m + 1) 2 R) with (rep (2 * m + 3) 2 R)
      by (replace (2 * m + 3) with (S (S (2 * m + 1))) by lia; reflexivity).
    apply steps_one. apply (step_mkCfgR_R _ 7 4 _ _ 5 _ (fh_H5 _ (h6_fh _ h6))).
  - split; [exact Hme | lia].
Qed.

Theorem rule_6_H_rep : forall tm (h6 : Fwp2_H6Core tm) n r m R, 1 <= m ->
  exists r' m' t, Reaches tm (Scfg (S r) 0 m (rep n 6 R)) (Scfg (S r') 0 m' R) t /\
    iter H_plus2 n m <= m' /\ (1 <= n -> m' <= t /\ 1 <= r').
Proof.
  intros tm h6. induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_6_H tm h6 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists (S r1), m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; split; [exact Ht1 | lia]]].
    + destruct (rule_6_H tm h6 r m (rep (S p') 6 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H_plus2_ge_17 m); lia).
      destruct (IH (S r1) m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H_plus2 (S (S p')) m) with (iter H_plus2 (S p') (H_plus2 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H_plus2_mono | exact Hm1] | exact Hm2].
      * intros _. destruct (Ht2 ltac:(lia)) as [Ht2a Hr2a]. lia.
Qed.

Local Lemma loop_D4_H7 : forall tm (h7 : Fwp2_H7Core tm) n L R,
  Reaches tm (mkCfgR (Some 3) (rep n 4 L) (4 :: R))
             (mkCfgR (Some 3) L (4 :: rep n 6 R)) n.
Proof.
  intros tm h7. induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 5 4 4 _ _ R (h7_D4 _ h7)) |].
  specialize (IH L (6 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Theorem reload_7_H : forall tm (h7 : Fwp2_H7Core tm) r m R,
  exists t, Reaches tm (Scfg (S (S r)) 0 m (7 :: R)) (Scfg (S r) 0 1 (rep (2 * m) 6 R)) t.
Proof.
  intros tm h7 r m R. destruct (sweep_HG tm (h6_fh _ (h7_h6 _ h7)) (S r) m 7 R) as [ts Hs].
  eexists. eapply reaches_trans.
  - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 6 2 7 _ _ R (h7_A7 _ h7)) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 5 4 7 _ _ R (h7_G7 _ h7)) |].
    apply (loop_D4_H7 tm h7 (2 * m + 1) (rep (S (S r)) 5 []) (6 :: R)).
  - rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 5 5 4 _ _ _ (h7_D4 _ h7)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 5 _ (fp_D5 _ (fh_fp _ (h6_fh _ (h7_h6 _ h7))))) |].
    replace (6 :: 6 :: rep (2 * m + 1) 6 R) with (6 :: 6 :: 6 :: rep (2 * m) 6 R)
      by (replace (2 * m + 1) with (S (2 * m)) by lia; reflexivity).
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 6 _ (h7_D6 _ h7)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 6 _ (h7_B6 _ h7)) |].
    apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 2 1 _ _ 6 _ (h7_C6 _ h7)).
Qed.

Theorem rule_7_H : forall tm (h7 : Fwp2_H7Core tm) r m R, 1 <= m ->
  exists r' m' t, Reaches tm (Scfg (S (S r)) 0 m (7 :: R)) (Scfg (S (S r')) 0 m' R) t /\
    H7_H m <= m' /\ m' <= t.
Proof.
  intros tm h7 r m R Hm.
  destruct (reload_7_H tm h7 r m R) as [t0 H0].
  destruct (rule_6_H_rep tm (h7_h6 _ h7) (2 * m) r 1 R ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (Ht2 ltac:(lia)) as [Ht2_le Hr2_pos].
  destruct r2 as [| r2']; [lia |].
  exists r2', m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split; [exact Hm2 | lia]].
Qed.

Theorem rule_7_H_rep : forall tm (h7 : Fwp2_H7Core tm) n r m R, 1 <= m ->
  exists r' m' t, Reaches tm (Scfg (S (S r)) 0 m (rep n 7 R)) (Scfg (S (S r')) 0 m' R) t /\
    iter H7_H n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  intros tm h7. induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_7_H tm h7 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_7_H tm h7 r m (rep (S p') 7 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H7_H_ge_17 m Hm); lia).
      destruct (IH r1 m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H7_H (S (S p')) m) with (iter H7_H (S p') (H7_H m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H7_H_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Local Lemma loop_G4_H8 : forall tm (h8 : Fwp2_H8Core tm) n L R,
  Reaches tm (mkCfgR (Some 6) (rep n 4 L) (4 :: R))
             (mkCfgR (Some 6) L (4 :: rep n 7 R)) n.
Proof.
  intros tm h8. induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 4 4 _ _ R (h8_G4 _ h8)) |].
  specialize (IH L (7 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_G5_H8 : forall tm (h8 : Fwp2_H8Core tm) n L R,
  Reaches tm (mkCfgR (Some 6) (rep n 5 L) (5 :: R))
             (mkCfgR (Some 6) L (5 :: rep n 5 R)) n.
Proof.
  intros tm h8. induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 4 5 5 _ _ R (fp_G5 _ (fh_fp _ (h6_fh _ (h7_h6 _ (h8_h7 _ h8)))))) |].
  specialize (IH L (5 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Theorem reload_8_H : forall tm (h8 : Fwp2_H8Core tm) r m R, 1 <= m ->
  exists t, Reaches tm (Scfg (S r) 0 m (8 :: R)) (Scfg (S (S (S r))) 0 1 (rep (2 * m - 1) 7 R)) t.
Proof.
  intros tm h8 r m R Hm. destruct m as [| m']; [lia |].
  set (fh := h6_fh _ (h7_h6 _ (h8_h7 _ h8))).
  set (fp := fh_fp _ fh).
  destruct (sweep_HG tm fh r (S m') 8 R) as [ts Hs].
  eexists. eapply reaches_trans.
  - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 7 2 8 _ _ R (h8_A8 _ h8)) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * S m' + 2) with (S (2 * S m' + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 4 8 _ _ R (h8_G8 _ h8)) |].
    apply (loop_G4_H8 tm h8 (2 * S m' + 1) (rep (S r) 5 []) (7 :: R)).
  - rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 5 4 _ _ _ (h8_G4 _ h8)) |].
    replace (7 :: 7 :: rep (2 * S m' + 1) 7 R) with (rep (2 * S m' + 3) 7 R)
      by (replace (2 * S m' + 3) with (S (S (2 * S m' + 1))) by lia; reflexivity).
    eapply reaches_trans; [apply (loop_G5_H8 tm h8 r [] (rep (2 * S m' + 3) 7 R)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil _ 6 4 5 _ _ (fp_G5 _ fp)) |].
    change (5 :: rep r 5 (rep (2 * S m' + 3) 7 R)) with (rep (S r) 5 (rep (2 * S m' + 3) 7 R)).
    eapply steps_succ; [apply (step_mkCfgR_L_nil _ 6 4 0 _ _ (fp_G0 _ fp)) |].
    change (5 :: rep (S r) 5 (rep (2 * S m' + 3) 7 R)) with (rep (S (S r)) 5 (rep (2 * S m' + 3) 7 R)).
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ (fp_F0 _ fp)) |].
    eapply reaches_trans; [apply (loop_B5_H tm fh (S (S r)) [5] (rep (2 * S m' + 3) 7 R)) |].
    rewrite rep_snoc_one.
    change (5 :: rep (S (S r)) 5 []) with (rep (S (S (S r))) 5 []).
    replace (2 * S m' + 3) with (S (S (S (S (2 * S m' - 1))))) by lia.
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 7 _ (h8_B7 _ h8)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ _ 7 _ (h8_C7 _ h8)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 4 2 _ _ 7 _ (h8_E7 _ h8)) |].
    apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 5 1 _ _ 7 _ (h8_F7 _ h8)).
Qed.

Theorem rule_8_H : forall tm (h8 : Fwp2_H8Core tm) r m R, 1 <= m ->
  exists r' m' t, Reaches tm (Scfg (S r) 0 m (8 :: R)) (Scfg (S (S r')) 0 m' R) t /\
    H8_H m <= m' /\ m' <= t.
Proof.
  intros tm h8 r m R Hm.
  destruct (reload_8_H tm h8 r m R Hm) as [t0 H0].
  destruct (rule_7_H_rep tm (h8_h7 _ h8) (2 * m - 1) (S r) 1 R ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2). split; [eapply reaches_trans; eassumption | split; [exact Hm2 |]].
  pose proof (Ht2 ltac:(lia)). lia.
Qed.

Theorem rule_8_H_rep : forall tm (h8 : Fwp2_H8Core tm) n r m R, 1 <= m ->
  exists r' m' t, Reaches tm (Scfg (S (S r)) 0 m (rep n 8 R)) (Scfg (S (S r')) 0 m' R) t /\
    iter H8_H n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  intros tm h8. induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_8_H tm h8 (S r) m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_8_H tm h8 (S r) m (rep (S p') 8 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H8_H_ge_17 m Hm); lia).
      destruct (IH r1 m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H8_H (S (S p')) m) with (iter H8_H (S p') (H8_H m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H8_H_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

(* Generic Cursor-5 Combinators *)

Theorem halt_cursor_5 : forall tm mark' r m,
  tm 0 5 = Some (mkAction (S mark') DR (Some 8)) ->
  tm 8 0 = Some (mkAction 1 DR None) ->
  exists cf, Reaches tm (Scfg r 0 m [5]) cf 2 /\ cfg_st cf = None.
Proof.
  intros tm mark' r m HA5 HI0. eexists. split.
  - eapply steps_succ; [apply (step_mkCfgR_R _ 0 mark' _ _ 5 [] HA5) |].
    apply steps_one. apply (step_mkCfgR_R_nil _ 8 0 _ _ HI0).
  - reflexivity.
Qed.

Theorem iter_cursor_rep :
  forall tm minR sym (H : nat -> nat),
    (forall x y, x <= y -> H x <= H y) ->
    (forall x, 1 <= x -> 1 <= H x) ->
    (forall r m R, 1 <= m ->
      exists r' m' t, Reaches tm (Scfg (r + minR) 0 m (5 :: sym :: R))
                                 (Scfg (r' + minR) 0 m' (5 :: R)) t /\ H m <= m' /\ m' <= t) ->
    forall n r m R, 1 <= m ->
      exists r' m' t, Reaches tm (Scfg (r + minR) 0 m (5 :: rep n sym R))
                                 (Scfg (r' + minR) 0 m' (5 :: R)) t /\
        iter H n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  intros tm minR sym H Hmono Hpos Hstep.
  induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (Hstep r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (Hstep r m (rep (S p') sym R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (Hpos m Hm); lia).
      destruct (IH r1 m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H (S (S p')) m) with (iter H (S p') (H m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [exact Hmono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Theorem iter_cursor_rep0 :
  forall tm minR sym (H : nat -> nat),
    (forall x y, x <= y -> H x <= H y) ->
    (forall r m R,
      exists r' m' t, Reaches tm (Scfg (r + minR) 0 m (5 :: sym :: R))
                                 (Scfg (r' + minR) 0 m' (5 :: R)) t /\ H m <= m' /\ m' <= t) ->
    forall n r m R,
      exists r' m' t, Reaches tm (Scfg (r + minR) 0 m (5 :: rep n sym R))
                                 (Scfg (r' + minR) 0 m' (5 :: R)) t /\
        iter H n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  intros tm minR sym H Hmono Hstep.
  induction n as [| p IH]; intros r m R.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (Hstep r m R) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (Hstep r m (rep (S p') sym R)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H (S (S p')) m) with (iter H (S p') (H m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [exact Hmono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma loop_L3 : forall tm q w' n L R,
  tm q 3 = Some (mkAction (S w') DL (Some q)) ->
  Reaches tm (mkCfgR (Some q) (rep n 3 L) (3 :: R))
             (mkCfgR (Some q) L (3 :: rep n (S w') R)) n.
Proof.
  intros tm q w' n L R Hq3. revert R.
  induction n as [| k IH]; intro R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ q w' 3 3 _ _ R Hq3) |].
  specialize (IH (S w' :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Theorem reload_51_4step : forall tm sw mark' low' s1 s2 s3 r m R,
  tm 0 5 = Some (mkAction (S mark') DR (Some 8)) ->
  tm 8 1 = Some (mkAction 5 DL (Some sw)) ->
  tm sw (S mark') = Some (mkAction (S low') DL (Some sw)) ->
  tm sw 2 = Some (mkAction (S low') DL (Some sw)) ->
  tm sw 3 = Some (mkAction (S low') DL (Some sw)) ->
  tm sw 5 = Some (mkAction 5 DR (Some 1)) ->
  tm 1 (S low') = Some (mkAction 3 DR (Some s1)) ->
  tm s1 (S low') = Some (mkAction 3 DR (Some s2)) ->
  tm s2 (S low') = Some (mkAction 3 DR (Some s3)) ->
  tm s3 (S low') = Some (mkAction 2 DR (Some 0)) ->
  1 <= m ->
  exists t, Reaches tm (Scfg (S r) 0 m (5 :: 1 :: R))
                       (Scfg (S r) 0 1 (rep (2 * m - 1) (S low') (5 :: R))) t.
Proof.
  intros tm sw mark' low' s1 s2 s3 r m R HA5 HI1 HswM Hsw2 Hsw3 Hsw5 HB H1 H2 H3 Hm.
  destruct m as [| m']; [lia |].
  eexists. eapply reaches_trans.
  - unfold Scfg.
    eapply steps_succ; [apply (step_mkCfgR_R _ 0 mark' _ _ 5 _ HA5) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 4 (S mark') 1 _ _ R HI1) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ sw low' 2 (S mark') _ _ _ HswM) |].
    replace (2 * S m' + 1) with (S (2 * S m')) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ sw low' 3 2 _ _ _ Hsw2) |].
    apply (loop_L3 tm sw low' (2 * S m') (rep (S r) 5 []) (S low' :: S low' :: 5 :: R) Hsw3).
  - rewrite rep_snoc_one, rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ sw low' 5 3 _ _ _ Hsw3) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ sw 4 _ _ 5 _ Hsw5) |].
    replace (S low' :: S low' :: S low' :: rep (2 * S m') (S low') (5 :: R))
      with (rep (2 * S m' + 3) (S low') (5 :: R))
      by (replace (2 * S m' + 3) with (S (S (S (2 * S m')))) by lia; reflexivity).
    replace (2 * S m' + 3) with (S (S (S (S (2 * S m' - 1))))) by lia.
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ (S low') _ HB) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ s1 2 _ _ (S low') _ H1) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ s2 2 _ _ (S low') _ H2) |].
    apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ s3 1 _ _ (S low') _ H3).
Qed.

Theorem reload_5mark_empty : forall tm mark' (fp : Fwp2Core tm) r m R,
  tm 0 5 = Some (mkAction (S mark') DR (Some 8)) ->
  tm 8 (S mark') = Some (mkAction 1 DL (Some 8)) ->
  tm 8 2 = Some (mkAction 1 DL (Some 8)) ->
  tm 8 3 = Some (mkAction 1 DL (Some 8)) ->
  tm 8 5 = Some (mkAction 5 DR (Some 7)) ->
  tm 7 1 = Some (mkAction 2 DR (Some 5)) ->
  tm 5 1 = Some (mkAction 1 DR (Some 9)) ->
  tm 9 1 = Some (mkAction 5 DL (Some 0)) ->
  exists t, Reaches tm (Scfg (S r) 0 m (5 :: S mark' :: R))
                       (Scfg (S r) 0 (Pempty r) (5 :: rep (2 * m + 1) 1 R)) t.
Proof.
  intros tm mark' fp r m R HA5 HIM HI2 HI3 HI5 HH1 HF1 HJ1.
  destruct (fwp2_empty3 tm fp r (5 :: rep (2 * m + 1) 1 R)) as [te [Hempty _]].
  eexists. eapply reaches_trans; [| exact Hempty].
  eapply reaches_trans.
  - unfold Scfg.
    eapply steps_succ; [apply (step_mkCfgR_R _ 0 mark' _ _ 5 _ HA5) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 0 (S mark') (S mark') _ _ R HIM) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 0 2 (S mark') _ _ _ HIM) |].
    replace (2 * m + 1) with (S (2 * m)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 0 3 2 _ _ _ HI2) |].
    apply (loop_L3 tm 8 0 (2 * m) (rep (S r) 5 []) (1 :: 1 :: 1 :: R) HI3).
  - rewrite rep_snoc_one, rep_snoc_one, rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 0 5 3 _ _ _ HI3) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 8 4 _ _ 5 _ HI5) |].
    change (1 :: 1 :: 1 :: 1 :: rep (2 * m) 1 R) with (1 :: 1 :: 1 :: rep (S (2 * m)) 1 R).
    replace (S (2 * m)) with (2 * m + 1) by lia.
    eapply steps_succ; [apply (step_mkCfgR_R _ 7 1 _ _ 1 _ HH1) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 0 _ _ 1 _ HF1) |].
    apply steps_one. apply (step_mkCfgR_L_cons _ 9 4 1 1 _ _ _ HJ1).
Qed.

Theorem reload_5top_zero : forall tm mark' top e1 e2 e3 r m R,
  tm 0 5 = Some (mkAction (S mark') DR (Some 8)) ->
  tm 8 top = Some (mkAction (S mark') DL (Some 10)) ->
  tm 10 (S mark') = Some (mkAction (S mark') DL (Some 10)) ->
  tm 10 2 = Some (mkAction (S mark') DL (Some 10)) ->
  tm 10 3 = Some (mkAction (S mark') DL (Some 10)) ->
  tm 10 5 = Some (mkAction 5 DR (Some e1)) ->
  tm e1 (S mark') = Some (mkAction 3 DR (Some e2)) ->
  tm e2 (S mark') = Some (mkAction 2 DR (Some e3)) ->
  tm e3 (S mark') = Some (mkAction 5 DL (Some 5)) ->
  tm 5 2 = Some (mkAction 2 DR (Some 0)) ->
  exists t, Reaches tm (Scfg (S r) 0 m (5 :: top :: R))
                       (Scfg (S r) 0 0 (5 :: rep (2 * m + 1) (S mark') R)) t.
Proof.
  intros tm mark' top e1 e2 e3 r m R HA5 HIt HKM HK2 HK3 HK5 He1 He2 He3 HF2.
  eexists. eapply reaches_trans.
  - unfold Scfg.
    eapply steps_succ; [apply (step_mkCfgR_R _ 0 mark' _ _ 5 _ HA5) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 8 mark' (S mark') top _ _ R HIt) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 10 mark' 2 (S mark') _ _ _ HKM) |].
    replace (2 * m + 1) with (S (2 * m)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 10 mark' 3 2 _ _ _ HK2) |].
    apply (loop_L3 tm 10 mark' (2 * m) (rep (S r) 5 []) (S mark' :: S mark' :: S mark' :: R) HK3).
  - rewrite rep_snoc_one, rep_snoc_one, rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 10 mark' 5 3 _ _ _ HK3) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 10 4 _ _ 5 _ HK5) |].
    change (S mark' :: S mark' :: S mark' :: S mark' :: rep (2 * m) (S mark') R)
      with (S mark' :: S mark' :: S mark' :: rep (S (2 * m)) (S mark') R).
    replace (S (2 * m)) with (2 * m + 1) by lia.
    eapply steps_succ; [apply (step_mkCfgR_R _ e1 2 _ _ (S mark') _ He1) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ e2 1 _ _ (S mark') _ He2) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ e3 4 2 (S mark') _ _ _ He3) |].
    apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 5 1 _ _ 2 _ HF2).
Qed.
