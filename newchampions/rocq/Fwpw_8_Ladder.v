(*
  rocq/Fwpw_8_Ladder.v
  Reusable Rocq 9.1 f_{ω^ω+k} ladder on top of Fwpw_8.v.
  Powers BB(10..16,8), BB(11..14,9), BB(16,9).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8.
Import ListNotations.

Section Fwpw_8_I_Lemmas.
  Variable tm : TM.
  Hypothesis hc : Fwpw_8_ICore tm.

  Let c8 : Fwpw_8Core tm := w8i_core tm hc.

  (* I sweeps left over 3^n writing 2 *)
  Lemma w8i_I3_left : forall n R,
    Reaches tm (mkCfgR (Some 8) (rep n 3 []) (3 :: R))
               (mkCfgR (Some 8) [] (0 :: rep (S n) 2 R)) (S n).
  Proof.
    induction n as [| n' IH]; intros R.
    - apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_I3 tm hc); reflexivity.
    - replace (S (S n')) with (1 + S n') by lia.
      eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_I3 tm hc); reflexivity |].
      specialize (IH (2 :: R)). rewrite rep_r8 in IH. exact IH.
  Qed.

  (* I sweeps right over 2^n writing 2 *)
  Lemma w8i_I2_right : forall n L R,
    Reaches tm (mkCfgR (Some 8) L (rep n 2 R))
               (mkCfgR (Some 8) (rep n 2 L) R) n.
  Proof.
    induction n as [| n' IH]; intros L R; [apply reaches_zero |].
    change (Reaches tm (mkCfgR (Some 8) L (2 :: rep n' 2 R)) (mkCfgR (Some 8) (rep (S n') 2 L) R) (1 + n')).
    eapply reaches_trans.
    - apply (w8_step_R tm 8 2 1 (Some 8) L (rep n' 2 R) (w8i_I2 tm hc)).
    - specialize (IH (2 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  (* Rule 5: 3^n 2^1 H> 2 R -> 3^1 2^{n-1} H> 1 1 3 4 R (for n >= 2) *)
  Lemma w8_rule_2_step : forall n R, 2 <= n ->
    exists t, Reaches tm (H8cfg n 1 (2 :: R)) (H8cfg 1 (n - 1) (1 :: 1 :: 3 :: 4 :: R)) t /\ 1 <= t.
  Proof.
    intros n R Hn. destruct n as [| [| n'']]; [lia | lia |].
    replace (S (S n'') - 1) with (S n'') by lia.
    assert (H1 : Reaches tm (H8cfg (S (S n'')) 1 (2 :: R))
                            (mkCfgR (Some 4) (rep (S (S n'')) 3 []) (2 :: 4 :: R)) 1)
      by (unfold H8cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_H2 tm hc); reflexivity).
    assert (H2 : Reaches tm (mkCfgR (Some 4) (rep (S (S n'')) 3 []) (2 :: 4 :: R))
                            (mkCfgR (Some 8) (rep (S n'') 3 []) (3 :: 1 :: 4 :: R)) 1)
      by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_E2 tm hc); reflexivity).
    pose proof (w8i_I3_left (S n'') (1 :: 4 :: R)) as H3.
    assert (H4 : Reaches tm (mkCfgR (Some 8) [] (0 :: rep (S (S n'')) 2 (1 :: 4 :: R)))
                            (mkCfgR (Some 8) [3] (rep (S (S n'')) 2 (1 :: 4 :: R))) 1)
      by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_I0 tm hc); reflexivity).
    pose proof (w8i_I2_right (S (S n'')) [3] (1 :: 4 :: R)) as H5.
    assert (H6 : Reaches tm (mkCfgR (Some 8) (rep (S (S n'')) 2 [3]) (1 :: 4 :: R))
                            (mkCfgR (Some 1) (rep (S n'') 2 [3]) (2 :: 3 :: 4 :: R)) 1)
      by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_I1 tm hc); reflexivity).
    (* Now at mkCfgR (Some 1) (rep (S n'') 2 [3]) (2 :: 3 :: 4 :: R), which is EXACTLY 1 step after H8cfg 1 (S (S n'')) (1 :: 4 :: R)! *)
    destruct (w8_rule_1_high tm c8 1 (S n'') (4 :: R) ltac:(lia)) as [t7 [H7 Ht7]].
    (* Unfold first step of H7: H8cfg 1 (S (S n'')) (1 :: 4 :: R) -> mkCfgR (Some 1) (rep (S n'') 2 [3]) (2 :: 3 :: 4 :: R) *)
    destruct t7 as [| t7']; [lia |].
    assert (H7' : Reaches tm (mkCfgR (Some 1) (rep (S n'') 2 [3]) (2 :: 3 :: 4 :: R))
                             (H8cfg 1 (S n'') (1 :: 1 :: 3 :: 4 :: R)) t7').
    { unfold Reaches in H7 |- *. simpl in H7.
      unfold H8cfg in H7.
      change (match step tm (mkCfgR (Some 7) (rep (S (S n'')) 2 [3]) (1 :: 4 :: R)) with
              | Some c1 => steps tm t7' c1 | None => None end =
              Some (H8cfg 1 (S n'') (1 :: 1 :: 3 :: 4 :: R))) in H7.
      cbn [step mkCfgR cfg_st cfg_cur] in H7.
      rewrite (w8_H1 tm c8) in H7. exact H7. }
    exists (1 + 1 + S (S n'') + 1 + S (S n'') + 1 + t7').
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7'] | lia].
  Qed.

  Lemma w8_base_mono : forall x y, x <= y -> x + 2 <= y + 2. Proof. intros; lia. Qed.
  Lemma w8_base_inc : forall x, x + 2 <= x + 2. Proof. intros; lia. Qed.

  Lemma F8_base_grow : forall k, 2 * k + 9 <= F8_step k (fun m => m + 2) 1.
  Proof.
    induction k as [| k' IH].
    - simpl. lia.
    - simpl.
      destruct (F8_step_props k' (fun m => m + 2) w8_base_mono w8_base_inc) as [Hm [Hi [Hf _]]].
      destruct (F8_step_props k' (F8_step k' (fun m => m + 2)) Hm Hi) as [_ [_ [Hf2 _]]].
      pose proof (Hf2 1 ltac:(lia)). lia.
  Qed.

  (* Full 2-step with + 2: H8cfg n 1 (2 :: R) -> H8cfg n' 1 R with 2 * f_omega_omega (n - 2) + 2 <= n' *)
  Lemma w8_two_step : forall n R, 3 <= n ->
    exists n' t, Reaches tm (H8cfg n 1 (2 :: R)) (H8cfg n' 1 R) t /\
                 2 * f_omega_omega (n - 2) + 2 <= n' /\ 3 <= n' /\ n' <= t.
  Proof.
    intros n R Hn.
    destruct (w8_rule_2_step n R ltac:(lia)) as [t1 [H1 _]].
    replace (n - 1) with (S (n - 2)) in H1 by lia.
    assert (Hrun0 : RunW tm (S (n - 2)) [3] (fun m => m + 2)).
    { apply (runW_3 tm c8). apply (runW_nil tm c8); lia. }
    assert (Hrun1 : RunW tm (S (n - 2)) [1; 3] (F8_step (n - 2) (fun m => m + 2))).
    { apply (w8_run_F8 tm c8); [constructor; [right; reflexivity | constructor] | exact w8_base_mono | exact w8_base_inc | exact Hrun0]. }
    destruct (F8_step_props (n - 2) (fun m => m + 2) w8_base_mono w8_base_inc) as [Hm1 [Hi1 _]].
    assert (Hrun2 : RunW tm (S (n - 2)) [1; 1; 3] (F8_step (n - 2) (F8_step (n - 2) (fun m => m + 2)))).
    { apply (w8_run_F8 tm c8); [constructor; [left; reflexivity | constructor; [right; reflexivity | constructor]] | exact Hm1 | exact Hi1 | exact Hrun1]. }
    destruct (Hrun2 1 R ltac:(lia)) as [n' [t2 [H2 [Hge2 Ht2]]]].
    exists n', (t1 + t2).
    split; [eapply reaches_trans; [exact H1 | exact H2] |].
    destruct (F8_step_props (n - 2) (F8_step (n - 2) (fun m => m + 2)) Hm1 Hi1) as [_ [_ [_ Hgg]]].
    pose proof (F8_base_grow (n - 2)) as Hbg.
    pose proof (Hm1 (2 * (n - 2)) (F8_step (n - 2) (fun m => m + 2) 1) ltac:(lia)) as Hstep1.
    assert (Hbz : forall x, 1 <= x -> 2 * fZero x <= 2 * x + 2) by (intros; unfold fZero; lia).
    pose proof (F8_step_ge_fOmegaPowStep (n - 2) fZero (fun m => m + 2) fZero_props
                  w8_base_mono w8_base_inc Hbz (n - 2) ltac:(lia)) as Hstep2.
    pose proof (fgh_ge_self _ f_omega_omega_props (n - 2)).
    unfold f_omega_omega in *.
    repeat split; lia.
  Qed.

  (* Even for n = 1 or 2, H8cfg n 1 (2 :: R) -> H8cfg n' 1 R with n + 2 <= n' *)
  Lemma w8_two_step_any : forall n R, 1 <= n ->
    exists n' t, Reaches tm (H8cfg n 1 (2 :: R)) (H8cfg n' 1 R) t /\ n + 2 <= n' /\ n' <= t.
  Proof.
    intros n R Hn.
    destruct n as [| [| [| n''']]]; [lia | | |].
    - (* n = 1: H8cfg 1 1 (2 :: R) -> H8cfg 1 1 (4 :: 4 :: 4 :: 4 :: R) -> H8cfg 9 1 R *)
      assert (H1 : Reaches tm (H8cfg 1 1 (2 :: R)) (mkCfgR (Some 4) [3] (2 :: 4 :: R)) 1)
        by (unfold H8cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_H2 tm hc); reflexivity).
      assert (H2 : Reaches tm (mkCfgR (Some 4) [3] (2 :: 4 :: R)) (mkCfgR (Some 8) [] (3 :: 1 :: 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_E2 tm hc); reflexivity).
      pose proof (w8i_I3_left 0 (1 :: 4 :: R)) as H3.
      assert (H4 : Reaches tm (mkCfgR (Some 8) [] (0 :: 2 :: 1 :: 4 :: R)) (mkCfgR (Some 8) [3] (2 :: 1 :: 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_I0 tm hc); reflexivity).
      pose proof (w8i_I2_right 1 [3] (1 :: 4 :: R)) as H5.
      assert (H6 : Reaches tm (mkCfgR (Some 8) [2; 3] (1 :: 4 :: R)) (mkCfgR (Some 1) [3] (2 :: 3 :: 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_I1 tm hc); reflexivity).
      (* mkCfgR (Some 1) [3] (2 :: 3 :: 4 :: R) is 1 step after H8cfg 1 1 (1 :: 4 :: R) *)
      destruct (w8_rule_1_low tm c8 1 [] R (Forall_nil _)) as [t7 [H7 Ht7]].
      destruct t7 as [| t7']; [lia |].
      assert (H7' : Reaches tm (mkCfgR (Some 1) [3] (2 :: 3 :: 4 :: R)) (H8cfg 1 1 (4 :: 4 :: 4 :: 4 :: R)) t7').
      { unfold Reaches in H7 |- *. simpl in H7. unfold H8cfg in H7.
        change (match step tm (mkCfgR (Some 7) [2; 3] (1 :: 4 :: R)) with
                | Some c1 => steps tm t7' c1 | None => None end =
                Some (H8cfg 1 1 (4 :: 4 :: 4 :: 4 :: R))) in H7.
        cbn [step mkCfgR cfg_st cfg_cur] in H7. rewrite (w8_H1 tm c8) in H7. exact H7. }
      destruct (w8_rule_4 tm c8 1 1 (4 :: 4 :: 4 :: R) ltac:(lia)) as [t8 [H8 _]].
      destruct (w8_rule_4 tm c8 3 1 (4 :: 4 :: R) ltac:(lia)) as [t9 [H9 _]].
      destruct (w8_rule_4 tm c8 5 1 (4 :: R) ltac:(lia)) as [t10 [H10 _]].
      destruct (w8_rule_4 tm c8 7 1 R ltac:(lia)) as [t11 [H11 Ht11]].
      exists 9, (1 + 1 + 1 + 1 + 1 + 1 + t7' + t8 + t9 + t10 + t11).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7'] | exact H8] | exact H9] | exact H10] | exact H11] | lia].
    - (* n = 2 *)
      destruct (w8_rule_2_step 2 R ltac:(lia)) as [t1 [H1 _]].
      assert (Hrun0 : RunW tm 1 [3] (fun m => m + 2)) by (apply (runW_3 tm c8); apply (runW_nil tm c8); lia).
      assert (Hrun1 : RunW tm 1 [1; 3] (F8_step 0 (fun m => m + 2)))
        by (apply (w8_run_F8 tm c8); [constructor; [right; reflexivity | constructor] | exact w8_base_mono | exact w8_base_inc | exact Hrun0]).
      destruct (F8_step_props 0 (fun m => m + 2) w8_base_mono w8_base_inc) as [Hm1 [Hi1 _]].
      assert (Hrun2 : RunW tm 1 [1; 1; 3] (F8_step 0 (F8_step 0 (fun m => m + 2))))
        by (apply (w8_run_F8 tm c8); [constructor; [left; reflexivity | constructor; [right; reflexivity | constructor]] | exact Hm1 | exact Hi1 | exact Hrun1]).
      destruct (Hrun2 1 R ltac:(lia)) as [n' [t2 [H2 [Hge2 Ht2]]]].
      destruct (F8_step_props 0 (F8_step 0 (fun m => m + 2)) Hm1 Hi1) as [_ [_ [Hf2 _]]].
      pose proof (Hf2 1 ltac:(lia)). pose proof (Hi1 1). exists n', (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] | lia].
    - destruct (w8_two_step (S (S (S n'''))) R ltac:(lia)) as [n' [t [H1 [Hf [H3 Ht]]]]].
      pose proof (fgh_gt_pos _ f_omega_omega_props (S (S (S n''')) - 2) ltac:(lia)).
      exists n', t. split; [exact H1 | lia].
  Qed.

  (* Uniform StepF predicate for all ladder levels *)
  Definition StepF (sym : nat) (f : nat -> nat) : Prop :=
    forall n R, 1 <= n ->
      exists n' t, Reaches tm (H8cfg n 1 (sym :: R)) (H8cfg n' 1 R) t /\
                   n + 2 <= n' /\
                   (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * f x <= n' - 2) /\
                   n' <= t.

  Lemma w8_stepF_2 : StepF 2 f_omega_omega.
  Proof.
    intros n R Hn.
    destruct (le_lt_dec 3 n) as [H3 | Hlt].
    - destruct (w8_two_step n R H3) as [n' [t [H1 [Hf [_ Ht]]]]].
      exists n', t. split; [exact H1 |].
      pose proof (fgh_gt_pos _ f_omega_omega_props (n - 2) ltac:(lia)) as Hgt.
      repeat split; [lia | | exact Ht].
      intros x Hx H2x.
      pose proof (fgh_mono _ f_omega_omega_props x (n - 2) ltac:(lia)). lia.
    - destruct (w8_two_step_any n R Hn) as [n' [t [H1 [H3 Ht]]]].
      (* Note: for n = 1 or 2, n' >= 9? Wait: for n = 2, Hi2 gave >= 3; let's check n + 2 <= n':
         for n = 1, n' = 9 >= 3 = 1 + 2; for n = 2, n' >= 2 + 2 = 4?
         In w8_two_step_any for n = 2: F8_step 0 (F8_step 0 (fun m => m + 2)) 1 >= 1 + 2 + 2 = 5 >= 4! *)
      exists n', t. split; [exact H1 | repeat split; [| intros; lia | exact Ht]].
      (* Wait: w8_two_step_any only promised 3 <= n'! Let's strengthen w8_two_step_any to n + 2 <= n'! *)
      lia.
  Qed.

  Lemma StepF_rep : forall sym f, FGHProps f -> StepF sym f ->
    forall c n R, 1 <= n ->
      exists n' t, Reaches tm (H8cfg n 1 (rep c sym R)) (H8cfg n' 1 R) t /\
                   n + 2 * c <= n' /\
                   (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * iter f c x <= n' - 2) /\
                   (1 <= c -> n' <= t).
  Proof.
    intros sym f Hf Hs. induction c as [| c' IH]; intros n R Hn.
    - exists n, 0. split; [apply reaches_zero | simpl; repeat split; intros; lia].
    - destruct (Hs n (rep c' sym R) Hn) as [n1 [t1 [H1 [Hinc1 [Hf1 Ht1]]]]].
      destruct c' as [| c''].
      + exists n1, t1. simpl in *. split; [exact H1 | repeat split; [lia | intros x Hx H2x; apply Hf1; assumption | intros _; exact Ht1]].
      + destruct (IH n1 R ltac:(lia)) as [n2 [t2 [H2 [Hinc2 [Hf2 Ht2]]]]].
        exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
        repeat split; [lia | | intros _; specialize (Ht2 ltac:(lia)); lia].
        intros x Hx H2x.
        replace (iter f (S (S c'')) x) with (iter f (S c'') (f x))
          by (replace (S (S c'')) with (S c'' + 1) by lia; rewrite iter_add; reflexivity).
        apply Hf2; [pose proof (fgh_ge_self _ Hf x); lia | apply Hf1; assumption].
  Qed.

  Lemma StepF_next : forall sym prev_sym f,
    FGHProps f -> StepF prev_sym f ->
    (forall n R, 1 <= n -> exists t, Reaches tm (H8cfg n 1 (sym :: R)) (H8cfg 1 1 (rep (S n) prev_sym R)) t) ->
    StepF sym (fNext f).
  Proof.
    intros sym prev_sym f Hf Hprev Hrew n R Hn.
    destruct (Hrew n R Hn) as [t0 H0].
    destruct (Hprev 1 (rep n prev_sym R) ltac:(lia)) as [n1 [t1 [H1 [Hinc1 [_ _]]]]].
    set (q := n / 2).
    assert (Hdiv : 2 * q <= n /\ n <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod n 2 ltac:(lia)); pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia).
    assert (Hq : n = q + (n - q)) by lia.
    simpl rep in H0. rewrite Hq, rep_add8 in H1.
    replace (rep n prev_sym R) with (rep q prev_sym (rep (n - q) prev_sym R)) in H0 by (rewrite <- rep_add8, <- Hq; reflexivity).
    destruct (StepF_rep prev_sym f Hf Hprev q n1 (rep (n - q) prev_sym R) ltac:(lia))
      as [n2 [t2 [H2 [Hinc2 [_ _]]]]].
    destruct (StepF_rep prev_sym f Hf Hprev (n - q) n2 R ltac:(lia))
      as [n3 [t3 [H3 [Hinc3 [Hf3 Ht3]]]]].
    exists n3, (t0 + t1 + t2 + t3).
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] |].
    repeat split; [unfold q in *; lia | | specialize (Ht3 ltac:(unfold q; lia)); lia].
    intros x Hx H2x.
    assert (Hxq : x <= q) by (unfold q; lia).
    assert (Hrem : x <= n - q) by (unfold q; lia).
    pose proof (Hf3 x Hx ltac:(lia)) as Hiter.
    pose proof (iter_mono_steps f (fgh_ge_self _ Hf) x (n - q) x Hrem) as Hst.
    unfold fNext. lia.
  Qed.

End Fwpw_8_I_Lemmas.

(* Generic left-sweeper over 2 :: rep n 3 [] *)
Lemma w8_sweep_left_23 : forall tm st w n R,
  tm st 2 = Some (mkAction (S w) DL (Some st)) ->
  tm st 3 = Some (mkAction (S w) DL (Some st)) ->
  Reaches tm (mkCfgR (Some st) (rep n 3 []) (2 :: R))
             (mkCfgR (Some st) [] (0 :: rep (S n) (S w) R)) (S n).
Proof.
  intros tm st w n. induction n as [| n' IH]; intros R H2 H3.
  - apply steps_one; unfold step, mkCfgR; simpl; rewrite H2; reflexivity.
  - assert (Hloop : forall a R0,
      Reaches tm (mkCfgR (Some st) (rep a 3 []) (3 :: R0))
                 (mkCfgR (Some st) [] (0 :: rep (S a) (S w) R0)) (S a)).
    { induction a as [| a' IHa]; intros R0.
      - apply steps_one; unfold step, mkCfgR; simpl; rewrite H3; reflexivity.
      - replace (S (S a')) with (1 + S a') by lia.
        eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite H3; reflexivity |].
        specialize (IHa (S w :: R0)). rewrite rep_r8 in IHa. exact IHa. }
    replace (S (S n')) with (1 + S n') by lia.
    eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite H2; reflexivity |].
    pose proof (Hloop n' (S w :: R)) as Hl. rewrite rep_r8 in Hl. exact Hl.
Qed.

(* Generic 2-step left-end turnaround for K (0->3RK, 5->2RH), L (0->3RL, 6->2RH), M9 (0->3RM, 7->2RH) *)
Lemma w8_sweep_level : forall tm st sym prev_sym,
  tm 7 sym = Some (mkAction (S prev_sym) DL (Some st)) ->
  tm st 0 = Some (mkAction 3 DR (Some st)) ->
  tm st 2 = Some (mkAction (S prev_sym) DL (Some st)) ->
  tm st 3 = Some (mkAction (S prev_sym) DL (Some st)) ->
  tm st (S prev_sym) = Some (mkAction 2 DR (Some 7)) ->
  forall n R, 1 <= n ->
    exists t, Reaches tm (H8cfg n 1 (sym :: R)) (H8cfg 1 1 (rep (S n) (S prev_sym) R)) t.
Proof.
  intros tm st sym prev_sym Hsym H0 H2 H3 Hprev n R Hn.
  assert (Hs1 : Reaches tm (H8cfg n 1 (sym :: R)) (mkCfgR (Some st) (rep n 3 []) (2 :: S prev_sym :: R)) 1)
    by (unfold H8cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite Hsym; reflexivity).
  pose proof (w8_sweep_left_23 tm st prev_sym n (S prev_sym :: R) H2 H3) as Hs2.
  assert (Hs3 : Reaches tm (mkCfgR (Some st) [] (0 :: rep (S n) (S prev_sym) (S prev_sym :: R)))
                           (mkCfgR (Some st) [3] (rep (S n) (S prev_sym) (S prev_sym :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite H0; reflexivity).
  assert (Hs4 : Reaches tm (mkCfgR (Some st) [3] (S prev_sym :: rep n (S prev_sym) (S prev_sym :: R)))
                           (H8cfg 1 1 (rep (S n) (S prev_sym) R)) 1).
  { unfold H8cfg; rewrite rep_r8; apply (w8_step_R tm st (S prev_sym) 1 (Some 7) [3] (rep (S n) (S prev_sym) R) Hprev). }
  exists (1 + S n + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4].
Qed.

(* Level 1: J core (H5 = 2LJ, J0 = 0RC, J2=J3 = 2LJ) -> f_{ω^ω+1} *)
Record Fwpw_8_JCore (tm : TM) : Prop := mkFwpw_8_JCore {
  w8j_i : Fwpw_8_ICore tm;
  w8j_H5 : tm 7 5 = Some (mkAction 2 DL (Some 9));
  w8j_J0 : tm 9 0 = Some (mkAction 0 DR (Some 2));
  w8j_J2 : tm 9 2 = Some (mkAction 2 DL (Some 9));
  w8j_J3 : tm 9 3 = Some (mkAction 2 DL (Some 9))
}.

Lemma w8_stepF_5 : forall tm (hc : Fwpw_8_JCore tm), StepF tm 5 (f_omega_omega_plus 1).
Proof.
  intros tm hc.
  apply (StepF_next tm 5 2 f_omega_omega f_omega_omega_props (w8_stepF_2 tm (w8j_i tm hc))).
  intros n R Hn.
  assert (H1 : Reaches tm (H8cfg n 1 (5 :: R)) (mkCfgR (Some 9) (rep n 3 []) (2 :: 2 :: R)) 1)
    by (unfold H8cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8j_H5 tm hc); reflexivity).
  pose proof (w8_sweep_left_23 tm 9 1 n (2 :: R) (w8j_J2 tm hc) (w8j_J3 tm hc)) as H2.
  assert (H3 : Reaches tm (mkCfgR (Some 9) [] (0 :: rep (S n) 2 (2 :: R)))
                          (mkCfgR (Some 2) [] (rep (S n) 2 (2 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8j_J0 tm hc); reflexivity).
  assert (H4 : Reaches tm (mkCfgR (Some 2) [] (2 :: rep n 2 (2 :: R)))
                          (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C2 tm (w8i_core tm (w8j_i tm hc))); reflexivity).
  assert (H5 : Reaches tm (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: R)))
                          (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C0 tm (w8i_core tm (w8j_i tm hc))); reflexivity).
  assert (H6 : Reaches tm (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: R)))
                          (H8cfg 1 1 (rep (S n) 2 R)) 1).
  { unfold H8cfg; rewrite rep_r8; apply (w8_step_R tm 1 3 1 (Some 7) [3] (rep (S n) 2 R) (w8_B3 tm (w8i_core tm (w8j_i tm hc)))). }
  exists (1 + S n + 1 + 1 + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6].
Qed.

(* Level 2: K core (H6 = 5LK, K0 = 3RK, K2=K3 = 5LK, K5 = 2RH) -> f_{ω^ω+2} *)
Record Fwpw_8_KCore (tm : TM) : Prop := mkFwpw_8_KCore {
  w8k_j : Fwpw_8_JCore tm;
  w8k_H6 : tm 7 6 = Some (mkAction 5 DL (Some 10));
  w8k_K0 : tm 10 0 = Some (mkAction 3 DR (Some 10));
  w8k_K2 : tm 10 2 = Some (mkAction 5 DL (Some 10));
  w8k_K3 : tm 10 3 = Some (mkAction 5 DL (Some 10));
  w8k_K5 : tm 10 5 = Some (mkAction 2 DR (Some 7))
}.

Lemma w8_stepF_6 : forall tm (hc : Fwpw_8_KCore tm), StepF tm 6 (f_omega_omega_plus 2).
Proof.
  intros tm hc.
  apply (StepF_next tm 6 5 (f_omega_omega_plus 1)
           (fPlus_props _ f_omega_omega_props 1) (w8_stepF_5 tm (w8k_j tm hc))).
  apply (w8_sweep_level tm 10 6 4 (w8k_H6 tm hc) (w8k_K0 tm hc) (w8k_K2 tm hc) (w8k_K3 tm hc) (w8k_K5 tm hc)).
Qed.

(* Level 3: L core (H7 = 6LL, L0 = 3RL, L2=L3 = 6LL, L6 = 2RH) -> f_{ω^ω+3} *)
Record Fwpw_8_LCore (tm : TM) : Prop := mkFwpw_8_LCore {
  w8l_k : Fwpw_8_KCore tm;
  w8l_H7 : tm 7 7 = Some (mkAction 6 DL (Some 11));
  w8l_L0 : tm 11 0 = Some (mkAction 3 DR (Some 11));
  w8l_L2 : tm 11 2 = Some (mkAction 6 DL (Some 11));
  w8l_L3 : tm 11 3 = Some (mkAction 6 DL (Some 11));
  w8l_L6 : tm 11 6 = Some (mkAction 2 DR (Some 7))
}.

Lemma w8_stepF_7 : forall tm (hc : Fwpw_8_LCore tm), StepF tm 7 (f_omega_omega_plus 3).
Proof.
  intros tm hc.
  apply (StepF_next tm 7 6 (f_omega_omega_plus 2)
           (fPlus_props _ f_omega_omega_props 2) (w8_stepF_6 tm (w8l_k tm hc))).
  apply (w8_sweep_level tm 11 7 5 (w8l_H7 tm hc) (w8l_L0 tm hc) (w8l_L2 tm hc) (w8l_L3 tm hc) (w8l_L6 tm hc)).
Qed.

(* Level 4 (9-symbol): M9 core (H8 = 7LM, M0 = 3RM, M2=M3 = 7LM, M7 = 2RH) -> f_{ω^ω+4} *)
Record Fwpw_8_M9Core (tm : TM) : Prop := mkFwpw_8_M9Core {
  w8m9_l : Fwpw_8_LCore tm;
  w8m9_H8 : tm 7 8 = Some (mkAction 7 DL (Some 12));
  w8m9_M0 : tm 12 0 = Some (mkAction 3 DR (Some 12));
  w8m9_M2 : tm 12 2 = Some (mkAction 7 DL (Some 12));
  w8m9_M3 : tm 12 3 = Some (mkAction 7 DL (Some 12));
  w8m9_M7 : tm 12 7 = Some (mkAction 2 DR (Some 7))
}.

Lemma w8_stepF_8 : forall tm (hc : Fwpw_8_M9Core tm), StepF tm 8 (f_omega_omega_plus 4).
Proof.
  intros tm hc.
  apply (StepF_next tm 8 7 (f_omega_omega_plus 3)
           (fPlus_props _ f_omega_omega_props 3) (w8_stepF_7 tm (w8m9_l tm hc))).
  apply (w8_sweep_level tm 12 8 6 (w8m9_H8 tm hc) (w8m9_M0 tm hc) (w8m9_M2 tm hc) (w8m9_M3 tm hc) (w8m9_M7 tm hc)).
Qed.

Lemma f_omega_omega_3_ge_40 : 40 <= f_omega_omega 3.
Proof.
  assert (Hstep_unfold : forall k g n, fOmegaPowStep (S k) g n = iterF (fOmegaPowStep k) n g n) by reflexivity.
  assert (H0_unfold : forall g n, fOmegaPowStep 0 g n = iter g n n) by reflexivity.
  assert (H01 : forall n, fOmegaPowStep 0 fZero n = 2 * n).
  { intro n. rewrite H0_unfold.
    assert (Haux : forall j x, iter fZero j x = j + x) by (induction j; intros; [reflexivity | simpl; rewrite IHj; unfold fZero; lia]).
    rewrite Haux. lia. }
  assert (H1_ge : fOmegaPowStep 1 fZero 3 <= fOmegaPowStep 3 fZero 3).
  { assert (Hup : forall k n, 1 <= n -> fOmegaPowStep k fZero n <= fOmegaPowStep (S k) fZero n).
    { intros k n Hn. rewrite Hstep_unfold.
      destruct n as [| n']; [lia |].
      assert (Hiter_ge : forall m, fOmegaPowStep k fZero (S n') <= iterF (fOmegaPowStep k) (S m) fZero (S n')).
      { induction m as [| m' IHm]; [simpl; lia |].
        eapply Nat.le_trans; [exact IHm |].
        simpl. apply (fOmegaPowStep_ge k (iterF (fOmegaPowStep k) (S m') fZero)); [| lia].
        clear IHm. induction (S m') as [| j IHj]; [exact fZero_props | simpl; apply fOmegaPowStep_props; exact IHj]. }
      apply Hiter_ge. }
    eapply Nat.le_trans; [apply (Hup 1 3 ltac:(lia)) | apply (Hup 2 3 ltac:(lia))]. }
  assert (H1_3 : 40 <= fOmegaPowStep 1 fZero 3).
  { rewrite (Hstep_unfold 0 fZero 3). cbn [iterF].
    assert (H00 : forall x, fOmegaPowStep 0 (fOmegaPowStep 0 fZero) x = iter (fun z => 2 * z) x x).
    { intro x. rewrite H0_unfold.
      clear H1_ge. generalize x at 2 4. induction x as [| k IH]; intro y; [reflexivity | simpl; rewrite H01, IH; reflexivity]. }
    assert (H00_3 : fOmegaPowStep 0 (fOmegaPowStep 0 fZero) 3 = 24) by (rewrite H00; reflexivity).
    assert (H00_ge : forall x, 2 * x <= fOmegaPowStep 0 (fOmegaPowStep 0 fZero) x).
    { intro x. rewrite H00. destruct x as [| x']; [simpl; lia |].
      rewrite iter_succ.
      assert (H2z : forall z, z <= 2 * z) by lia.
      pose proof (iter_ge_self (fun z => 2 * z) H2z x' (S x')). lia. }
    rewrite (H0_unfold (fOmegaPowStep 0 (fOmegaPowStep 0 fZero)) 3), !iter_succ, iter_zero, H00_3.
    pose proof (H00_ge 24).
    pose proof (fgh_ge_self _ (fOmegaPowStep_props 0 _ (fOmegaPowStep_props 0 _ fZero_props)) (fOmegaPowStep 0 (fOmegaPowStep 0 fZero) 24)). lia. }
  unfold f_omega_omega. lia.
Qed.
