(*
  rocq/Fwpw_8_Peeker.v
  Parity-preserving (Odd) peeker ladder on top of Fwpw_8.v.
  Powers BB(14,8), BB(15,8), BB(16,8), BB(16,9).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder.
Import ListNotations.

Definition StepFOdd (tm : TM) (sym : nat) (f : nat -> nat) : Prop :=
  forall n R, 1 <= n ->
    exists n' t, Reaches tm (H8cfg n 1 (sym :: R)) (H8cfg n' 1 R) t /\
                 n + 2 <= n' /\
                 (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * f x <= n' - 2) /\
                 n' <= t /\ Nat.Odd n'.

Lemma StepFOdd_rep : forall tm sym f, FGHProps f -> StepFOdd tm sym f ->
  forall c n R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H8cfg n 1 (rep c sym R)) (H8cfg n' 1 R) t /\
                 n + 2 * c <= n' /\
                 (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * iter f c x <= n' - 2) /\
                 (1 <= c -> n' <= t) /\ Nat.Odd n'.
Proof.
  intros tm sym f Hf Hs. induction c as [| c' IH]; intros n R Hn Ho.
  - exists n, 0. split; [apply reaches_zero | simpl; repeat split; [lia | intros; lia | lia | exact Ho]].
  - destruct (Hs n (rep c' sym R) Hn) as [n1 [t1 [H1 [Hinc1 [Hf1 [Ht1 Ho1]]]]]].
    destruct c' as [| c''].
    + exists n1, t1. simpl in *. split; [exact H1 | repeat split; [lia | intros x Hx H2x; apply Hf1; assumption | intros _; exact Ht1 | exact Ho1]].
    + destruct (IH n1 R ltac:(lia) Ho1) as [n2 [t2 [H2 [Hinc2 [Hf2 [Ht2 Ho2]]]]]].
      exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
      repeat split; [lia | | intros _; specialize (Ht2 ltac:(lia)); lia | exact Ho2].
      intros x Hx H2x.
      replace (iter f (S (S c'')) x) with (iter f (S c'') (f x))
        by (replace (S (S c'')) with (S c'' + 1) by lia; rewrite iter_add; reflexivity).
      apply Hf2; [pose proof (fgh_ge_self _ Hf x); lia | apply Hf1; assumption].
Qed.

Lemma StepFOdd_next : forall tm sym prev_sym f,
  FGHProps f -> StepFOdd tm prev_sym f ->
  (forall n R, 1 <= n -> exists t, Reaches tm (H8cfg n 1 (sym :: R)) (H8cfg 1 1 (rep (S n) prev_sym R)) t) ->
  StepFOdd tm sym (fNext f).
Proof.
  intros tm sym prev_sym f Hf Hprev Hrew n R Hn.
  destruct (Hrew n R Hn) as [t0 H0].
  destruct (Hprev 1 (rep n prev_sym R) ltac:(lia)) as [n1 [t1 [H1 [Hinc1 [_ [_ Ho1]]]]]].
  set (q := n / 2).
  assert (Hdiv : 2 * q <= n /\ n <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod n 2 ltac:(lia)); pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia).
  assert (Hq : n = q + (n - q)) by lia.
  simpl rep in H0. rewrite Hq, rep_add8 in H1.
  replace (rep n prev_sym R) with (rep q prev_sym (rep (n - q) prev_sym R)) in H0 by (rewrite <- rep_add8, <- Hq; reflexivity).
  destruct (StepFOdd_rep tm prev_sym f Hf Hprev q n1 (rep (n - q) prev_sym R) ltac:(lia) Ho1)
    as [n2 [t2 [H2 [Hinc2 [_ [_ Ho2]]]]]].
  destruct (StepFOdd_rep tm prev_sym f Hf Hprev (n - q) n2 R ltac:(lia) Ho2)
    as [n3 [t3 [H3 [Hinc3 [Hf3 [Ht3 Ho3]]]]]].
  exists n3, (t0 + t1 + t2 + t3).
  split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] |].
  repeat split; [lia | | specialize (Ht3 ltac:(lia)); lia | exact Ho3].
  intros x Hx H2x.
  assert (Hxq : x <= q) by lia.
  assert (Hrem : x <= n - q) by lia.
  pose proof (Hf3 x Hx ltac:(lia)) as Hiter.
  pose proof (iter_mono_steps f (fgh_ge_self _ Hf) x (n - q) x Hrem) as Hst.
  unfold fNext. lia.
Qed.

Lemma w8_stepFOdd_2 : forall tm (hc : Fwpw_8_ICore tm), StepFOdd tm 2 f_omega_omega.
Proof.
  intros tm hc n R Hn.
  destruct (le_lt_dec 3 n) as [H3 | Hlt].
  - destruct (w8_rule_2_step tm hc n R ltac:(lia)) as [t1 [H1 _]].
    replace (n - 1) with (S (n - 2)) in H1 by lia.
    pose proof (w8_run_1_rep3_odd tm (w8i_core tm hc) (n - 2) 1) as Hrun1.
    destruct (F8_step_props (n - 2) (fun m => m + 2) (w8_base_mono) (w8_base_inc)) as [Hm1 [Hi1 _]].
    assert (Hrun2 : RunWOdd tm (S (n - 2)) [1; 1; 3] (F8_step (n - 2) (F8_step (n - 2) (fun m => m + 2)))).
    { apply (w8_run_F8_odd tm (w8i_core tm hc)); [constructor; [left; reflexivity | constructor; [right; reflexivity | constructor]] | exact Hm1 | exact Hi1 | exact Hrun1]. }
    destruct (Hrun2 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 [Hge2 [Ht2 Ho']]]]].
    exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
    destruct (F8_step_props (n - 2) (F8_step (n - 2) (fun m => m + 2)) Hm1 Hi1) as [_ [_ [_ Hgg]]].
    pose proof (F8_base_grow (n - 2)) as Hbg.
    pose proof (Hm1 (2 * (n - 2)) (F8_step (n - 2) (fun m => m + 2) 1) ltac:(lia)) as Hstep1.
    assert (Hbz : forall x, 1 <= x -> 2 * fZero x <= 2 * x + 2) by (intros; unfold fZero; lia).
    pose proof (F8_step_ge_fOmegaPowStep (n - 2) fZero (fun m => m + 2) fZero_props
                  w8_base_mono w8_base_inc Hbz (n - 2) ltac:(lia)) as Hstep2.
    pose proof (fgh_gt_pos _ f_omega_omega_props (n - 2) ltac:(lia)) as Hgt.
    unfold f_omega_omega in *.
    repeat split; [lia | | lia | exact Ho'].
    intros x Hx H2x. pose proof (fgh_mono _ f_omega_omega_props x (n - 2) ltac:(lia)).
    unfold f_omega_omega in *. lia.
  - destruct n as [| [| n'']]; [lia | |].
    + destruct (w8_two_step_any tm hc 1 R ltac:(lia)) as [n' [t [H1 [Hinc Ht]]]].
      (* For n = 1, w8_two_step_any literally produced n' = 9 (Odd)! Wait: let's just use w8_rule_2_step for n=2 and explicit 9 for n=1! *)
      clear H1 Hinc Ht n' t.
      assert (H1 : Reaches tm (H8cfg 1 1 (2 :: R)) (mkCfgR (Some 4) [3] (2 :: 4 :: R)) 1)
        by (unfold H8cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_H2 tm hc); reflexivity).
      assert (H2 : Reaches tm (mkCfgR (Some 4) [3] (2 :: 4 :: R)) (mkCfgR (Some 8) [] (3 :: 1 :: 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_E2 tm hc); reflexivity).
      pose proof (w8i_I3_left tm hc 0 (1 :: 4 :: R)) as H3.
      assert (H4 : Reaches tm (mkCfgR (Some 8) [] (0 :: 2 :: 1 :: 4 :: R)) (mkCfgR (Some 8) [3] (2 :: 1 :: 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_I0 tm hc); reflexivity).
      pose proof (w8i_I2_right tm hc 1 [3] (1 :: 4 :: R)) as H5.
      assert (H6 : Reaches tm (mkCfgR (Some 8) [2; 3] (1 :: 4 :: R)) (mkCfgR (Some 1) [3] (2 :: 3 :: 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8i_I1 tm hc); reflexivity).
      destruct (w8_rule_1_low tm (w8i_core tm hc) 1 [] R (Forall_nil _)) as [t7 [H7 Ht7]].
      destruct t7 as [| t7']; [lia |].
      assert (H7' : Reaches tm (mkCfgR (Some 1) [3] (2 :: 3 :: 4 :: R)) (H8cfg 1 1 (4 :: 4 :: 4 :: 4 :: R)) t7').
      { unfold Reaches in H7 |- *. simpl in H7. unfold H8cfg in H7.
        change (match step tm (mkCfgR (Some 7) [2; 3] (1 :: 4 :: R)) with
                | Some c1 => steps tm t7' c1 | None => None end =
                Some (H8cfg 1 1 (4 :: 4 :: 4 :: 4 :: R))) in H7.
        cbn [step mkCfgR cfg_st cfg_cur] in H7. rewrite (w8_H1 tm (w8i_core tm hc)) in H7. exact H7. }
      destruct (w8_rule_4 tm (w8i_core tm hc) 1 1 (4 :: 4 :: 4 :: R) ltac:(lia)) as [t8 [H8 _]].
      destruct (w8_rule_4 tm (w8i_core tm hc) 3 1 (4 :: 4 :: R) ltac:(lia)) as [t9 [H9 _]].
      destruct (w8_rule_4 tm (w8i_core tm hc) 5 1 (4 :: R) ltac:(lia)) as [t10 [H10 _]].
      destruct (w8_rule_4 tm (w8i_core tm hc) 7 1 R ltac:(lia)) as [t11 [H11 Ht11]].
      exists 9, (1 + 1 + 1 + 1 + 1 + 1 + t7' + t8 + t9 + t10 + t11).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7'] | exact H8] | exact H9] | exact H10] | exact H11] | repeat split; [lia | intros; lia | lia | exists 4; lia]].
    + destruct n''; [| lia].
      destruct (w8_rule_2_step tm hc 2 R ltac:(lia)) as [t1 [H1 _]].
      pose proof (w8_run_1_rep3_odd tm (w8i_core tm hc) 0 1) as Hrun1.
      destruct (F8_step_props 0 (fun m => m + 2) w8_base_mono w8_base_inc) as [Hm1 [Hi1 _]].
      assert (Hrun2 : RunWOdd tm 1 [1; 1; 3] (F8_step 0 (F8_step 0 (fun m => m + 2)))).
      { apply (w8_run_F8_odd tm (w8i_core tm hc)); [constructor; [left; reflexivity | constructor; [right; reflexivity | constructor]] | exact Hm1 | exact Hi1 | exact Hrun1]. }
      destruct (Hrun2 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 [Hge2 [Ht2 Ho']]]]].
      destruct (F8_step_props 0 (F8_step 0 (fun m => m + 2)) Hm1 Hi1) as [_ [_ [Hf2 _]]].
      pose proof (Hf2 1 ltac:(lia)). pose proof (Hi1 1).
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | repeat split; [lia | intros; lia | lia | exact Ho']].
Qed.

Lemma w8_stepFOdd_5 : forall tm (hc : Fwpw_8_JCore tm), StepFOdd tm 5 (f_omega_omega_plus 1).
Proof.
  intros tm hc.
  apply (StepFOdd_next tm 5 2 f_omega_omega f_omega_omega_props (w8_stepFOdd_2 tm (w8j_i tm hc))).
  intros n R Hn.
  assert (H1 : Reaches tm (H8cfg n 1 (5 :: R)) (mkCfgR (Some 9) (rep n 3 []) (2 :: 2 :: R)) 1)
    by (unfold H8cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8j_H5 tm hc); reflexivity).
  pose proof (w8_sweep_left_23 tm 9 1 n (2 :: R) (w8j_J2 tm hc) (w8j_J3 tm hc)) as H2.
  assert (H3 : Reaches tm (mkCfgR (Some 9) [] (0 :: rep (S n) 2 (2 :: R))) (mkCfgR (Some 2) [] (rep (S n) 2 (2 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8j_J0 tm hc); reflexivity).
  assert (H4 : Reaches tm (mkCfgR (Some 2) [] (2 :: rep n 2 (2 :: R))) (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C2 tm (w8i_core tm (w8j_i tm hc))); reflexivity).
  assert (H5 : Reaches tm (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: R))) (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C0 tm (w8i_core tm (w8j_i tm hc))); reflexivity).
  assert (H6 : Reaches tm (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: R))) (H8cfg 1 1 (rep (S n) 2 R)) 1)
    by (unfold H8cfg; rewrite rep_r8; apply (w8_step_R tm 1 3 1 (Some 7) [3] (rep (S n) 2 R) (w8_B3 tm (w8i_core tm (w8j_i tm hc))))).
  exists (1 + S n + 1 + 1 + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6].
Qed.

Lemma w8_stepFOdd_6 : forall tm (hc : Fwpw_8_KCore tm), StepFOdd tm 6 (f_omega_omega_plus 2).
Proof.
  intros tm hc.
  apply (StepFOdd_next tm 6 5 (f_omega_omega_plus 1) (fPlus_props _ f_omega_omega_props 1) (w8_stepFOdd_5 tm (w8k_j tm hc))).
  apply (w8_sweep_level tm 10 6 4 (w8k_H6 tm hc) (w8k_K0 tm hc) (w8k_K2 tm hc) (w8k_K3 tm hc) (w8k_K5 tm hc)).
Qed.

(* Peeker StepF7Odd: on ODD n, H8cfg n 1 (7 :: sym :: R) -> H8cfg n' 1 (7 :: R) with Odd n' *)
Definition StepF7Odd (tm : TM) (sym : nat) (f : nat -> nat) : Prop :=
  forall n R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H8cfg n 1 (7 :: sym :: R)) (H8cfg n' 1 (7 :: R)) t /\
                 n + 2 <= n' /\
                 (forall x, 1 <= x -> 4 * x <= n - 2 -> 4 * f x <= n' - 2) /\
                 n' <= t /\ Nat.Odd n'.

Lemma StepF7Odd_rep : forall tm sym f, FGHProps f -> StepF7Odd tm sym f ->
  forall c n R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H8cfg n 1 (7 :: rep c sym R)) (H8cfg n' 1 (7 :: R)) t /\
                 n + 2 * c <= n' /\
                 (forall x, 1 <= x -> 4 * x <= n - 2 -> 4 * iter f c x <= n' - 2) /\
                 (1 <= c -> n' <= t) /\ Nat.Odd n'.
Proof.
  intros tm sym f Hf Hs. induction c as [| c' IH]; intros n R Hn Ho.
  - exists n, 0. split; [apply reaches_zero | simpl; repeat split; [lia | intros; lia | lia | exact Ho]].
  - destruct (Hs n (rep c' sym R) Hn Ho) as [n1 [t1 [H1 [Hinc1 [Hf1 [Ht1 Ho1]]]]]].
    destruct c' as [| c''].
    + exists n1, t1. simpl in *. split; [exact H1 | repeat split; [lia | intros x Hx H4x; apply Hf1; assumption | intros _; exact Ht1 | exact Ho1]].
    + destruct (IH n1 R ltac:(lia) Ho1) as [n2 [t2 [H2 [Hinc2 [Hf2 [Ht2 Ho2]]]]]].
      exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
      repeat split; [lia | | intros _; specialize (Ht2 ltac:(lia)); lia | exact Ho2].
      intros x Hx H4x.
      replace (iter f (S (S c'')) x) with (iter f (S c'') (f x))
        by (replace (S (S c'')) with (S c'' + 1) by lia; rewrite iter_add; reflexivity).
      apply Hf2; [pose proof (fgh_ge_self _ Hf x); lia | apply Hf1; assumption].
Qed.

Lemma f_omega_omega_ge_2n : forall n, 1 <= n -> 2 * n <= f_omega_omega n.
Proof.
  intros n Hn.
  assert (H01 : forall x, fOmegaPowStep 0 fZero x = 2 * x).
  { intro x. change (iter fZero x x = 2 * x).
    assert (Haux : forall j y, iter fZero j y = j + y) by (induction j; intros; [reflexivity | simpl; rewrite IHj; unfold fZero; lia]).
    rewrite Haux. lia. }
  assert (Hup : forall k x, 1 <= x -> fOmegaPowStep 0 fZero x <= fOmegaPowStep k fZero x).
  { induction k as [| k' IH]; intros x Hx; [lia |].
    eapply Nat.le_trans; [apply IH; exact Hx |].
    assert (Hsu : forall j g m, fOmegaPowStep (S j) g m = iterF (fOmegaPowStep j) m g m) by reflexivity.
    rewrite Hsu. destruct x as [| x']; [lia |].
    assert (Hig : forall m, fOmegaPowStep k' fZero (S x') <= iterF (fOmegaPowStep k') (S m) fZero (S x')).
    { induction m as [| m' IHm]; [simpl; lia |].
      eapply Nat.le_trans; [exact IHm |].
      simpl. apply (fOmegaPowStep_ge k' (iterF (fOmegaPowStep k') (S m') fZero)); [| lia].
      clear IHm. induction (S m') as [| j IHj]; [exact fZero_props | simpl; apply fOmegaPowStep_props; exact IHj]. }
    apply Hig. }
  unfold f_omega_omega. pose proof (Hup n n Hn). rewrite H01 in H. exact H.
Qed.

Lemma f_omega_omega_plus_ge_2n : forall k n, 1 <= n -> 2 * n <= f_omega_omega_plus k n.
Proof.
  intros k n Hn.
  assert (Hle : f_omega_omega n <= f_omega_omega_plus k n)
    by (unfold f_omega_omega_plus; apply (fPlus_mono_idx f_omega_omega f_omega_omega_props 0 k n Hn ltac:(lia))).
  pose proof (f_omega_omega_ge_2n n Hn). lia.
Qed.

Lemma w8_peeker_77_odd : forall tm (hc : Fwpw_8_PeekerNCore tm),
  forall n R, 1 <= n ->
    exists n' t, Reaches tm (H8cfg n 1 (7 :: 7 :: R)) (H8cfg n' 1 R) t /\
                 n + 2 <= n' /\
                 (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * f_omega_omega_plus 3 x <= n' - 2) /\
                 n' <= t /\ Nat.Odd n'.
Proof.
  intros tm hc n R Hn.
  assert (H1 : Reaches tm (H8cfg n 1 (7 :: 7 :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (7 :: R)) 1)
    by (unfold H8cfg; apply (w8_step_R tm 7 7 1 (Some 12) _ _ (pn_H7 tm hc))).
  assert (H2 : Reaches tm (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (7 :: R)) (mkCfgR (Some 11) (2 :: rep n 3 []) (2 :: 6 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pn_M7 tm hc); reflexivity).
  assert (H3 : Reaches tm (mkCfgR (Some 11) (2 :: rep n 3 []) (2 :: 6 :: R)) (mkCfgR (Some 11) (rep n 3 []) (2 :: 6 :: 6 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pn_L2 tm hc); reflexivity).
  pose proof (w8_sweep_left_23 tm 11 5 n (6 :: 6 :: R) (pn_L2 tm hc) (pn_L3 tm hc)) as H4.
  assert (H5 : Reaches tm (mkCfgR (Some 11) [] (0 :: rep (S n) 6 (6 :: 6 :: R))) (mkCfgR (Some 11) [3] (rep (S n) 6 (6 :: 6 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pn_L0 tm hc); reflexivity).
  assert (H6 : Reaches tm (mkCfgR (Some 11) [3] (6 :: rep n 6 (6 :: 6 :: R))) (H8cfg 1 1 (rep (S (S n)) 6 R)) 1)
    by (unfold H8cfg; rewrite !rep_r8; apply (w8_step_R tm 11 6 1 (Some 7) [3] _ (pn_L6 tm hc))).
  pose proof (w8_stepFOdd_6 tm (pn_k tm hc)) as Hs6.
  destruct (Hs6 1 (rep (S n) 6 R) ltac:(lia)) as [n1 [t7 [H7 [Hinc7 [_ [_ Ho1]]]]]].
  set (q := S n / 2).
  assert (Hdiv : 2 * q <= S n /\ S n <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod (S n) 2 ltac:(lia)); pose proof (Nat.mod_upper_bound (S n) 2 ltac:(lia)); lia).
  assert (Hq : S n = q + (S n - q)) by lia.
  change (Reaches tm (mkCfgR (Some 11) [3] (6 :: rep n 6 (6 :: 6 :: R))) (H8cfg 1 1 (6 :: rep (S n) 6 R)) 1) in H6.
  replace (rep (S n) 6 R) with (rep q 6 (rep (S n - q) 6 R)) in H6, H7 by (rewrite <- rep_add8, <- Hq; reflexivity).
  destruct (StepFOdd_rep tm 6 (f_omega_omega_plus 2) (fPlus_props _ f_omega_omega_props 2) Hs6 q n1 (rep (S n - q) 6 R) ltac:(lia) Ho1)
    as [n2 [t8 [H8 [Hinc8 [_ [_ Ho2]]]]]].
  destruct (StepFOdd_rep tm 6 (f_omega_omega_plus 2) (fPlus_props _ f_omega_omega_props 2) Hs6 (S n - q) n2 R ltac:(lia) Ho2)
    as [n3 [t9 [H9 [Hinc9 [Hf9 [Ht9 Ho3]]]]]].
  exists n3, (1 + 1 + 1 + S n + 1 + 1 + t7 + t8 + t9).
  split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] |].
  repeat split; [lia | | specialize (Ht9 ltac:(lia)); lia | exact Ho3].
  intros x Hx H2x.
  assert (Hxq : x <= q) by lia.
  assert (Hrem : x <= S n - q) by lia.
  pose proof (Hf9 x Hx ltac:(lia)) as Hiter.
  pose proof (iter_mono_steps (f_omega_omega_plus 2) (fgh_ge_self _ (fPlus_props _ f_omega_omega_props 2)) x (S n - q) x Hrem) as Hst.
  assert (Heq : forall k m, f_omega_omega_plus (S k) m = iter (f_omega_omega_plus k) m m) by reflexivity.
  rewrite (Heq 2 x). lia.
Qed.

Lemma w8_peeker_77_pairs : forall tm (hc : Fwpw_8_PeekerNCore tm),
  forall c n R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H8cfg n 1 (rep (2 * c) 7 R)) (H8cfg n' 1 R) t /\
                 n + 2 * c <= n' /\
                 (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * iter (f_omega_omega_plus 3) c x <= n' - 2) /\
                 (1 <= c -> n' <= t) /\ Nat.Odd n'.
Proof.
  intros tm hc. induction c as [| c' IH]; intros n R Hn Ho.
  - exists n, 0. split; [apply reaches_zero | simpl; repeat split; [lia | intros; lia | lia | exact Ho]].
  - replace (2 * S c') with (2 + 2 * c') by lia. rewrite rep_add8. simpl rep.
    destruct (w8_peeker_77_odd tm hc n (rep (2 * c') 7 R) Hn) as [n1 [t1 [H1 [Hinc1 [Hf1 [Ht1 Ho1]]]]]].
    destruct c' as [| c''].
    + exists n1, t1. simpl in *. split; [exact H1 | repeat split; [lia | intros x Hx H2x; apply Hf1; assumption | intros _; exact Ht1 | exact Ho1]].
    + destruct (IH n1 R ltac:(lia) Ho1) as [n2 [t2 [H2 [Hinc2 [Hf2 [Ht2 Ho2]]]]]].
      exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
      repeat split; [lia | | intros _; specialize (Ht2 ltac:(lia)); lia | exact Ho2].
      intros x Hx H2x.
      replace (iter (f_omega_omega_plus 3) (S (S c'')) x) with (iter (f_omega_omega_plus 3) (S c'') (f_omega_omega_plus 3 x))
        by (replace (S (S c'')) with (S c'' + 1) by lia; rewrite iter_add; reflexivity).
      apply Hf2; [pose proof (fgh_ge_self _ (fPlus_props _ f_omega_omega_props 3) x); unfold f_omega_omega_plus; lia | apply Hf1; assumption].
Qed.

Lemma w8_peeker_6_odd : forall tm (hc : Fwpw_8_PeekerNCore tm), StepF7Odd tm 6 (f_omega_omega_plus 4).
Proof.
  intros tm hc n R Hn [p Hp].
  assert (H1 : Reaches tm (H8cfg n 1 (7 :: 6 :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (6 :: R)) 1)
    by (unfold H8cfg; apply (w8_step_R tm 7 7 1 (Some 12) _ _ (pn_H7 tm hc))).
  assert (H2 : Reaches tm (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (6 :: R)) (mkCfgR (Some 13) (2 :: rep n 3 []) (2 :: 7 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pn_M6 tm hc); reflexivity).
  assert (H3 : Reaches tm (mkCfgR (Some 13) (2 :: rep n 3 []) (2 :: 7 :: R)) (mkCfgR (Some 13) (rep n 3 []) (2 :: 7 :: 7 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pn_N2 tm hc); reflexivity).
  pose proof (w8_sweep_left_23 tm 13 6 n (7 :: 7 :: R) (pn_N2 tm hc) (pn_N3 tm hc)) as H4.
  assert (H5 : Reaches tm (mkCfgR (Some 13) [] (0 :: rep (S n) 7 (7 :: 7 :: R))) (mkCfgR (Some 13) [3] (rep (S n) 7 (7 :: 7 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pn_N0 tm hc); reflexivity).
  assert (H6 : Reaches tm (mkCfgR (Some 13) [3] (7 :: rep n 7 (7 :: 7 :: R))) (H8cfg 1 1 (rep (2 * (S p)) 7 (7 :: R))) 1).
  { unfold H8cfg; rewrite !rep_r8. replace (S (S n)) with (S (2 * S p)) by lia.
    rewrite <- rep_r8. apply (w8_step_R tm 13 7 1 (Some 7) [3] _ (pn_N7 tm hc)). }
  set (q := S p / 2).
  assert (Hdiv : 2 * q <= S p /\ S p <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod (S p) 2 ltac:(lia)); pose proof (Nat.mod_upper_bound (S p) 2 ltac:(lia)); lia).
  assert (Hq : 2 * S p = 2 * q + 2 * (S p - q)) by lia.
  rewrite Hq, rep_add8 in H6.
  destruct (w8_peeker_77_pairs tm hc q 1 (rep (2 * (S p - q)) 7 (7 :: R)) ltac:(lia) (ex_intro _ 0 eq_refl))
    as [n1 [t7 [H7 [Hinc7 [_ [_ Ho1]]]]]].
  destruct (w8_peeker_77_pairs tm hc (S p - q) n1 (7 :: R) ltac:(lia) Ho1)
    as [n2 [t8 [H8 [Hinc8 [Hf8 [Ht8 Ho2]]]]]].
  exists n2, (1 + 1 + 1 + S n + 1 + 1 + t7 + t8).
  split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] |].
  repeat split; [lia | | specialize (Ht8 ltac:(lia)); lia | exact Ho2].
  intros x Hx H4x.
  assert (Hxq : x <= q) by lia.
  assert (Hrem : S x <= S p - q) by lia.
  pose proof (Hf8 x Hx ltac:(lia)) as Hiter.
  pose proof (iter_mono_steps (f_omega_omega_plus 3) (fgh_ge_self _ (fPlus_props _ f_omega_omega_props 3)) (S x) (S p - q) x Hrem) as Hst.
  rewrite iter_succ in Hst.
  pose proof (f_omega_omega_plus_ge_2n 3 (iter (f_omega_omega_plus 3) x x) ltac:(pose proof (iter_ge_self (f_omega_omega_plus 3) (fgh_ge_self _ (fPlus_props _ f_omega_omega_props 3)) x x); lia)).
  assert (Heq : forall k m, f_omega_omega_plus (S k) m = iter (f_omega_omega_plus k) m m) by reflexivity.
  rewrite (Heq 3 x). lia.
Qed.

(* Generic StepF7Odd_next for O (5) and P (2) *)
Lemma StepF7Odd_next : forall tm sym prev_sym k,
  StepF7Odd tm prev_sym (f_omega_omega_plus k) ->
  (forall n R, 1 <= n -> Nat.Odd n -> exists n1 t, Reaches tm (H8cfg n 1 (7 :: sym :: R)) (H8cfg n1 1 (7 :: rep n prev_sym R)) t /\ 3 <= n1 /\ Nat.Odd n1) ->
  StepF7Odd tm sym (f_omega_omega_plus (S k)).
Proof.
  intros tm sym prev_sym k Hprev Hrew n R Hn Ho.
  destruct (Hrew n R Hn Ho) as [n1 [t0 [H0 [Hn1 Ho1]]]].
  set (q := n / 2).
  assert (Hdiv : 2 * q <= n /\ n <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod n 2 ltac:(lia)); pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia).
  assert (Hq : n = q + (n - q)) by lia.
  replace (rep n prev_sym R) with (rep q prev_sym (rep (n - q) prev_sym R)) in H0 by (rewrite <- rep_add8, <- Hq; reflexivity).
  destruct (StepF7Odd_rep tm prev_sym (f_omega_omega_plus k) (fPlus_props _ f_omega_omega_props k) Hprev q n1 (rep (n - q) prev_sym R) ltac:(lia) Ho1)
    as [n2 [t2 [H2 [Hinc2 [_ [_ Ho2]]]]]].
  destruct (StepF7Odd_rep tm prev_sym (f_omega_omega_plus k) (fPlus_props _ f_omega_omega_props k) Hprev (n - q) n2 R ltac:(lia) Ho2)
    as [n3 [t3 [H3 [Hinc3 [Hf3 [Ht3 Ho3]]]]]].
  exists n3, (t0 + t2 + t3).
  split; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H2] | exact H3] |].
  repeat split; [lia | | specialize (Ht3 ltac:(lia)); lia | exact Ho3].
  intros x Hx H4x.
  assert (Hxq : 2 * x <= q) by lia.
  assert (Hrem : x <= n - q) by lia.
  pose proof (Hf3 x Hx ltac:(lia)) as Hiter.
  pose proof (iter_mono_steps (f_omega_omega_plus k) (fgh_ge_self _ (fPlus_props _ f_omega_omega_props k)) x (n - q) x Hrem) as Hst.
  assert (Heq : forall j m, f_omega_omega_plus (S j) m = iter (f_omega_omega_plus j) m m) by reflexivity.
  rewrite (Heq k x). lia.
Qed.

(* Peeker O core (BB15_8, BB16_8, BB16_9) *)
Record Fwpw_8_PeekerOCore (tm : TM) : Prop := mkFwpw_8_PeekerOCore {
  po_n : Fwpw_8_PeekerNCore tm;
  po_M5 : tm 12 5 = Some (mkAction 6 DL (Some 14));
  po_O0 : tm 14 0 = Some (mkAction 3 DR (Some 13));
  po_O2 : tm 14 2 = Some (mkAction 6 DL (Some 14));
  po_O3 : tm 14 3 = Some (mkAction 6 DL (Some 14));
  po_O6 : tm 14 6 = Some (mkAction 2 DR (Some 12));
  po_N6 : tm 13 6 = Some (mkAction 2 DR (Some 14))
}.

Lemma w8_peeker_5_odd : forall tm (hc : Fwpw_8_PeekerOCore tm), StepF7Odd tm 5 (f_omega_omega_plus 5).
Proof.
  intros tm hc.
  apply (StepF7Odd_next tm 5 6 4 (w8_peeker_6_odd tm (po_n tm hc))).
  intros n R Hn Ho.
  assert (H1 : Reaches tm (H8cfg n 1 (7 :: 5 :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (5 :: R)) 1)
    by (unfold H8cfg; apply (w8_step_R tm 7 7 1 (Some 12) _ _ (pn_H7 tm (po_n tm hc)))).
  assert (H2 : Reaches tm (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (5 :: R)) (mkCfgR (Some 14) (2 :: rep n 3 []) (2 :: 6 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (po_M5 tm hc); reflexivity).
  assert (H3 : Reaches tm (mkCfgR (Some 14) (2 :: rep n 3 []) (2 :: 6 :: R)) (mkCfgR (Some 14) (rep n 3 []) (2 :: 6 :: 6 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (po_O2 tm hc); reflexivity).
  pose proof (w8_sweep_left_23 tm 14 5 n (6 :: 6 :: R) (po_O2 tm hc) (po_O3 tm hc)) as H4.
  assert (H5 : Reaches tm (mkCfgR (Some 14) [] (0 :: rep (S n) 6 (6 :: 6 :: R))) (mkCfgR (Some 13) [3] (rep (S n) 6 (6 :: 6 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (po_O0 tm hc); reflexivity).
  assert (H6 : Reaches tm (mkCfgR (Some 13) [3] (6 :: rep n 6 (6 :: 6 :: R))) (mkCfgR (Some 14) [2; 3] (rep n 6 (6 :: 6 :: R))) 1)
    by (apply (w8_step_R tm 13 6 1 (Some 14) [3] _ (po_N6 tm hc))).
  assert (H7 : Reaches tm (mkCfgR (Some 14) [2; 3] (6 :: rep n 6 (6 :: R))) (mkCfgR (Some 12) [2; 2; 3] (rep n 6 (6 :: R))) 1)
    by (apply (w8_step_R tm 14 6 1 (Some 12) [2; 3] _ (po_O6 tm hc))).
  (* Now at mkCfgR (Some 12) [2; 2; 3] (6 :: rep n 6 R), which is 1 step after H8cfg 1 1 (7 :: 6 :: rep n 6 R)!
     Apply w8_peeker_6_odd at n=1! *)
  destruct (w8_peeker_6_odd tm (po_n tm hc) 1 (rep n 6 R) ltac:(lia) (ex_intro _ 0 eq_refl)) as [n1 [t8 [H8 [Hinc8 [_ [Ht8 Ho1]]]]]].
  destruct t8 as [| t8']; [lia |].
  assert (H8' : Reaches tm (mkCfgR (Some 12) [2; 2; 3] (6 :: rep n 6 R)) (H8cfg n1 1 (7 :: rep n 6 R)) t8').
  { unfold Reaches in H8 |- *. simpl in H8. unfold H8cfg in H8.
    change (match step tm (mkCfgR (Some 7) [2; 3] (7 :: 6 :: rep n 6 R)) with
            | Some c1 => steps tm t8' c1 | None => None end = Some (H8cfg n1 1 (7 :: rep n 6 R))) in H8.
    cbn [step mkCfgR cfg_st cfg_cur] in H8. rewrite (pn_H7 tm (po_n tm hc)) in H8. exact H8. }
  exists n1, (1 + 1 + 1 + S n + 1 + 1 + 1 + t8').
  split.
  - rewrite !rep_r8 in H4; rewrite !rep_r8 in H5; rewrite !rep_r8 in H6; rewrite !rep_r8 in H7.
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8'].
  - split; [lia | exact Ho1].
Qed.

(* Peeker P core (BB16_8, BB16_9) *)
Record Fwpw_8_PeekerPCore (tm : TM) : Prop := mkFwpw_8_PeekerPCore {
  pp_o : Fwpw_8_PeekerOCore tm;
  pp_M2 : tm 12 2 = Some (mkAction 5 DL (Some 15));
  pp_P0 : tm 15 0 = Some (mkAction 3 DR (Some 14));
  pp_P2 : tm 15 2 = Some (mkAction 5 DL (Some 15));
  pp_P3 : tm 15 3 = Some (mkAction 5 DL (Some 15));
  pp_P5 : tm 15 5 = Some (mkAction 2 DR (Some 12));
  pp_O5 : tm 14 5 = Some (mkAction 2 DR (Some 15))
}.

Lemma w8_peeker_2_odd : forall tm (hc : Fwpw_8_PeekerPCore tm), StepF7Odd tm 2 (f_omega_omega_plus 6).
Proof.
  intros tm hc.
  apply (StepF7Odd_next tm 2 5 5 (w8_peeker_5_odd tm (pp_o tm hc))).
  intros n R Hn Ho.
  assert (H1 : Reaches tm (H8cfg n 1 (7 :: 2 :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (2 :: R)) 1)
    by (unfold H8cfg; apply (w8_step_R tm 7 7 1 (Some 12) _ _ (pn_H7 tm (po_n tm (pp_o tm hc))))).
  assert (H2 : Reaches tm (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (2 :: R)) (mkCfgR (Some 15) (2 :: rep n 3 []) (2 :: 5 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pp_M2 tm hc); reflexivity).
  assert (H3 : Reaches tm (mkCfgR (Some 15) (2 :: rep n 3 []) (2 :: 5 :: R)) (mkCfgR (Some 15) (rep n 3 []) (2 :: 5 :: 5 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pp_P2 tm hc); reflexivity).
  pose proof (w8_sweep_left_23 tm 15 4 n (5 :: 5 :: R) (pp_P2 tm hc) (pp_P3 tm hc)) as H4.
  assert (H5 : Reaches tm (mkCfgR (Some 15) [] (0 :: rep (S n) 5 (5 :: 5 :: R))) (mkCfgR (Some 14) [3] (rep (S n) 5 (5 :: 5 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (pp_P0 tm hc); reflexivity).
  assert (H6 : Reaches tm (mkCfgR (Some 14) [3] (5 :: rep n 5 (5 :: 5 :: R))) (mkCfgR (Some 15) [2; 3] (rep n 5 (5 :: 5 :: R))) 1)
    by (apply (w8_step_R tm 14 5 1 (Some 15) [3] _ (pp_O5 tm hc))).
  assert (H7 : Reaches tm (mkCfgR (Some 15) [2; 3] (5 :: rep n 5 (5 :: R))) (mkCfgR (Some 12) [2; 2; 3] (rep n 5 (5 :: R))) 1)
    by (apply (w8_step_R tm 15 5 1 (Some 12) [2; 3] _ (pp_P5 tm hc))).
  destruct (w8_peeker_5_odd tm (pp_o tm hc) 1 (rep n 5 R) ltac:(lia) (ex_intro _ 0 eq_refl)) as [n1 [t8 [H8 [Hinc8 [_ [Ht8 Ho1]]]]]].
  destruct t8 as [| t8']; [lia |].
  assert (H8' : Reaches tm (mkCfgR (Some 12) [2; 2; 3] (5 :: rep n 5 R)) (H8cfg n1 1 (7 :: rep n 5 R)) t8').
  { unfold Reaches in H8 |- *. simpl in H8. unfold H8cfg in H8.
    change (match step tm (mkCfgR (Some 7) [2; 3] (7 :: 5 :: rep n 5 R)) with
            | Some c1 => steps tm t8' c1 | None => None end = Some (H8cfg n1 1 (7 :: rep n 5 R))) in H8.
    cbn [step mkCfgR cfg_st cfg_cur] in H8. rewrite (pn_H7 tm (po_n tm (pp_o tm hc))) in H8. exact H8. }
  exists n1, (1 + 1 + 1 + S n + 1 + 1 + 1 + t8').
  split.
  - rewrite !rep_r8 in H4; rewrite !rep_r8 in H5; rewrite !rep_r8 in H6; rewrite !rep_r8 in H7.
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8'].
  - split; [lia | exact Ho1].
Qed.
