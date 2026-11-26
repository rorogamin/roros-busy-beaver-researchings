(*
  rocq/Fwpw_5_Ladder.v
  Reusable Rocq 9.1 f_{ω^ω+k} ladder on top of Fwpw_5.v.
  Powers all 8 genuine Fwpw_5/6/7 champions: BB(13,5), BB(15..16,5), BB(13,6), BB(15..16,6), BB(13..14,7).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_5 Fwpw_8_Peeker.
Import ListNotations.

Definition StepF5 (tm : TM) (sA sym : nat) (f : nat -> nat) : Prop :=
  forall n R, 1 <= n ->
    exists n' t, Reaches tm (H5cfg sA n 1 (sym :: R)) (H5cfg sA n' 1 R) t /\
                 n + 2 <= n' /\
                 (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * f x <= n' - 2) /\
                 n' <= t.

Lemma StepF5_rep : forall tm sA sym f, FGHProps f -> StepF5 tm sA sym f ->
  forall c n R, 1 <= n ->
    exists n' t, Reaches tm (H5cfg sA n 1 (rep c sym R)) (H5cfg sA n' 1 R) t /\
                 n + 2 * c <= n' /\
                 (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * iter f c x <= n' - 2) /\
                 (1 <= c -> n' <= t).
Proof.
  intros tm sA sym f Hf Hs. induction c as [| c' IH]; intros n R Hn.
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

Lemma StepF5_next : forall tm sA sym prev_sym f,
  FGHProps f -> StepF5 tm sA prev_sym f ->
  (forall n R, 1 <= n -> exists t, Reaches tm (H5cfg sA n 1 (sym :: R)) (H5cfg sA 1 1 (rep (S n) prev_sym R)) t) ->
  StepF5 tm sA sym (fNext f).
Proof.
  intros tm sA sym prev_sym f Hf Hprev Hrew n R Hn.
  destruct (Hrew n R Hn) as [t0 H0].
  destruct (Hprev 1 (rep n prev_sym R) ltac:(lia)) as [n1 [t1 [H1 [Hinc1 [_ _]]]]].
  set (q := n / 2).
  assert (Hdiv : 2 * q <= n /\ n <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod n 2 ltac:(lia)); pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia).
  assert (Hq : n = q + (n - q)) by lia.
  simpl rep in H0. rewrite Hq, rep_add8 in H1.
  replace (rep n prev_sym R) with (rep q prev_sym (rep (n - q) prev_sym R)) in H0 by (rewrite <- rep_add8, <- Hq; reflexivity).
  destruct (StepF5_rep tm sA prev_sym f Hf Hprev q n1 (rep (n - q) prev_sym R) ltac:(lia))
    as [n2 [t2 [H2 [Hinc2 [_ _]]]]].
  destruct (StepF5_rep tm sA prev_sym f Hf Hprev (n - q) n2 R ltac:(lia))
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

(* Generic base rewrite: 3^n 2^1 sA> sym_base R -> 3^1 2^{S n} sA> 1 4 R *)
Lemma w5_base_rewrite : forall tm sA sB sC sD sE sF sG sH sI sJ sK sL sym_base,
  Fwpw_5Core tm sA sB sC sD sE sF sG sH sI sJ sK sL ->
  tm sA sym_base = Some (mkAction 4 DL (Some sH)) ->
  tm sI 0 = Some (mkAction 2 DR (Some sC)) ->
  forall n R, 1 <= n ->
    exists t, Reaches tm (H5cfg sA n 1 (sym_base :: R)) (H5cfg sA 1 (S n) (1 :: 4 :: R)) t.
Proof.
  intros tm sA sB sC sD sE sF sG sH sI sJ sK sL sym_base hc HsA HsI n R Hn.
  destruct n as [| n']; [lia |].
  assert (H1 : Reaches tm (H5cfg sA (S n') 1 (sym_base :: R)) (mkCfgR (Some sH) (rep (S n') 3 []) (2 :: 4 :: R)) 1)
    by (unfold H5cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite HsA; reflexivity).
  assert (H2 : Reaches tm (mkCfgR (Some sH) (3 :: rep n' 3 []) (2 :: 4 :: R)) (mkCfgR (Some sG) (rep n' 3 []) (3 :: 1 :: 4 :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_H2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
  assert (Hgi : forall a R0,
    Reaches tm (mkCfgR (Some sG) (rep a 3 []) (3 :: R0)) (mkCfgR (Some sI) [] (0 :: rep a 3 (2 :: R0))) (a + 1)).
  { intros a R0. destruct a as [| a'].
    - apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_G3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity.
    - assert (Hg1 : Reaches tm (mkCfgR (Some sG) (3 :: rep a' 3 []) (3 :: R0)) (mkCfgR (Some sI) (rep a' 3 []) (3 :: 2 :: R0)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_G3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (Hi : forall k R1, Reaches tm (mkCfgR (Some sI) (rep k 3 []) (3 :: R1)) (mkCfgR (Some sI) [] (0 :: rep (S k) 3 R1)) (S k)).
      { induction k as [| k' IHk]; intros R1.
        - apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_I3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity.
        - replace (S (S k')) with (1 + S k') by lia.
          eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_I3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity |].
          specialize (IHk (3 :: R1)). rewrite rep_r8 in IHk. exact IHk. }
      replace (S a' + 1) with (1 + S a') by lia.
      eapply reaches_trans; [exact Hg1 | apply (Hi a' (2 :: R0))]. }
  pose proof (Hgi n' (1 :: 4 :: R)) as H3.
  assert (H4 : Reaches tm (mkCfgR (Some sI) [] (0 :: rep n' 3 (2 :: 1 :: 4 :: R)))
                          (mkCfgR (Some sC) [2] (rep n' 3 (2 :: 1 :: 4 :: R))) 1)
    by (apply (w8_step_R tm sI 0 1 (Some sC) [] (rep n' 3 (2 :: 1 :: 4 :: R)) HsI)).
  pose proof (w5_C3_right tm sA sB sC sD sE sF sG sH sI sJ sK sL hc n' [2] (2 :: 1 :: 4 :: R)) as H5.
  rewrite rep_r8 in H5.
  pose proof (w5_C2_left tm sA sB sC sD sE sF sG sH sI sJ sK sL hc (S n') [] (1 :: 4 :: R)) as H6.
  assert (H7 : Reaches tm (mkCfgR (Some sC) [] (2 :: rep (S n') 3 (1 :: 4 :: R)))
                          (mkCfgR (Some sC) [] (0 :: rep (S (S n')) 3 (1 :: 4 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
  assert (H8 : Reaches tm (mkCfgR (Some sC) [] (0 :: rep (S (S n')) 3 (1 :: 4 :: R)))
                          (mkCfgR (Some sB) [3] (rep (S (S n')) 3 (1 :: 4 :: R))) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
  assert (H9 : Reaches tm (mkCfgR (Some sB) [3] (3 :: rep (S n') 3 (1 :: 4 :: R)))
                          (H5cfg sA 1 1 (rep (S n') 3 (1 :: 4 :: R))) 1)
    by (unfold H5cfg; apply (w8_step_R tm sB 3 1 (Some sA) [3] _ (w5_B3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc))).
  pose proof (w5_rule_3_rep tm sA sB sC sD sE sF sG sH sI sJ sK sL hc (S n') 1 1 (1 :: 4 :: R)) as H10.
  replace (S n' + 1) with (S (S n')) in H10 by lia.
  exists (1 + 1 + (n' + 1) + 1 + n' + S n' + 1 + 1 + 1 + S n').
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | exact H10].
Qed.

(* Generic base f_{ω^ω} step: if H5cfg sA n 1 (sym :: R) -> H5cfg sA 1 (S n) (1 :: 4 :: R), then StepF5 tm sA sym f_omega_omega *)
Lemma w5_stepF_omega_omega : forall tm sA sB sC sD sE sF sG sH sI sJ sK sL sym,
  Fwpw_5Core tm sA sB sC sD sE sF sG sH sI sJ sK sL ->
  (forall n R, 1 <= n -> exists t, Reaches tm (H5cfg sA n 1 (sym :: R)) (H5cfg sA 1 (S n) (1 :: 4 :: R)) t) ->
  StepF5 tm sA sym f_omega_omega.
Proof.
  intros tm sA sB sC sD sE sF sG sH sI sJ sK sL sym hc Hrew n R Hn.
  destruct (Hrew n R Hn) as [t0 H0].
  destruct (w5_rule_1_high tm sA sB sC sD sE sF sG sH sI sJ sK sL hc 1 n (4 :: R) Hn) as [t1 [H1 _]].
  destruct n as [| n']; [lia |].
  assert (Hrun0 : RunW5 tm sA (S n') [3] (fun m => m + 2))
    by (apply (runW5_3 tm sA sB sC sD sE sF sG sH sI sJ sK sL hc); apply (runW5_nil tm sA sB sC sD sE sF sG sH sI sJ sK sL hc); lia).
  assert (Hrun1 : RunW5 tm sA (S n') [1; 3] (F8_step n' (fun m => m + 2)))
    by (apply (w5_run_F8 tm sA sB sC sD sE sF sG sH sI sJ sK sL hc); [constructor; [right; reflexivity | constructor] | exact w8_base_mono | exact w8_base_inc | exact Hrun0]).
  destruct (F8_step_props n' (fun m => m + 2) w8_base_mono w8_base_inc) as [Hm1 [Hi1 _]].
  assert (Hrun2 : RunW5 tm sA (S n') [1; 1; 3] (F8_step n' (F8_step n' (fun m => m + 2))))
    by (apply (w5_run_F8 tm sA sB sC sD sE sF sG sH sI sJ sK sL hc); [constructor; [left; reflexivity | constructor; [right; reflexivity | constructor]] | exact Hm1 | exact Hi1 | exact Hrun1]).
  destruct (Hrun2 1 R ltac:(lia)) as [n'0 [t2 [H2 [Hge2 Ht2]]]].
  exists n'0, (t0 + t1 + t2).
  split; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] |].
  destruct (F8_step_props n' (F8_step n' (fun m => m + 2)) Hm1 Hi1) as [_ [_ [Hf2 Hgg]]].
  pose proof (F8_base_grow n') as Hbg.
  pose proof (Hm1 (2 * n') (F8_step n' (fun m => m + 2) 1) ltac:(lia)) as Hstep1.
  destruct n' as [| n''].
  - pose proof (Hf2 1 ltac:(lia)). pose proof (Hi1 1). repeat split; [lia | intros; lia | lia].
  - assert (Hbz : forall x, 1 <= x -> 2 * fZero x <= 2 * x + 2) by (intros; unfold fZero; lia).
    pose proof (F8_step_ge_fOmegaPowStep (S n'') fZero (fun m => m + 2) fZero_props
                  w8_base_mono w8_base_inc Hbz (S n'') ltac:(lia)) as Hstep2.
    pose proof (fgh_gt_pos _ f_omega_omega_props (S n'') ltac:(lia)) as Hgt.
    unfold f_omega_omega in *.
    repeat split; [lia | | lia].
    intros x Hx H2x. pose proof (fgh_mono _ f_omega_omega_props x (S n'') ltac:(lia)).
    unfold f_omega_omega in *. lia.
Qed.

(* Parity-preserving RunW5Odd on Fwpw_5Core *)
Section Fwpw_5_Odd.
  Variable tm : TM.
  Variables sA sB sC sD sE sF sG sH sI sJ sK sL : nat.
  Hypothesis hc : Fwpw_5Core tm sA sB sC sD sE sF sG sH sI sJ sK sL.

  Definition RunW5Odd (k : nat) (w : list nat) (f : nat -> nat) : Prop :=
    forall m R, 1 <= m -> Nat.Odd m ->
      exists n' t, Reaches tm (H5cfg sA m k (w ++ 4 :: R)) (H5cfg sA n' 1 R) t /\
                   f m <= n' /\ n' <= t /\ Nat.Odd n'.

  Lemma runW5Odd_rep_app : forall f w,
    (forall x y, x <= y -> f x <= f y) -> (forall x, x <= f x) -> RunW5Odd 1 w f ->
    forall c m R, 1 <= m -> Nat.Odd m ->
      exists n' t, Reaches tm (H5cfg sA m 1 (rep_app c (w ++ [4]) R)) (H5cfg sA n' 1 R) t /\
                   iter f c m <= n' /\ (1 <= c -> n' <= t) /\ Nat.Odd n'.
  Proof.
    intros f w Hmono Hself Hw. induction c as [| c' IH]; intros m R Hm Ho.
    - exists m, 0. split; [apply reaches_zero | simpl; repeat split; [lia | lia | exact Ho]].
    - simpl rep_app. rewrite <- app_assoc. simpl.
      destruct (Hw m (rep_app c' (w ++ [4]) R) Hm Ho) as [n1 [t1 [H1 [Hf1 [Ht1 Ho1]]]]].
      destruct c' as [| c''].
      + exists n1, t1. simpl in *. split; [exact H1 | repeat split; [lia | lia | exact Ho1]].
      + assert (Hn1 : 1 <= n1) by (pose proof (Hself m); lia).
        destruct (IH n1 R Hn1 Ho1) as [n2 [t2 [H2 [Hf2 [Ht2 Ho2]]]]].
        exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
        repeat split; [| intros _; specialize (Ht2 ltac:(lia)); lia | exact Ho2].
        assert (Hsh : f (iter f (S c'') m) = iter f (S c'') (f m)).
        { change (iter f (S (S c'')) m = iter f (S c'') (f m)).
          replace (S (S c'')) with (S c'' + 1) by lia. rewrite iter_add. reflexivity. }
        rewrite Hsh.
        eapply Nat.le_trans; [apply iter_mono_arg; [exact Hmono | exact Hf1] | exact Hf2].
  Qed.

  Lemma w5_run_F8_odd : forall k w f,
    W8Word w -> (forall x y, x <= y -> f x <= f y) -> (forall x, x + 2 <= f x) ->
    RunW5Odd (S k) w f ->
    RunW5Odd (S k) (1 :: w) (F8_step k f).
  Proof.
    induction k as [| k' IH]; intros w f Hw Hmono Hinc Hrun m R Hm Ho.
    - destruct (w5_rule_1_low tm sA sB sC sD sE sF sG sH sI sJ sK sL hc m w R Hw) as [t1 [H1 _]].
      destruct (runW5Odd_rep_app f w Hmono (fun x => ltac:(pose proof (Hinc x); lia)) Hrun (m + 3) 1 R ltac:(lia) (ex_intro _ 0 eq_refl))
        as [n' [t2 [H2 [Hf2 [Ht2 Ho']]]]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | repeat split; [exact Hf2 | specialize (Ht2 ltac:(lia)); lia | exact Ho']].
    - destruct (w5_rule_1_high tm sA sB sC sD sE sF sG sH sI sJ sK sL hc m (S k') (w ++ 4 :: R) ltac:(lia)) as [t1 [H1 _]].
      assert (Hrep1 : forall c,
        RunW5Odd (S k') (rep c 1 (3 :: w)) (iterF (F8_step k') c f) /\
        (forall x y, x <= y -> iterF (F8_step k') c f x <= iterF (F8_step k') c f y) /\
        (forall x, x + 2 <= iterF (F8_step k') c f x)).
      { induction c as [| c' [IHr [IHm IHi]]].
        - repeat split; [| exact Hmono | exact Hinc].
          intros a R0 Ha Hao.
          pose proof (w5_rule_3 tm sA sB sC sD sE sF sG sH sI sJ sK sL hc a (S k') (w ++ 4 :: R0)) as Hs1.
          destruct (Hrun a R0 Ha Hao) as [n' [t2 [Hs2 [Hf2 [Ht2 Ho']]]]].
          exists n', (1 + t2). split; [eapply reaches_trans; [exact Hs1 | exact Hs2] | repeat split; [exact Hf2 | lia | exact Ho']].
        - simpl. destruct (F8_step_props k' _ IHm IHi) as [A [B _]].
          repeat split; [| exact A | exact B].
          apply IH; [| exact IHm | exact IHi | exact IHr].
          assert (Hwr : forall j u, W8Word u -> W8Word (rep j 1 u))
            by (induction j; intros; [exact H | constructor; [left; reflexivity | apply IHj; exact H]]).
          apply Hwr; constructor; [right; reflexivity | exact Hw]. }
      assert (Hra : rep (S m) 1 (3 :: w ++ 4 :: R) = rep (S m) 1 (3 :: w) ++ 4 :: R)
        by (clear; induction (S m); simpl; [reflexivity | f_equal; exact IHn]).
      rewrite Hra in H1.
      destruct (proj1 (Hrep1 (S m)) 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 [Hf2 [Ht2 Ho']]]]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | repeat split; [exact Hf2 | lia | exact Ho']].
  Qed.

  Lemma w5_run_1_rep3_odd : forall k j,
    RunW5Odd (S k) (1 :: rep j 3 []) (F8_step k (fun m => m + 2)).
  Proof.
    induction k as [| k' IH]; intros j m R Hm [q Hq].
    - destruct (w5_rule_1_low tm sA sB sC sD sE sF sG sH sI sJ sK sL hc m (rep j 3 []) R) as [t1 [H1 _]].
      { clear. induction j; [constructor | constructor; [right; reflexivity | exact IHj]]. }
      assert (Hone : forall a R0, 1 <= a ->
        exists t, Reaches tm (H5cfg sA a 1 (rep j 3 [] ++ 4 :: R0)) (H5cfg sA (a + j + 2) 1 R0) t /\ a + j + 2 <= t).
      { intros a R0 Ha.
        assert (Hra : rep j 3 [] ++ 4 :: R0 = rep j 3 (4 :: R0)) by (clear; induction j; simpl; [reflexivity | f_equal; exact IHj]).
        rewrite Hra.
        pose proof (w5_rule_3_rep tm sA sB sC sD sE sF sG sH sI sJ sK sL hc j a 1 (4 :: R0)) as Hs1.
        destruct (w5_rule_4 tm sA sB sC sD sE sF sG sH sI sJ sK sL hc a (j + 1) R0 ltac:(lia)) as [t2 [Hs2 Ht2]].
        replace (a + (j + 1) + 1) with (a + j + 2) in Hs2, Ht2 by lia.
        exists (j + t2). split; [eapply reaches_trans; [exact Hs1 | exact Hs2] | lia]. }
      assert (Hrep : forall c a R0, 1 <= a ->
        exists t, Reaches tm (H5cfg sA a 1 (rep_app c (rep j 3 [] ++ [4]) R0)) (H5cfg sA (a + c * (j + 2)) 1 R0) t /\ (1 <= c -> a + c * (j + 2) <= t)).
      { induction c as [| c' IHc]; intros a R0 Ha.
        - exists 0. replace (a + 0 * (j + 2)) with a by lia. split; [apply reaches_zero | lia].
        - simpl rep_app. rewrite <- app_assoc. simpl.
          destruct (Hone a (rep_app c' (rep j 3 [] ++ [4]) R0) Ha) as [t2 [Hs2 Ht2]].
          destruct c' as [| c''].
          + exists t2. simpl in *. replace (a + (j + 2 + 0)) with (a + j + 2) by lia. split; [exact Hs2 | lia].
          + destruct (IHc (a + j + 2) R0 ltac:(lia)) as [t3 [Hs3 Ht3]].
            replace (a + j + 2 + S c'' * (j + 2)) with (a + S (S c'') * (j + 2)) in Hs3, Ht3 by lia.
            exists (t2 + t3). split; [eapply reaches_trans; [exact Hs2 | exact Hs3] | intros _; specialize (Ht3 ltac:(lia)); lia]. }
      destruct (Hrep (m + 3) 1 R ltac:(lia)) as [t2 [H2 Ht2]].
      assert (Hiter : forall c z, iter (fun x => x + 2) c z = z + 2 * c)
        by (induction c; intro z; [simpl; lia | rewrite iter_succ, IHc; lia]).
      exists (1 + (m + 3) * (j + 2)), (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] |].
      repeat split.
      + simpl. rewrite Hiter. nia.
      + specialize (Ht2 ltac:(lia)). lia.
      + exists ((q + 2) * (j + 2)). nia.
    - destruct (w5_rule_1_high tm sA sB sC sD sE sF sG sH sI sJ sK sL hc m (S k') (rep j 3 [] ++ 4 :: R) ltac:(lia)) as [t1 [H1 _]].
      assert (Hbase : RunW5Odd (S k') (1 :: rep (S j) 3 []) (F8_step k' (fun x => x + 2))) by apply IH.
      assert (Hrep1 : forall c,
        RunW5Odd (S k') (rep (S c) 1 (rep (S j) 3 [])) (iterF (F8_step k') (S c) (fun x => x + 2)) /\
        (forall x y, x <= y -> iterF (F8_step k') (S c) (fun x => x + 2) x <= iterF (F8_step k') (S c) (fun x => x + 2) y) /\
        (forall x, x + 2 <= iterF (F8_step k') (S c) (fun x => x + 2) x)).
      { induction c as [| c' [IHr [IHm IHi]]].
        - destruct (F8_step_props k' (fun x => x + 2) w8_base_mono w8_base_inc) as [A [B _]].
          simpl. repeat split; [exact Hbase | exact A | exact B].
        - simpl. destruct (F8_step_props k' _ IHm IHi) as [A [B _]].
          repeat split; [| exact A | exact B].
          apply w5_run_F8_odd; [| exact IHm | exact IHi | exact IHr].
          assert (Hwr : forall u0 u, W8Word u -> W8Word (rep u0 1 u))
            by (induction u0; intros; [exact H | constructor; [left; reflexivity | apply IHu0; exact H]]).
          apply (Hwr (S c')). clear. constructor; [right; reflexivity |]. induction j; [constructor | constructor; [right; reflexivity | exact IHj]]. }
      assert (Hra : rep (S m) 1 (3 :: rep j 3 [] ++ 4 :: R) = rep (S m) 1 (rep (S j) 3 []) ++ 4 :: R)
        by (clear; induction (S m); simpl; [reflexivity | f_equal; exact IHn]).
      rewrite Hra in H1.
      destruct (proj1 (Hrep1 m) 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 [Hf2 [Ht2 Ho']]]]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | repeat split; [exact Hf2 | lia | exact Ho']].
  Qed.

  Lemma w5_init_14_odd : forall R,
    exists n' t, Reaches tm (H5cfg sA 1 2 (1 :: 4 :: R)) (H5cfg sA n' 1 R) t /\ 481 <= n' /\ n' <= t /\ Nat.Odd n'.
  Proof.
    intro R.
    destruct (w5_rule_1_high tm sA sB sC sD sE sF sG sH sI sJ sK sL hc 1 1 (4 :: R) ltac:(lia)) as [t1 [H1 _]].
    assert (Hrun1 : RunW5Odd 1 [1; 3] (F8_step 0 (fun x => x + 3))).
    { intros m R0 Hm [q Hq].
      destruct (w5_rule_1_low tm sA sB sC sD sE sF sG sH sI sJ sK sL hc m [3] R0 ltac:(constructor; [right; reflexivity | constructor])) as [ta [Ha _]].
      assert (Hone : forall a R1, 1 <= a ->
        exists t, Reaches tm (H5cfg sA a 1 (3 :: 4 :: R1)) (H5cfg sA (a + 3) 1 R1) t /\ a + 3 <= t).
      { intros a R1 Ha1.
        pose proof (w5_rule_3 tm sA sB sC sD sE sF sG sH sI sJ sK sL hc a 1 (4 :: R1)) as Hs1.
        destruct (w5_rule_4 tm sA sB sC sD sE sF sG sH sI sJ sK sL hc a 2 R1 ltac:(lia)) as [t2 [Hs2 Ht2]].
        replace (a + 2 + 1) with (a + 3) in Hs2, Ht2 by lia.
        exists (1 + t2). split; [eapply reaches_trans; [exact Hs1 | exact Hs2] | lia]. }
      assert (Hrep : forall c a R1, 1 <= a ->
        exists t, Reaches tm (H5cfg sA a 1 (rep_app c [3; 4] R1)) (H5cfg sA (a + 3 * c) 1 R1) t /\ (1 <= c -> a + 3 * c <= t)).
      { induction c as [| c' IHc]; intros a R1 Ha1.
        - exists 0. replace (a + 3 * 0) with a by lia. split; [apply reaches_zero | lia].
        - simpl rep_app.
          destruct (Hone a (rep_app c' [3; 4] R1) Ha1) as [t2 [Hs2 Ht2]].
          destruct c' as [| c''].
          + exists t2. simpl in *. replace (a + (3 + 0)) with (a + 3) by lia. split; [exact Hs2 | lia].
          + destruct (IHc (a + 3) R1 ltac:(lia)) as [t3 [Hs3 Ht3]].
            replace (a + 3 + 3 * S c'') with (a + 3 * S (S c'')) in Hs3, Ht3 by lia.
            exists (t2 + t3). split; [eapply reaches_trans; [exact Hs2 | exact Hs3] | intros _; specialize (Ht3 ltac:(lia)); lia]. }
      destruct (Hrep (m + 3) 1 R0 ltac:(lia)) as [tb [Hb Htb]].
      assert (Hiter : forall c z, iter (fun x => x + 3) c z = z + 3 * c)
        by (induction c; intro z; [simpl; lia | rewrite iter_succ, IHc; lia]).
      exists (1 + 3 * (m + 3)), (ta + tb).
      split; [eapply reaches_trans; [exact Ha | exact Hb] |].
      repeat split; [simpl; rewrite Hiter; lia | specialize (Htb ltac:(lia)); lia | exists (3 * (q + 2)); lia]. }
    assert (Hm3 : forall x y, x <= y -> x + 3 <= y + 3) by (intros; lia).
    assert (Hi3 : forall x, x + 2 <= x + 3) by (intros; lia).
    destruct (F8_step_props 0 (fun m => m + 3) Hm3 Hi3) as [Hm1 [Hi1 _]].
    assert (Hrun2 : RunW5Odd 1 [1; 1; 3] (F8_step 0 (F8_step 0 (fun m => m + 3)))).
    { apply w5_run_F8_odd; [constructor; [left; reflexivity | constructor; [right; reflexivity | constructor]] | exact Hm1 | exact Hi1 | exact Hrun1]. }
    destruct (Hrun2 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 [Hf2 [Ht2 Ho']]]]].
    assert (H481 : F8_step 0 (F8_step 0 (fun m => m + 3)) 1 = 481) by reflexivity.
    rewrite H481 in Hf2.
    exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | repeat split; [lia | lia | exact Ho']].
  Qed.

End Fwpw_5_Odd.

(* Parity-preserving StepF5Odd ladder + peeker combinators *)
Definition StepF5Odd (tm : TM) (sA sym : nat) (f : nat -> nat) : Prop :=
  forall n R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H5cfg sA n 1 (sym :: R)) (H5cfg sA n' 1 R) t /\
                 n + 2 <= n' /\
                 (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * f x <= n' - 2) /\
                 n' <= t /\ Nat.Odd n'.

Lemma StepF5Odd_rep : forall tm sA sym f, FGHProps f -> StepF5Odd tm sA sym f ->
  forall c n R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H5cfg sA n 1 (rep c sym R)) (H5cfg sA n' 1 R) t /\
                 n + 2 * c <= n' /\
                 (forall x, 1 <= x -> 2 * x <= n - 2 -> 2 * iter f c x <= n' - 2) /\
                 (1 <= c -> n' <= t) /\ Nat.Odd n'.
Proof.
  intros tm sA sym f Hf Hs. induction c as [| c' IH]; intros n R Hn Ho.
  - exists n, 0. split; [apply reaches_zero | simpl; repeat split; [lia | intros; lia | lia | exact Ho]].
  - destruct (Hs n (rep c' sym R) Hn Ho) as [n1 [t1 [H1 [Hinc1 [Hf1 [Ht1 Ho1]]]]]].
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

Lemma w5_stepFOdd_omega_omega : forall tm sA sB sC sD sE sF sG sH sI sJ sK sL sym,
  Fwpw_5Core tm sA sB sC sD sE sF sG sH sI sJ sK sL ->
  (forall n R, 1 <= n -> exists t, Reaches tm (H5cfg sA n 1 (sym :: R)) (H5cfg sA 1 (S n) (1 :: 4 :: R)) t) ->
  StepF5Odd tm sA sym f_omega_omega.
Proof.
  intros tm sA sB sC sD sE sF sG sH sI sJ sK sL sym hc Hrew n R Hn Ho.
  destruct (Hrew n R Hn) as [t0 H0].
  destruct (w5_rule_1_high tm sA sB sC sD sE sF sG sH sI sJ sK sL hc 1 n (4 :: R) Hn) as [t1 [H1 _]].
  destruct n as [| n']; [lia |].
  pose proof (w5_run_1_rep3_odd tm sA sB sC sD sE sF sG sH sI sJ sK sL hc n' 1) as Hrun1.
  destruct (F8_step_props n' (fun m => m + 2) w8_base_mono w8_base_inc) as [Hm1 [Hi1 _]].
  assert (Hrun2 : RunW5Odd tm sA (S n') [1; 1; 3] (F8_step n' (F8_step n' (fun m => m + 2))))
    by (apply (w5_run_F8_odd tm sA sB sC sD sE sF sG sH sI sJ sK sL hc); [constructor; [left; reflexivity | constructor; [right; reflexivity | constructor]] | exact Hm1 | exact Hi1 | exact Hrun1]).
  destruct (Hrun2 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n'0 [t2 [H2 [Hge2 [Ht2 Ho']]]]].
  exists n'0, (t0 + t1 + t2).
  split; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] |].
  destruct (F8_step_props n' (F8_step n' (fun m => m + 2)) Hm1 Hi1) as [_ [_ [Hf2 Hgg]]].
  pose proof (F8_base_grow n') as Hbg.
  pose proof (Hm1 (2 * n') (F8_step n' (fun m => m + 2) 1) ltac:(lia)) as Hstep1.
  destruct n' as [| n''].
  - pose proof (Hf2 1 ltac:(lia)). pose proof (Hi1 1). repeat split; [lia | intros; lia | lia | exact Ho'].
  - assert (Hbz : forall x, 1 <= x -> 2 * fZero x <= 2 * x + 2) by (intros; unfold fZero; lia).
    pose proof (F8_step_ge_fOmegaPowStep (S n'') fZero (fun m => m + 2) fZero_props
                  w8_base_mono w8_base_inc Hbz (S n'') ltac:(lia)) as Hstep2.
    pose proof (fgh_gt_pos _ f_omega_omega_props (S n'') ltac:(lia)) as Hgt.
    unfold f_omega_omega in *.
    repeat split; [lia | | lia | exact Ho'].
    intros x Hx H2x. pose proof (fgh_mono _ f_omega_omega_props x (S n'') ltac:(lia)).
    unfold f_omega_omega in *. lia.
Qed.

(* Pair consumption on non-empty right tail (x :: R) so writing 0 never hits cons0 [] *)
Definition StepF5Odd_pair_ne (tm : TM) (sA p : nat) (f : nat -> nat) : Prop :=
  forall n x R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H5cfg sA n 1 (p :: p :: x :: R)) (H5cfg sA n' 1 (x :: R)) t /\
                 n + 2 <= n' /\
                 (forall z, 1 <= z -> 2 * z <= n - 2 -> 2 * f z <= n' - 2) /\
                 n' <= t /\ Nat.Odd n'.

Lemma StepF5Odd_pair_ne_from_sym : forall tm sA p prev f,
  FGHProps f -> StepF5Odd tm sA prev f ->
  (forall n x R, 1 <= n -> exists t, Reaches tm (H5cfg sA n 1 (p :: p :: x :: R)) (H5cfg sA 1 1 (rep (n + 2) prev (x :: R))) t) ->
  StepF5Odd_pair_ne tm sA p (fNext f).
Proof.
  intros tm sA p prev f Hf Hprev Hrew n x R Hn Ho.
  destruct (Hrew n x R Hn) as [t0 H0].
  replace (n + 2) with (S (S n)) in H0 by lia.
  change (Reaches tm (H5cfg sA n 1 (p :: p :: x :: R)) (H5cfg sA 1 1 (prev :: rep (S n) prev (x :: R))) t0) in H0.
  destruct (Hprev 1 (rep (S n) prev (x :: R)) ltac:(lia) (ex_intro _ 0 eq_refl))
    as [n1 [t1 [H1 [Hinc1 [_ [_ Ho1]]]]]].
  set (q := n / 2).
  assert (Hdiv : 2 * q <= n /\ n <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod n 2 ltac:(lia)); pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia).
  assert (Hq : S n = q + (S n - q)) by lia.
  rewrite Hq, rep_add8 in H0, H1.
  destruct (StepF5Odd_rep tm sA prev f Hf Hprev q n1 (rep (S n - q) prev (x :: R)) ltac:(lia) Ho1)
    as [n2 [t2 [H2 [Hinc2 [_ [_ Ho2]]]]]].
  destruct (StepF5Odd_rep tm sA prev f Hf Hprev (S n - q) n2 (x :: R) ltac:(lia) Ho2)
    as [n3 [t3 [H3 [Hinc3 [Hf3 [Ht3 Ho3]]]]]].
  exists n3, (t0 + t1 + t2 + t3).
  split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] |].
  repeat split; [unfold q in *; lia | | specialize (Ht3 ltac:(unfold q; lia)); lia | exact Ho3].
  intros z Hz H2z.
  assert (Hzq : z <= q) by (unfold q; lia).
  assert (Hrem : z <= S n - q) by (unfold q; lia).
  pose proof (Hf3 z Hz ltac:(lia)) as Hiter.
  pose proof (iter_mono_steps f (fgh_ge_self _ Hf) z (S n - q) z Hrem) as Hst.
  unfold fNext. lia.
Qed.

Lemma StepF5Odd_pair_ne_rep : forall tm sA p f, FGHProps f -> StepF5Odd_pair_ne tm sA p f ->
  forall c n x R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H5cfg sA n 1 (rep (2 * c) p (x :: R))) (H5cfg sA n' 1 (x :: R)) t /\
                 n + 2 * c <= n' /\
                 (forall z, 1 <= z -> 2 * z <= n - 2 -> 2 * iter f c z <= n' - 2) /\
                 (1 <= c -> n' <= t) /\ Nat.Odd n'.
Proof.
  intros tm sA p f Hf Hp. induction c as [| c' IH]; intros n x R Hn Ho.
  - exists n, 0. split; [apply reaches_zero | simpl; repeat split; [lia | intros; lia | lia | exact Ho]].
  - destruct c' as [| c''].
    + simpl (2 * 1) in *. simpl rep.
      destruct (Hp n x R Hn Ho) as [n1 [t1 [H1 [Hinc1 [Hf1 [Ht1 Ho1]]]]]].
      exists n1, t1. simpl in *. split; [exact H1 | repeat split; [lia | intros z Hz H2z; apply Hf1; assumption | intros _; exact Ht1 | exact Ho1]].
    + assert (Hrew : rep (2 * S (S c'')) p (x :: R) = p :: p :: p :: rep (S (2 * c'')) p (x :: R))
        by (replace (2 * S (S c'')) with (S (S (S (S (2 * c''))))) by lia; reflexivity).
      rewrite Hrew.
      destruct (Hp n p (rep (S (2 * c'')) p (x :: R)) Hn Ho) as [n1 [t1 [H1 [Hinc1 [Hf1 [_ Ho1]]]]]].
      destruct (IH n1 x R ltac:(lia) Ho1) as [n2 [t2 [H2 [Hinc2 [Hf2 [Ht2 Ho2]]]]]].
      replace (rep (2 * S c'') p (x :: R)) with (p :: rep (S (2 * c'')) p (x :: R)) in H2
        by (replace (2 * S c'') with (S (S (2 * c''))) by lia; reflexivity).
      exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
      repeat split; [lia | | intros _; specialize (Ht2 ltac:(lia)); lia | exact Ho2].
      intros z Hz H2z.
      replace (iter f (S (S c'')) z) with (iter f (S c'') (f z))
        by (replace (S (S c'')) with (S c'' + 1) by lia; rewrite iter_add; reflexivity).
      apply Hf2; [pose proof (fgh_ge_self _ Hf z); lia | apply Hf1; assumption].
Qed.

(* Peeker StepF5Odd_peeker on (p :: sym :: R) -> (p :: R) with 4 * x <= n - 2 *)
Definition StepF5Odd_peeker (tm : TM) (sA p sym : nat) (f : nat -> nat) : Prop :=
  forall n R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H5cfg sA n 1 (p :: sym :: R)) (H5cfg sA n' 1 (p :: R)) t /\
                 n + 2 <= n' /\
                 (forall x, 1 <= x -> 4 * x <= n - 2 -> 4 * f x <= n' - 2) /\
                 n' <= t /\ Nat.Odd n'.

Lemma StepF5Odd_peeker_rep : forall tm sA p sym f, FGHProps f -> StepF5Odd_peeker tm sA p sym f ->
  forall c n R, 1 <= n -> Nat.Odd n ->
    exists n' t, Reaches tm (H5cfg sA n 1 (p :: rep c sym R)) (H5cfg sA n' 1 (p :: R)) t /\
                 n + 2 * c <= n' /\
                 (forall x, 1 <= x -> 4 * x <= n - 2 -> 4 * iter f c x <= n' - 2) /\
                 (1 <= c -> n' <= t) /\ Nat.Odd n'.
Proof.
  intros tm sA p sym f Hf Hs. induction c as [| c' IH]; intros n R Hn Ho.
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

Lemma StepF5Odd_peeker_from_pair : forall tm sA p sym f,
  FGHProps f -> (forall z, 1 <= z -> 2 * z <= f z) -> StepF5Odd_pair_ne tm sA p f ->
  (forall n R, 1 <= n -> Nat.Odd n -> exists t, Reaches tm (H5cfg sA n 1 (p :: sym :: R)) (H5cfg sA 1 1 (rep (n + 2) p R)) t) ->
  StepF5Odd_peeker tm sA p sym (fNext f).
Proof.
  intros tm sA p sym f Hf H2f Hp Hrew n R Hn [u Hu].
  destruct (Hrew n R Hn (ex_intro _ u Hu)) as [t0 H0].
  replace (n + 2) with (2 * (S u) + 1) in H0 by lia.
  rewrite rep_add8 in H0. simpl (rep 1 p R) in H0.
  set (q := S u / 2).
  assert (Hdiv : 2 * q <= S u /\ S u <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod (S u) 2 ltac:(lia)); pose proof (Nat.mod_upper_bound (S u) 2 ltac:(lia)); lia).
  assert (Hq : 2 * S u = 2 * q + 2 * (S u - q)) by lia.
  rewrite Hq, rep_add8, rep_snoc_one in H0.
  destruct (StepF5Odd_pair_ne_rep tm sA p f Hf Hp q 1 p (rep (2 * (S u - q)) p R) ltac:(lia) (ex_intro _ 0 eq_refl))
    as [n1 [t1 [H1 [Hinc1 [_ [_ Ho1]]]]]].
  destruct (StepF5Odd_pair_ne_rep tm sA p f Hf Hp (S u - q) n1 p R ltac:(lia) Ho1)
    as [n2 [t2 [H2 [Hinc2 [Hf2 [Ht2 Ho2]]]]]].
  rewrite rep_snoc_one in H2.
  exists n2, (t0 + t1 + t2).
  split; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] |].
  repeat split; [unfold q in *; lia | | specialize (Ht2 ltac:(unfold q; lia)); lia | exact Ho2].
  intros x Hx H4x.
  assert (Hxq : x <= q) by (unfold q; lia).
  assert (Hrem : S x <= S u - q) by (unfold q; lia).
  pose proof (Hf2 x Hx ltac:(lia)) as Hiter.
  pose proof (iter_mono_steps f (fgh_ge_self _ Hf) (S x) (S u - q) x Hrem) as Hst.
  rewrite iter_succ in Hst.
  pose proof (H2f (iter f x x) ltac:(pose proof (iter_ge_self f (fgh_ge_self _ Hf) x x); lia)).
  unfold fNext. lia.
Qed.

Lemma StepF5Odd_peeker_from_triple : forall tm sA p sym prev_sym f0 f,
  FGHProps f -> StepF5Odd_pair_ne tm sA p f0 -> StepF5Odd_peeker tm sA p prev_sym f ->
  (forall n R, 1 <= n -> Nat.Odd n -> exists t, Reaches tm (H5cfg sA n 1 (p :: sym :: R)) (H5cfg sA 1 1 (p :: p :: p :: rep n prev_sym R)) t) ->
  StepF5Odd_peeker tm sA p sym (fNext f).
Proof.
  intros tm sA p sym prev_sym f0 f Hf Hp Hprev Hrew n R Hn Ho.
  destruct (Hrew n R Hn Ho) as [t0 H0].
  destruct (Hp 1 p (rep n prev_sym R) ltac:(lia) (ex_intro _ 0 eq_refl))
    as [n1 [t1 [H1 [Hinc1 [_ [_ Ho1]]]]]].
  set (q := n / 2).
  assert (Hdiv : 2 * q <= n /\ n <= 2 * q + 1) by (unfold q; pose proof (Nat.div_mod n 2 ltac:(lia)); pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia).
  assert (Hq : n = q + (n - q)) by lia.
  replace (rep n prev_sym R) with (rep q prev_sym (rep (n - q) prev_sym R)) in H0, H1
    by (rewrite <- rep_add8, <- Hq; reflexivity).
  destruct (StepF5Odd_peeker_rep tm sA p prev_sym f Hf Hprev q n1 (rep (n - q) prev_sym R) ltac:(lia) Ho1)
    as [n2 [t2 [H2 [Hinc2 [_ [_ Ho2]]]]]].
  destruct (StepF5Odd_peeker_rep tm sA p prev_sym f Hf Hprev (n - q) n2 R ltac:(lia) Ho2)
    as [n3 [t3 [H3 [Hinc3 [Hf3 [Ht3 Ho3]]]]]].
  exists n3, (t0 + t1 + t2 + t3).
  split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] |].
  repeat split; [unfold q in *; lia | | specialize (Ht3 ltac:(unfold q; lia)); lia | exact Ho3].
  intros x Hx H4x.
  assert (Hge2x : 4 * x <= n2 - 2) by (unfold q in *; lia).
  assert (Hrem : x <= n - q) by (unfold q in *; lia).
  pose proof (Hf3 x Hx Hge2x) as Hiter.
  pose proof (iter_mono_steps f (fgh_ge_self _ Hf) x (n - q) x Hrem) as Hst.
  unfold fNext. lia.
Qed.

Lemma w5_sweep_left_23 : forall tm st w n R,
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

Lemma w5_sweep_left_23_ne : forall tm st w n x R,
  tm st 2 = Some (mkAction w DL (Some st)) ->
  tm st 3 = Some (mkAction w DL (Some st)) ->
  Reaches tm (mkCfgR (Some st) (rep n 3 []) (2 :: x :: R))
             (mkCfgR (Some st) [] (0 :: rep (S n) w (x :: R))) (S n).
Proof.
  intros tm st w n. induction n as [| n' IH]; intros x R H2 H3.
  - apply steps_one; unfold step, mkCfgR; simpl; rewrite H2, cons0_cons; reflexivity.
  - assert (Hloop : forall a y R0,
      Reaches tm (mkCfgR (Some st) (rep a 3 []) (3 :: y :: R0))
                 (mkCfgR (Some st) [] (0 :: rep (S a) w (y :: R0))) (S a)).
    { induction a as [| a' IHa]; intros y R0.
      - apply steps_one; unfold step, mkCfgR; simpl; rewrite H3, cons0_cons; reflexivity.
      - replace (S (S a')) with (1 + S a') by lia.
        eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite H3, cons0_cons; reflexivity |].
        specialize (IHa w (y :: R0)). rewrite rep_r8 in IHa. exact IHa. }
    replace (S (S n')) with (1 + S n') by lia.
    eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite H2, cons0_cons; reflexivity |].
    pose proof (Hloop n' w (x :: R)) as Hl. rewrite rep_r8 in Hl. exact Hl.
Qed.

Lemma f_omega_omega_3_ge_96 : 96 <= f_omega_omega 3.
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
  assert (H1_3 : 96 <= fOmegaPowStep 1 fZero 3).
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
    pose proof (H00_ge (fOmegaPowStep 0 (fOmegaPowStep 0 fZero) 24)).
    lia. }
  unfold f_omega_omega. lia.
Qed.

