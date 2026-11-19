(*
  rocq/Jacobzheng.v
  Reusable, axiom-free Rocq 9.1 library for the 15-state Jacobzheng Busy Beaver
  f_{ω×2} engine (shared by BB18_2, BB19_2, and BB20_2).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz JZMath.
Import ListNotations.

Record JZEngine (tm : TM) : Prop := mkJZEngine {
  jz_A0 : tm 0  0 = Some (mkAction 1 DL (Some 1));
  jz_A1 : tm 0  1 = Some (mkAction 0 DL (Some 12));
  jz_B0 : tm 1  0 = Some (mkAction 1 DR (Some 2));
  jz_B1 : tm 1  1 = Some (mkAction 1 DR (Some 13));
  jz_C0 : tm 2  0 = Some (mkAction 1 DR (Some 3));
  jz_C1 : tm 2  1 = Some (mkAction 1 DR (Some 2));
  jz_D0 : tm 3  0 = Some (mkAction 0 DL (Some 4));
  jz_D1 : tm 3  1 = Some (mkAction 1 DR (Some 16));
  jz_E0 : tm 4  0 = Some (mkAction 1 DL (Some 5));
  jz_E1 : tm 4  1 = Some (mkAction 1 DL (Some 4));
  jz_F0 : tm 5  0 = Some (mkAction 0 DL (Some 6));
  jz_F1 : tm 5  1 = Some (mkAction 1 DL (Some 4));
  jz_G0 : tm 6  0 = Some (mkAction 1 DR (Some 7));
  jz_G1 : tm 6  1 = Some (mkAction 1 DR (Some 8));
  jz_H0 : tm 7  0 = Some (mkAction 0 DR (Some 7));
  jz_H1 : tm 7  1 = Some (mkAction 0 DR (Some 2));
  jz_I0 : tm 8  0 = Some (mkAction 0 DR (Some 9));
  jz_I1 : tm 8  1 = Some (mkAction 1 DR (Some 7));
  jz_J1 : tm 9  1 = Some (mkAction 0 DR (Some 10));
  jz_K1 : tm 10 1 = Some (mkAction 1 DR (Some 11));
  jz_L1 : tm 11 1 = Some (mkAction 1 DR (Some 9));
  jz_M0 : tm 12 0 = Some (mkAction 1 DL (Some 0));
  jz_M1 : tm 12 1 = Some (mkAction 1 DL (Some 12));
  jz_N0 : tm 13 0 = Some (mkAction 0 DL (Some 0));
  jz_N1 : tm 13 1 = Some (mkAction 0 DR (Some 14));
  jz_O0 : tm 14 0 = Some (mkAction 0 DL (Some 2));
  jz_O1 : tm 14 1 = Some (mkAction 1 DR (Some 15));
  jz_P0 : tm 15 0 = Some (mkAction 0 DL (Some 0));
  jz_P1 : tm 15 1 = Some (mkAction 1 DR (Some 13));
  jz_Q0 : tm 16 0 = Some (mkAction 0 DL (Some 17));
  jz_Q1 : tm 16 1 = Some (mkAction 1 DL (Some 0));
  jz_R0 : tm 17 0 = Some (mkAction 0 DR (Some 8));
  jz_R1 : tm 17 1 = Some (mkAction 1 DL (Some 17))
}.

Fixpoint rep01 (m : nat) (tail : list nat) : list nat :=
  match m with
  | 0 => tail
  | S k => 0 :: 1 :: rep01 k tail
  end.

Fixpoint rep10 (m : nat) (tail : list nat) : list nat :=
  match m with
  | 0 => tail
  | S k => 1 :: 0 :: rep10 k tail
  end.

Fixpoint rep110 (k : nat) (tail : list nat) : list nat :=
  match k with
  | 0 => tail
  | S p => 1 :: 1 :: 0 :: rep110 p tail
  end.

Fixpoint rep101 (k : nat) (tail : list nat) : list nat :=
  match k with
  | 0 => tail
  | S p => 1 :: 0 :: 1 :: rep101 p tail
  end.

Fixpoint rl (xs R : list nat) : list nat :=
  match xs with
  | [] => R
  | a :: xs' => rep a 1 (cons0 0 (rl xs' R))
  end.

Lemma rep01_zero_unfold : forall m a tail,
  rep01 m (0 :: a :: tail) = 0 :: rep10 m (a :: tail).
Proof. induction m as [| k IH]; intros a tail; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rep01_snoc : forall m R, rep01 m (0 :: 1 :: R) = rep01 (S m) R.
Proof. induction m as [| k IH]; intro R; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma one_rep01_eq_rep10 : forall m R, 1 :: rep01 m R = rep10 m (1 :: R).
Proof. induction m as [| k IH]; intro R; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rep110_snoc : forall k L, rep110 k (1 :: 1 :: 0 :: L) = rep110 (S k) L.
Proof. induction k as [| p IH]; intro L; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rep101_snoc : forall k R, rep101 k (1 :: 0 :: 1 :: R) = rep101 (S k) R.
Proof. induction k as [| p IH]; intro R; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma cons0_ne_nil : forall x ys, ys <> [] -> cons0 x ys = x :: ys.
Proof. intros x [| y ys'] H; [contradiction | destruct x; reflexivity]. Qed.

Lemma jz_cons0_succ : forall w xs, cons0 (S w) xs = S w :: xs.
Proof. reflexivity. Qed.

Lemma jz_cons0_cons : forall w x xs, cons0 w (x :: xs) = w :: x :: xs.
Proof. intros [| w] x xs; reflexivity. Qed.

Lemma jz_cons0_zero_nil : cons0 0 [] = [].
Proof. reflexivity. Qed.

Ltac simp_cons0 := rewrite ?jz_cons0_succ, ?jz_cons0_cons, ?jz_cons0_zero_nil.

Lemma rl_ne_nil : forall xs a R, rl xs (a :: R) <> [].
Proof.
  induction xs as [| b xs' IH]; intros a R; cbn [rl].
  - discriminate.
  - destruct b as [| k]; cbn [rep].
    + rewrite cons0_ne_nil by apply IH. discriminate.
    + discriminate.
Qed.

Lemma one_rep101_eq_rl : forall q a R,
  1 :: rep101 q (a :: R) = rl (rep q 2 []) (1 :: a :: R).
Proof.
  induction q as [| k IH]; intros a R; cbn [rep101 rep rl].
  - reflexivity.
  - rewrite IH, cons0_ne_nil by apply rl_ne_nil. reflexivity.
Qed.

Lemma rl_rep_one : forall m a R,
  rep10 m (a :: R) = rl (rep m 1 []) (a :: R).
Proof.
  induction m as [| k IH]; intros a R; cbn [rep10 rep rl].
  - reflexivity.
  - rewrite <- IH, cons0_ne_nil; [reflexivity | destruct k; discriminate].
Qed.

Lemma rl_append : forall xs ys a R,
  rl (xs ++ ys) (a :: R) = rl xs (rl ys (a :: R)).
Proof.
  induction xs as [| b xs' IH]; intros ys a R; cbn [app rl].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma rep_add_sym : forall a b s L, rep a s (rep b s L) = rep (a + b) s L.
Proof. induction a as [| k IH]; intros b s L; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rep_snoc_sym : forall k s L, rep k s (s :: L) = rep (S k) s L.
Proof.
  intros k s L. replace (S k) with (k + 1) by lia.
  rewrite <- rep_add_sym. reflexivity.
Qed.

Lemma step_R_cons : forall tm q cur w nx L R,
  tm q cur = Some (mkAction w DR nx) ->
  step tm (mkCfgR (Some q) L (cur :: R)) = Some (mkCfgR nx (cons0 w L) R).
Proof.
  intros tm q cur w nx L [| b R'] Ht; unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_R_zero : forall tm q w nx L R,
  tm q 0 = Some (mkAction w DR nx) ->
  step tm (mkCfgR (Some q) L (cons0 0 R)) = Some (mkCfgR nx (cons0 w L) R).
Proof.
  intros tm q w nx L [| b R'] Ht; unfold step, mkCfgR, cons0; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_L_cons : forall tm q cur w nx a L R,
  tm q cur = Some (mkAction w DL nx) ->
  step tm (mkCfgR (Some q) (a :: L) (cur :: R)) = Some (mkCfgR nx L (a :: cons0 w R)).
Proof.
  intros tm q cur w nx a L R Ht; unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_L_zero_cons : forall tm q w nx a L R,
  tm q 0 = Some (mkAction w DL nx) ->
  step tm (mkCfgR (Some q) (a :: L) (cons0 0 R)) = Some (mkCfgR nx L (a :: cons0 w R)).
Proof.
  intros tm q w nx a L [| b R'] Ht; unfold step, mkCfgR, cons0; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_L_nil : forall tm q cur w nx R,
  tm q cur = Some (mkAction w DL nx) ->
  step tm (mkCfgR (Some q) [] (cur :: R)) = Some (mkCfgR nx [] (0 :: cons0 w R)).
Proof.
  intros tm q cur w nx R Ht; unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Definition CI (n : nat) (R : list nat) : Config :=
  mkCfgR (Some 2) (rep n 1 []) (cons0 0 R).

Definition SW (m n : nat) (R : list nat) : Config :=
  mkCfgR (Some 2) (rep n 1 (rep01 m [0; 1])) (cons0 0 R).

Definition CO (m n : nat) (R : list nat) : Config :=
  mkCfgR (Some 2) (rep n 1 (rep01 m [0; 0; 1])) (cons0 0 R).

Definition EX (n : nat) (R : list nat) : Config :=
  mkCfgR (Some 9) [0; 1] (rep n 1 (cons0 0 R)).

Definition CanReach (tm : TM) (c1 c2 : Config) : Prop :=
  exists t, Reaches tm c1 c2 t.

Lemma canReach_refl : forall tm c, CanReach tm c c.
Proof. intros tm c. exists 0. apply reaches_zero. Qed.

Lemma canReach_trans : forall tm c1 c2 c3,
  CanReach tm c1 c2 -> CanReach tm c2 c3 -> CanReach tm c1 c3.
Proof.
  intros tm c1 c2 c3 [t1 H1] [t2 H2].
  exists (t1 + t2). eapply reaches_trans; eassumption.
Qed.

Lemma reaches_one : forall tm c1 c2, step tm c1 = Some c2 -> Reaches tm c1 c2 1.
Proof. intros tm c1 c2 H. unfold Reaches. simpl. rewrite H. reflexivity. Qed.

Lemma canReach_step : forall tm c1 c2 c3,
  step tm c1 = Some c2 -> CanReach tm c2 c3 -> CanReach tm c1 c3.
Proof.
  intros tm c1 c2 c3 H1 [t H2].
  exists (1 + t). eapply reaches_trans; [apply reaches_one; exact H1 | exact H2].
Qed.

Lemma iter_add_one_jz : forall g k x, iter g k (g x) = iter g (S k) x.
Proof.
  intros g k x. replace (S k) with (k + 1) by lia.
  rewrite iter_add. reflexivity.
Qed.

Section EngineLemmas.
Variable tm : TM.
Hypothesis He : JZEngine tm.

Lemma jz_boot : Reaches tm initConfig (EX 5 []) 26.
Proof.
  assert (H1 : Reaches tm initConfig (mkCfgR (Some 2) [0; 0; 1] [1; 1; 1]) 13).
  { unfold Reaches, initConfig, mkCfgR.
    repeat (cbn [steps]; unfold step; simpl; first [
      rewrite (jz_A0 _ He) | rewrite (jz_B0 _ He) | rewrite (jz_C0 _ He) |
      rewrite (jz_C1 _ He) | rewrite (jz_D0 _ He) | rewrite (jz_E0 _ He) |
      rewrite (jz_E1 _ He) | rewrite (jz_F0 _ He) | rewrite (jz_G0 _ He) |
      rewrite (jz_H0 _ He) | rewrite (jz_H1 _ He) ]).
    reflexivity. }
  assert (H2 : Reaches tm (mkCfgR (Some 2) [0; 0; 1] [1; 1; 1]) (EX 5 []) 13).
  { unfold Reaches, EX, mkCfgR, rep, cons0.
    repeat (cbn [steps]; unfold step; simpl; first [
      rewrite (jz_C0 _ He) | rewrite (jz_C1 _ He) | rewrite (jz_D0 _ He) |
      rewrite (jz_E0 _ He) | rewrite (jz_E1 _ He) | rewrite (jz_F0 _ He) |
      rewrite (jz_G1 _ He) | rewrite (jz_I0 _ He) ]).
    reflexivity. }
  replace 26 with (13 + 13) by lia.
  eapply reaches_trans; [exact H1 | exact H2].
Qed.

Lemma jz_triJKL : forall k a L R,
  Reaches tm (mkCfgR (Some 9) (a :: L) (rep (3 * k) 1 R))
             (mkCfgR (Some 9) (rep110 k (a :: L)) R) (3 * k).
Proof.
  induction k as [| p IH]; intros a L R.
  - cbn [Nat.mul rep rep110]. apply reaches_zero.
  - replace (3 * S p) with (3 + 3 * p) by lia.
    rewrite <- rep_add_sym. cbn [rep].
    replace (3 + 3 * p) with (1 + (1 + (1 + 3 * p))) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_R_cons; apply (jz_J1 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_R_cons; apply (jz_K1 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_R_cons; apply (jz_L1 _ He) | simp_cons0].
    specialize (IH 1 (1 :: 0 :: a :: L) R).
    rewrite rep110_snoc in IH. exact IH.
Qed.

Lemma loop_C1 : forall k L R,
  Reaches tm (mkCfgR (Some 2) L (rep k 1 R))
             (mkCfgR (Some 2) (rep k 1 L) R) k.
Proof.
  induction k as [| p IH]; intros L R; simpl.
  - apply reaches_zero.
  - replace (S p) with (1 + p) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_R_cons; apply (jz_C1 _ He) |].
    simp_cons0. specialize (IH (1 :: L) R).
    rewrite rep_snoc_sym in IH. exact IH.
Qed.

Lemma loop_E1 : forall k L R,
  Reaches tm (mkCfgR (Some 4) (rep k 1 L) (1 :: R))
             (mkCfgR (Some 4) L (rep k 1 (1 :: R))) k.
Proof.
  induction k as [| p IH]; intros L R; simpl.
  - apply reaches_zero.
  - replace (S p) with (1 + p) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_E1 _ He) |].
    simp_cons0. specialize (IH L (1 :: R)).
    rewrite rep_snoc_sym in IH. exact IH.
Qed.

Lemma loop_M1 : forall k L R,
  Reaches tm (mkCfgR (Some 12) (rep k 1 L) (1 :: R))
             (mkCfgR (Some 12) L (rep k 1 (1 :: R))) k.
Proof.
  induction k as [| p IH]; intros L R; simpl.
  - apply reaches_zero.
  - replace (S p) with (1 + p) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_M1 _ He) |].
    simp_cons0. specialize (IH L (1 :: R)).
    rewrite rep_snoc_sym in IH. exact IH.
Qed.

Lemma loop_R1 : forall k L R,
  Reaches tm (mkCfgR (Some 17) (rep k 1 L) (1 :: R))
             (mkCfgR (Some 17) L (rep k 1 (1 :: R))) k.
Proof.
  induction k as [| p IH]; intros L R; simpl.
  - apply reaches_zero.
  - replace (S p) with (1 + p) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_R1 _ He) |].
    simp_cons0. specialize (IH L (1 :: R)).
    rewrite rep_snoc_sym in IH. exact IH.
Qed.

Lemma loop_EF_10 : forall m L R,
  Reaches tm (mkCfgR (Some 4) (rep10 m L) (0 :: R))
             (mkCfgR (Some 4) L (0 :: rep (2 * m) 1 R)) (2 * m).
Proof.
  induction m as [| p IH]; intros L R.
  - cbn [Nat.mul rep rep10]. apply reaches_zero.
  - cbn [rep10].
    replace (2 * S p) with (1 + (1 + 2 * p)) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_E0 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_F1 _ He) | simp_cons0].
    specialize (IH L (1 :: 1 :: R)).
    rewrite rep_snoc_sym, rep_snoc_sym in IH.
    replace (1 + (1 + 2 * p)) with (S (S (2 * p))) by lia. exact IH.
Qed.

Lemma loop_EF_110 : forall k L R,
  Reaches tm (mkCfgR (Some 4) (rep110 k L) (0 :: R))
             (mkCfgR (Some 4) L (0 :: rep (3 * k) 1 R)) (3 * k).
Proof.
  induction k as [| p IH]; intros L R.
  - cbn [Nat.mul rep rep110]. apply reaches_zero.
  - cbn [rep110].
    replace (3 * S p) with (1 + (1 + (1 + 3 * p))) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_E0 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_F1 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_E1 _ He) | simp_cons0].
    specialize (IH L (1 :: 1 :: 1 :: R)).
    rewrite rep_snoc_sym, rep_snoc_sym, rep_snoc_sym in IH.
    replace (1 + (1 + (1 + 3 * p))) with (S (S (S (3 * p)))) by lia. exact IH.
Qed.

Lemma loop_NOP : forall k a L R,
  Reaches tm (mkCfgR (Some 13) (a :: L) (rep (3 * k) 1 R))
             (mkCfgR (Some 13) (rep110 k (a :: L)) R) (3 * k).
Proof.
  induction k as [| p IH]; intros a L R.
  - cbn [Nat.mul rep rep110]. apply reaches_zero.
  - replace (3 * S p) with (3 + 3 * p) by lia.
    rewrite <- rep_add_sym. cbn [rep].
    replace (3 + 3 * p) with (1 + (1 + (1 + 3 * p))) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_R_cons; apply (jz_N1 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_R_cons; apply (jz_O1 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_R_cons; apply (jz_P1 _ He) | simp_cons0].
    specialize (IH 1 (1 :: 0 :: a :: L) R).
    rewrite rep110_snoc in IH. exact IH.
Qed.

Lemma jz_M_loop : forall k L R,
  Reaches tm (mkCfgR (Some 12) (rep110 k L) (0 :: R))
             (mkCfgR (Some 12) L (0 :: rep101 k R)) (3 * k).
Proof.
  induction k as [| p IH]; intros L R.
  - cbn [Nat.mul rep110 rep101]. apply reaches_zero.
  - cbn [rep110].
    replace (3 * S p) with (1 + (1 + (1 + 3 * p))) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_M0 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
    specialize (IH L (1 :: 0 :: 1 :: R)).
    rewrite rep101_snoc in IH. exact IH.
Qed.

Lemma loop_MA_10 : forall m L R,
  Reaches tm (mkCfgR (Some 12) (rep10 m L) (0 :: R))
             (mkCfgR (Some 12) L (0 :: rep01 m R)) (2 * m).
Proof.
  induction m as [| p IH]; intros L R.
  - cbn [Nat.mul rep10 rep01]. apply reaches_zero.
  - cbn [rep10].
    replace (2 * S p) with (1 + (1 + 2 * p)) by lia.
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_M0 _ He) | simp_cons0].
    eapply reaches_trans; [apply reaches_one; eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
    specialize (IH L (0 :: 1 :: R)).
    rewrite rep01_snoc in IH. exact IH.
Qed.

Lemma jz_M_finish : forall R,
  CanReach tm (mkCfgR (Some 12) [1] (0 :: R)) (CI 3 (1 :: R)).
Proof.
  intro R.
  eapply canReach_step; [eapply step_L_cons; apply (jz_M0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_M0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_A0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_B0 _ He) | simp_cons0].
  exists 2. exact (loop_C1 2 [1] (0 :: 1 :: R)).
Qed.

Lemma rule_CI_0 : forall n R,
  CanReach tm (CI n (cons0 0 R)) (CO 0 (n + 1) R).
Proof.
  intros n R. unfold CI.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_zero_cons; apply (jz_D0 _ He) |].
  eapply canReach_trans; [exists n; exact (loop_E1 n [] (cons0 0 R)) |].
  rewrite rep_snoc_sym.
  eapply canReach_step; [eapply step_L_nil; apply (jz_E1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_E0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_F0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_G0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_H0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_H1 _ He) | simp_cons0].
  replace (n + 1) with (S n) by lia.
  exists (S n). exact (loop_C1 (S n) [0; 0; 1] (cons0 0 R)).
Qed.

Lemma rule_SW_0 : forall m n R,
  CanReach tm (SW m n (cons0 0 R)) (CO 0 (n + 2 * m + 3) R).
Proof.
  intros m n R. unfold SW.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_zero_cons; apply (jz_D0 _ He) |].
  eapply canReach_trans; [exists n; exact (loop_E1 n (rep01 m [0; 1]) (cons0 0 R)) |].
  rewrite rep_snoc_sym, rep01_zero_unfold.
  eapply canReach_step; [eapply step_L_cons; apply (jz_E1 _ He) | simp_cons0].
  eapply canReach_trans; [exists (2 * m); exact (loop_EF_10 m [1] (1 :: rep n 1 (cons0 0 R))) |].
  eapply canReach_step; [eapply step_L_cons; apply (jz_E0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_F1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_E0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_F0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_G0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_H0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_H1 _ He) | simp_cons0].
  assert (Hr : 1 :: 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R)) =
               rep (n + 2 * m + 3) 1 (cons0 0 R)).
  { rewrite rep_snoc_sym, rep_add_sym.
    change (rep (S (S (S (2 * m) + n))) 1 (cons0 0 R) = rep (n + 2 * m + 3) 1 (cons0 0 R)).
    f_equal. lia. }
  rewrite Hr.
  exists (n + 2 * m + 3). exact (loop_C1 (n + 2 * m + 3) [0; 0; 1] (cons0 0 R)).
Qed.

Lemma rule_CO_0 : forall m n R,
  CanReach tm (CO m n (cons0 0 R)) (EX (n + 2 * m + 2) R).
Proof.
  intros m n R. unfold CO.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_zero_cons; apply (jz_D0 _ He) |].
  eapply canReach_trans; [exists n; exact (loop_E1 n (rep01 m [0; 0; 1]) (cons0 0 R)) |].
  rewrite rep_snoc_sym, rep01_zero_unfold.
  eapply canReach_step; [eapply step_L_cons; apply (jz_E1 _ He) | simp_cons0].
  eapply canReach_trans; [exists (2 * m); exact (loop_EF_10 m [0; 1] (1 :: rep n 1 (cons0 0 R))) |].
  eapply canReach_step; [eapply step_L_cons; apply (jz_E0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_F0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_G1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_I0 _ He) | simp_cons0].
  assert (Hr : 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R)) =
               rep (n + 2 * m + 2) 1 (cons0 0 R)).
  { rewrite rep_snoc_sym, rep_add_sym.
    change (rep (S (S (2 * m) + n)) 1 (cons0 0 R) = rep (n + 2 * m + 2) 1 (cons0 0 R)).
    f_equal. lia. }
  rewrite Hr. apply canReach_refl.
Qed.

Lemma rule_CI_10 : forall n R,
  CanReach tm (CI n (1 :: cons0 0 R)) (SW 0 n R).
Proof.
  intros n R. unfold CI.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_D1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_zero_cons; apply (jz_Q0 _ He) |].
  eapply canReach_trans; [exists (S n); exact (loop_R1 (S n) [] (cons0 0 R)) |].
  rewrite rep_snoc_sym.
  eapply canReach_step; [eapply step_L_nil; apply (jz_R1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_R0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_I1 _ He) | simp_cons0; simpl rep].
  eapply canReach_step; [eapply step_R_cons; apply (jz_H1 _ He) | simp_cons0].
  exists n. exact (loop_C1 n [0; 1] (cons0 0 R)).
Qed.

Lemma rule_SW_10 : forall m n R,
  CanReach tm (SW m n (1 :: cons0 0 R)) (SW (S m) n R).
Proof.
  intros m n R. unfold SW.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_D1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_zero_cons; apply (jz_Q0 _ He) |].
  eapply canReach_trans; [exists (S n); exact (loop_R1 (S n) (rep01 m [0; 1]) (cons0 0 R)) |].
  rewrite rep_snoc_sym, rep01_zero_unfold.
  eapply canReach_step; [eapply step_L_cons; apply (jz_R1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_R0 _ He) |].
  assert (H0 : cons0 0 (rep10 m [1]) = rep01 m [0; 1]).
  { rewrite cons0_ne_nil by (destruct m; discriminate). rewrite <- rep01_zero_unfold. reflexivity. }
  rewrite H0.
  eapply canReach_step; [eapply step_R_cons; apply (jz_I1 _ He) | simp_cons0; simpl rep].
  eapply canReach_step; [eapply step_R_cons; apply (jz_H1 _ He) | simp_cons0].
  exists n. exact (loop_C1 n (0 :: 1 :: rep01 m [0; 1]) (cons0 0 R)).
Qed.

Lemma rule_CO_10 : forall m n R,
  CanReach tm (CO m n (1 :: cons0 0 R)) (CO (S m) n R).
Proof.
  intros m n R. unfold CO.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_D1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_zero_cons; apply (jz_Q0 _ He) |].
  eapply canReach_trans; [exists (S n); exact (loop_R1 (S n) (rep01 m [0; 0; 1]) (cons0 0 R)) |].
  rewrite rep_snoc_sym, rep01_zero_unfold.
  eapply canReach_step; [eapply step_L_cons; apply (jz_R1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_R0 _ He) |].
  assert (H0 : cons0 0 (rep10 m [0; 1]) = rep01 m [0; 0; 1]).
  { rewrite cons0_ne_nil by (destruct m; discriminate). rewrite <- rep01_zero_unfold. reflexivity. }
  rewrite H0.
  eapply canReach_step; [eapply step_R_cons; apply (jz_I1 _ He) | simp_cons0; simpl rep].
  eapply canReach_step; [eapply step_R_cons; apply (jz_H1 _ He) | simp_cons0].
  exists n. exact (loop_C1 n (0 :: 1 :: rep01 m [0; 0; 1]) (cons0 0 R)).
Qed.

Lemma rule_CI_11 : forall n R,
  CanReach tm (CI n (1 :: 1 :: R)) (CI (n + 4) (1 :: R)).
Proof.
  intros n R. unfold CI.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_D1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_Q1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_trans; [exists n; exact (loop_M1 n [] (0 :: 1 :: R)) |].
  rewrite rep_snoc_sym. cbn [rep].
  eapply canReach_step; [eapply step_L_nil; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_M0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_nil; apply (jz_A0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_B0 _ He) | simp_cons0].
  assert (Hr : 1 :: 1 :: 1 :: rep n 1 (0 :: 1 :: R) = rep (n + 3) 1 (0 :: 1 :: R)).
  { replace (n + 3) with (3 + n) by lia. rewrite <- rep_add_sym. reflexivity. }
  rewrite Hr.
  exists (n + 3).
  pose proof (loop_C1 (n + 3) [1] (0 :: 1 :: R)) as Hc.
  rewrite rep_snoc_sym in Hc.
  replace (S (n + 3)) with (n + 4) in Hc by lia.
  exact Hc.
Qed.

Lemma rule_CI_11_iter : forall k a R,
  CanReach tm (CI a (rep (k + 1) 1 R)) (CI (a + 4 * k) (1 :: R)).
Proof.
  induction k as [| p IH]; intros a R.
  - replace (a + 4 * 0) with a by lia. apply canReach_refl.
  - replace (S p + 1) with (S (S p)) by lia. simpl rep.
    eapply canReach_trans; [apply rule_CI_11 |].
    replace (1 :: rep p 1 R) with (rep (p + 1) 1 R)
      by (replace (p + 1) with (S p) by lia; reflexivity).
    specialize (IH (a + 4) R).
    replace (a + 4 + 4 * p) with (a + 4 * S p) in IH by lia.
    exact IH.
Qed.

Lemma rule_SW_10_iter : forall k m n a R,
  CanReach tm (SW m n (rl (rep k 1 []) (a :: R))) (SW (m + k) n (a :: R)).
Proof.
  induction k as [| p IH]; intros m n a R; simpl.
  - rewrite Nat.add_0_r. apply canReach_refl.
  - eapply canReach_trans; [apply rule_SW_10 |].
    specialize (IH (S m) n a R).
    replace (S m + p) with (m + S p) in IH by lia. exact IH.
Qed.

Lemma rule_CO_10_iter : forall k m n a R,
  CanReach tm (CO m n (rl (rep k 1 []) (a :: R))) (CO (m + k) n (a :: R)).
Proof.
  induction k as [| p IH]; intros m n a R; simpl.
  - rewrite Nat.add_0_r. apply canReach_refl.
  - eapply canReach_trans; [apply rule_CO_10 |].
    specialize (IH (S m) n a R).
    replace (S m + p) with (m + S p) in IH by lia. exact IH.
Qed.

Lemma rule_SW_11_raw : forall m n R,
  CanReach tm (SW m n (1 :: 1 :: R))
              (CI 3 (rl (rep m 1 []) (rep (n + 2) 1 (0 :: 1 :: R)))).
Proof.
  intros m n R. unfold SW.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_D1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_Q1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_trans; [exists n; exact (loop_M1 n (rep01 m [0; 1]) (0 :: 1 :: R)) |].
  rewrite rep_snoc_sym, rep01_zero_unfold.
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_trans; [exists (2 * m); exact (loop_MA_10 m [1] (1 :: rep n 1 (0 :: 1 :: R))) |].
  eapply canReach_trans; [apply jz_M_finish |].
  rewrite one_rep01_eq_rep10, rl_rep_one.
  replace (1 :: 1 :: rep n 1 (0 :: 1 :: R)) with (rep (n + 2) 1 (0 :: 1 :: R))
    by (replace (n + 2) with (S (S n)) by lia; reflexivity).
  apply canReach_refl.
Qed.

Lemma SW_step : forall m n R,
  CanReach tm (SW m n (1 :: 1 :: R)) (SW m (h m n) (1 :: R)).
Proof.
  induction m as [| m' IH]; intros n R.
  - eapply canReach_trans; [apply rule_SW_11_raw | cbn [rep rl]].
    replace (n + 2) with ((n + 1) + 1) by lia.
    eapply canReach_trans; [apply rule_CI_11_iter |].
    replace (3 + 4 * (n + 1)) with (h 0 n) by (cbn [h]; lia).
    apply (rule_CI_10 (h 0 n) (1 :: R)).
  - eapply canReach_trans; [apply rule_SW_11_raw | cbn [rep rl]].
    eapply canReach_trans; [apply rule_CI_10 |].
    replace (n + 2) with (S (n + 1)) by lia. simpl rep.
    eapply canReach_trans; [apply rule_SW_10_iter | rewrite Nat.add_0_l].
    assert (Hiter : forall k a T,
      CanReach tm (SW m' a (rep (k + 1) 1 T)) (SW m' (iter (h m') k a) (1 :: T))).
    { induction k as [| p IHp]; intros a T.
      - apply canReach_refl.
      - replace (S p + 1) with (S (S p)) by lia. simpl rep.
        eapply canReach_trans; [apply IH |].
        replace (1 :: rep p 1 T) with (rep (p + 1) 1 T)
          by (replace (p + 1) with (S p) by lia; reflexivity).
        specialize (IHp (h m' a) T).
        rewrite iter_add_one_jz in IHp. exact IHp. }
    replace (1 :: rep (n + 1) 1 (0 :: 1 :: R)) with (rep ((n + 1) + 1) 1 (0 :: 1 :: R))
      by (replace (n + 1 + 1) with (S (n + 1)) by lia; reflexivity).
    eapply canReach_trans; [apply Hiter |].
    apply (rule_SW_10 m' (h (S m') n) (1 :: R)).
Qed.

Lemma SW_chain : forall k m n R,
  CanReach tm (SW m n (rl (rep k 2 []) R)) (SW (m + k) (hc m k n) R).
Proof.
  induction k as [| p IH]; intros m n R; simpl.
  - rewrite Nat.add_0_r. apply canReach_refl.
  - eapply canReach_trans; [apply SW_step |].
    eapply canReach_trans; [apply rule_SW_10 |].
    specialize (IH (S m) (h m n) R).
    replace (S m + p) with (m + S p) in IH by lia. exact IH.
Qed.

Lemma rule_CO_0_11 : forall n R,
  CanReach tm (CO 0 n (1 :: 1 :: R)) (CO 0 (ho 0 n) (1 :: R)).
Proof.
  intros n R. unfold CO. simpl rep01.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_D1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_Q1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_trans; [exists n; exact (loop_M1 n [0; 0; 1] (0 :: 1 :: R)) |].
  rewrite rep_snoc_sym. cbn [rep].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_B1 _ He) | simp_cons0].
  destruct (mod3_cases n) as [[q Hq] | [[q Hq] | [q Hq]]]; subst.
  - rewrite ho0_mod0.
    assert (Hr : 1 :: 1 :: 1 :: rep (3 * q) 1 (0 :: 1 :: R) =
                 rep (3 * S q) 1 (0 :: 1 :: R)).
    { replace (3 * S q) with (3 + 3 * q) by lia. rewrite <- rep_add_sym. reflexivity. }
    rewrite Hr.
    eapply canReach_trans; [exists (3 * S q); exact (loop_NOP (S q) 1 [] (0 :: 1 :: R)) |].
    simpl rep110.
    eapply canReach_step; [eapply step_L_cons; apply (jz_N0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
    eapply canReach_trans; [exists (3 * q); exact (jz_M_loop q [1] (1 :: 0 :: 0 :: 1 :: R)) |].
    eapply canReach_trans; [apply jz_M_finish |].
    rewrite one_rep101_eq_rl.
    assert (Hrl : rl (rep q 2 []) (1 :: 1 :: 0 :: 0 :: 1 :: R) =
                  1 :: 1 :: cons0 0 (rl (rep q 2 []) (0 :: 1 :: R))).
    { pose proof (rl_append (rep q 2 []) [2] 0 (1 :: R)) as Heq.
      assert (He2 : rep q 2 [] ++ [2] = 2 :: rep q 2 []).
      { clear Hr Heq. induction q as [| k IHk]; simpl; [reflexivity | rewrite IHk; reflexivity]. }
      rewrite He2 in Heq. simpl in Heq. symmetry. exact Heq. }
    rewrite Hrl.
    eapply canReach_trans; [apply rule_CI_11 |].
    eapply canReach_trans; [apply rule_CI_10 |].
    eapply canReach_trans; [apply SW_chain | rewrite Nat.add_0_l].
    apply (rule_SW_0 q (hc 0 q 7) (1 :: R)).
  - rewrite ho0_mod1.
    assert (Hr : 1 :: 1 :: 1 :: rep (3 * q + 1) 1 (0 :: 1 :: R) =
                 rep (3 * S q) 1 (1 :: 0 :: 1 :: R)).
    { rewrite <- rep_add_sym with (a := 3 * q) (b := 1).
      replace (3 * S q) with (3 + 3 * q) by lia.
      rewrite <- rep_add_sym. reflexivity. }
    rewrite Hr.
    eapply canReach_trans; [exists (3 * S q); exact (loop_NOP (S q) 1 [] (1 :: 0 :: 1 :: R)) |].
    eapply canReach_step; [eapply step_R_cons; apply (jz_N1 _ He) |].
    rewrite cons0_ne_nil by (simpl; discriminate).
    eapply canReach_step; [eapply step_L_cons; apply (jz_O0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_R_cons; apply (jz_C0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_cons; apply (jz_D0 _ He) | simp_cons0].
    simpl rep110.
    eapply canReach_step; [eapply step_L_cons; apply (jz_E1 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_cons; apply (jz_E1 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_cons; apply (jz_E1 _ He) | simp_cons0].
    eapply canReach_trans; [exists (3 * q); exact (loop_EF_110 q [1] (1 :: 1 :: 1 :: 0 :: 1 :: R)) |].
    eapply canReach_step; [eapply step_L_cons; apply (jz_E0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_nil; apply (jz_F1 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_nil; apply (jz_E0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_nil; apply (jz_F0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_R_cons; apply (jz_G0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_R_cons; apply (jz_H0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_R_cons; apply (jz_H1 _ He) | simp_cons0].
    assert (Hrr : 1 :: 1 :: rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R) =
                  rep (3 * q + 5) 1 (0 :: 1 :: R)).
    { rewrite rep_snoc_sym, rep_snoc_sym, rep_snoc_sym.
      replace (3 * q + 5) with (2 + S (S (S (3 * q)))) by lia.
      rewrite <- rep_add_sym. reflexivity. }
    rewrite Hrr.
    exists (3 * q + 5). exact (loop_C1 (3 * q + 5) [0; 0; 1] (0 :: 1 :: R)).
  - rewrite ho0_mod2.
    assert (Hr : 1 :: 1 :: 1 :: rep (3 * q + 2) 1 (0 :: 1 :: R) =
                 rep (3 * S q) 1 (1 :: 1 :: 0 :: 1 :: R)).
    { rewrite <- rep_add_sym with (a := 3 * q) (b := 2).
      replace (3 * S q) with (3 + 3 * q) by lia.
      rewrite <- rep_add_sym. reflexivity. }
    rewrite Hr.
    eapply canReach_trans; [exists (3 * S q); exact (loop_NOP (S q) 1 [] (1 :: 1 :: 0 :: 1 :: R)) |].
    eapply canReach_step; [eapply step_R_cons; apply (jz_N1 _ He) |].
    rewrite cons0_ne_nil by (simpl; discriminate).
    eapply canReach_step; [eapply step_R_cons; apply (jz_O1 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_cons; apply (jz_P0 _ He) | simp_cons0].
    eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
    eapply canReach_trans; [exists (3 * S q); exact (jz_M_loop (S q) [1] (0 :: 0 :: 1 :: R)) |].
    eapply canReach_trans; [apply jz_M_finish |].
    rewrite one_rep101_eq_rl. simpl rep. simpl rl.
    eapply canReach_trans; [apply rule_CI_11 |].
    eapply canReach_trans; [apply rule_CI_10 |].
    eapply canReach_trans; [apply SW_chain | rewrite Nat.add_0_l].
    eapply canReach_trans; [apply (rule_SW_10 q (hc 0 q 7) (0 :: 1 :: R)) |].
    replace (S q) with (q + 1) by lia.
    apply (rule_SW_0 (q + 1) (hc 0 q 7) (1 :: R)).
Qed.

Lemma rule_CO_succ_11_raw : forall m n R,
  CanReach tm (CO (S m) n (1 :: 1 :: R))
              (CO m 6 (rep (n + 2) 1 (0 :: 1 :: R))).
Proof.
  intros m n R. unfold CO.
  eapply canReach_step; [eapply step_R_zero; apply (jz_C0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_D1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_Q1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_trans; [exists n; exact (loop_M1 n (rep01 (S m) [0; 0; 1]) (0 :: 1 :: R)) |].
  rewrite rep_snoc_sym, rep01_zero_unfold.
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_trans; [exists (2 * S m); exact (loop_MA_10 (S m) [0; 1] (1 :: rep n 1 (0 :: 1 :: R))) |].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_B1 _ He) | simp_cons0; simpl rep01].
  eapply canReach_step; [eapply step_R_cons; apply (jz_N1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_O1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_P0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_trans; [apply jz_M_finish |].
  eapply canReach_trans; [apply (rule_CI_10 3 (0 :: 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R)))) |].
  eapply canReach_trans; [apply (rule_SW_0 0 3 (1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R)))) |].
  rewrite one_rep01_eq_rep10, rl_rep_one.
  replace (1 :: 1 :: rep n 1 (0 :: 1 :: R)) with (rep (n + 2) 1 (0 :: 1 :: R))
    by (replace (n + 2) with (S (S n)) by lia; reflexivity).
  replace (n + 2) with (S (n + 1)) by lia. simpl rep.
  pose proof (rule_CO_10_iter m 0 6 1 (rep (n + 1) 1 (0 :: 1 :: R))) as H10.
  rewrite Nat.add_0_l in H10. exact H10.
Qed.

Lemma CO_step : forall m n R,
  CanReach tm (CO m n (1 :: 1 :: R)) (CO m (ho m n) (1 :: R)).
Proof.
  induction m as [| m' IH]; intros n R.
  - apply rule_CO_0_11.
  - eapply canReach_trans; [apply rule_CO_succ_11_raw |].
    assert (Hiter : forall k a T,
      CanReach tm (CO m' a (rep (k + 1) 1 T)) (CO m' (iter (ho m') k a) (1 :: T))).
    { induction k as [| p IHp]; intros a T.
      - apply canReach_refl.
      - replace (S p + 1) with (S (S p)) by lia. simpl rep.
        eapply canReach_trans; [apply IH |].
        replace (1 :: rep p 1 T) with (rep (p + 1) 1 T)
          by (replace (p + 1) with (S p) by lia; reflexivity).
        specialize (IHp (ho m' a) T).
        rewrite iter_add_one_jz in IHp. exact IHp. }
    replace (n + 2) with ((n + 1) + 1) by lia.
    eapply canReach_trans; [apply Hiter |].
    apply (rule_CO_10 m' (ho (S m') n) (1 :: R)).
Qed.

Lemma CO_iter : forall k m n R,
  CanReach tm (CO m n (rep (k + 1) 1 R)) (CO m (iter (ho m) k n) (1 :: R)).
Proof.
  induction k as [| p IH]; intros m n R.
  - apply canReach_refl.
  - replace (S p + 1) with (S (S p)) by lia. simpl rep.
    eapply canReach_trans; [apply CO_step |].
    replace (1 :: rep p 1 R) with (rep (p + 1) 1 R)
      by (replace (p + 1) with (S p) by lia; reflexivity).
    specialize (IH m (ho m n) R).
    rewrite iter_add_one_jz in IH. exact IH.
Qed.

Lemma CO_chain : forall k m n R,
  CanReach tm (CO m n (rl (rep k 2 []) R)) (CO (m + k) (hoc m k n) R).
Proof.
  induction k as [| p IH]; intros m n R; simpl.
  - rewrite Nat.add_0_r. apply canReach_refl.
  - eapply canReach_trans; [apply CO_step |].
    eapply canReach_trans; [apply rule_CO_10 |].
    specialize (IH (S m) (ho m n) R).
    replace (S m + p) with (m + S p) in IH by lia. exact IH.
Qed.

End EngineLemmas.
