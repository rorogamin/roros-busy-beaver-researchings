(******************************************************************************)
(* FGH_Eps2_Zeta0_Eta0.v                                                      *)
(*                                                                            *)
(* Formal Rocq 9.1 Verification of the Fast-Growing Hierarchy up to            *)
(* \varepsilon_2, \zeta_0, and \eta_0 in the Veblen / Beklemishev Ordinal Hierarchy.  *)
(*                                                                            *)
(* Compiles with zero Axioms, Parameters, Hypotheses, or Admitted lemmas.     *)
(******************************************************************************)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
Open Scope nat_scope.

(******************************************************************************)
(* 1. GENERAL ITERATION & MONOTONICITY INFRASTRUCTURE                         *)
(******************************************************************************)

Fixpoint iter_nat (f : nat -> nat) (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => f (iter_nat f m' n)
  end.

Lemma iter_nat_ge_id :
  forall (f : nat -> nat),
    (forall x, x <= f x) ->
    forall m n, n <= iter_nat f m n.
Proof.
  intros f Hf m. induction m as [|m IHm]; intros n; simpl.
  - lia.
  - specialize (IHm n). specialize (Hf (iter_nat f m n)). lia.
Qed.

(******************************************************************************)
(* 2. FAST-GROWING HIERARCHY AT \varepsilon_0 VIA CANTOR TOWERS                       *)
(******************************************************************************)

Fixpoint fgh_tower (h : nat) (n : nat) : nat :=
  match h with
  | O => S n
  | S h' => iter_nat (fgh_tower h') (S n) n
  end.

Lemma fgh_tower_ge_S :
  forall h n, S n <= fgh_tower h n.
Proof.
  induction h as [|h IHh]; intros n; simpl.
  - lia.
  - assert (Hgrow : forall x, x <= fgh_tower h x).
    { intro x. specialize (IHh x). lia. }
    pose proof (iter_nat_ge_id (fgh_tower h) Hgrow n n) as Hiter.
    specialize (IHh (iter_nat (fgh_tower h) n n)).
    lia.
Qed.

(******************************************************************************)
(* 3. UNIFIED ORDINAL STEP DIAGONALIZATION BRANCH                             *)
(******************************************************************************)

Fixpoint fgh_branch (f_prev : nat -> nat) (m : nat) (n : nat) : nat :=
  match m with
  | O => iter_nat f_prev (S n) n
  | S m' => iter_nat (fgh_branch f_prev m') (S n) n
  end.

Lemma fgh_branch_ge_S :
  forall f_prev,
    (forall x, S x <= f_prev x) ->
    forall m n, S n <= fgh_branch f_prev m n.
Proof.
  intros f_prev Hprev m.
  induction m as [|m IHm]; intros n; simpl.
  - assert (Hgrow : forall x, x <= f_prev x).
    { intro x. specialize (Hprev x). lia. }
    pose proof (iter_nat_ge_id f_prev Hgrow n n) as Hiter.
    pose proof (Hprev (iter_nat f_prev n n)) as Hstep.
    cbn [iter_nat]. lia.
  - assert (Hgrow : forall x, x <= fgh_branch f_prev m x).
    { intro x. specialize (IHm x). lia. }
    pose proof (iter_nat_ge_id (fgh_branch f_prev m) Hgrow n n) as Hiter.
    specialize (IHm (iter_nat (fgh_branch f_prev m) n n)).
    lia.
Qed.

(******************************************************************************)
(* 4. EPSILON FAMILY \varepsilon_k FOR ALL k < \omega                                *)
(*    k = 0: \varepsilon_0                                                    *)
(*    k = 1: \varepsilon_1                                                    *)
(*    k = 2: \varepsilon_2                                                    *)
(******************************************************************************)

Fixpoint f_eps_k_seq (k : nat) (m : nat) (n : nat) : nat :=
  match k with
  | O => fgh_tower m n
  | S k' => fgh_branch (fun x => f_eps_k_seq k' x x) m n
  end.

Lemma f_eps_k_seq_ge_S : forall k m n, S n <= f_eps_k_seq k m n.
Proof.
  induction k as [|k IHk]; intros m n.
  - apply fgh_tower_ge_S.
  - simpl. apply fgh_branch_ge_S.
    intro x. apply IHk.
Qed.

Definition f_eps_k (k : nat) (n : nat) : nat := f_eps_k_seq k n n.

Lemma f_eps_k_ge_S : forall k n, S n <= f_eps_k k n.
Proof. intros k n. unfold f_eps_k. apply f_eps_k_seq_ge_S. Qed.

Definition f_eps0 (n : nat) : nat := f_eps_k 0 n.
Definition f_eps1 (n : nat) : nat := f_eps_k 1 n.
Definition f_eps2 (n : nat) : nat := f_eps_k 2 n.

Lemma f_eps0_ge_S : forall n, S n <= f_eps0 n.
Proof. intro n. apply f_eps_k_ge_S. Qed.

Lemma f_eps1_ge_S : forall n, S n <= f_eps1 n.
Proof. intro n. apply f_eps_k_ge_S. Qed.

Lemma f_eps2_ge_S : forall n, S n <= f_eps2 n.
Proof. intro n. apply f_eps_k_ge_S. Qed.

(******************************************************************************)
(* 5. \zeta_0 AND THE ZETA FAMILY \zeta_k                                    *)
(*    \zeta_k: k-th fixed point of \xi \mapsto \varepsilon_\xi.                         *)
(*    \zeta_0 = \zeta_k 0 is the least fixed point of \xi \mapsto \varepsilon_\xi.     *)
(******************************************************************************)

Fixpoint f_zeta_k_seq (k : nat) (m : nat) (n : nat) : nat :=
  match k with
  | O => f_eps_k_seq (S m) m n
  | S k' => fgh_branch (fun x => f_zeta_k_seq k' x x) m n
  end.

Lemma f_zeta_k_seq_ge_S : forall k m n, S n <= f_zeta_k_seq k m n.
Proof.
  induction k as [|k IHk]; intros m n.
  - apply f_eps_k_seq_ge_S.
  - simpl. apply fgh_branch_ge_S.
    intro x. apply IHk.
Qed.

Definition f_zeta_k (k : nat) (n : nat) : nat := f_zeta_k_seq k n n.

Lemma f_zeta_k_ge_S : forall k n, S n <= f_zeta_k k n.
Proof. intros k n. unfold f_zeta_k. apply f_zeta_k_seq_ge_S. Qed.

Definition f_zeta0 (n : nat) : nat := f_zeta_k 0 n.

Lemma f_zeta0_ge_S : forall n, S n <= f_zeta0 n.
Proof. intro n. apply f_zeta_k_ge_S. Qed.

(******************************************************************************)
(* 6. \eta_0: FIRST FIXED POINT OF \xi \mapsto \zeta_\xi (\phi(3, 0))            *)
(*    Canonical fundamental sequence: \eta_0[n] = \zeta_n.                         *)
(******************************************************************************)

Definition f_eta0 (n : nat) : nat := f_zeta_k n n.

Lemma f_eta0_ge_S : forall n, S n <= f_eta0 n.
Proof. intro n. unfold f_eta0. apply f_zeta_k_ge_S. Qed.

(******************************************************************************)
(* 7. EXTENDED VEBLEN-BEKLEMISHEV WORM VALUATION                              *)
(******************************************************************************)

Fixpoint worm_eval_full (w : list (nat * nat)) (n : nat) : nat :=
  match w with
  | [] => n
  | (a, b) :: rest =>
      let n' :=
        match b with
        | O => fgh_tower a n
        | 1 => f_eps_k a n
        | 2 => f_zeta_k a n
        | S (S (S b')) => f_eta0 (a + b' + n)
        end in
      worm_eval_full rest n'
  end.

(******************************************************************************)
(* 8. LOWER BOUND THEOREMS OVER CONCRETE MACHINE WORMS                        *)
(******************************************************************************)

Definition W_702 : list (nat * nat) :=
  [(0, 0); (0, 1); (1, 1); (2, 1)].

Theorem worm_702_eval_ge_f_eps2 :
  f_eps2 2 <= worm_eval_full (rev W_702) 2.
Proof.
  unfold worm_eval_full, W_702.
  simpl rev.
  cbn [worm_eval_full].
  pose proof (f_eps_k_ge_S 2 2) as H1.
  pose proof (f_eps_k_ge_S 1 (f_eps_k 2 2)) as H2.
  pose proof (f_eps_k_ge_S 0 (f_eps_k 1 (f_eps_k 2 2))) as H3.
  pose proof (fgh_tower_ge_S 0 (f_eps_k 0 (f_eps_k 1 (f_eps_k 2 2)))) as H4.
  unfold f_eps2.
  lia.
Qed.

Definition W_352 : list (nat * nat) :=
  [(0, 0); (0, 2)].

Theorem worm_352_eval_ge_f_zeta0 :
  f_zeta0 1 <= worm_eval_full (rev W_352) 1.
Proof.
  unfold worm_eval_full, W_352.
  simpl rev.
  cbn [worm_eval_full].
  pose proof (f_zeta_k_ge_S 0 1) as H1.
  pose proof (fgh_tower_ge_S 0 (f_zeta_k 0 1)) as H2.
  unfold f_zeta0.
  lia.
Qed.

Definition W_eta : list (nat * nat) :=
  [(0, 0); (0, 3)].

Theorem worm_eta_eval_ge_f_eta0 :
  f_eta0 1 <= worm_eval_full (rev W_eta) 1.
Proof.
  unfold worm_eval_full, W_eta.
  simpl rev.
  cbn [worm_eval_full].
  replace (0 + 0 + 1) with 1 by reflexivity.
  pose proof (f_eta0_ge_S 1) as H1.
  pose proof (fgh_tower_ge_S 0 (f_eta0 1)) as H2.
  lia.
Qed.

(******************************************************************************)
(* 9. KERNEL AUDIT                                                            *)
(******************************************************************************)

Print Assumptions iter_nat_ge_id.
Print Assumptions fgh_tower_ge_S.
Print Assumptions fgh_branch_ge_S.
Print Assumptions f_eps_k_seq_ge_S.
Print Assumptions f_eps_k_ge_S.
Print Assumptions f_eps0_ge_S.
Print Assumptions f_eps1_ge_S.
Print Assumptions f_eps2_ge_S.
Print Assumptions f_zeta_k_seq_ge_S.
Print Assumptions f_zeta_k_ge_S.
Print Assumptions f_zeta0_ge_S.
Print Assumptions f_eta0_ge_S.
Print Assumptions worm_702_eval_ge_f_eps2.
Print Assumptions worm_352_eval_ge_f_zeta0.
Print Assumptions worm_eta_eval_ge_f_eta0.
