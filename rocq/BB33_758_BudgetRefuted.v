(*
  Rocq counterpart of [cryptids_a6/BusyBeaver/BB33/M_758_BudgetRefuted.lean].

  Holdout #758 = 1RB2LC1RC_2LC---2RB_2LA0LB0RA.

  [Budget B] of [BB33_758_TBudget] bounds the growth of [Q = a + 2c] over the
  prefixes of [run], and [run] stops **only** on [Out.halt].  The accelerated
  map does not halt from the post-[j] states: it keeps returning to [a = 1]
  (rule [h]) and halving [c] again, so [Survives n] holds for every [n] while
  [Q] grows by at least 3 per step.  Hence no [Budget B] holds, and the
  hypothesis of [postJ_survives_le_10000] can never be discharged.

  The witness below is the *smallest* post-[j] state,
  [(2*3^1 - 1, 1) = (5, 1)]: it survives 10001 steps and reaches
  [(485, 25453)], where [Q] has risen by 51384 > 30000.

  The stopping rule that makes the halving-time question well posed is [ht] of
  [BB33_758_Halving844] ([Out.halt], or [a' = 1], or [2*c' <= c0]).  The budget
  has to be restated over that rule before the alternation bound of
  [BB33_758_ATTACK.md] §15 has any content.

  No [Admitted], no [Parameter], no [Axiom].
*)

From Stdlib Require Import Arith Lia.
From Top Require Import BB33_758_TBudget.

(* ------------------------------------------------------------------ *)
(** ** 1. The witness run                                             *)
(* ------------------------------------------------------------------ *)

(** 10001 accelerated steps from the smallest post-[j] state [(5,1)]. *)
Lemma run_10001 : run 10001 (5, 1) = Some (485, 25453).
Proof. vm_compute. reflexivity. Qed.

(** Along those 10001 steps [Q = a + 2*c] grows by 51384, not by 30000. *)
Lemma Q_run_10001 : Q 485 25453 = Q 5 1 + 51384.
Proof. vm_compute. reflexivity. Qed.

(** So [(5,1)] survives 10001 steps, comfortably past the claimed 10000. *)
Lemma survives_10001 : Survives 10001 5 1.
Proof. exists 485, 25453. exact run_10001. Qed.

(* ------------------------------------------------------------------ *)
(** ** 2. Consequences                                                *)
(* ------------------------------------------------------------------ *)

(** **The conclusion of the universal bound is false at [(5,1)].** *)
Theorem not_survives_le_10000 : ~ (forall n, Survives n 5 1 -> n <= 10000).
Proof.
  intros h.
  pose proof (h 10001 survives_10001) as H.
  clear h.
  cbn in H.
  lia.
Qed.

(** **The budget of 30000 is false**, so [postJ_survives_le_10000] is vacuous. *)
Theorem not_budget_30000 : ~ Budget 30000.
Proof.
  intros hB.
  unfold Budget in hB.
  assert (h1 : Q 5 1 + 3 * 10001 <= Q 485 25453)
    by (apply run_Q; exact run_10001).
  assert (h2 : Q 485 25453 <= Q 5 1 + 30000).
  { apply (hB 1 1 10001 485 25453).
    - lia. - lia. - cbn; lia.
    - exact run_10001. }
  cbn in h1, h2.
  lia.
Qed.

(** The same run refutes every budget below [3 * 10001]. *)
Theorem not_budget_of_lt (B : nat) (hB : B < 30003) : ~ Budget B.
Proof.
  intros h.
  unfold Budget in h.
  assert (h1 : Q 5 1 + 3 * 10001 <= Q 485 25453)
    by (apply run_Q; exact run_10001).
  assert (h2 : Q 485 25453 <= Q 5 1 + B).
  { apply (h 1 1 10001 485 25453).
    - lia. - lia. - cbn; lia.
    - exact run_10001. }
  cbn -[Q] in hB, h1, h2.
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 3. Every claim is closed                                       *)
(* ------------------------------------------------------------------ *)

Print Assumptions run_10001.
Print Assumptions Q_run_10001.
Print Assumptions survives_10001.
Print Assumptions not_survives_le_10000.
Print Assumptions not_budget_30000.
Print Assumptions not_budget_of_lt.
