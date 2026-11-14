From Stdlib Require Import List ZArith Arith Lia Bool.
Fixpoint iter_nat (f : nat -> nat) (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => f (iter_nat f m' n)
  end.

(* Variant B: same goal, explicit chaining instead of lia. *)
Lemma vB :
  forall (f : nat -> nat), (forall x, x <= f x) -> forall m n, f n <= iter_nat f (S m) n.
Proof.
  intros f Hf m. induction m as [|m IHm]; intros n; simpl.
  - lia.
  - eapply Nat.le_trans; [ exact (IHm n) | ].
    specialize (Hf (iter_nat f (S m) n)). exact Hf.
Qed.
