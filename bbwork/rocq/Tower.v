(* The rule behind the eps_0 machine's round loop, proved symbolically.

   One round: the source block has v marks, the destination starts from one
   seed mark and grows by two marks per source mark, so the block that results
   has 1 + 2 v marks.  The drive runs that round once per counter mark, so c
   rounds take a block of v marks to (v + 1) * 2^c - 1 marks, and starting from
   a single mark n stages give the tower of two's.

   What is here: the value rule, its closed form, monotonicity, and the tower
   growth.  What is not here: any step count, and any formula for f_eps_0.
   The tower is f_omega-scale growth -- one stage is one exponentiation, n
   stages is a tower of height n.  A machine at eps_0 needs the number of
   stages itself to decay from a tower; that is a different construction, not a
   lemma about this one. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Open Scope nat_scope.

Definition round (v : nat) : nat := 2 * v + 1.

Fixpoint rounds (c v : nat) : nat :=
  match c with
  | 0 => v
  | S c' => rounds c' (round v)
  end.

Lemma round_ge : forall v, v <= round v.
Proof. intros v; unfold round; lia. Qed.

Lemma round_seed : forall v, round v = 1 + 2 * v.
Proof. intros v; unfold round; lia. Qed.

Lemma rounds_ge : forall c v, v <= rounds c v.
Proof.
  induction c as [| c IH]; intros v.
  - simpl. lia.
  - simpl. apply Nat.le_trans with (round v).
    + apply round_ge.
    + apply IH.
Qed.

Lemma rounds_shift : forall c v, round (rounds c v) = rounds c (round v).
Proof.
  induction c as [| c IH]; intros v.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma pow2_succ : forall c, 2 ^ S c = 2 * 2 ^ c.
Proof. intros c; simpl; reflexivity. Qed.

Theorem rounds_closed : forall c v, rounds c v + 1 = (v + 1) * 2 ^ c.
Proof.
  induction c as [| c IH]; intros v.
  - simpl. lia.
  - simpl. rewrite IH. unfold round. nia.
Qed.

Lemma rounds_ge_pow2 : forall c v, 2 ^ c <= rounds c v + 1.
Proof. intros c v; rewrite rounds_closed; nia. Qed.

Fixpoint tower (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => round (tower k)
  end.

Lemma tower_succ : forall n, tower (S n) = 2 * tower n + 1.
Proof. intros n; simpl; unfold round; lia. Qed.

Lemma tower_is_rounds : forall n, tower n = rounds n 1.
Proof.
  induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite rounds_shift. reflexivity.
Qed.

Lemma tower_dominates_pow2 : forall n, 2 ^ n <= tower n + 1.
Proof.
  induction n as [| n IH].
  - simpl. lia.
  - rewrite pow2_succ. rewrite tower_succ. lia.
Qed.

Lemma tower_strict : forall n, tower n < tower (S n).
Proof. intros n; rewrite tower_succ; lia. Qed.

Print Assumptions rounds_closed.
Print Assumptions tower_is_rounds.
Print Assumptions tower_dominates_pow2.

(* The cost of c rounds, given what a round costs.  [sum_rounds] is the total
   number of marks the drive touches, one per round: round i sees a block of
   [rounds i v] marks.  [linear_cost] is then the schema "k steps per round,
   plus one step per mark touched", with k covering the fixed part of a round
   (the two append steps, the erase, the turn).  The closed form is exact. *)

Fixpoint sum_rounds (c v : nat) : nat :=
  match c with
  | 0 => 0
  | S c' => v + sum_rounds c' (round v)
  end.

Lemma sum_rounds_closed : forall c v,
  sum_rounds c v + c + (v + 1) = (v + 1) * 2 ^ c.
Proof.
  induction c as [| c IH]; intros v.
  - simpl. lia.
  - simpl. assert (H := IH (round v)).
    unfold round in *. nia.
Qed.

Definition linear_cost (k c v : nat) : nat := k * c + sum_rounds c v.

Theorem linear_cost_closed : forall k c v,
  linear_cost k c v + c + (v + 1) = k * c + (v + 1) * 2 ^ c.
Proof.
  intros k c v. unfold linear_cost.
  assert (H := sum_rounds_closed c v). nia.
Qed.

Print Assumptions sum_rounds_closed.
Print Assumptions linear_cost_closed.
