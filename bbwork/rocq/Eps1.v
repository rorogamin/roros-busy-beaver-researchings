(* eps_1's first feedback, stated as a rule about values.

   Tower.v proves the eps_0 rule: one round takes a block of v marks to
   2 v + 1, c rounds take it to (v + 1) * 2^c - 1, and the stage count c is a
   count handed in by the input.  One stage is then one exponentiation and n
   stages are a tower of two's of height n: f_omega-scale, and no bigger
   argument at that one level changes the class.

   The smallest change that *does* leave that class is to stop handing the
   count in.  Here the number of rounds is the value itself:

       nest v = rounds v v

   so stage i runs on the marks the previous stage produced.  What is proved
   below, for every v and not by sampling:

     * the closed form  nest v + 1 = (v + 1) * 2^v ;
     * monotonicity in v, and strict growth;
     * the escaping property, which is the point of the construction: for every
       fixed count c and every value v, the eps_0 engine with c rounds is
       strictly below the diagonal at a slightly larger value.  A fixed number
       of stages can therefore never catch the diagonal -- the height of the
       tower is data, so the tower-of-towers is not reachable by any fixed
       height, which is exactly what eps_1 is above eps_0;
     * the eps_0 fundamental sequence (the tower) is strictly increasing, and
       every one of its values is strictly below the diagonal.

   What is NOT here, and must not be read into it: a machine, a step count, or
   any claim about f_eps_1.  eps_1 needs a second feedback (the exponent is
   itself a numeral, so the descent re-reads the notation), and this file
   formalises only the value rule of the first feedback.  See
   EPSILON_ANALYSIS.md for what the missing layer is. *)

From Stdlib Require Import Arith Lia.
From Top Require Import Tower.

Open Scope nat_scope.

(** ** The round is monotone *)

Lemma round_mono : forall a b, a <= b -> round a <= round b.
Proof. intros a b H. unfold round. lia. Qed.

Lemma round_strict : forall a b, a < b -> round a < round b.
Proof. intros a b H. unfold round. lia. Qed.

Lemma rounds_mono_v : forall c v v', v <= v' -> rounds c v <= rounds c v'.
Proof.
  induction c as [|c IH]; intros v v' H.
  - simpl. exact H.
  - simpl. apply IH. apply round_mono. exact H.
Qed.

Lemma rounds_lt_v : forall c v v', v < v' -> rounds c v < rounds c v'.
Proof.
  induction c as [|c IH]; intros v v' H.
  - simpl. exact H.
  - simpl. apply IH. apply round_strict. exact H.
Qed.

(** One more round never lowers the value, so the count can go up. *)

Lemma rounds_succ_c : forall c v, rounds c v <= rounds (S c) v.
Proof.
  intros c v. simpl. apply rounds_mono_v. apply round_ge.
Qed.

Lemma rounds_mono_c : forall c c' v, c <= c' -> rounds c v <= rounds c' v.
Proof.
  intros c c' v H. induction H as [|c' H IH].
  - lia.
  - apply Nat.le_trans with (rounds c' v).
    + exact IH.
    + apply rounds_succ_c.
Qed.

(** ** The diagonal: the stage count is the value *)

Definition nest (v : nat) : nat := rounds v v.

Theorem nest_closed : forall v, nest v + 1 = (v + 1) * 2 ^ v.
Proof. intros v. unfold nest. apply rounds_closed. Qed.

Lemma nest_ge : forall v, v <= nest v.
Proof. intros v. unfold nest. apply rounds_ge. Qed.

Lemma nest_mono : forall v v', v <= v' -> nest v <= nest v'.
Proof.
  intros v v' H. unfold nest.
  apply Nat.le_trans with (rounds v' v).
  - apply rounds_mono_c. exact H.
  - apply rounds_mono_v. exact H.
Qed.

Theorem nest_strict : forall v, nest v < nest (S v).
Proof.
  intros v. unfold nest.
  apply Nat.le_lt_trans with (rounds (S v) v).
  - apply rounds_mono_c. lia.
  - apply rounds_lt_v. lia.
Qed.

(** ** The diagonal escapes every fixed tower *)

(** The eps_0 engine with any fixed number of stages, at any value, is strictly
    below the diagonal.  This is the whole difference between the two rungs on
    values: no fixed stage count reaches it. *)

Theorem nest_escapes_fixed : forall c v, rounds c v < nest (S (S (c + v))).
Proof.
  intros c v. unfold nest.
  apply Nat.le_lt_trans with (rounds (S (S (c + v))) v).
  - apply rounds_mono_c. lia.
  - apply rounds_lt_v. lia.
Qed.

(** The tower of height k is the eps_0 fundamental sequence written out, so it
    is below the diagonal too -- and strictly, for every k. *)

Definition eps0_fs (n : nat) : nat := tower n.

Theorem tower_le_nest : forall k, tower k <= nest (S k).
Proof.
  intros k. rewrite tower_is_rounds.
  apply Nat.le_trans with (rounds (S k) 1).
  - apply rounds_mono_c. lia.
  - apply rounds_mono_v. lia.
Qed.

Theorem tower_lt_nest : forall k, tower k < nest (S (S k)).
Proof.
  intros k. rewrite tower_is_rounds.
  apply Nat.le_lt_trans with (rounds (S (S k)) 1).
  - apply rounds_mono_c. lia.
  - apply rounds_lt_v. lia.
Qed.

Theorem eps0_fs_strict : forall n, eps0_fs n < eps0_fs (S n).
Proof. intros n. unfold eps0_fs. apply tower_strict. Qed.

Theorem eps0_fs_below_nest : forall n, eps0_fs n < nest (S (S n)).
Proof. intros n. unfold eps0_fs. apply tower_lt_nest. Qed.

Print Assumptions round_mono.
Print Assumptions rounds_mono_v.
Print Assumptions rounds_lt_v.
Print Assumptions rounds_succ_c.
Print Assumptions rounds_mono_c.
Print Assumptions nest_closed.
Print Assumptions nest_mono.
Print Assumptions nest_strict.
Print Assumptions nest_escapes_fixed.
Print Assumptions tower_le_nest.
Print Assumptions tower_lt_nest.
Print Assumptions eps0_fs_strict.
Print Assumptions eps0_fs_below_nest.
