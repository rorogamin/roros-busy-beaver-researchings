(** * Turing machines: semantics, step counts, tape score. *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Symbols and directions *)

Inductive sym : Type := bl | on.

Definition dirn : Type := bool.  (* true = right, false = left *)

(** A configuration is a "zipper": the cells to the left of the head (nearest
    first), the cell under the head, and the cells to the right (nearest
    first).  A missing cell is [bl], so the tape is infinite in both
    directions and initially blank. *)

Record conf : Type := mkConf {
  cst  : nat;          (* state *)
  clft : list sym;     (* cells left of the head, reversed *)
  ccur : sym;          (* cell under the head *)
  crgt : list sym      (* cells right of the head *)
}.

Definition table : Type := nat -> sym -> option (sym * dirn * nat).

(** One transition: write, move, change state. *)
Definition step (t : table) (c : conf) : option conf :=
  match t (cst c) (ccur c) with
  | None => None
  | Some (w, d, s) =>
      if d then
        Some (mkConf s (w :: clft c) (hd bl (crgt c)) (tl (crgt c)))
      else
        Some (mkConf s (tl (clft c)) (hd bl (clft c)) (w :: crgt c))
  end.

Fixpoint run (t : table) (k : nat) (c : conf) : option conf :=
  match k with
  | 0 => Some c
  | S k' => match step t c with
            | None => None
            | Some c' => run t k' c'
            end
  end.

Lemma run_S : forall t k c,
  run t (S k) c =
  match step t c with
  | Some c' => run t k c'
  | None => None
  end.
Proof. intros. reflexivity. Qed.

Lemma run_add : forall t a b c,
  run t (a + b) c =
  match run t a c with
  | None => None
  | Some c' => run t b c'
  end.
Proof.
  intros t a. induction a as [|a IH]; intros b c.
  - cbn [Nat.add run]. reflexivity.
  - cbn [Nat.add run]. destruct (step t c) as [c'|].
    + apply IH.
    + reflexivity.
Qed.

(** [halted t c]: the machine has no transition at [c]. *)
Definition halted (t : table) (c : conf) : Prop := t (cst c) (ccur c) = None.

(** ** Reachability with a lower bound on the number of steps *)

Definition ReachL (t : table) (c c' : conf) (n : nat) : Prop :=
  exists k, n <= k /\ run t k c = Some c'.

Lemma ReachL_mono : forall t c c' n m,
  n <= m -> ReachL t c c' m -> ReachL t c c' n.
Proof.
  intros t c c' n m H [k [Hk Hr]]. exists k. split; [lia|exact Hr].
Qed.

Lemma ReachL_trans : forall t c1 c2 c3 n1 n2,
  ReachL t c1 c2 n1 -> ReachL t c2 c3 n2 -> ReachL t c1 c3 (n1 + n2).
Proof.
  intros t c1 c2 c3 n1 n2 [k1 [H1 R1]] [k2 [H2 R2]].
  exists (k1 + k2). split; [lia|].
  rewrite run_add, R1. exact R2.
Qed.

Lemma ReachL_refl : forall t c, ReachL t c c 0.
Proof. intros. exists 0. split; [lia|reflexivity]. Qed.

(** ** Notation for blocks of cells *)

Definition ones (n : nat) : list sym := repeat on n.
Definition zeros (n : nat) : list sym := repeat bl n.

Lemma ones_app : forall a b, ones (a + b) = ones a ++ ones b.
Proof. intros. unfold ones. rewrite repeat_app. reflexivity. Qed.

Lemma zeros_app : forall a b, zeros (a + b) = zeros a ++ zeros b.
Proof. intros. unfold zeros. rewrite repeat_app. reflexivity. Qed.

(** ** Tape score: the number of [on] cells on the tape *)

Fixpoint nblk (l : list sym) : nat :=
  match l with
  | [] => 0
  | x :: l' => (if x then 0 else 1) + nblk l'
  end.

Definition score (c : conf) : nat := nblk (clft c) + (if ccur c then 0 else 1) + nblk (crgt c).

Lemma nblk_zeros : forall n, nblk (zeros n) = 0.
Proof.
  intros n. induction n as [|n IH].
  - reflexivity.
  - change (nblk (bl :: zeros n) = 0). cbn [nblk]. rewrite IH. reflexivity.
Qed.

Lemma nblk_ones : forall n, nblk (ones n) = n.
Proof.
  intros n. induction n as [|n IH].
  - reflexivity.
  - change (nblk (on :: ones n) = S n). cbn [nblk]. rewrite IH. reflexivity.
Qed.

Lemma nblk_app : forall a b, nblk (a ++ b) = nblk a + nblk b.
Proof.
  intros a b. induction a as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. lia.
Qed.

