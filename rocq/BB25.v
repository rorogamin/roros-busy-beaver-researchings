(** * A five-symbol Turing-machine layer for BB(2,5).

    This is deliberately separate from [TM.v], whose [sym] has only two
    symbols.  A configuration is a zipper: the cells immediately left of the
    head (nearest first), the cell under the head, and the cells immediately
    right (nearest first).  Missing cells are blank symbol [b0]. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

Inductive sym5 : Type := b0 | b1 | b2 | b3 | b4.

Definition dir5 : Type := bool.  (* true = right, false = left *)

Record conf5 : Type := mkConf5 {
  st5   : nat;
  left5 : list sym5;
  cur5  : sym5;
  right5: list sym5
}.

Definition table5 : Type := nat -> sym5 -> option (sym5 * dir5 * nat).

Definition step5 (t : table5) (c : conf5) : option conf5 :=
  match t (st5 c) (cur5 c) with
  | None => None
  | Some (w, d, q) =>
      if d then
        Some (mkConf5 q (w :: left5 c) (hd b0 (right5 c)) (tl (right5 c)))
      else
        Some (mkConf5 q (tl (left5 c)) (hd b0 (left5 c)) (w :: right5 c))
  end.

Fixpoint run5 (t : table5) (k : nat) (c : conf5) : option conf5 :=
  match k with
  | 0 => Some c
  | S k' =>
      match step5 t c with
      | None => None
      | Some c' => run5 t k' c'
      end
  end.

Lemma run5_S : forall t k c,
  run5 t (S k) c =
  match step5 t c with
  | Some c' => run5 t k c'
  | None => None
  end.
Proof. intros. reflexivity. Qed.

Lemma run5_add : forall t a b c,
  run5 t (a + b) c =
  match run5 t a c with
  | None => None
  | Some c' => run5 t b c'
  end.
Proof.
  intros t a. induction a as [|a IH]; intros b c.
  - cbn [Nat.add run5]. reflexivity.
  - cbn [Nat.add run5]. destruct (step5 t c) as [c'|].
    + apply IH.
    + reflexivity.
Qed.

(** A canonical BB(2,5) cycle-start configuration for the two machines in
    the current investigation.  The binary cells are stored least
    significant first; the terminator [3,1] is appended to the left zipper.
    [tern] is a flat list of two-cell ternary digits and [pad] is the number
    of trailing [b2] cells on the right. *)

Definition cycleStart (bin tern : list sym5) (pad : nat) : conf5 :=
  mkConf5 0 (bin ++ [b3; b1]) b2 (tern ++ repeat b2 pad).

Definition init5 : conf5 := mkConf5 0 [] b0 [].
