(** * Executable halting / score / step checks, with soundness lemmas. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM.
Import ListNotations.

(** [scoreb t k c] is the tape score after [k] steps (0 if the machine has
    already halted, which cannot happen for a live machine). *)
Definition scoreb (t : table) (k : nat) (c : conf) : nat :=
  match run t k c with
  | Some c' => score c'
  | None => 0
  end.

(** [haltsb t k c]: running [k] steps from [c] lands in a halting configuration. *)
Definition haltsb (t : table) (k : nat) (c : conf) : bool :=
  match run t k c with
  | None => false
  | Some c' =>
      match t (cst c') (ccur c') with
      | None => true
      | Some _ => false
      end
  end.

(** [okb t k ns sc c]: from [c], [k] steps are enough to halt, the halt
    configuration has at least [sc] ones on the tape, and [ns <= k]. *)
Definition okb (t : table) (k ns sc : nat) (c : conf) : bool :=
  (ns <=? k) && (sc <=? scoreb t k c) && haltsb t k c.

Lemma haltsb_sound : forall t k c,
  haltsb t k c = true -> exists c', run t k c = Some c' /\ halted t c'.
Proof.
  intros t k c H. unfold haltsb in H.
  destruct (run t k c) as [c'|] eqn:E; [|discriminate H].
  destruct (t (cst c') (ccur c')) as [[[w d] s]|] eqn:E2; [discriminate H|].
  exists c'. split; [reflexivity|]. unfold halted. exact E2.
Qed.

Lemma okb_sound : forall t k ns sc c,
  okb t k ns sc c = true ->
  exists c', ns <= k /\ sc <= score c' /\ run t k c = Some c' /\ halted t c'.
Proof.
  intros t k ns sc c H. unfold okb in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply andb_true_iff in H1. destruct H1 as [Hns Hsc].
  apply Nat.leb_le in Hns.
  destruct (haltsb_sound t k c H2) as [c' [E Hh]].
  apply Nat.leb_le in Hsc. unfold scoreb in Hsc. rewrite E in Hsc.
  exists c'. split; [exact Hns|]. split; [exact Hsc|]. split; assumption.
Qed.

(** ** The tower function: a concrete stand-in for the Wainer hierarchy at [omega]. *)

Fixpoint tower (h : nat) : nat :=
  match h with
  | 0 => 1
  | S h' => 2 ^ (tower h')
  end.

Lemma tower_3 : tower 3 = 16.
Proof. reflexivity. Qed.

Lemma tower_4 : tower 4 = 65536.
Proof. reflexivity. Qed.

Lemma tower_5 : tower 5 = 2 ^ 65536.
Proof. reflexivity. Qed.
