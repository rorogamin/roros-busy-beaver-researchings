(** * FGH_CNF: CNF below omega^omega

    This is the first reusable ordinal layer for the blank-tape FGH machines.
    It is deliberately small enough to prove now:

      [Some l]  is the finite CNF term whose coefficient of omega^i is
                [nth i l 0];
      [None]    is omega^omega.

    [nf] only requires the leading coefficient to be nonzero; all lower
    coefficients may be zero.  [fs] implements the standard fundamental
    sequence:

      (omega^e * (c+1))[n] = omega^e * c + omega^(e-1) * (n+1)
      (omega^omega)[n]     = omega^n

    The theorem [fs_lt] is the descent fact the machine layer needs: every
    limit step is strictly below the ordinal it came from.  [nf_fs] keeps the
    representation canonical, so [fs] can be iterated without a separate
    normalisation pass.

    This file does not yet define the Wainer hierarchy or a Turing machine.
    It is the ordinal layer on which those are built. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

(** ** Ordinal terms

    [None] is omega^omega.  [Some l] is a finite CNF term.  The list is
    indexed by exponent: position 0 is the omega^0 coefficient, position 1
    the omega^1 coefficient, and so on. *)

Definition ON : Type := option (list nat).

Definition nf_list (l : list nat) : Prop :=
  match rev l with
  | [] => True
  | c :: _ => c <> 0
  end.

Definition nf (a : ON) : Prop :=
  match a with
  | None => True
  | Some l => nf_list l
  end.

Definition has_exp (a : ON) : Prop :=
  match a with
  | None => True
  | Some l => 2 <= length l
  end.

(** A finite CNF term is a limit only when its constant coefficient is zero
    and it has a higher term.  Thus [omega + 2] is a successor, while
    [omega * 2] and [omega] are limits. *)
Definition limit (a : ON) : Prop :=
  match a with
  | None => True
  | Some l =>
      match l with
      | 0 :: _ => 2 <= length l
      | _ => False
      end
  end.

Lemma limit_has_exp : forall a, limit a -> has_exp a.
Proof.
  intros a H. destruct a as [l|]; [|exact I].
  unfold limit in H. destruct l as [|c l'].
  - simpl in H. contradiction.
  - destruct c.
    + simpl in H. unfold has_exp. simpl. exact H.
    + simpl in H. contradiction.
Qed.

(** ** Order

    Reversed coefficient lists are compared by length first: a longer list
    has a larger leading exponent.  At equal length, coefficients are compared
    lexicographically from the leading term down.  This is exactly the
    Cantor-normal-form order on the represented terms. *)

Fixpoint lex_eq (a b : list nat) : Prop :=
  match a, b with
  | ca :: a', cb :: b' => ca < cb \/ (ca = cb /\ lex_eq a' b')
  | [], [] => False
  | _, _ => False
  end.

Definition lt_rev (a b : list nat) : Prop :=
  length a < length b \/ (length a = length b /\ lex_eq a b).

Definition lt_list (a b : list nat) : Prop :=
  lt_rev (rev a) (rev b).

Definition lt (a b : ON) : Prop :=
  match a, b with
  | Some x, Some y => lt_list x y
  | Some _, None => True
  | None, _ => False
  end.

(** ** Fundamental sequences *)

Definition fs_finite (l : list nat) (n : nat) : ON :=
  match rev l with
  | [] => Some []
  | [_] => Some []
  | c :: x :: tl =>
      if Nat.eqb c 1
      then Some (rev ((x + n + 1) :: tl))
      else Some (rev ((c - 1) :: (x + n + 1) :: tl))
  end.

Definition fs (a : ON) (n : nat) : ON :=
  match a with
  | None => Some (rev (1 :: repeat 0 n))
  | Some l => fs_finite l n
  end.

(** ** The canonical-form invariant is preserved *)

Lemma nf_fs : forall a n, nf a -> nf (fs a n).
Proof.
  intros a n Hnf. destruct a as [l|].
  - unfold fs, fs_finite.
    destruct (rev l) as [|c r] eqn:Er.
    + simpl. exact I.
    + destruct r as [|x tl] eqn:Er2.
      * simpl. exact I.
      * assert (Hc : c <> 0).
        { unfold nf, nf_list in Hnf. rewrite Er in Hnf. exact Hnf. }
        destruct (Nat.eqb c 1) eqn:E.
        -- apply Nat.eqb_eq in E. subst c.
           unfold nf, nf_list. rewrite rev_involutive.
           simpl. lia.
        -- apply Nat.eqb_neq in E.
           assert (Hc1 : 1 < c) by lia.
           unfold nf, nf_list. rewrite rev_involutive.
           simpl. lia.
  - unfold fs, nf, nf_list. rewrite rev_involutive.
    simpl. discriminate.
Qed.

(** ** Every limit fundamental sequence strictly decreases *)

Lemma fs_lt : forall a n, nf a -> limit a -> lt (fs a n) a.
Proof.
  intros a n Hnf Hlim.
  pose proof (limit_has_exp a Hlim) as Hexp.
  destruct a as [l|].
  - unfold has_exp in Hexp.
    destruct (rev l) as [|c r] eqn:Er.
    + assert (Hlen0 : length l = 0).
      { rewrite <- (length_rev l). rewrite Er. reflexivity. }
      lia.
    + destruct r as [|x tl] eqn:Er2.
      * assert (Hlen1 : length l = 1).
        { rewrite <- (length_rev l). rewrite Er. reflexivity. }
        lia.
      * assert (Hc : c <> 0).
        { unfold nf, nf_list in Hnf. rewrite Er in Hnf. exact Hnf. }
        unfold fs, fs_finite. rewrite Er.
        unfold lt, lt_list, lt_rev.
        rewrite !length_rev.
        assert (Hlen : length l = S (S (length tl))).
        { rewrite <- (length_rev l). rewrite Er. simpl. lia. }
        destruct (Nat.eqb c 1) eqn:E.
        -- apply Nat.eqb_eq in E. subst c.
           rewrite rev_involutive.
           rewrite Hlen.
           left. simpl. lia.
        -- apply Nat.eqb_neq in E.
           assert (Hc1 : 1 < c) by lia.
           rewrite rev_involutive.
           rewrite Hlen.
           right. split; [simpl; lia|].
           rewrite Er.
           simpl. left. lia.
  - unfold fs, lt. simpl. exact I.
Qed.

(** ** Concrete checks for the first three transfinite rungs *)

Example fs_omega_2 : fs (Some [0; 1]) 2 = Some [3].
Proof. vm_compute. reflexivity. Qed.

Example fs_omega_mul_2_2 : fs (Some [0; 2]) 2 = Some [3; 1].
Proof. vm_compute. reflexivity. Qed.

Example fs_omega_sq_2 : fs (Some [0; 0; 1]) 2 = Some [0; 3].
Proof. vm_compute. reflexivity. Qed.

Example fs_omega_omega_2 : fs None 2 = Some [0; 0; 1].
Proof. vm_compute. reflexivity. Qed.

Example fs_omega2_lt : lt (fs (Some [0; 2]) 2) (Some [0; 2]).
Proof.
  apply fs_lt.
  - unfold nf, nf_list. simpl. discriminate.
  - unfold limit. simpl. lia.
Qed.

Print Assumptions nf_fs.
Print Assumptions fs_lt.
