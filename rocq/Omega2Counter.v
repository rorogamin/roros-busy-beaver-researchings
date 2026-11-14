(** * Omega2Counter: a blank-tape counter machine for the omega*2 descent

    This is a literal four-symbol machine.  It is not a timer: the tape carries

      wall  A^a  0  marker  N^n  ...

    with the head on the cell immediately left of [marker].  [a] is the
    coefficient of omega, [n] is the current fundamental-sequence index, and
    the number [b] of N cells to the left of the marker is the coefficient of
    omega^0.  The loop has exactly the two moves of the omega*2 chain:

      b > 0:  pred  (a,b,n) -> (a,b-1,n+1)
      b = 0:  fs    (a,b,n) -> (a-1,n,n)      (a > 0)

    and it halts at (0,0,n).  The boot below installs a = 10, b = 0, n = 1 on
    a blank tape.  The concrete run is checked by the kernel; the closed-form
    theorem [omega2_chain_closed] records the resulting 2^a*n behaviour of the
    abstract chain.  This file proves the machine's descent behaviour.  It
    does not claim a step-count lower bound for f_{omega*2}; that is a separate
    growth obligation. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

(** ** Four-symbol tape semantics *)

Inductive osym : Type :=
  | O0 : osym   (* blank *)
  | OA : osym   (* coefficient of omega *)
  | ON : osym   (* counter / fundamental-sequence index *)
  | OM : osym.  (* wall and moving marker *)

Definition odir : Type := bool.  (* true = right, false = left *)

Record oconf : Type := mkOConf {
  ost  : nat;
  olft : list osym;   (* cells left of the head, nearest first *)
  ocur : osym;
  orgt : list osym    (* cells right of the head, nearest first *)
}.

Definition otable : Type := nat -> osym -> option (osym * odir * nat).

Definition ostep (t : otable) (c : oconf) : option oconf :=
  match t (ost c) (ocur c) with
  | None => None
  | Some (w, d, s) =>
      if d then
        Some (mkOConf s (w :: olft c) (hd O0 (orgt c)) (tl (orgt c)))
      else
        Some (mkOConf s (tl (olft c)) (hd O0 (olft c)) (w :: orgt c))
  end.

Fixpoint orun (t : otable) (k : nat) (c : oconf) : option oconf :=
  match k with
  | 0 => Some c
  | S k' => match ostep t c with
            | None => None
            | Some c' => orun t k' c'
            end
  end.

Lemma orun_S : forall t k c,
  orun t (S k) c =
  match ostep t c with
  | Some c' => orun t k c'
  | None => None
  end.
Proof. intros. reflexivity. Qed.

Lemma orun_add : forall t a b c,
  orun t (a + b) c =
  match orun t a c with
  | None => None
  | Some c' => orun t b c'
  end.
Proof.
  intros t a. induction a as [|a IH]; intros b c.
  - cbn [Nat.add orun]. reflexivity.
  - cbn [Nat.add orun]. destruct (ostep t c) as [c'|].
    + apply IH.
    + reflexivity.
Qed.

Definition ohalted (t : otable) (c : oconf) : Prop :=
  t (ost c) (ocur c) = None.

(** ** The literal transition table

    States:
      0        boot: left wall
      1..10    boot: ten A marks
      11       boot: separator
      12       boot: marker
      13       boot: first N
      14       boot: move left of the marker
      15       loop
      16..18   pred (marker left, old marker to N, append N)
      19..21   fs (decrement A, move marker to the right end)
      22       halt (no row)
*)

Definition tbl : otable := fun s b =>
  match s with
  | 0 => match b with
    | O0 => Some (OM, true, 1)
    | _ => None
    end
  | 1 => match b with O0 => Some (OA, true, 2) | _ => None end
  | 2 => match b with O0 => Some (OA, true, 3) | _ => None end
  | 3 => match b with O0 => Some (OA, true, 4) | _ => None end
  | 4 => match b with O0 => Some (OA, true, 5) | _ => None end
  | 5 => match b with O0 => Some (OA, true, 6) | _ => None end
  | 6 => match b with O0 => Some (OA, true, 7) | _ => None end
  | 7 => match b with O0 => Some (OA, true, 8) | _ => None end
  | 8 => match b with O0 => Some (OA, true, 9) | _ => None end
  | 9 => match b with O0 => Some (OA, true, 10) | _ => None end
  | 10 => match b with O0 => Some (OA, true, 11) | _ => None end
  | 11 => match b with O0 => Some (O0, true, 12) | _ => None end
  | 12 => match b with O0 => Some (OM, true, 13) | _ => None end
  | 13 => match b with O0 => Some (ON, false, 14) | _ => None end
  | 14 => match b with OM => Some (OM, false, 15) | _ => None end
  | 15 => match b with
    | ON => Some (OM, true, 16)     (* pred: the old N becomes the new marker *)
    | O0 => Some (O0, false, 19)    (* b = 0: fundamental sequence *)
    | _ => None
    end
  | 16 => match b with OM => Some (ON, true, 17) | _ => None end
  | 17 => match b with
    | ON => Some (ON, true, 17)     (* walk to the right end of the N block *)
    | O0 => Some (ON, false, 18)    (* append one N *)
    | _ => None
    end
  | 18 => match b with
    | ON => Some (ON, false, 18)    (* walk back to the new marker *)
    | OM => Some (OM, false, 15)
    | _ => None
    end
  | 19 => match b with
    | O0 => Some (O0, false, 19)    (* scan left through the A region *)
    | OA => Some (O0, true, 20)     (* spend one A *)
    | OM => Some (OM, false, 22)    (* a = 0: halt at the left wall *)
    | _ => None
    end
  | 20 => match b with
    | O0 => Some (O0, true, 20)     (* return to the marker *)
    | OM => Some (O0, true, 21)     (* erase the old marker *)
    | _ => None
    end
  | 21 => match b with
    | ON => Some (ON, true, 21)     (* cross the N block *)
    | O0 => Some (OM, false, 15)    (* marker at the right end: b = n *)
    | _ => None
    end
  | _ => None
  end.

Definition entry : oconf := mkOConf 0 [] O0 [].

(** ** The concrete blank-tape run *)

Definition nsteps : nat := 703409.

Definition osym_eqb (x y : osym) : bool :=
  match x, y with
  | O0, O0 => true
  | OA, OA => true
  | ON, ON => true
  | OM, OM => true
  | _, _ => false
  end.

Fixpoint count_sym (s : osym) (l : list osym) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if osym_eqb x s then 1 else 0) + count_sym s xs
  end.

Definition countA (c : oconf) : nat :=
  count_sym OA (olft c ++ ocur c :: orgt c).

Definition countN (c : oconf) : nat :=
  count_sym ON (olft c ++ ocur c :: orgt c).

Theorem omega2_counter_halts :
  exists c', orun tbl nsteps entry = Some c' /\ ohalted tbl c' /\
             countA c' = 0 /\ countN c' = 1024.
Proof.
  vm_compute.
  eexists. repeat split; reflexivity.
Qed.

(** The boot leaves a = 10, b = 0, n = 1 with the head left of the marker. *)
Example omega2_boot :
  orun tbl 15 entry =
  Some (mkOConf 15
    [OA; OA; OA; OA; OA; OA; OA; OA; OA; OA; OM]
    O0
    [OM; ON]).
Proof. vm_compute. reflexivity. Qed.

(** ** The abstract chain

    This is the rule the loop implements, independent of the tape.  It is
    stated with a decreasing first component, so the proof is structural. *)

Fixpoint preds (b n : nat) : nat :=
  match b with
  | 0 => n
  | S b' => preds b' (S n)
  end.

Fixpoint cycle (a n : nat) : nat :=
  match a with
  | 0 => n
  | S a' => cycle a' (preds n n)
  end.

Lemma preds_add : forall b n, preds b n = b + n.
Proof.
  intros b. induction b as [|b IH]; intros n.
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma cycle_closed : forall a n, cycle a n = 2 ^ a * n.
Proof.
  intros a. induction a as [|a IH]; intros n.
  - simpl. lia.
  - simpl. rewrite IH. rewrite preds_add.
    replace (n + n) with (2 * n) by lia.
    replace (2 ^ S a) with (2 * 2 ^ a) by reflexivity.
    ring.
Qed.

Theorem omega2_chain_closed :
  forall a n, cycle a n = 2 ^ a * n.
Proof. exact cycle_closed. Qed.

Example omega2_chain_10_1 : cycle 10 1 = 1024.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions omega2_counter_halts.
Print Assumptions omega2_boot.
Print Assumptions omega2_chain_closed.
