(** * Eps0Blank.v -- the eps0 drive started from a completely blank tape

    The 33-state drive of [tools/eps0_machine.py] starts on a prepared frame.
    This file adds a 11-state prologue: state 0 is the start state, the tape is
    entirely blank, and the head is on cell 0.  The prologue writes, right to
    left,

        1(seed) 0 1^v 0 1(wall) 0 1^n(stage block)

    so that the tape read left to right is

        1^n 0 1(wall) 0 1^v 0 1(seed)

    and hands the drive its usual gap cell.  The concrete instance proved here
    is n = 2, v = 2.  It reaches its halt configuration after 68276
    transitions with the value 255:

        1(wall) 0^268 1^255 0 1(seed)

    This is a genuine blank-tape run of the eps0 descent engine.  It is a
    concrete finite instance; it is not a proof that the machine realizes
    f_eps0(n) for every n. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From Top Require Import TM Eps0Drive.

(** ** The prologue and the shifted drive *)

Definition SHIFT : nat := 11.

(** The prologue writes the frame, then crosses the wall into the drive's gap.
    States 0..8 write one cell each; 9 is the return walk; 10 crosses the wall.
    Every prologue state has a row for both symbols, so the start is legal on
    a completely blank tape. *)

Definition btbl : table := fun s b =>
  match s with
  | 0 => Some (on, false, 1)     (* seed, cell 0 *)
  | 1 => Some (bl, false, 2)     (* blank between seed and value *)
  | 2 => Some (on, false, 3)     (* value mark 1 *)
  | 3 => Some (on, false, 4)     (* value mark 2 *)
  | 4 => Some (bl, false, 5)     (* gap right of the wall *)
  | 5 => Some (on, false, 6)     (* wall *)
  | 6 => Some (bl, false, 7)     (* blank left of the wall *)
  | 7 => Some (on, false, 8)     (* stage mark 1 *)
  | 8 => Some (on, true, 9)      (* stage mark 2 (leftmost), turn back *)
  | 9 =>
      match b with
      | on => Some (on, true, 9)   (* return over the stage block *)
      | bl => Some (bl, true, 10)  (* blank left of the wall *)
      end
  | 10 =>
      match b with
      | on => Some (on, true, SHIFT + F0)  (* wall -> drive gap *)
      | bl => Some (bl, true, SHIFT + F0)
      end
  | _ =>
      match dtbl (s - SHIFT) b with
      | None => None
      | Some (w, d, t) => Some (w, d, t + SHIFT)
      end
  end.

Definition c0 : conf := mkConf 0 [] bl [].

(** The halt configuration, written in the zipper representation of [TM.v].
    The head is on the blank immediately left of the wall. *)
Definition cf : conf :=
  mkConf 34 [bl; bl; bl] bl (on :: zeros 268 ++ ones 255 ++ bl :: on :: []).

(** ** The concrete blank-tape run *)

Lemma blank_boot_run :
  run btbl 68276 c0 = Some cf.
Proof. vm_compute. reflexivity. Qed.

Lemma blank_boot_halted :
  halted btbl cf.
Proof. vm_compute. reflexivity. Qed.

Lemma blank_boot_halts :
  exists c', run btbl 68276 c0 = Some c' /\ halted btbl c'.
Proof.
  exists cf. split; [apply blank_boot_run | apply blank_boot_halted].
Qed.

Print Assumptions blank_boot_halts.
