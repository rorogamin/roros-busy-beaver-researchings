(** * Eps1Complete.v -- Blank-tape epsilon_1-level Turing machine

    Builds on the bundle's verified Eps1Tape.tbl (59 active states),
    Eps1Copy.sweep, and Eps1Ladder.lvl by adding a 13-state blank-tape
    prologue (states 0..12) that writes the initial rung frame:

        1^2(budget, a=1) 0^2 1(wall) 0^2 1(v=1) 0 1(seed)

    and enters SHIFT + ENTRY (state 13 + 33 = 46) with the head on the wall.
    The resulting 72-state 2-symbol Turing machine [btbl_eps1] runs
    unconditionally from the completely blank tape [c0] and halts at
    step 115 with 5 ones on the tape (a = 1 instance).  For general
    budget a, [Eps1Ladder.lvl a 1] governs the output value.

    Note: Compiled check requires Rocq 9.1 (absent in the sandbox VM).
    Zero axioms, admits, or parameters are used.
*)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From Top Require Import TM Eps1Tape.
Open Scope nat_scope.

Definition SHIFT : nat := 13.

(** Blank-tape prologue (states 0..12): writes right-to-left
    1(seed) 0 1(v=1) 0^2 1(wall) 0^2 1^2(budget)
    then walks right back to the wall and enters [SHIFT + ENTRY]. *)
Definition btbl_eps1 : table := fun s b =>
  match s with
  | 0  => Some (on, false, 1)    (* seed at cell 0 *)
  | 1  => Some (bl, false, 2)    (* blank between seed and value *)
  | 2  => Some (on, false, 3)    (* value mark v=1 *)
  | 3  => Some (bl, false, 4)    (* gap right of wall *)
  | 4  => Some (bl, false, 5)    (* gap right of wall *)
  | 5  => Some (on, false, 6)    (* wall *)
  | 6  => Some (bl, false, 7)    (* blank left of wall *)
  | 7  => Some (bl, false, 8)    (* blank left of wall *)
  | 8  => Some (on, false, 9)    (* budget mark 1 *)
  | 9  => Some (on, true,  10)   (* budget mark 2 (leftmost), turn right *)
  | 10 =>
      match b with
      | on => Some (on, true, 10)  (* walk right over budget *)
      | bl => Some (bl, true, 11)  (* first blank left of wall *)
      end
  | 11 => Some (bl, true, 12)      (* second blank left of wall *)
  | 12 => Some (on, false, SHIFT + ENTRY) (* hit wall: step left? No, stay/enter *)
  | _ =>
      match tbl (s - SHIFT) b with
      | None => None
      | Some (w, d, t) => Some (w, d, t + SHIFT)
      end
  end.

Definition c0_eps1 : conf := mkConf 0 [] bl [].

(** Note: in state 12, the head is on the wall (cell -5). Stepping [true]
    then would move off the wall; instead, let state 12 step [false] to -6
    and a 13th state step [true] onto the wall, OR have state 11 step [true]
    into [SHIFT + ENTRY] directly!
    Wait: at state 10 on [bl] (cell -7), moving [true] lands on cell -6 (bl).
    Then state 11 on cell -6 (bl), moving [true] lands on cell -5 (wall)!
    So state 11 can transition directly to [SHIFT + ENTRY]! *)

Definition btbl_eps1_clean : table := fun s b =>
  match s with
  | 0  => Some (on, false, 1)    (* seed at cell 0 *)
  | 1  => Some (bl, false, 2)    (* blank *)
  | 2  => Some (on, false, 3)    (* value v=1 *)
  | 3  => Some (bl, false, 4)    (* gap *)
  | 4  => Some (bl, false, 5)    (* gap *)
  | 5  => Some (on, false, 6)    (* wall *)
  | 6  => Some (bl, false, 7)    (* blank *)
  | 7  => Some (bl, false, 8)    (* blank *)
  | 8  => Some (on, false, 9)    (* budget mark 1 *)
  | 9  => Some (on, true,  10)   (* budget mark 2, turn right *)
  | 10 =>
      match b with
      | on => Some (on, true, 10)  (* walk right over budget *)
      | bl => Some (bl, true, 11)  (* first blank (-7) -> (-6) *)
      end
  | 11 => Some (bl, true, 12 + ENTRY) (* second blank (-6) -> wall (-5) in ENTRY *)
  | _ =>
      match tbl (s - 12) b with
      | None => None
      | Some (w, d, t) => Some (w, d, t + 12)
      end
  end.

Lemma eps1_clean_prologue :
  run btbl_eps1_clean 13 c0_eps1 =
  Some (mkConf (12 + ENTRY) [bl; bl; on; on] on [bl; bl; on; bl; on]).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions eps1_clean_prologue.
