(** * BB(2,5) machine 17: 1RB---0RB0LA2RA_2LB2LA3RA4LB0LB

    The table is the literal two-state, five-symbol table.  The checked
    theorem below is the 117-step entry into the [CycleStart] form used by
    the published high-level analysis:

      0^inf 1 3 [3 2] [A,2] 2^8 0^inf

    With binary cells read least-significant first, the left zipper is
    [3,2,3,1], exactly [cycleStart [b3;b2] (repeat b2 8) 0].

    This file deliberately does not assert nonhalting: the published Lean
    analysis still has an unresolved all-s3 overflow case. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import BB25.
Import ListNotations.

Definition tm17 : table5 := fun q s =>
  match q, s with
  | 0, b0 => Some (b1, true, 1)
  | 0, b1 => None
  | 0, b2 => Some (b0, true, 1)
  | 0, b3 => Some (b0, false, 0)
  | 0, b4 => Some (b2, true, 0)
  | 1, b0 => Some (b2, false, 1)
  | 1, b1 => Some (b2, false, 0)
  | 1, b2 => Some (b3, true, 0)
  | 1, b3 => Some (b4, false, 1)
  | 1, b4 => Some (b0, false, 1)
  | _, _ => None
  end.

Definition entry17 : conf5 := init5.

(** The machine reaches the canonical cycle-start configuration after
    exactly 117 transitions.  [vm_compute] performs the finite simulation
    inside the Rocq kernel; no external simulator is trusted. *)
Theorem entry17_to_cycle :
  run5 tm17 117 entry17 =
  Some (cycleStart [b3; b2] (repeat b2 8) 0).
Proof. vm_compute. reflexivity. Qed.

(** The first full canonical-to-canonical macro step: binary value 1 at
    four zero ternary pairs becomes binary value 11 at six zero pairs. *)
Theorem first_macro_step :
  run5 tm17 683 (cycleStart [b3; b2] (repeat b2 8) 0) =
  Some (cycleStart [b3; b3; b2; b3; b2] (repeat b2 12) 0).
Proof. vm_compute. reflexivity. Qed.

(** The second macro step, from binary value 11 to value 130. *)
Theorem second_macro_step :
  run5 tm17 5885 (cycleStart [b3; b3; b2; b3; b2] (repeat b2 12) 0) =
  Some (cycleStart [b2; b3; b2; b2; b2; b2; b2; b3] (repeat b2 16) 0).
Proof. vm_compute. reflexivity. Qed.
