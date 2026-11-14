(** * Machine 7: exponential-growth blank-tape machine

    39 states, 2 symbols, blank tape, head at 0 in state 0.
    The table is literal (see machines/machine_7_omega); the proofs below evaluate the
    concrete run with [vm_compute], so nothing is assumed beyond the Rocq kernel. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Bounds.
Import ListNotations.

Definition entry : conf := mkConf 0 [] bl [].

Definition nsteps : nat := 419574070.
Definition claim : nat := 16384.

Definition tbl : table := fun s b =>
  match s with
  | 0 => match b with
    | bl => Some (bl, true, 15)
    | on => Some (bl, true, 1)
    end
  | 1 => match b with
    | bl => Some (bl, true, 2)
    | on => Some (on, true, 3)
    end
  | 2 => match b with
    | bl => Some (bl, true, 2)
    | on => Some (on, true, 4)
    end
  | 3 => match b with
    | bl => Some (bl, true, 4)
    | on => Some (on, true, 3)
    end
  | 4 => match b with
    | bl => Some (on, true, 5)
    | on => Some (on, true, 4)
    end
  | 5 => match b with
    | bl => Some (on, false, 6)
    | _ => None
    end
  | 6 => match b with
    | bl => Some (bl, false, 7)
    | on => Some (on, false, 6)
    end
  | 7 => match b with
    | bl => Some (bl, false, 9)
    | on => Some (on, false, 8)
    end
  | 8 => match b with
    | bl => Some (bl, true, 0)
    | on => Some (on, false, 8)
    end
  | 9 => match b with
    | bl => Some (bl, false, 9)
    | on => Some (on, false, 10)
    end
  | 10 => match b with
    | bl => Some (bl, true, 11)
    | on => Some (on, false, 10)
    end
  | 11 => match b with
    | on => Some (bl, true, 12)
    | _ => None
    end
  | 12 => match b with
    | on => Some (on, true, 13)
    | _ => None
    end
  | 13 => match b with
    | bl => Some (bl, true, 14)
    | on => Some (on, true, 13)
    end
  | 14 => match b with
    | bl => Some (bl, true, 14)
    | on => Some (bl, true, 1)
    end
  | 15 => match b with
    | bl => Some (on, true, 16)
    | _ => None
    end
  | 16 => match b with
    | bl => Some (on, true, 17)
    | _ => None
    end
  | 17 => match b with
    | bl => Some (on, true, 18)
    | _ => None
    end
  | 18 => match b with
    | bl => Some (on, true, 19)
    | _ => None
    end
  | 19 => match b with
    | bl => Some (on, true, 20)
    | _ => None
    end
  | 20 => match b with
    | bl => Some (on, true, 21)
    | _ => None
    end
  | 21 => match b with
    | bl => Some (on, true, 22)
    | _ => None
    end
  | 22 => match b with
    | bl => Some (on, true, 23)
    | _ => None
    end
  | 23 => match b with
    | bl => Some (on, true, 24)
    | _ => None
    end
  | 24 => match b with
    | bl => Some (on, true, 25)
    | _ => None
    end
  | 25 => match b with
    | bl => Some (on, true, 26)
    | _ => None
    end
  | 26 => match b with
    | bl => Some (on, true, 27)
    | _ => None
    end
  | 27 => match b with
    | bl => Some (on, true, 28)
    | _ => None
    end
  | 28 => match b with
    | bl => Some (bl, true, 29)
    | _ => None
    end
  | 29 => match b with
    | bl => Some (on, true, 30)
    | _ => None
    end
  | 30 => match b with
    | bl => Some (on, true, 31)
    | _ => None
    end
  | 31 => match b with
    | bl => Some (bl, true, 32)
    | _ => None
    end
  | 32 => match b with
    | bl => Some (on, true, 33)
    | _ => None
    end
  | 33 => match b with
    | bl => Some (bl, false, 34)
    | _ => None
    end
  | 34 => match b with
    | bl => Some (bl, false, 35)
    | on => Some (on, false, 34)
    end
  | 35 => match b with
    | bl => Some (bl, false, 35)
    | on => Some (on, false, 36)
    end
  | 36 => match b with
    | bl => Some (bl, false, 37)
    | on => Some (on, false, 36)
    end
  | 37 => match b with
    | bl => Some (bl, false, 37)
    | on => Some (on, false, 38)
    end
  | 38 => match b with
    | bl => Some (bl, true, 13)
    | on => Some (on, false, 38)
    end
  | _ => None
  end.

(** Machine machine7 halts after exactly 419574070 steps with 20480 ones on the tape. *)

Theorem machine7_halts :
  exists c', claim <= nsteps /\ claim <= score c' /\
              run tbl nsteps entry = Some c' /\ halted tbl c'.
Proof.
  apply okb_sound with (ns := claim) (sc := claim).
  vm_compute. reflexivity.
Qed.

(** Score and step count both dominate [tower 3]. *)
Theorem machine7_tower :
  exists c', run tbl nsteps entry = Some c' /\
              tower 3 <= score c' /\ tower 3 <= nsteps.
Proof.
  pose proof (machine7_halts) as [c' [H1 [H2 [H3 H4]]]].
  exists c'. split; [exact H3|].
  assert (Ht : tower 3 <= claim).
  { apply Nat.leb_le. vm_compute. reflexivity. }
  split.
  - apply Nat.le_trans with claim; [exact Ht|exact H2].
  - apply Nat.le_trans with claim; [exact Ht|exact H1].
Qed.

Print Assumptions machine7_halts.
Print Assumptions machine7_tower.
