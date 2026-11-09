(** * Machine 4: ladder machine with a fuel block on the tape

    54 states, 2 symbols, blank tape, head at 0 in state 0.
    The table is literal (see machines/machine_4_ladder.txt); the proofs below evaluate the
    concrete run with [vm_compute], so nothing is assumed beyond the Rocq kernel. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Bounds.
Import ListNotations.

Definition entry : conf := mkConf 0 [] bl [].

Definition nsteps : nat := 6582195.
Definition claim : nat := 2560.

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
    | bl => Some (bl, true, 40)
    | on => Some (on, true, 13)
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
    | bl => Some (bl, true, 18)
    | _ => None
    end
  | 18 => match b with
    | bl => Some (bl, true, 19)
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
    | bl => Some (bl, true, 22)
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
    | bl => Some (bl, true, 25)
    | _ => None
    end
  | 25 => match b with
    | bl => Some (on, true, 26)
    | _ => None
    end
  | 26 => match b with
    | bl => Some (bl, false, 27)
    | _ => None
    end
  | 27 => match b with
    | bl => Some (bl, false, 28)
    | on => Some (on, false, 27)
    end
  | 28 => match b with
    | bl => Some (bl, false, 28)
    | on => Some (on, false, 29)
    end
  | 29 => match b with
    | bl => Some (bl, false, 30)
    | on => Some (on, false, 29)
    end
  | 30 => match b with
    | bl => Some (bl, false, 30)
    | on => Some (on, false, 31)
    end
  | 31 => match b with
    | bl => Some (bl, true, 13)
    | on => Some (on, false, 31)
    end
  | 40 => match b with
    | bl => Some (bl, true, 40)
    | on => Some (on, true, 41)
    end
  | 41 => match b with
    | bl => Some (bl, true, 50)
    | on => Some (on, true, 41)
    end
  | 42 => match b with
    | bl => Some (bl, false, 43)
    | on => Some (on, false, 42)
    end
  | 43 => match b with
    | bl => Some (bl, false, 44)
    | on => Some (on, false, 42)
    end
  | 44 => match b with
    | bl => Some (bl, false, 44)
    | on => Some (on, false, 45)
    end
  | 45 => match b with
    | bl => Some (bl, true, 46)
    | on => Some (on, false, 45)
    end
  | 46 => match b with
    | on => Some (bl, true, 47)
    | _ => None
    end
  | 47 => match b with
    | on => Some (on, true, 48)
    | _ => None
    end
  | 48 => match b with
    | bl => Some (bl, true, 49)
    | on => Some (on, true, 48)
    end
  | 49 => match b with
    | bl => Some (bl, true, 49)
    | on => Some (on, true, 13)
    end
  | 50 => match b with
    | bl => Some (on, true, 51)
    | _ => None
    end
  | 51 => match b with
    | bl => Some (on, true, 52)
    | _ => None
    end
  | 52 => match b with
    | bl => Some (bl, true, 53)
    | _ => None
    end
  | 53 => match b with
    | bl => Some (on, true, 42)
    | _ => None
    end
  | _ => None
  end.

(** Machine 4 halts after exactly 6582195 steps with 2563 ones on the tape.
    The fuel block holds one cell per ladder stage: C = 1^2 -> 10 ones -> 2560 ones. *)

Theorem machine4_halts :
  exists c', claim <= nsteps /\ claim <= score c' /\
              run tbl nsteps entry = Some c' /\ halted tbl c'.
Proof.
  apply okb_sound with (ns := claim) (sc := claim).
  vm_compute. reflexivity.
Qed.

Theorem machine4_tower :
  exists c', run tbl nsteps entry = Some c' /\
              tower 3 <= score c' /\ tower 3 <= nsteps.
Proof.
  pose proof (machine4_halts) as [c' [H1 [H2 [H3 H4]]]].
  exists c'. split; [exact H3|].
  assert (Ht : tower 3 <= claim).
  { apply Nat.leb_le. vm_compute. reflexivity. }
  split.
  - apply Nat.le_trans with claim; [exact Ht|exact H2].
  - apply Nat.le_trans with claim; [exact Ht|exact H1].
Qed.

Print Assumptions machine4_halts.
Print Assumptions machine4_tower.
