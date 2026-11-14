(** * Machine 15 (candidate): 15-state 2-symbol trim of the BB(18) f_{w*2}^2 family.

    The table is the candidate in machines/candidate_15_omega2.txt.  This file
    verifies one concrete fact: the blank-tape run reaches 50,000,000 steps
    without halting.  It does NOT prove the f_{w*2}(13) claim.  The machine's
    static right-hand numeral/program has not been given a semantics, so the
    halt time and the level are not established.  The continuation variant
    makes [14/0] write 1, move right, and enter state H (7), so the writer
    continues into the next 13-field stack instead of halting. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM.
Import ListNotations.

Definition entry : conf := mkConf 0 [] bl [].

Definition nsteps : nat := 50000000.

Definition tbl : table := fun s b =>
  match s with
  | 0 => match b with
    | bl => Some (on, false, 7)
    | on => Some (bl, false, 6)
    end
  | 1 => match b with
    | bl => Some (bl, false, 8)
    | on => Some (on, true, 2)
    end
  | 2 => match b with
    | bl => Some (bl, false, 3)
    | on => Some (on, false, 0)
    end
  | 3 => match b with
    | bl => Some (bl, true, 4)
    | on => Some (on, false, 3)
    end
  | 4 => match b with
    | bl => Some (bl, true, 7)
    | on => Some (on, true, 11)
    end
  | 5 => match b with
    | bl => Some (on, true, 1)
    | on => Some (on, true, 5)
    end
  | 6 => match b with
    | bl => Some (on, false, 0)
    | on => Some (on, false, 6)
    end
  | 7 => match b with
    | bl => Some (on, true, 5)
    | on => Some (bl, true, 14)
    end
  | 8 => match b with
    | bl => Some (on, false, 9)
    | on => Some (on, false, 8)
    end
  | 9 => match b with
    | bl => Some (bl, false, 10)
    | on => Some (on, false, 8)
    end
  | 10 => match b with
    | bl => Some (on, true, 11)
    | on => Some (on, true, 4)
    end
  | 11 => match b with
    | bl => Some (bl, true, 11)
    | on => Some (bl, true, 5)
    end
  | 12 => match b with
    | bl => Some (bl, false, 0)
    | on => Some (bl, true, 13)
    end
  | 13 => match b with
    | bl => Some (bl, false, 0)
    | on => Some (on, true, 14)
    end
  | 14 => match b with
    | bl => Some (on, true, 7)
    | on => Some (on, true, 12)
    end
  | _ => None
  end.

Theorem machine15_no_halt_50m :
  exists c', run tbl nsteps entry = Some c'.
Proof.
  vm_compute.
  eexists. reflexivity.
Qed.

Print Assumptions machine15_no_halt_50m.
