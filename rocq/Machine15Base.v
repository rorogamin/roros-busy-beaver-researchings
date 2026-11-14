(** * Machine15Base: the official 15-state 2-symbol BB(15) base

    The table is transcribed from

      1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO
      _1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM

    States 0..14 are the 15 active states A..O.  [1RZ] is a halting
    transition: it writes 1, moves right, and then stops.  The [table] type
    represents the stop as the sink [halt_state] = 15, which is not an active
    state and has no rows.  Thus the table has 16 numeric states, but the
    machine is still the 15-state machine.

    [lift q] is the base with its single halt transition redirected to [q].
    This is the base hook for a next-level gadget: [lift 7] is the known
    continuation variant, and [lift halt_state] is the base itself.  No level
    claim is made here; the concrete base is only proved not to reach its halt
    within 50,000,000 blank-tape steps. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Machine15.
Import ListNotations.

Definition entry : conf := mkConf 0 [] bl [].

Definition nsteps : nat := 50000000.

(** The inactive sink for [1RZ]. *)
Definition halt_state : nat := 15.

Definition base : table := fun s b =>
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
    | bl => Some (on, true, halt_state)  (* 1RZ: write, move right, halt *)
    | on => Some (on, true, 12)          (* 1RM: write, move right, state M *)
    end
  | _ => None
  end.

(** Replace the single [14/0] halt transition by a transition to [q]. *)
Definition lift (q : nat) : table := fun s b =>
  match s, b with
  | 14, bl => Some (on, true, q)
  | _, _ => base s b
  end.

(** The known continuation variant: enter H on the trailing 1. *)
Definition next_cont : table := lift 7.

(** The exact halting row of the official machine. *)
Lemma base_halt_row :
  base 14 bl = Some (on, true, halt_state).
Proof. reflexivity. Qed.

(** The sink really is a sink, on both symbols. *)
Lemma base_halt_state : forall b, base halt_state b = None.
Proof. intros b. destruct b; reflexivity. Qed.

(** The base's halt row is the only row changed by [lift]. *)
Lemma lift_halt_row : forall q,
  lift q 14 bl = Some (on, true, q).
Proof. intros q. reflexivity. Qed.

(** The continuation table starts by redirecting the halt into state H. *)
Lemma next_cont_halt_row :
  next_cont 14 bl = Some (on, true, 7).
Proof. reflexivity. Qed.

(** [lift halt_state] is exactly the official base. *)
Lemma lift_halt_is_base :
  forall s b, lift halt_state s b = base s b.
Proof.
  intros s b. destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]];
    destruct b; reflexivity.
Qed.

(** [next_cont] is exactly the existing continuation table, pointwise. *)
Lemma next_cont_eq_variant :
  forall s b, next_cont s b = Machine15.tbl s b.
Proof.
  intros s b.
  destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]];
    destruct b; reflexivity.
Qed.

(** The blank-tape base does not reach its halt in 50,000,000 steps. *)
Theorem machine15_base_no_halt_50m :
  exists c', run base nsteps entry = Some c'.
Proof.
  vm_compute.
  eexists. reflexivity.
Qed.

Print Assumptions base_halt_row.
Print Assumptions base_halt_state.
Print Assumptions lift_halt_row.
Print Assumptions next_cont_halt_row.
Print Assumptions lift_halt_is_base.
Print Assumptions next_cont_eq_variant.
Print Assumptions machine15_base_no_halt_50m.
