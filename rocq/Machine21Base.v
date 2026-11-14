(** * Machine21Base: the 21-state omega^2 row as an edit of the 15-state base

    This is the BB(21) row

      0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH
      _1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH
      _1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR

    treated as the next row in the same BB(7)..BB(25) edited lineage, not as
    an unrelated machine.  [champion_rows] is the recorded row.  [edited21]
    starts from [Machine15Base.base] and writes those 21 rows with [set_row];
    [table21_eq_edited] proves the literal 21-state table is exactly that
    edit.  [table21_rows] proves the literal table has the recorded rows.

    State 17/0 is the halt row [1RZ]: it writes 1, moves right, and enters the
    inactive sink 21.  The 21 active states are 0..20; the sink is not an
    active state.  The only checked run fact is that the blank-tape machine
    does not halt within the stated prefix.  No omega^2 value claim is proved
    here. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Machine15Base.
Import ListNotations.

Definition entry : conf := mkConf 0 [] bl [].

Definition nsteps : nat := 3000000.

(** The inactive sink for [1RZ]. *)
Definition halt_state : nat := 21.

(** The literal 21-state table. *)
Definition table21 : table := fun s b =>
  match s with
  | 0 => match b with
    | bl => Some (bl, false, 8)
    | on => Some (bl, false, 5)
    end
  | 1 => match b with
    | bl => Some (bl, true, 9)
    | on => Some (on, true, 6)
    end
  | 2 => match b with
    | bl => Some (bl, true, 3)
    | on => Some (on, false, 2)
    end
  | 3 => match b with
    | bl => Some (on, true, 7)
    | on => Some (on, true, 4)
    end
  | 4 => match b with
    | bl => Some (on, false, 14)
    | on => Some (bl, true, 7)
    end
  | 5 => match b with
    | bl => Some (on, false, 0)
    | on => Some (on, false, 5)
    end
  | 6 => match b with
    | bl => Some (bl, false, 2)
    | on => Some (on, false, 0)
    end
  | 7 => match b with
    | bl => Some (on, true, 1)
    | on => Some (on, true, 7)
    end
  | 8 => match b with
    | bl => Some (on, true, 3)
    | on => Some (bl, false, 5)
    end
  | 9 => match b with
    | bl => Some (on, false, 15)
    | on => Some (bl, true, 10)
    end
  | 10 => match b with
    | bl => Some (bl, false, 12)
    | on => Some (on, false, 11)
    end
  | 11 => match b with
    | bl => Some (bl, false, 11)
    | on => Some (on, false, 12)
    end
  | 12 => match b with
    | bl => Some (on, false, 4)
    | on => Some (on, false, 13)
    end
  | 13 => match b with
    | bl => Some (bl, true, 16)
    | on => Some (bl, false, 12)
    end
  | 14 => match b with
    | bl => Some (bl, true, 15)
    | on => Some (on, false, 14)
    end
  | 15 => match b with
    | bl => Some (on, false, 17)
    | on => Some (bl, true, 7)
    end
  | 16 => match b with
    | bl => Some (on, false, 5)
    | on => Some (on, true, 16)
    end
  | 17 => match b with
    | bl => Some (on, true, 21)
    | on => Some (bl, false, 18)
    end
  | 18 => match b with
    | bl => Some (on, false, 7)
    | on => Some (bl, false, 19)
    end
  | 19 => match b with
    | bl => Some (on, false, 7)
    | on => Some (on, false, 20)
    end
  | 20 => match b with
    | bl => Some (bl, false, 4)
    | on => Some (on, false, 17)
    end
  | _ => None
  end.

(** A compact row record for data-level identity checks.  [r_w] and [r_d] are
    0/1 codes; [r_q] is the numeric next state, with 21 the halt sink. *)
Record row_code : Type := {
  r_state : nat;
  r_w0 : nat; r_d0 : nat; r_q0 : nat;
  r_w1 : nat; r_d1 : nat; r_q1 : nat
}.

Definition champion_rows : list row_code := [
  {| r_state := 0; r_w0 := 0; r_d0 := 0; r_q0 := 8; r_w1 := 0; r_d1 := 0; r_q1 := 5 |};
  {| r_state := 1; r_w0 := 0; r_d0 := 1; r_q0 := 9; r_w1 := 1; r_d1 := 1; r_q1 := 6 |};
  {| r_state := 2; r_w0 := 0; r_d0 := 1; r_q0 := 3; r_w1 := 1; r_d1 := 0; r_q1 := 2 |};
  {| r_state := 3; r_w0 := 1; r_d0 := 1; r_q0 := 7; r_w1 := 1; r_d1 := 1; r_q1 := 4 |};
  {| r_state := 4; r_w0 := 1; r_d0 := 0; r_q0 := 14; r_w1 := 0; r_d1 := 1; r_q1 := 7 |};
  {| r_state := 5; r_w0 := 1; r_d0 := 0; r_q0 := 0; r_w1 := 1; r_d1 := 0; r_q1 := 5 |};
  {| r_state := 6; r_w0 := 0; r_d0 := 0; r_q0 := 2; r_w1 := 1; r_d1 := 0; r_q1 := 0 |};
  {| r_state := 7; r_w0 := 1; r_d0 := 1; r_q0 := 1; r_w1 := 1; r_d1 := 1; r_q1 := 7 |};
  {| r_state := 8; r_w0 := 1; r_d0 := 1; r_q0 := 3; r_w1 := 0; r_d1 := 0; r_q1 := 5 |};
  {| r_state := 9; r_w0 := 1; r_d0 := 0; r_q0 := 15; r_w1 := 0; r_d1 := 1; r_q1 := 10 |};
  {| r_state := 10; r_w0 := 0; r_d0 := 0; r_q0 := 12; r_w1 := 1; r_d1 := 0; r_q1 := 11 |};
  {| r_state := 11; r_w0 := 0; r_d0 := 0; r_q0 := 11; r_w1 := 1; r_d1 := 0; r_q1 := 12 |};
  {| r_state := 12; r_w0 := 1; r_d0 := 0; r_q0 := 4; r_w1 := 1; r_d1 := 0; r_q1 := 13 |};
  {| r_state := 13; r_w0 := 0; r_d0 := 1; r_q0 := 16; r_w1 := 0; r_d1 := 0; r_q1 := 12 |};
  {| r_state := 14; r_w0 := 0; r_d0 := 1; r_q0 := 15; r_w1 := 1; r_d1 := 0; r_q1 := 14 |};
  {| r_state := 15; r_w0 := 1; r_d0 := 0; r_q0 := 17; r_w1 := 0; r_d1 := 1; r_q1 := 7 |};
  {| r_state := 16; r_w0 := 1; r_d0 := 0; r_q0 := 5; r_w1 := 1; r_d1 := 1; r_q1 := 16 |};
  {| r_state := 17; r_w0 := 1; r_d0 := 1; r_q0 := 21; r_w1 := 0; r_d1 := 0; r_q1 := 18 |};
  {| r_state := 18; r_w0 := 1; r_d0 := 0; r_q0 := 7; r_w1 := 0; r_d1 := 0; r_q1 := 19 |};
  {| r_state := 19; r_w0 := 1; r_d0 := 0; r_q0 := 7; r_w1 := 1; r_d1 := 0; r_q1 := 20 |};
  {| r_state := 20; r_w0 := 0; r_d0 := 0; r_q0 := 4; r_w1 := 1; r_d1 := 0; r_q1 := 17 |}
].

Definition code_of_sym (x : sym) : nat :=
  match x with bl => 0 | on => 1 end.
Definition code_of_dir (d : dirn) : nat := if d then 1 else 0.
Definition sym_of_code (w : nat) : sym := if Nat.eqb w 0 then bl else on.
Definition dir_of_code (d : nat) : dirn := if Nat.eqb d 0 then false else true.

Definition row_code_of_table (t : table) (s : nat) : option row_code :=
  match t s bl, t s on with
  | Some (w0, d0, q0), Some (w1, d1, q1) =>
      Some {| r_state := s;
              r_w0 := code_of_sym w0; r_d0 := code_of_dir d0; r_q0 := q0;
              r_w1 := code_of_sym w1; r_d1 := code_of_dir d1; r_q1 := q1 |}
  | _, _ => None
  end.

(** The literal table has exactly the 21 recorded rows. *)
Lemma table21_rows :
  map (fun s => row_code_of_table table21 s) (seq 0 21) =
  map Some champion_rows.
Proof. vm_compute. reflexivity. Qed.

Definition row_action (r : row_code) (b : sym) : option (sym * dirn * nat) :=
  match b with
  | bl => Some (sym_of_code (r_w0 r), dir_of_code (r_d0 r), r_q0 r)
  | on => Some (sym_of_code (r_w1 r), dir_of_code (r_d1 r), r_q1 r)
  end.

Definition set_row (t : table) (r : row_code) : table :=
  fun s b => if Nat.eqb (r_state r) s then row_action r b else t s b.

(** The base table with the 21 recorded rows written over it. *)
Definition edited21 : table := fold_left set_row champion_rows base.

(** On every active state and the halt sink, the literal table is the edit. *)
Lemma table21_eq_edited :
  forall s b, s <= 21 -> table21 s b = edited21 s b.
Proof.
  intros s b H.
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  destruct s as [|s]; [destruct b; vm_compute; reflexivity|].
  vm_compute; reflexivity.
Qed.

(** The blank-tape prefix: no halt in the stated number of steps. *)
Theorem table21_no_halt_3m :
  exists c', run table21 nsteps entry = Some c'.
Proof.
  vm_compute.
  eexists. reflexivity.
Qed.

(** The redirect hook, placed on the row that actually halts: state 17/0. *)
Definition lift (q : nat) : table := fun s b =>
  match s, b with
  | 17, bl => Some (on, true, q)
  | _, _ => table21 s b
  end.

Lemma lift_halt_row :
  forall q, lift q 17 bl = Some (on, true, q).
Proof. intro q. reflexivity. Qed.

Print Assumptions table21_rows.
Print Assumptions table21_eq_edited.
Print Assumptions table21_no_halt_3m.
Print Assumptions lift_halt_row.
