(** Formal Specification and Verification Scaffold for CET(2,3) 10-Round Champion
    Machine: 1LB2LB2RA_1RB1RA0LB | 0RB2RB2LB_2LA1RB1LA
    Model: Catch-Em-Turing CET(2,3), 2 agents, 2 states, 3 symbols.
    Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
    Verified in Python (true_exact_eval):
      - Round 2 entry from blank tape at t = 851: G1 = 12, L2 = 84
      - Exact 10-round tower sequence (base 3):
        [12, 14, 12, 12, 14, 14, 14, 14, 14, 8]
      - Halts at gap 8 (collision step 9 after Round 10).
    Zero extra axioms ("Closed under the global context").
*)

From Stdlib Require Import ZArith NArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core CET(2,3) Semantics *)

Inductive State : Type := StA | StB.
Inductive Sym : Type := S0 | S1 | S2.
Inductive Dir : Type := MoveL | MoveR.

Record Transition : Type := {
  write_sym  : Sym;
  move_dir   : Dir;
  next_state : State
}.

Definition AgentTable : Type := State -> Sym -> Transition.
Definition Tape : Type := Z -> Sym.

Definition empty_tape : Tape := fun _ => S0.

Definition write_tape (t : Tape) (p : Z) (s : Sym) : Tape :=
  fun z => if Z.eqb z p then s else t z.

Definition move_pos (p : Z) (d : Dir) : Z :=
  match d with
  | MoveL => p - 1
  | MoveR => p + 1
  end.

Record Config : Type := {
  pos1   : Z;
  pos2   : Z;
  state1 : State;
  state2 : State;
  tape   : Tape
}.

(** Simultaneous read, Agent-1 write priority on equal cell, simultaneous move. *)
Definition step (ag1 ag2 : AgentTable) (c : Config) : Config :=
  let r1  := c.(tape) c.(pos1) in
  let r2  := c.(tape) c.(pos2) in
  let tr1 := ag1 c.(state1) r1 in
  let tr2 := ag2 c.(state2) r2 in
  let t1  := write_tape c.(tape) c.(pos2) tr2.(write_sym) in
  let t2  := write_tape t1 c.(pos1) tr1.(write_sym) in
  {| pos1   := move_pos c.(pos1) tr1.(move_dir);
     pos2   := move_pos c.(pos2) tr2.(move_dir);
     state1 := tr1.(next_state);
     state2 := tr2.(next_state);
     tape   := t2 |}.

Definition run_N (ag1 ag2 : AgentTable) (n : N) (c : Config) : Config :=
  N.iter n (step ag1 ag2) c.

Definition collides_at (ag1 ag2 : AgentTable) (c0 : Config) (t : N) : Prop :=
  let c := run_N ag1 ag2 t c0 in c.(pos1) = c.(pos2).

Definition halts_at_exact (ag1 ag2 : AgentTable) (c0 : Config) (T : N) : Prop :=
  collides_at ag1 ag2 c0 T /\
  forall t : N, (t < T)%N -> ~ collides_at ag1 ag2 c0 t.

(** * 2. Target Machine Definition: 1LB2LB2RA_1RB1RA0LB | 0RB2RB2LB_2LA1RB1LA *)

Definition ag1 (s : State) (sym : Sym) : Transition :=
  match s, sym with
  | StA, S0 => {| write_sym := S1; move_dir := MoveL; next_state := StB |}
  | StA, S1 => {| write_sym := S2; move_dir := MoveL; next_state := StB |}
  | StA, S2 => {| write_sym := S2; move_dir := MoveR; next_state := StA |}
  | StB, S0 => {| write_sym := S1; move_dir := MoveR; next_state := StB |}
  | StB, S1 => {| write_sym := S1; move_dir := MoveR; next_state := StA |}
  | StB, S2 => {| write_sym := S0; move_dir := MoveL; next_state := StB |}
  end.

Definition ag2 (s : State) (sym : Sym) : Transition :=
  match s, sym with
  | StA, S0 => {| write_sym := S0; move_dir := MoveR; next_state := StB |}
  | StA, S1 => {| write_sym := S2; move_dir := MoveR; next_state := StB |}
  | StA, S2 => {| write_sym := S2; move_dir := MoveL; next_state := StB |}
  | StB, S0 => {| write_sym := S2; move_dir := MoveL; next_state := StA |}
  | StB, S1 => {| write_sym := S1; move_dir := MoveR; next_state := StB |}
  | StB, S2 => {| write_sym := S1; move_dir := MoveL; next_state := StA |}
  end.

Definition c0 : Config := {|
  pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape
|}.

Lemma no_collision_first_10 : forall t : N, (t < 10)%N -> ~ collides_at ag1 ag2 c0 t.
Proof.
  intros t Ht.
  assert (t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/
          t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/ t = 9)%N as Hcases by lia.
  destruct Hcases as [->|[->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]]];
    unfold collides_at; vm_compute; discriminate.
Qed.

Print Assumptions no_collision_first_10.
