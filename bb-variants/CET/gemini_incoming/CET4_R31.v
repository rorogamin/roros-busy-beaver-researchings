(** Formal Specification and Verification Scaffold for CET(4) 31-Round Champion
    Machine: 1LB1RA_1RC0LD_1LA0LB_0RB0RA | 1RB0LC_1LA0RC_1LD0RA_1RC1RA
    Model: Catch-Em-Turing CET(4,2), 2 agents, 4 states, 2 symbols.
    Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
    Verified in Python (true_exact_eval):
      - Round 2 entry from blank tape: G1 = 30, L2 = 116
      - Exact 31-round tower sequence:
        [30, 22, 28, 28, 30, 24, 28, 14, 16, 28, 24, 24, 8, 18, 12, 30,
         12, 14, 16, 28, 30, 26, 12, 14, 28, 14, 8, 26, 24, 22, 32]
      - Halts at gap 32 (collision step 30 after Round 31).
    Zero extra axioms ("Closed under the global context").
*)

From Stdlib Require Import ZArith NArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core CET(4) Semantics *)

Inductive State : Type := StA | StB | StC | StD.
Inductive Dir : Type := MoveL | MoveR.

Record Transition : Type := {
  write_sym  : bool;
  move_dir   : Dir;
  next_state : State
}.

Definition AgentTable : Type := State -> bool -> Transition.
Definition Tape : Type := Z -> bool.

Definition empty_tape : Tape := fun _ => false.

Definition write_tape (t : Tape) (p : Z) (s : bool) : Tape :=
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

(** * 2. Target Machine Definition: 1LB1RA_1RC0LD_1LA0LB_0RB0RA | 1RB0LC_1LA0RC_1LD0RA_1RC1RA *)

Definition ag1 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StA, true  => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StB, false => {| write_sym := true;  move_dir := MoveR; next_state := StC |}
  | StB, true  => {| write_sym := false; move_dir := MoveL; next_state := StD |}
  | StC, false => {| write_sym := true;  move_dir := MoveL; next_state := StA |}
  | StC, true  => {| write_sym := false; move_dir := MoveL; next_state := StB |}
  | StD, false => {| write_sym := false; move_dir := MoveR; next_state := StB |}
  | StD, true  => {| write_sym := false; move_dir := MoveR; next_state := StA |}
  end.

Definition ag2 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StA, true  => {| write_sym := false; move_dir := MoveL; next_state := StC |}
  | StB, false => {| write_sym := true;  move_dir := MoveL; next_state := StA |}
  | StB, true  => {| write_sym := false; move_dir := MoveR; next_state := StC |}
  | StC, false => {| write_sym := true;  move_dir := MoveL; next_state := StD |}
  | StC, true  => {| write_sym := false; move_dir := MoveR; next_state := StA |}
  | StD, false => {| write_sym := true;  move_dir := MoveR; next_state := StC |}
  | StD, true  => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  end.

Definition c0 : Config := {|
  pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape
|}.

Lemma write_tape_same : forall t p s, write_tape t p s p = s.
Proof. intros. unfold write_tape. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma write_tape_other : forall t p s x, x <> p -> write_tape t p s x = t x.
Proof. intros. unfold write_tape. destruct (Z.eqb_spec x p); congruence. Qed.

Lemma no_collision_first_10 : forall t : N, (t < 10)%N -> ~ collides_at ag1 ag2 c0 t.
Proof.
  intros t Ht.
  assert (t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/
          t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/ t = 9)%N as Hcases by lia.
  destruct Hcases as [->|[->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]]];
    unfold collides_at; vm_compute; discriminate.
Qed.

Print Assumptions no_collision_first_10.
