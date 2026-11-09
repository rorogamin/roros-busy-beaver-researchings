From Stdlib Require Import ZArith List Bool Lia PeanoNat.
Open Scope Z_scope.

Inductive State := StA | StB.
Inductive Dir := MoveL | MoveR.

Record Transition := {
  write_sym : bool;
  move_dir : Dir;
  next_state : State
}.

Definition AgentTable := State -> bool -> Transition.

Definition Tape := Z -> bool.
Definition empty_tape : Tape := fun _ => false.
Definition write_tape (t : Tape) (p : Z) (s : bool) : Tape :=
  fun x => if Z.eqb x p then s else t x.

Record Config := {
  pos1 : Z;
  pos2 : Z;
  state1 : State;
  state2 : State;
  tape : Tape
}.

Definition step (ag1 ag2 : AgentTable) (c : Config) : Config :=
  let r1 := c.(tape) c.(pos1) in
  let r2 := c.(tape) c.(pos2) in
  let tr1 := ag1 c.(state1) r1 in
  let tr2 := ag2 c.(state2) r2 in
  let t1 := write_tape c.(tape) c.(pos2) tr2.(write_sym) in
  let t2 := write_tape t1 c.(pos1) tr1.(write_sym) in
  let p1' := match tr1.(move_dir) with MoveL => (c.(pos1) - 1)%Z | MoveR => (c.(pos1) + 1)%Z end in
  let p2' := match tr2.(move_dir) with MoveL => (c.(pos2) - 1)%Z | MoveR => (c.(pos2) + 1)%Z end in
  {| pos1 := p1'; pos2 := p2'; state1 := tr1.(next_state); state2 := tr2.(next_state); tape := t2 |}.

Fixpoint run (ag1 ag2 : AgentTable) (n : nat) (c : Config) : Config :=
  match n with
  | O => c
  | S m => step ag1 ag2 (run ag1 ag2 m c)
  end.

Definition is_collision (c : Config) : Prop := c.(pos1) = c.(pos2).

Definition collides_at (ag1 ag2 : AgentTable) (c0 : Config) (t : nat) : Prop :=
  is_collision (run ag1 ag2 t c0).

Definition quasi_halts (ag1 ag2 : AgentTable) (c0 : Config) : Prop :=
  exists T : nat, forall t : nat, (t >= T)%nat -> ~ collides_at ag1 ag2 c0 t.

Definition non_quasi_halts (ag1 ag2 : AgentTable) (c0 : Config) : Prop :=
  ~ quasi_halts ag1 ag2 c0.

Definition infinitely_many_collisions (ag1 ag2 : AgentTable) (c0 : Config) : Prop :=
  forall T : nat, exists t : nat, (t >= T)%nat /\ collides_at ag1 ag2 c0 t.

Lemma infinite_collisions_implies_non_quasihalt :
  forall ag1 ag2 c0, infinitely_many_collisions ag1 ag2 c0 -> non_quasi_halts ag1 ag2 c0.
Proof.
  intros ag1 ag2 c0 Hinf Hqh.
  destruct Hqh as [T Hno].
  destruct (Hinf T) as [t [Hge Hcol]].
  apply (Hno t Hge Hcol).
Qed.

(* Agent 1: 1RB0RB_1RA0LB *)
Definition agent1 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StA, true  => {| write_sym := false; move_dir := MoveR; next_state := StB |}
  | StB, false => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StB, true  => {| write_sym := false; move_dir := MoveL; next_state := StB |}
  end.

(* Agent 2: 1RB0RB_1LA1RA *)
Definition agent2 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StA, true  => {| write_sym := false; move_dir := MoveR; next_state := StB |}
  | StB, false => {| write_sym := true;  move_dir := MoveL; next_state := StA |}
  | StB, true  => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  end.

Definition c0 : Config := {|
  pos1 := 0;
  pos2 := 2;
  state1 := StA;
  state2 := StA;
  tape := empty_tape
|}.

Definition machine_collides (t : nat) : Prop := collides_at agent1 agent2 c0 t.

Lemma collision_at_2 : machine_collides 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma collision_at_3 : machine_collides 3%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma collision_at_6 : machine_collides 6%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma collision_at_54 : machine_collides 54%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma collision_at_1366 : machine_collides 1366%nat.
Proof. vm_compute. reflexivity. Qed.
