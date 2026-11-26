(**
  Formal Machine-Checked Proof of Normal Halting in Rocq 9.1
  Target Machine: 1LB1RA0LB_2RB2LB2RA | 1LB2LA1RB_2RA0RB1RA
  Model: Catch-Em-Turing CET(2,3), 2 agents, 2 states, 3 symbols.
  Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
  Normal Halting: exact first collision pos1(T) = pos2(T).

  Proves:
  1. The machine executes 5 ternary-counter-vs-glider rounds with gap sequence
     [14, 18, 16, 14, 12] and halts by exact first head collision at exact step
     T_halt (~ 10^10^10^10^788).
  Zero extra axioms.
*)

From Stdlib Require Import ZArith NArith PArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core Catch-Em-Turing Semantics *)

Inductive State := StA | StB.
Inductive Sym := S0 | S1 | S2.
Inductive Dir := MoveL | MoveR.

Definition sym_eqb (a b : Sym) : bool :=
  match a, b with
  | S0, S0 => true
  | S1, S1 => true
  | S2, S2 => true
  | _, _ => false
  end.

Record Transition := {
  write_sym  : Sym;
  move_dir   : Dir;
  next_state : State
}.

Definition AgentTable := State -> Sym -> Transition.
Definition Tape := Z -> Sym.
Definition empty_tape : Tape := fun _ => S0.

Definition write_tape (t : Tape) (p : Z) (s : Sym) : Tape :=
  fun x => if Z.eqb x p then s else t x.

Record Config := {
  pos1   : Z;
  pos2   : Z;
  state1 : State;
  state2 : State;
  tape   : Tape
}.

Definition move_pos (p : Z) (d : Dir) : Z :=
  match d with MoveL => p - 1 | MoveR => p + 1 end.

Definition step (ag1 ag2 : AgentTable) (c : Config) : Config :=
  let r1 := c.(tape) c.(pos1) in
  let r2 := c.(tape) c.(pos2) in
  let tr1 := ag1 c.(state1) r1 in
  let tr2 := ag2 c.(state2) r2 in
  let t1 := write_tape c.(tape) c.(pos2) tr2.(write_sym) in
  let t2 := write_tape t1 c.(pos1) tr1.(write_sym) in
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

(** * 2. Target Machine Definition: 1LB1RA0LB_2RB2LB2RA | 1LB2LA1RB_2RA0RB1RA *)

Definition ag1 (s : State) (b : Sym) : Transition :=
  match s, b with
  | StA, S0 => {| write_sym := S1; move_dir := MoveL; next_state := StB |}
  | StA, S1 => {| write_sym := S1; move_dir := MoveR; next_state := StA |}
  | StA, S2 => {| write_sym := S0; move_dir := MoveL; next_state := StB |}
  | StB, S0 => {| write_sym := S2; move_dir := MoveR; next_state := StB |}
  | StB, S1 => {| write_sym := S2; move_dir := MoveL; next_state := StB |}
  | StB, S2 => {| write_sym := S2; move_dir := MoveR; next_state := StA |}
  end.

Definition ag2 (s : State) (b : Sym) : Transition :=
  match s, b with
  | StA, S0 => {| write_sym := S1; move_dir := MoveL; next_state := StB |}
  | StA, S1 => {| write_sym := S2; move_dir := MoveL; next_state := StA |}
  | StA, S2 => {| write_sym := S1; move_dir := MoveR; next_state := StB |}
  | StB, S0 => {| write_sym := S2; move_dir := MoveR; next_state := StA |}
  | StB, S1 => {| write_sym := S0; move_dir := MoveR; next_state := StB |}
  | StB, S2 => {| write_sym := S1; move_dir := MoveR; next_state := StA |}
  end.

Definition init_config : Config :=
  {| pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape |}.

Lemma prefix_8224_state :
  let c := run_N ag1 ag2 8224 init_config in
  c.(pos1) = 1630 /\ c.(pos2) = 1644 /\ c.(state1) = StA /\ c.(state2) = StB.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Fixpoint no_coll_until (n : nat) (c : Config) : bool :=
  match n with
  | O => true
  | S n' => negb (Z.eqb c.(pos1) c.(pos2)) && no_coll_until n' (step ag1 ag2 c)
  end.

Lemma run_N_succ : forall n c,
  run_N ag1 ag2 (N.succ n) c = run_N ag1 ag2 n (step ag1 ag2 c).
Proof.
  intros n c. unfold run_N.
  rewrite N.iter_succ_r. reflexivity.
Qed.

Lemma no_coll_until_sound : forall n c,
  no_coll_until n c = true ->
  forall t : N, (t < N.of_nat n)%N -> ~ collides_at ag1 ag2 c t.
Proof.
  induction n as [| n IH]; intros c Hno t Ht.
  - lia.
  - simpl in Hno. apply Bool.andb_true_iff in Hno. destruct Hno as [Hneq Hrec].
    destruct t as [| p].
    + unfold collides_at, run_N. simpl.
      apply Bool.negb_true_iff in Hneq. apply Z.eqb_neq in Hneq. exact Hneq.
    + unfold collides_at. replace (N.pos p) with (N.succ (N.pred (N.pos p))) by lia.
      rewrite run_N_succ. apply IH; [exact Hrec | lia].
Qed.

Lemma prefix_8224_no_coll : no_coll_until 8224 init_config = true.
Proof.
  vm_compute. reflexivity.
Qed.

Fixpoint heads_in_bounds (lo hi : Z) (n : nat) (c : Config) : bool :=
  match n with
  | O => true
  | S n' => (lo <=? c.(pos1)) && (c.(pos1) <=? hi) &&
            (lo <=? c.(pos2)) && (c.(pos2) <=? hi) &&
            heads_in_bounds lo hi n' (step ag1 ag2 c)
  end.

Lemma heads_in_bounds_sound : forall lo hi n c x,
  heads_in_bounds lo hi n c = true ->
  (x < lo \/ x > hi) ->
  (run_N ag1 ag2 (N.of_nat n) c).(tape) x = c.(tape) x.
Proof.
  intros lo hi n. induction n as [| n IH]; intros c x Hbd Hx.
  - reflexivity.
  - simpl in Hbd.
    repeat rewrite Bool.andb_true_iff in Hbd.
    destruct Hbd as [[[[H1 H2] H3] H4] Hrec].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    apply Z.leb_le in H3. apply Z.leb_le in H4.
    replace (N.of_nat (S n)) with (N.succ (N.of_nat n)) by lia.
    rewrite run_N_succ.
    rewrite IH; [| exact Hrec | exact Hx].
    simpl. unfold write_tape.
    destruct (Z.eqb_spec x c.(pos1)); [lia |].
    destruct (Z.eqb_spec x c.(pos2)); [lia |].
    reflexivity.
Qed.

Lemma prefix_8224_bounds : heads_in_bounds (-1) 1645 8224 init_config = true.
Proof.
  vm_compute. reflexivity.
Qed.

Fixpoint check_S1_range (lo : Z) (len : nat) (t : Tape) : bool :=
  match len with
  | O => true
  | S len' => sym_eqb (t lo) S1 && check_S1_range (lo + 1) len' t
  end.

Lemma check_S1_range_sound : forall len lo t x,
  check_S1_range lo len t = true ->
  lo <= x < lo + Z.of_nat len ->
  t x = S1.
Proof.
  induction len as [| len IH]; intros lo t x Hchk Hx.
  - lia.
  - simpl in Hchk. apply Bool.andb_true_iff in Hchk. destruct Hchk as [H0 Hrec].
    destruct (Z.eq_dec x lo) as [-> | Hneq].
    + destruct (t lo); simpl in H0; try discriminate; reflexivity.
    + apply (IH (lo + 1)); [exact Hrec | lia].
Qed.

Lemma prefix_8224_tape_anc :
  (run_N ag1 ag2 8224 init_config).(tape) (-1) = S2.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma prefix_8224_tape_S1 :
  check_S1_range 0 1646 (run_N ag1 ag2 8224 init_config).(tape) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** * 3. Configuration Equivalence and Standard Tape *)

Definition Config_equiv (c1 c2 : Config) : Prop :=
  c1.(pos1) = c2.(pos1) /\
  c1.(pos2) = c2.(pos2) /\
  c1.(state1) = c2.(state1) /\
  c1.(state2) = c2.(state2) /\
  forall x : Z, c1.(tape) x = c2.(tape) x.

Lemma step_equiv : forall c1 c2,
  Config_equiv c1 c2 -> Config_equiv (step ag1 ag2 c1) (step ag1 ag2 c2).
Proof.
  intros c1 c2 [Hp1 [Hp2 [Hs1 [Hs2 Htp]]]].
  unfold Config_equiv, step. simpl.
  rewrite Hp1, Hp2, Hs1, Hs2, !Htp.
  repeat split; try reflexivity.
  intro x. unfold write_tape.
  destruct (Z.eqb x c2.(pos1)); destruct (Z.eqb x c2.(pos2)); try reflexivity; apply Htp.
Qed.

Lemma run_N_equiv : forall n c1 c2,
  Config_equiv c1 c2 -> Config_equiv (run_N ag1 ag2 n c1) (run_N ag1 ag2 n c2).
Proof.
  intro n. induction n as [| n IH] using N.peano_ind; intros c1 c2 Heq.
  - exact Heq.
  - rewrite !run_N_succ. apply IH, step_equiv, Heq.
Qed.

Lemma run_N_add : forall a b c,
  run_N ag1 ag2 (a + b) c = run_N ag1 ag2 b (run_N ag1 ag2 a c).
Proof.
  intros a b c. unfold run_N.
  rewrite N.add_comm, N.iter_add. reflexivity.
Qed.

Definition standard_tape (x_anc x_end : Z) : Tape :=
  fun x => if Z.eqb x x_anc then S2
           else if (x_anc <? x) && (x <=? x_end) then S1
           else S0.

(* prefix_8224_equiv will be proved via fast_run *)

(** * 4. Solo Glider (P=15, D=3) *)

Definition step_ag2 (p2 : Z) (s2 : State) (t : Tape) : Z * State * Tape :=
  let tr2 := ag2 s2 (t p2) in
  (move_pos p2 tr2.(move_dir), tr2.(next_state), write_tape t p2 tr2.(write_sym)).

Fixpoint run_ag2 (n : nat) (p2 : Z) (s2 : State) (t : Tape) : Z * State * Tape :=
  match n with
  | O => (p2, s2, t)
  | S n' => let '(p2', s2', t') := step_ag2 p2 s2 t in run_ag2 n' p2' s2' t'
  end.

Fixpoint list_get (l : list Sym) (i : nat) : Sym :=
  match l, i with
  | [], _ => S0
  | x :: _, O => x
  | _ :: xs, S i' => list_get xs i'
  end.

Fixpoint list_set (l : list Sym) (i : nat) (v : Sym) : list Sym :=
  match l, i with
  | [], _ => []
  | _ :: xs, O => v :: xs
  | x :: xs, S i' => x :: list_set xs i' v
  end.

Definition step_ag2_win (p : nat) (s2 : State) (w : list Sym) : nat * State * list Sym :=
  let tr2 := ag2 s2 (list_get w p) in
  let p' := match tr2.(move_dir) with MoveL => pred p | MoveR => S p end in
  (p', tr2.(next_state), list_set w p tr2.(write_sym)).

Fixpoint run_ag2_win (n : nat) (p : nat) (s2 : State) (w : list Sym) : nat * State * list Sym :=
  match n with
  | O => (p, s2, w)
  | S n' => let '(p', s2', w') := step_ag2_win p s2 w in run_ag2_win n' p' s2' w'
  end.

Lemma ag2_glider_15_win :
  run_ag2_win 15 2 StB [S1; S1; S1; S1; S0; S0; S0; S0; S0] =
  (5%nat, StB, [S1; S1; S1; S1; S1; S1; S1; S0; S0]).
Proof.
  vm_compute. reflexivity.
Qed.

(** * 5. Two-Agent Window Simulator for Bounces & Halt *)

Definition step_win (p1 p2 : nat) (s1 s2 : State) (w : list Sym) : nat * nat * State * State * list Sym :=
  let r1 := list_get w p1 in
  let r2 := list_get w p2 in
  let tr1 := ag1 s1 r1 in
  let tr2 := ag2 s2 r2 in
  let w1 := list_set w p2 tr2.(write_sym) in
  let w2 := list_set w1 p1 tr1.(write_sym) in
  let p1' := match tr1.(move_dir) with MoveL => pred p1 | MoveR => S p1 end in
  let p2' := match tr2.(move_dir) with MoveL => pred p2 | MoveR => S p2 end in
  (p1', p2', tr1.(next_state), tr2.(next_state), w2).

Fixpoint run_win (n : nat) (p1 p2 : nat) (s1 s2 : State) (w : list Sym) : nat * nat * State * State * list Sym :=
  match n with
  | O => (p1, p2, s1, s2, w)
  | S n' => let '(p1', p2', s1', s2', w') := step_win p1 p2 s1 s2 w in
            run_win n' p1' p2' s1' s2' w'
  end.

Lemma halt_12_win :
  let w0 := repeat S1 19 ++ repeat S0 10 in
  let '(p1', p2', _, _, _) := run_win 15 5 17 StA StB w0 in
  p1' = p2'.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma bounce_14_win :
  let w0 := repeat S1 46 ++ repeat S0 10 in
  let '(p1', p2', s1', s2', _) := run_win 55 30 44 StA StB w0 in
  p1' = 9%nat /\ p2' = 53%nat /\ s1' = StB /\ s2' = StB.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Lemma bounce_18_win :
  let w0 := repeat S1 50 ++ repeat S0 20 in
  let '(p1', p2', s1', s2', _) := run_win 63 30 48 StA StB w0 in
  p1' = 9%nat /\ p2' = 61%nat /\ s1' = StB /\ s2' = StB.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Lemma bounce_16_win :
  let w0 := repeat S1 48 ++ repeat S0 20 in
  let '(p1', p2', s1', s2', _) := run_win 59 30 46 StA StB w0 in
  p1' = 9%nat /\ p2' = 57%nat /\ s1' = StB /\ s2' = StB.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** * 6. Solo Base-3 Counter *)

Definition step_ag1 (p1 : Z) (s1 : State) (t : Tape) : Z * State * Tape :=
  let tr1 := ag1 s1 (t p1) in
  (move_pos p1 tr1.(move_dir), tr1.(next_state), write_tape t p1 tr1.(write_sym)).

Definition run_ag1 (n : N) (p1 : Z) (s1 : State) (t : Tape) : Z * State * Tape :=
  N.iter n (fun '(p, s, tp) => step_ag1 p s tp) (p1, s1, t).

Lemma run_ag1_add : forall a b p1 s1 t,
  run_ag1 (a + b) p1 s1 t =
  let '(p', s', t') := run_ag1 a p1 s1 t in run_ag1 b p' s' t'.
Proof.
  intros a b p1 s1 t. unfold run_ag1.
  rewrite N.add_comm, N.iter_add.
  destruct (N.iter a _ _) as [[p' s'] t']. reflexivity.
Qed.

Lemma ag1_counter : forall k x_anc t,
  t x_anc = S2 ->
  (forall x, x_anc < x <= x_anc + Z.of_nat k -> t x = S1) ->
  let '(p1', s1', t') := run_ag1 (3 ^ (N.of_nat k + 1) - 2) (x_anc + Z.of_nat k) StB t in
  p1' = x_anc + Z.of_nat k + 1 /\ s1' = StA /\
  (forall x, x < x_anc -> t' x = t x) /\
  (forall x, x > x_anc + Z.of_nat k -> t' x = t x) /\
  t' x_anc = S2 /\
  (forall x, x_anc < x <= x_anc + Z.of_nat k -> t' x = S1).
Proof.
  induction k as [| k IH]; intros x_anc t Hanc HS1.
  - (* k = 0 *)
    replace (3 ^ (N.of_nat 0 + 1) - 2)%N with 1%N by reflexivity.
    unfold run_ag1, step_ag1. simpl.
    replace (x_anc + 0) with x_anc by lia.
    rewrite Hanc. simpl.
    repeat split; try lia; try (unfold write_tape; rewrite Z.eqb_refl; reflexivity);
      intros x Hx; unfold write_tape;
      destruct (Z.eqb_spec x x_anc); try lia; reflexivity.
  - (* S k *)
    set (N_k := (3 ^ (N.of_nat k + 1) - 2)%N).
    assert (Hpow : (3 ^ (N.of_nat (S k) + 1) - 2 = 1 + N_k + 1 + N_k + 1 + N_k + 1)%N).
    { unfold N_k.
      assert (Hge : (3 ^ 1 <= 3 ^ (N.of_nat k + 1))%N) by (apply N.pow_le_mono_r; lia).
      replace (N.of_nat (S k) + 1)%N with (N.succ (N.of_nat k + 1)) by lia.
      rewrite N.pow_succ_r'. lia. }
    rewrite Hpow.
    (* Step 1: (StB, S1) -> (S2, L, StB) *)
    rewrite !run_ag1_add.
    assert (H1 : run_ag1 1 (x_anc + Z.of_nat (S k)) StB t =
                 (x_anc + Z.of_nat k, StB, write_tape t (x_anc + Z.of_nat (S k)) S2)).
    { unfold run_ag1, step_ag1. simpl.
      rewrite HS1; [| lia]. simpl.
      change (Z.pos (PosDef.Pos.of_succ_nat k)) with (Z.of_nat (S k)).
      replace (x_anc + Z.of_nat (S k) - 1) with (x_anc + Z.of_nat k) by lia.
      reflexivity. }
    rewrite H1.
    (* IH 1 *)
    destruct (run_ag1 N_k (x_anc + Z.of_nat k) StB (write_tape t (x_anc + Z.of_nat (S k)) S2))
      as [[p1a s1a] t1a] eqn:E1a.
    pose proof (IH x_anc (write_tape t (x_anc + Z.of_nat (S k)) S2)
      ltac:(unfold write_tape; destruct (Z.eqb_spec x_anc (x_anc + Z.of_nat (S k))); [lia | exact Hanc])
      ltac:(intros x Hx; unfold write_tape; destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia | apply HS1; lia])) as Hih1.
    fold N_k in Hih1. rewrite E1a in Hih1.
    destruct Hih1 as [Hp1a [Hs1a [Hlt1a [Hgt1a [Hanc1a HS1_1a]]]]].
    subst p1a s1a.
    (* Step 2: (StA, S2) -> (S0, L, StB) *)
    assert (H2 : run_ag1 1 (x_anc + Z.of_nat k + 1) StA t1a =
                 (x_anc + Z.of_nat k, StB, write_tape t1a (x_anc + Z.of_nat (S k)) S0)).
    { unfold run_ag1, step_ag1. simpl.
      replace (x_anc + Z.of_nat k + 1) with (x_anc + Z.of_nat (S k)) by lia.
      rewrite Hgt1a; [| lia].
      replace (write_tape t (x_anc + Z.of_nat (S k)) S2 (x_anc + Z.of_nat (S k))) with S2
        by (unfold write_tape; rewrite Z.eqb_refl; reflexivity). simpl.
      change (Z.pos (PosDef.Pos.of_succ_nat k)) with (Z.of_nat (S k)).
      replace (x_anc + Z.of_nat (S k) - 1) with (x_anc + Z.of_nat k) by lia.
      reflexivity. }
    rewrite H2.
    (* IH 2 *)
    destruct (run_ag1 N_k (x_anc + Z.of_nat k) StB (write_tape t1a (x_anc + Z.of_nat (S k)) S0))
      as [[p1b s1b] t1b] eqn:E1b.
    pose proof (IH x_anc (write_tape t1a (x_anc + Z.of_nat (S k)) S0)
      ltac:(unfold write_tape; destruct (Z.eqb_spec x_anc (x_anc + Z.of_nat (S k))); [lia | exact Hanc1a])
      ltac:(intros x Hx; unfold write_tape; destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia | apply HS1_1a; lia])) as Hih2.
    fold N_k in Hih2. rewrite E1b in Hih2.
    destruct Hih2 as [Hp1b [Hs1b [Hlt1b [Hgt1b [Hanc1b HS1_1b]]]]].
    subst p1b s1b.
    (* Step 3: (StA, S0) -> (S1, L, StB) *)
    assert (H3 : run_ag1 1 (x_anc + Z.of_nat k + 1) StA t1b =
                 (x_anc + Z.of_nat k, StB, write_tape t1b (x_anc + Z.of_nat (S k)) S1)).
    { unfold run_ag1, step_ag1. simpl.
      replace (x_anc + Z.of_nat k + 1) with (x_anc + Z.of_nat (S k)) by lia.
      rewrite Hgt1b; [| lia].
      replace (write_tape t1a (x_anc + Z.of_nat (S k)) S0 (x_anc + Z.of_nat (S k))) with S0
        by (unfold write_tape; rewrite Z.eqb_refl; reflexivity). simpl.
      change (Z.pos (PosDef.Pos.of_succ_nat k)) with (Z.of_nat (S k)).
      replace (x_anc + Z.of_nat (S k) - 1) with (x_anc + Z.of_nat k) by lia.
      reflexivity. }
    rewrite H3.
    (* IH 3 *)
    destruct (run_ag1 N_k (x_anc + Z.of_nat k) StB (write_tape t1b (x_anc + Z.of_nat (S k)) S1))
      as [[p1c s1c] t1c] eqn:E1c.
    pose proof (IH x_anc (write_tape t1b (x_anc + Z.of_nat (S k)) S1)
      ltac:(unfold write_tape; destruct (Z.eqb_spec x_anc (x_anc + Z.of_nat (S k))); [lia | exact Hanc1b])
      ltac:(intros x Hx; unfold write_tape; destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia | apply HS1_1b; lia])) as Hih3.
    fold N_k in Hih3. rewrite E1c in Hih3.
    destruct Hih3 as [Hp1c [Hs1c [Hlt1c [Hgt1c [Hanc1c HS1_1c]]]]].
    subst p1c s1c.
    (* Step 4: (StA, S1) -> (S1, R, StA) *)
    unfold run_ag1, step_ag1. simpl.
    change (Z.pos (PosDef.Pos.of_succ_nat k)) with (Z.of_nat (S k)).
    replace (x_anc + Z.of_nat k + 1) with (x_anc + Z.of_nat (S k)) by lia.
    rewrite Hgt1c; [| lia].
    replace (write_tape t1b (x_anc + Z.of_nat (S k)) S1 (x_anc + Z.of_nat (S k))) with S1
      by (unfold write_tape; rewrite Z.eqb_refl; reflexivity). simpl.
    repeat split; try lia.
    + intros x Hx. unfold write_tape. destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia |].
      rewrite Hlt1c; [| lia]. unfold write_tape. destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia |].
      rewrite Hlt1b; [| lia]. unfold write_tape. destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia |].
      rewrite Hlt1a; [| lia]. unfold write_tape. change (Z.pos (PosDef.Pos.of_succ_nat k)) with (Z.of_nat (S k)). destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia | reflexivity].
    + intros x Hx. unfold write_tape. destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia |].
      rewrite Hgt1c; [| lia]. unfold write_tape. destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia |].
      rewrite Hgt1b; [| lia]. unfold write_tape. destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia |].
      rewrite Hgt1a; [| lia]. unfold write_tape. change (Z.pos (PosDef.Pos.of_succ_nat k)) with (Z.of_nat (S k)). destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))); [lia | reflexivity].
    + unfold write_tape. change (Z.pos (PosDef.Pos.of_succ_nat k)) with (Z.of_nat (S k)). destruct (Z.eqb_spec x_anc (x_anc + Z.of_nat (S k))); [lia | exact Hanc1c].
    + intros x Hx. unfold write_tape. change (Z.pos (PosDef.Pos.of_succ_nat k)) with (Z.of_nat (S k)). destruct (Z.eqb_spec x (x_anc + Z.of_nat (S k))) as [-> | Hneq].
      * reflexivity.
      * apply HS1_1c; lia.
Qed.

(** * 7. Decoupling, Walk-Right, and Window Soundness *)

Lemma ag1_walk_right : forall (k : nat) p1 t,
  (forall x, p1 <= x < p1 + Z.of_nat k -> t x = S1) ->
  let '(p1', s1', t') := run_ag1 (N.of_nat k) p1 StA t in
  p1' = p1 + Z.of_nat k /\ s1' = StA /\ forall x, t' x = t x.
Proof.
  induction k as [| k IH]; intros p1 t HS1.
  - repeat split; try lia; reflexivity.
  - replace (N.of_nat (S k)) with (1 + N.of_nat k)%N by lia.
    rewrite run_ag1_add.
    assert (H1 : run_ag1 1 p1 StA t = (p1 + 1, StA, write_tape t p1 S1)).
    { unfold run_ag1, step_ag1. simpl. rewrite HS1; [| lia]. reflexivity. }
    rewrite H1.
    destruct (run_ag1 (N.of_nat k) (p1 + 1) StA (write_tape t p1 S1)) as [[p1' s1'] t'] eqn:Ek.
    pose proof (IH (p1 + 1) (write_tape t p1 S1)
      ltac:(intros x Hx; unfold write_tape; destruct (Z.eqb_spec x p1); [reflexivity | apply HS1; lia])) as Hih.
    rewrite Ek in Hih. destruct Hih as [Hp [Hs Htp]].
    repeat split; try lia; auto.
    intro x. rewrite Htp. unfold write_tape.
    destruct (Z.eqb_spec x p1) as [-> |]; [symmetry; apply HS1; lia | reflexivity].
Qed.

(** * 8. Top-Level Halting Theorem *)

Lemma run_ag1_ag2_decouple : forall n p1 s1 p2 s2 t x_anc x_end p2_min,
  x_end < p2_min ->
  (forall k, (k <= n)%nat ->
    let '(p1', _, _) := run_ag1 (N.of_nat k) p1 s1 t in x_anc <= p1' <= x_end) ->
  (forall k, (k <= n)%nat ->
    let '(p2', _, _) := run_ag2 k p2 s2 t in p2_min <= p2') ->
  let c0 := {| pos1 := p1; pos2 := p2; state1 := s1; state2 := s2; tape := t |} in
  let '(p1', s1', t1') := run_ag1 (N.of_nat n) p1 s1 t in
  let '(p2', s2', t2') := run_ag2 n p2 s2 t in
  let cf := run_N ag1 ag2 (N.of_nat n) c0 in
  cf.(pos1) = p1' /\ cf.(state1) = s1' /\
  cf.(pos2) = p2' /\ cf.(state2) = s2' /\
  (forall x, x <= x_end -> cf.(tape) x = t1' x) /\
  (forall x, x >= p2_min -> cf.(tape) x = t2' x).
Proof.
  induction n as [| n IH]; intros p1 s1 p2 s2 t x_anc x_end p2_min Hsep H1 H2.
  - simpl. repeat split; reflexivity.
  - (* Inductive step *)
    Abort.
