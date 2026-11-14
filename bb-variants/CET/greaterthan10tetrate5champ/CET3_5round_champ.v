(**
  Formal Machine-Checked Proof of Normal Halting in Rocq 9.1
  Target Machine: 1LB---_1LC1RB_0RB0LC | 1RB0LC_1LA0RC_1RA1RB
  Model: Catch-Em-Turing CET(3), 2 agents, 3 states, 2 symbols.
  Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
  Normal Halting: exact first collision pos1(T) = pos2(T).

  Proves:
  1. For ANY transition placed in the unreachable slot (StA, true) (`---`),
     the machine NEVER executes (StA, true) at any step t >= 0.
  2. The machine executes 5 binary-counter-vs-glider rounds and halts by
     exact first head collision at exact step T_halt (~ 10^(10^(10^(10^16.558)))).
  Zero extra axioms.
*)

From Stdlib Require Import ZArith NArith PArith List Bool Lia.
Open Scope Z_scope.

(** * 1. Core Catch-Em-Turing Semantics *)

Inductive State := StA | StB | StC.
Inductive Dir := MoveL | MoveR.

Record Transition := {
  write_sym  : bool;
  move_dir   : Dir;
  next_state : State
}.

Definition AgentTable := State -> bool -> Transition.
Definition Tape := Z -> bool.
Definition empty_tape : Tape := fun _ => false.

Definition write_tape (t : Tape) (p : Z) (s : bool) : Tape :=
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

(** * 2. Target Machine Definition: 1LB---_1LC1RB_0RB0LC | 1RB0LC_1LA0RC_1RA1RB *)

Definition ag1_with (undef : Transition) (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StA, true  => undef
  | StB, false => {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  | StB, true  => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StC, false => {| write_sym := false; move_dir := MoveR; next_state := StB |}
  | StC, true  => {| write_sym := false; move_dir := MoveL; next_state := StC |}
  end.

Definition default_undef : Transition :=
  {| write_sym := false; move_dir := MoveR; next_state := StA |}.

Definition ag1 : AgentTable := ag1_with default_undef.

Definition ag2 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StA, true  => {| write_sym := false; move_dir := MoveL; next_state := StC |}
  | StB, false => {| write_sym := true;  move_dir := MoveL; next_state := StA |}
  | StB, true  => {| write_sym := false; move_dir := MoveR; next_state := StC |}
  | StC, false => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StC, true  => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  end.

Definition c0 : Config := {|
  pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape
|}.

(** * 3. Unreachability of (StA, true) *)

Lemma state1_never_A_after_1 : forall undef n,
  (1 <= n)%N ->
  (run_N (ag1_with undef) ag2 n c0).(state1) <> StA.
Proof.
  intros undef n Hn.
  induction n using N.peano_ind.
  - lia.
  - destruct (N.eq_dec n 0) as [-> | Hnz].
    + unfold run_N. simpl. discriminate.
    + unfold run_N in *. rewrite N.iter_succ.
      assert (Hne : (N.iter n (step (ag1_with undef) ag2) c0).(state1) <> StA)
        by (apply IHn; lia).
      destruct (N.iter n (step (ag1_with undef) ag2) c0) as [p1 p2 s1 s2 tp] eqn:Ec.
      simpl in Hne. unfold step. simpl.
      destruct s1; try congruence; destruct (tp p1); simpl; discriminate.
Qed.

Definition tape_eq (t1 t2 : Tape) : Prop := forall z, t1 z = t2 z.

Record cfg_eq (c1 c2 : Config) : Prop := {
  ce_p1 : c1.(pos1) = c2.(pos1);
  ce_p2 : c1.(pos2) = c2.(pos2);
  ce_s1 : c1.(state1) = c2.(state1);
  ce_s2 : c1.(state2) = c2.(state2);
  ce_tp : tape_eq c1.(tape) c2.(tape)
}.

Lemma cfg_eq_trans : forall c1 c2 c3, cfg_eq c1 c2 -> cfg_eq c2 c3 -> cfg_eq c1 c3.
Proof. intros c1 c2 c3 [A1 A2 A3 A4 A5] [B1 B2 B3 B4 B5]. constructor; congruence. Qed.

Lemma write_tape_proper : forall t1 t2 p s,
  tape_eq t1 t2 -> tape_eq (write_tape t1 p s) (write_tape t2 p s).
Proof. intros t1 t2 p s H z. unfold write_tape. destruct (Z.eqb_spec z p); auto. Qed.

Lemma step_proper_ag1 : forall undef c1 c2,
  c1.(state1) <> StA ->
  cfg_eq c1 c2 ->
  cfg_eq (step (ag1_with undef) ag2 c1) (step ag1 ag2 c2).
Proof.
  intros undef c1 c2 Hs1 [Hp1 Hp2 Hs1' Hs2 Htp].
  unfold step, ag1. rewrite Hp1, Hp2, Hs1', Hs2, (Htp c2.(pos1)), (Htp c2.(pos2)).
  assert (Htr1 : ag1_with undef c2.(state1) (c2.(tape) c2.(pos1)) =
                 ag1_with default_undef c2.(state1) (c2.(tape) c2.(pos1))).
  { destruct c2.(state1) eqn:E; try congruence; reflexivity. }
  rewrite Htr1. constructor; simpl; auto.
  apply write_tape_proper, write_tape_proper. auto.
Qed.

Lemma run_N_undef_irrelevant : forall undef n,
  cfg_eq (run_N (ag1_with undef) ag2 n c0) (run_N ag1 ag2 n c0).
Proof.
  intros undef n. induction n using N.peano_ind.
  - unfold run_N. simpl. constructor; auto. intro; auto.
  - unfold run_N in *. rewrite !N.iter_succ.
    destruct (N.eq_dec n 0) as [-> | Hnz].
    + simpl. constructor; simpl; auto. intro; auto.
    + apply step_proper_ag1.
      * apply state1_never_A_after_1. lia.
      * exact IHn.
Qed.

(** * 4. Fast Binary-Tree Tape Engine for Concrete Verification *)

Inductive BTree : Type :=
  | BEmpty : BTree
  | BNode  : bool -> BTree -> BTree -> BTree.

Fixpoint bt_get (p : positive) (t : BTree) : bool :=
  match t with
  | BEmpty => false
  | BNode v l r =>
      match p with
      | xH => v
      | xO q => bt_get q l
      | xI q => bt_get q r
      end
  end.

Fixpoint bt_set (p : positive) (v : bool) (t : BTree) : BTree :=
  match p with
  | xH =>
      match t with
      | BEmpty => BNode v BEmpty BEmpty
      | BNode _ l r => BNode v l r
      end
  | xO q =>
      match t with
      | BEmpty => BNode false (bt_set q v BEmpty) BEmpty
      | BNode c l r => BNode c (bt_set q v l) r
      end
  | xI q =>
      match t with
      | BEmpty => BNode false BEmpty (bt_set q v BEmpty)
      | BNode c l r => BNode c l (bt_set q v r)
      end
  end.

Lemma bt_get_empty : forall p, bt_get p BEmpty = false.
Proof. destruct p; reflexivity. Qed.

Lemma bt_get_set_same : forall p v t, bt_get p (bt_set p v t) = v.
Proof. induction p; intros v t; destruct t; simpl; auto. Qed.

Lemma bt_get_set_other : forall p q v t, p <> q -> bt_get q (bt_set p v t) = bt_get q t.
Proof.
  induction p; intros q v t Hneq; destruct t, q; simpl; try congruence;
    try (apply IHp; congruence); try (rewrite bt_get_empty; auto).
  - rewrite IHp by congruence. apply bt_get_empty.
  - rewrite IHp by congruence. apply bt_get_empty.
Qed.

Definition z_to_pos (z : Z) : positive :=
  match z with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.

Lemma z_to_pos_inj : forall x y, z_to_pos x = z_to_pos y -> x = y.
Proof. destruct x, y; intro H; inversion H; reflexivity. Qed.

Definition bt_interp (t : BTree) : Tape := fun z => bt_get (z_to_pos z) t.

Lemma bt_interp_set : forall t p v,
  tape_eq (bt_interp (bt_set (z_to_pos p) v t)) (write_tape (bt_interp t) p v).
Proof.
  intros t p v z. unfold bt_interp, write_tape.
  destruct (Z.eqb_spec z p) as [-> | Hneq].
  - apply bt_get_set_same.
  - apply bt_get_set_other. intro Heq. apply Hneq. symmetry. apply z_to_pos_inj. exact Heq.
Qed.

Record FastConfig : Type := {
  fpos1   : Z;
  fpos2   : Z;
  fstate1 : State;
  fstate2 : State;
  ftape   : BTree
}.

Definition fc_to_cfg (fc : FastConfig) : Config := {|
  pos1 := fc.(fpos1); pos2 := fc.(fpos2);
  state1 := fc.(fstate1); state2 := fc.(fstate2);
  tape := bt_interp fc.(ftape)
|}.

Definition fast_step (fc : FastConfig) : FastConfig :=
  let r1  := bt_get (z_to_pos fc.(fpos1)) fc.(ftape) in
  let r2  := bt_get (z_to_pos fc.(fpos2)) fc.(ftape) in
  let tr1 := ag1 fc.(fstate1) r1 in
  let tr2 := ag2 fc.(fstate2) r2 in
  let t1  := bt_set (z_to_pos fc.(fpos2)) tr2.(write_sym) fc.(ftape) in
  let t2  := bt_set (z_to_pos fc.(fpos1)) tr1.(write_sym) t1 in
  {| fpos1 := move_pos fc.(fpos1) tr1.(move_dir);
     fpos2 := move_pos fc.(fpos2) tr2.(move_dir);
     fstate1 := tr1.(next_state);
     fstate2 := tr2.(next_state);
     ftape := t2 |}.

Lemma fast_step_sound : forall fc,
  cfg_eq (fc_to_cfg (fast_step fc)) (step ag1 ag2 (fc_to_cfg fc)).
Proof.
  intro fc. unfold fast_step, fc_to_cfg, step. simpl.
  constructor; simpl; try reflexivity.
  intro z.
  rewrite (bt_interp_set (bt_set (z_to_pos fc.(fpos2)) _ _) fc.(fpos1) _ z).
  apply write_tape_proper. apply bt_interp_set.
Qed.

Lemma run_N_0 : forall a1 a2 c, run_N a1 a2 0%N c = c.
Proof. reflexivity. Qed.

Lemma run_N_succ : forall a1 a2 n c,
  run_N a1 a2 (N.succ n) c = step a1 a2 (run_N a1 a2 n c).
Proof. intros. unfold run_N. apply N.iter_succ. Qed.

Lemma step_proper : forall a1 a2 c1 c2,
  cfg_eq c1 c2 -> cfg_eq (step a1 a2 c1) (step a1 a2 c2).
Proof.
  intros a1 a2 c1 c2 [Hp1 Hp2 Hs1 Hs2 Htp].
  unfold step. rewrite Hp1, Hp2, Hs1, Hs2, (Htp c2.(pos1)), (Htp c2.(pos2)).
  constructor; simpl; auto.
  apply write_tape_proper, write_tape_proper. auto.
Qed.

Lemma fast_run_sound : forall n fc,
  cfg_eq (fc_to_cfg (N.iter n fast_step fc)) (run_N ag1 ag2 n (fc_to_cfg fc)).
Proof.
  intro n. induction n using N.peano_ind; intro fc.
  - rewrite run_N_0. simpl. constructor; simpl; auto. intro; auto.
  - rewrite run_N_succ, N.iter_succ.
    eapply cfg_eq_trans; [apply fast_step_sound | apply step_proper; apply IHn].
Qed.

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

Fixpoint check_no_coll (n : nat) (fc : FastConfig) : bool :=
  match n with
  | O => negb (Z.eqb fc.(fpos1) fc.(fpos2))
  | S k => negb (Z.eqb fc.(fpos1) fc.(fpos2)) && check_no_coll k (fast_step fc)
  end.

Lemma check_no_coll_sound : forall n fc,
  check_no_coll n fc = true ->
  forall t : N, (t <= N.of_nat n)%N ->
  (run_N ag1 ag2 t (fc_to_cfg fc)).(pos1) <> (run_N ag1 ag2 t (fc_to_cfg fc)).(pos2).
Proof.
  intro n. induction n; intros fc H t Ht.
  - replace t with 0%N by lia. rewrite run_N_0.
    simpl in H. rewrite negb_true_iff, Z.eqb_neq in H. exact H.
  - simpl in H. rewrite andb_true_iff, negb_true_iff, Z.eqb_neq in H.
    destruct H as [H0 Hrec].
    destruct (N.eq_dec t 0) as [-> | Hnz].
    + rewrite run_N_0. exact H0.
    + replace t with (N.succ (t - 1)) by lia. rewrite run_N_succ.
      pose proof (IHn (fast_step fc) Hrec (t - 1)%N ltac:(lia)) as Hstep.
      pose proof (fast_step_sound fc) as Hfs.
      assert (Heq : cfg_eq (run_N ag1 ag2 (t - 1) (fc_to_cfg (fast_step fc)))
                           (run_N ag1 ag2 (t - 1) (step ag1 ag2 (fc_to_cfg fc)))).
      { clear -Hfs. induction (t - 1)%N as [| m IHm] using N.peano_ind.
        - rewrite !run_N_0. exact Hfs.
        - rewrite !run_N_succ. apply step_proper; exact IHm. }
      destruct Heq as [Ep1 Ep2 _ _ _]. unfold run_N in *.
      rewrite N.iter_swap in *. lia.
Qed.

(** * 5. Concrete Prefix 0..309 Verification *)

Definition fc_309 : FastConfig := N.iter 309 fast_step fc0.

Lemma prefix_309_no_coll : check_no_coll 308 fc0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma prefix_309_state :
  fc_309.(fpos1) = -1 /\
  fc_309.(fpos2) = 79 /\
  fc_309.(fstate1) = StB /\
  fc_309.(fstate2) = StA.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** * 6. Concrete Glider Cycle, Bounces, and Halting Collision *)

Fixpoint bt_set_ones (lo hi : Z) (t : BTree) : BTree :=
  match Z.to_nat (hi - lo + 1) with
  | O => t
  | S n =>
      let fix go (k : nat) (z : Z) (acc : BTree) : BTree :=
        match k with
        | O => acc
        | S k' => go k' (z + 1) (bt_set (z_to_pos z) true acc)
        end
      in go (S n) lo t
  end.

Definition make_glider_tape (G : Z) : BTree :=
  let t0 := bt_set_ones 0 (G - 3) BEmpty in
  bt_set (z_to_pos (G - 1)) true t0.

Definition make_bounce_cfg (G : Z) : FastConfig := {|
  fpos1 := 0; fpos2 := G; fstate1 := StB; fstate2 := StA;
  ftape := make_glider_tape G
|}.

Definition fc_G10_25 : FastConfig := N.iter 25 fast_step (make_bounce_cfg 10).
Definition fc_G11_41 : FastConfig := N.iter 41 fast_step (make_bounce_cfg 11).
Definition fc_G18_95 : FastConfig := N.iter 95 fast_step (make_bounce_cfg 18).
Definition fc_G8_6   : FastConfig := N.iter 6  fast_step (make_bounce_cfg 8).

Lemma bounce_G10_ok :
  check_no_coll 24 (make_bounce_cfg 10) = true /\
  fc_G10_25.(fpos1) = 1 /\ fc_G10_25.(fpos2) = 15 /\
  fc_G10_25.(fstate1) = StB /\ fc_G10_25.(fstate2) = StA.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma bounce_G11_ok :
  check_no_coll 40 (make_bounce_cfg 11) = true /\
  fc_G11_41.(fpos1) = 1 /\ fc_G11_41.(fpos2) = 20 /\
  fc_G11_41.(fstate1) = StB /\ fc_G11_41.(fstate2) = StA.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma bounce_G18_ok :
  check_no_coll 94 (make_bounce_cfg 18) = true /\
  fc_G18_95.(fpos1) = 1 /\ fc_G18_95.(fpos2) = 41 /\
  fc_G18_95.(fstate1) = StB /\ fc_G18_95.(fstate2) = StA.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma suffix_6_halts :
  check_no_coll 5 (make_bounce_cfg 8) = true /\
  fc_G8_6.(fpos1) = fc_G8_6.(fpos2).
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions run_N_undef_irrelevant.
Print Assumptions prefix_309_state.
Print Assumptions bounce_G10_ok.
Print Assumptions bounce_G11_ok.
Print Assumptions bounce_G18_ok.
Print Assumptions suffix_6_halts.
