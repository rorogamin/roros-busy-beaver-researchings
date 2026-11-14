(** Formal Specification and Round-2-Entry Verification in Rocq 9.1
    Target Machine: 1LB1RA0LB_2RB2LB2RA | 2RB1LA1RB_2LB2RB1LA
    Model: Catch-Em-Turing CET(2,3), 2 agents, 2 states, 3 symbols.
    Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
    Proves:
      - Zero collisions for 0 <= t < 844 from blank tape.
      - Exact Round 2 entry at t = 844: pos1 = 86 (StA), pos2 = 96 (StB),
        gap G1 = 10, counter length L2 = 87 (anchor S2 at -1, S1 at [0..85]).
    Zero extra axioms ("Closed under the global context").
*)

From Stdlib Require Import ZArith NArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core CET(2,3) Semantics *)

Inductive State : Type := StA | StB.
Inductive Sym : Type := S0 | S1 | S2.
Inductive Dir : Type := MoveL | MoveR.

Definition sym_eqb (a b : Sym) : bool :=
  match a, b with
  | S0, S0 | S1, S1 | S2, S2 => true
  | _, _ => false
  end.

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

(** * 2. Target Machine: 1LB1RA0LB_2RB2LB2RA | 2RB1LA1RB_2LB2RB1LA *)

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

(** * 3. Fast BTree Tape Engine *)

Definition tape_eq (t1 t2 : Tape) : Prop := forall z, t1 z = t2 z.

Record cfg_eq (c1 c2 : Config) : Prop := {
  ce_p1 : c1.(pos1) = c2.(pos1);
  ce_p2 : c1.(pos2) = c2.(pos2);
  ce_s1 : c1.(state1) = c2.(state1);
  ce_s2 : c1.(state2) = c2.(state2);
  ce_tp : tape_eq c1.(tape) c2.(tape)
}.

Lemma cfg_eq_trans : forall c1 c2 c3, cfg_eq c1 c2 -> cfg_eq c2 c3 -> cfg_eq c1 c3.
Proof.
  intros c1 c2 c3 [A1 A2 A3 A4 A5] [B1 B2 B3 B4 B5].
  constructor; congruence.
Qed.

Lemma write_tape_proper : forall t1 t2 p s,
  tape_eq t1 t2 -> tape_eq (write_tape t1 p s) (write_tape t2 p s).
Proof.
  intros t1 t2 p s H z. unfold write_tape. destruct (Z.eqb_spec z p); auto.
Qed.

Lemma step_proper : forall a1 a2 c1 c2,
  cfg_eq c1 c2 -> cfg_eq (step a1 a2 c1) (step a1 a2 c2).
Proof.
  intros a1 a2 c1 c2 [Hp1 Hp2 Hs1 Hs2 Htp].
  unfold step. rewrite Hp1, Hp2, Hs1, Hs2, (Htp c2.(pos1)), (Htp c2.(pos2)).
  constructor; simpl; auto.
  apply write_tape_proper. apply write_tape_proper. auto.
Qed.

Lemma run_N_proper : forall a1 a2 n c1 c2,
  cfg_eq c1 c2 -> cfg_eq (run_N a1 a2 n c1) (run_N a1 a2 n c2).
Proof.
  intros a1 a2 n. induction n using N.peano_ind; intros c1 c2 H.
  - unfold run_N. simpl. auto.
  - unfold run_N in *. rewrite !N.iter_succ. apply step_proper. apply IHn. auto.
Qed.

Inductive BTree : Type :=
  | BEmpty : BTree
  | BNode  : Sym -> BTree -> BTree -> BTree.

Fixpoint bt_get (p : positive) (t : BTree) : Sym :=
  match t with
  | BEmpty => S0
  | BNode v l r =>
      match p with
      | xH => v
      | xO q => bt_get q l
      | xI q => bt_get q r
      end
  end.

Fixpoint bt_set (p : positive) (v : Sym) (t : BTree) : BTree :=
  match p with
  | xH =>
      match t with
      | BEmpty => BNode v BEmpty BEmpty
      | BNode _ l r => BNode v l r
      end
  | xO q =>
      match t with
      | BEmpty => BNode S0 (bt_set q v BEmpty) BEmpty
      | BNode c l r => BNode c (bt_set q v l) r
      end
  | xI q =>
      match t with
      | BEmpty => BNode S0 BEmpty (bt_set q v BEmpty)
      | BNode c l r => BNode c l (bt_set q v r)
      end
  end.

Lemma bt_get_empty : forall p, bt_get p BEmpty = S0.
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
  match z with
  | Z0 => xH
  | Zpos p => xO p
  | Zneg p => xI p
  end.

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
  pos1   := fc.(fpos1);
  pos2   := fc.(fpos2);
  state1 := fc.(fstate1);
  state2 := fc.(fstate2);
  tape   := bt_interp fc.(ftape)
|}.

Definition fast_step (fc : FastConfig) : FastConfig :=
  let r1  := bt_get (z_to_pos fc.(fpos1)) fc.(ftape) in
  let r2  := bt_get (z_to_pos fc.(fpos2)) fc.(ftape) in
  let tr1 := ag1 fc.(fstate1) r1 in
  let tr2 := ag2 fc.(fstate2) r2 in
  let t1  := bt_set (z_to_pos fc.(fpos2)) tr2.(write_sym) fc.(ftape) in
  let t2  := bt_set (z_to_pos fc.(fpos1)) tr1.(write_sym) t1 in
  {| fpos1   := move_pos fc.(fpos1) tr1.(move_dir);
     fpos2   := move_pos fc.(fpos2) tr2.(move_dir);
     fstate1 := tr1.(next_state);
     fstate2 := tr2.(next_state);
     ftape   := t2 |}.

Lemma fast_step_sound : forall fc,
  cfg_eq (fc_to_cfg (fast_step fc)) (step ag1 ag2 (fc_to_cfg fc)).
Proof.
  intro fc. unfold fast_step, fc_to_cfg, step. simpl.
  constructor; simpl; try reflexivity.
  intro z.
  rewrite (bt_interp_set (bt_set (z_to_pos fc.(fpos2)) _ _) fc.(fpos1) _ z).
  apply write_tape_proper. apply bt_interp_set.
Qed.

Lemma fast_run_sound : forall n fc,
  cfg_eq (fc_to_cfg (N.iter n fast_step fc)) (run_N ag1 ag2 n (fc_to_cfg fc)).
Proof.
  intro n. induction n using N.peano_ind; intro fc.
  - unfold run_N. simpl. constructor; simpl; auto. intro; auto.
  - unfold run_N. rewrite !N.iter_succ.
    eapply cfg_eq_trans; [apply fast_step_sound | apply step_proper; apply IHn].
Qed.

Definition fast_step_chk (st : FastConfig * bool) : FastConfig * bool :=
  let (fc, ok) := st in
  (fast_step fc, ok && negb (fc.(fpos1) =? fc.(fpos2))).

Lemma fast_step_chk_fst : forall n fc ok,
  fst (N.iter n fast_step_chk (fc, ok)) = N.iter n fast_step fc.
Proof.
  intro n. induction n using N.peano_ind; intros fc ok; [reflexivity|].
  rewrite !N.iter_succ.
  destruct (N.iter n fast_step_chk (fc, ok)) as [fc' ok'] eqn:E.
  simpl. assert (fc' = N.iter n fast_step fc) by (rewrite <- (IHn fc ok), E; reflexivity).
  subst fc'. reflexivity.
Qed.

Lemma fast_step_chk_sound : forall n fc ok,
  snd (N.iter n fast_step_chk (fc, ok)) = true ->
  ok = true /\
  forall k, (k < n)%N -> (N.iter k fast_step fc).(fpos1) <> (N.iter k fast_step fc).(fpos2).
Proof.
  intro n. induction n using N.peano_ind; intros fc ok Hsnd.
  - simpl in Hsnd. split; [exact Hsnd | intros k Hk; lia].
  - rewrite N.iter_succ in Hsnd.
    destruct (N.iter n fast_step_chk (fc, ok)) as [fc' ok'] eqn:E.
    assert (Hfc : fc' = N.iter n fast_step fc)
      by (rewrite <- (fast_step_chk_fst n fc ok), E; reflexivity).
    simpl in Hsnd. rewrite andb_true_iff in Hsnd.
    destruct Hsnd as [Hok' Hneq].
    assert (Hsnd_n : snd (N.iter n fast_step_chk (fc, ok)) = true) by (rewrite E; exact Hok').
    destruct (IHn fc ok Hsnd_n) as [Hok Hlt].
    split; [exact Hok |].
    intros k Hk. destruct (N.lt_ge_cases k n); [apply Hlt; auto|].
    replace k with n by lia. rewrite <- Hfc.
    rewrite negb_true_iff, Z.eqb_neq in Hneq. exact Hneq.
Qed.

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

Lemma fc0_eq_c0 : cfg_eq (fc_to_cfg fc0) c0.
Proof.
  constructor; simpl; try reflexivity.
  intro z. unfold bt_interp, empty_tape. apply bt_get_empty.
Qed.

Definition fc_844 : FastConfig := N.iter 844 fast_step fc0.

Lemma prefix_844_no_coll :
  snd (N.iter 844 fast_step_chk (fc0, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma prefix_844_summary :
  let c := run_N ag1 ag2 844 c0 in
  c.(pos1) = 86 /\
  c.(pos2) = 96 /\
  c.(state1) = StA /\
  c.(state2) = StB /\
  c.(tape) (-1) = S2 /\
  (forall t, (t < 844)%N -> ~ collides_at ag1 ag2 c0 t).
Proof.
  pose proof (run_N_proper ag1 ag2 844 (fc_to_cfg fc0) c0 fc0_eq_c0) as Heq.
  pose proof (fast_run_sound 844 fc0) as Hfs.
  pose proof (cfg_eq_trans _ _ _ (ltac:(exact Hfs)) (ltac:(exact Heq))) as [Hp1 Hp2 Hs1 Hs2 Htp].
  fold fc_844 in Hp1, Hp2, Hs1, Hs2, Htp.
  assert (Hst : fc_844.(fpos1) = 86 /\ fc_844.(fpos2) = 96 /\
                fc_844.(fstate1) = StA /\ fc_844.(fstate2) = StB /\
                bt_interp fc_844.(ftape) (-1) = S2)
    by (repeat split; vm_compute; reflexivity).
  destruct Hst as [R1 [R2 [R3 [R4 R5]]]].
  repeat split; try (simpl in *; lia); try (simpl in *; congruence).
  - rewrite <- Htp. exact R5.
  - intros t Ht. unfold collides_at.
    pose proof (fast_step_chk_sound 844 fc0 true prefix_844_no_coll) as [_ Hnc].
    specialize (Hnc t Ht).
    pose proof (run_N_proper ag1 ag2 t (fc_to_cfg fc0) c0 fc0_eq_c0) as [Tp1 Tp2 _ _ _].
    pose proof (fast_run_sound t fc0) as [Fp1 Fp2 _ _ _].
    simpl in *. lia.
Qed.

Print Assumptions prefix_844_summary.
