(** Formal Machine-Checked Proof of Normal Halting in Rocq 9.1
    Target Machine: 1LB1RA_1RC0LD_1LA0LB_0RB0RA | 1RB0LC_1LA0RC_1LD0RA_1RC1RA
    Model: Catch-Em-Turing CET(4,2), 2 agents, 4 states, 2 symbols.
    Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
    Exact halting step:
      exact_T_halt = 3720 + 160 + (27 * 2^141 - 121) + 27 * ((2^141 - 44) / 26) + 30
                   = 78159823316003962837401627984426228547406259 (~7.816e43)
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

(** * 3. Equivalence, Shift, and Agreement Laws *)

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

Lemma write_tape_same : forall t p s, write_tape t p s p = s.
Proof. intros. unfold write_tape. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma write_tape_other : forall t p s x, x <> p -> write_tape t p s x = t x.
Proof. intros. unfold write_tape. destruct (Z.eqb_spec x p); congruence. Qed.

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

Lemma run_N_0 : forall a1 a2 c, run_N a1 a2 0%N c = c.
Proof. reflexivity. Qed.

Lemma run_N_succ : forall a1 a2 n c,
  run_N a1 a2 (N.succ n) c = step a1 a2 (run_N a1 a2 n c).
Proof. intros. unfold run_N. apply N.iter_succ. Qed.

Lemma run_N_add : forall a1 a2 p q c,
  run_N a1 a2 (p + q) c = run_N a1 a2 p (run_N a1 a2 q c).
Proof. intros. unfold run_N. apply N.iter_add. Qed.

Lemma no_coll_add : forall a1 a2 p q c,
  (forall t, (t < q)%N -> (run_N a1 a2 t c).(pos1) <> (run_N a1 a2 t c).(pos2)) ->
  (forall t, (t < p)%N -> (run_N a1 a2 t (run_N a1 a2 q c)).(pos1) <>
                         (run_N a1 a2 t (run_N a1 a2 q c)).(pos2)) ->
  forall t, (t < p + q)%N -> (run_N a1 a2 t c).(pos1) <> (run_N a1 a2 t c).(pos2).
Proof.
  intros a1 a2 p q c Hq Hp t Ht.
  destruct (N.lt_ge_cases t q) as [Hlt | Hge].
  - apply Hq; auto.
  - replace t with ((t - q) + q)%N by lia.
    rewrite run_N_add. apply Hp. lia.
Qed.

Definition shift_cfg (delta : Z) (c : Config) : Config := {|
  pos1   := c.(pos1) + delta;
  pos2   := c.(pos2) + delta;
  state1 := c.(state1);
  state2 := c.(state2);
  tape   := fun z => c.(tape) (z - delta)
|}.

Lemma shift_cfg_pos1 : forall d c, (shift_cfg d c).(pos1) = c.(pos1) + d.
Proof. intros; reflexivity. Qed.
Lemma shift_cfg_pos2 : forall d c, (shift_cfg d c).(pos2) = c.(pos2) + d.
Proof. intros; reflexivity. Qed.
Lemma shift_cfg_state1 : forall d c, (shift_cfg d c).(state1) = c.(state1).
Proof. intros; reflexivity. Qed.
Lemma shift_cfg_state2 : forall d c, (shift_cfg d c).(state2) = c.(state2).
Proof. intros; reflexivity. Qed.

Lemma step_shift : forall a1 a2 d c,
  cfg_eq (step a1 a2 (shift_cfg d c)) (shift_cfg d (step a1 a2 c)).
Proof.
  intros a1 a2 d c. unfold step, shift_cfg. simpl.
  replace (c.(pos1) + d - d) with c.(pos1) by lia.
  replace (c.(pos2) + d - d) with c.(pos2) by lia.
  constructor; simpl; try (destruct move_dir; lia); try reflexivity.
  intro z. unfold write_tape.
  destruct (Z.eqb_spec z (c.(pos1) + d)) as [E1|N1];
    destruct (Z.eqb_spec (z - d) c.(pos1)) as [E1'|N1']; try lia; auto.
  destruct (Z.eqb_spec z (c.(pos2) + d)) as [E2|N2];
    destruct (Z.eqb_spec (z - d) c.(pos2)) as [E2'|N2']; try lia; auto.
Qed.

Lemma run_N_shift : forall a1 a2 d n c,
  cfg_eq (run_N a1 a2 n (shift_cfg d c)) (shift_cfg d (run_N a1 a2 n c)).
Proof.
  intros a1 a2 d n. induction n using N.peano_ind; intro c.
  - rewrite !run_N_0. constructor; simpl; auto. intro; auto.
  - rewrite !run_N_succ.
    eapply cfg_eq_trans; [apply step_proper; apply IHn | apply step_shift].
Qed.

Lemma run_N_agree_range : forall a1 a2 lo hi n c1 c2,
  c1.(pos1) = c2.(pos1) ->
  c1.(pos2) = c2.(pos2) ->
  c1.(state1) = c2.(state1) ->
  c1.(state2) = c2.(state2) ->
  (forall z, lo <= z <= hi -> c1.(tape) z = c2.(tape) z) ->
  (forall k, (k < n)%N ->
    lo <= (run_N a1 a2 k c1).(pos1) <= hi /\
    lo <= (run_N a1 a2 k c1).(pos2) <= hi) ->
  (run_N a1 a2 n c1).(pos1) = (run_N a1 a2 n c2).(pos1) /\
  (run_N a1 a2 n c1).(pos2) = (run_N a1 a2 n c2).(pos2) /\
  (run_N a1 a2 n c1).(state1) = (run_N a1 a2 n c2).(state1) /\
  (run_N a1 a2 n c1).(state2) = (run_N a1 a2 n c2).(state2) /\
  (forall z, lo <= z <= hi -> (run_N a1 a2 n c1).(tape) z = (run_N a1 a2 n c2).(tape) z) /\
  (forall z, z < lo \/ z > hi -> (run_N a1 a2 n c2).(tape) z = c2.(tape) z) /\
  (forall k, (k < n)%N ->
    (run_N a1 a2 k c1).(pos1) = (run_N a1 a2 k c2).(pos1) /\
    (run_N a1 a2 k c1).(pos2) = (run_N a1 a2 k c2).(pos2)).
Proof.
  intros a1 a2 lo hi n. induction n using N.peano_ind; intros c1 c2 Hp1 Hp2 Hs1 Hs2 Htp Hbd.
  - rewrite !run_N_0. repeat split; auto. intros k Hk; lia.
  - assert (Hbd_n : forall k, (k < n)%N ->
      lo <= (run_N a1 a2 k c1).(pos1) <= hi /\ lo <= (run_N a1 a2 k c1).(pos2) <= hi)
      by (intros k Hk; apply Hbd; lia).
    destruct (IHn c1 c2 Hp1 Hp2 Hs1 Hs2 Htp Hbd_n)
      as [Ip1 [Ip2 [Is1 [Is2 [Itp [Iout Iprev]]]]]].
    destruct (Hbd n ltac:(lia)) as [Hbn1 Hbn2].
    rewrite !run_N_succ.
    set (r1 := run_N a1 a2 n c1). set (r2 := run_N a1 a2 n c2).
    assert (Hr1 : r1.(tape) r1.(pos1) = r2.(tape) r2.(pos1))
      by (rewrite <- Ip1; apply Itp; exact Hbn1).
    assert (Hr2 : r1.(tape) r1.(pos2) = r2.(tape) r2.(pos2))
      by (rewrite <- Ip2; apply Itp; exact Hbn2).
    unfold step. rewrite Ip1, Ip2, Is1, Is2, Hr1, Hr2.
    repeat split; simpl; auto.
    + intros z Hz. unfold write_tape.
      destruct (Z.eqb_spec z r2.(pos1)); auto.
      destruct (Z.eqb_spec z r2.(pos2)); auto.
    + intros z Hz. unfold write_tape.
      destruct (Z.eqb_spec z r2.(pos1)) as [E1|N1]; [lia|].
      destruct (Z.eqb_spec z r2.(pos2)) as [E2|N2]; [lia|].
      apply Iout; exact Hz.
    + intros k Hk. destruct (N.lt_ge_cases k n) as [Hlt | Hge].
      * apply Iprev; exact Hlt.
      * replace k with n by lia. split; assumption.
Qed.

(** * 4. Fast Binary-Tree Tape Engine *)

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
  match z with
  | Z0 => xH
  | Zpos p => xO p
  | Zneg p => xI p
  end.

Definition pos_to_z (p : positive) : Z :=
  match p with
  | xH => Z0
  | xO q => Zpos q
  | xI q => Zneg q
  end.

Lemma z_pos_z : forall z, pos_to_z (z_to_pos z) = z.
Proof. destruct z; reflexivity. Qed.

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
  - rewrite run_N_0. simpl. constructor; simpl; auto. intro; auto.
  - rewrite run_N_succ, N.iter_succ.
    eapply cfg_eq_trans; [apply fast_step_sound | apply step_proper; apply IHn].
Qed.

Lemma fc_to_cfg_pos1 : forall fc, (fc_to_cfg fc).(pos1) = fc.(fpos1).
Proof. intros; reflexivity. Qed.
Lemma fc_to_cfg_pos2 : forall fc, (fc_to_cfg fc).(pos2) = fc.(fpos2).
Proof. intros; reflexivity. Qed.
Lemma fc_to_cfg_state1 : forall fc, (fc_to_cfg fc).(state1) = fc.(fstate1).
Proof. intros; reflexivity. Qed.
Lemma fc_to_cfg_state2 : forall fc, (fc_to_cfg fc).(state2) = fc.(fstate2).
Proof. intros; reflexivity. Qed.

Definition fast_step_chk_range (lo hi : Z) (st : FastConfig * bool) : FastConfig * bool :=
  let (fc, ok) := st in
  let ok_pre := ok && negb (fc.(fpos1) =? fc.(fpos2))
                   && (lo <=? fc.(fpos1)) && (fc.(fpos1) <=? hi)
                   && (lo <=? fc.(fpos2)) && (fc.(fpos2) <=? hi) in
  (fast_step fc, ok_pre).

Lemma fast_step_chk_range_fst : forall n lo hi fc ok,
  fst (N.iter n (fast_step_chk_range lo hi) (fc, ok)) = N.iter n fast_step fc.
Proof.
  intro n. induction n using N.peano_ind; intros lo hi fc ok.
  - reflexivity.
  - rewrite !N.iter_succ.
    destruct (N.iter n (fast_step_chk_range lo hi) (fc, ok)) as [fc' ok'] eqn:E.
    simpl. assert (fc' = N.iter n fast_step fc) by (rewrite <- (IHn lo hi fc ok), E; reflexivity).
    subst fc'. reflexivity.
Qed.

Lemma fast_step_chk_range_sound : forall n lo hi fc ok,
  snd (N.iter n (fast_step_chk_range lo hi) (fc, ok)) = true ->
  ok = true /\
  forall k, (k < n)%N ->
    let fc_k := N.iter k fast_step fc in
    fc_k.(fpos1) <> fc_k.(fpos2) /\
    lo <= fc_k.(fpos1) <= hi /\
    lo <= fc_k.(fpos2) <= hi.
Proof.
  intro n. induction n using N.peano_ind; intros lo hi fc ok Hsnd.
  - simpl in Hsnd. split; [exact Hsnd | intros k Hk; lia].
  - rewrite N.iter_succ in Hsnd.
    destruct (N.iter n (fast_step_chk_range lo hi) (fc, ok)) as [fc' ok'] eqn:E.
    assert (Hfc : fc' = N.iter n fast_step fc)
      by (rewrite <- (fast_step_chk_range_fst n lo hi fc ok), E; reflexivity).
    simpl in Hsnd. rewrite !andb_true_iff in Hsnd.
    destruct Hsnd as [[[[[Hok' Hneq] Hlo1] Hhi1] Hlo2] Hhi2].
    assert (Hsnd_n : snd (N.iter n (fast_step_chk_range lo hi) (fc, ok)) = true)
      by (rewrite E; exact Hok').
    destruct (IHn lo hi fc ok Hsnd_n) as [Hok Hlt].
    split; [exact Hok |].
    intros k Hk.
    destruct (N.lt_ge_cases k n) as [Hlt_k | Hge_k].
    + apply Hlt; exact Hlt_k.
    + replace k with n by lia. rewrite <- Hfc.
      rewrite negb_true_iff, Z.eqb_neq in Hneq.
      rewrite !Z.leb_le in Hlo1, Hhi1, Hlo2, Hhi2.
      repeat split; auto; lia.
Qed.

Fixpoint bt_bounded_aux (lo hi : Z) (k : positive -> positive) (t : BTree) : bool :=
  match t with
  | BEmpty => true
  | BNode v l r =>
      let z := pos_to_z (k xH) in
      (if v then (lo <=? z) && (z <=? hi) else true) &&
      bt_bounded_aux lo hi (fun q => k (xO q)) l &&
      bt_bounded_aux lo hi (fun q => k (xI q)) r
  end.

Lemma bt_bounded_aux_sound : forall lo hi t k p,
  bt_bounded_aux lo hi k t = true ->
  bt_get p t = true ->
  lo <= pos_to_z (k p) <= hi.
Proof.
  intros lo hi. induction t; intros k p Hb Hg.
  - rewrite bt_get_empty in Hg. discriminate.
  - simpl in Hb. rewrite !andb_true_iff in Hb. destruct Hb as [[Hv Hl] Hr].
    destruct p; simpl in Hg.
    + apply (IHt2 (fun q => k (xI q)) p Hr Hg).
    + apply (IHt1 (fun q => k (xO q)) p Hl Hg).
    + rewrite Hg in Hv. rewrite andb_true_iff, !Z.leb_le in Hv. exact Hv.
Qed.

Lemma bt_bounded_sound : forall lo hi t z,
  bt_bounded_aux lo hi (fun q => q) t = true ->
  z < lo \/ z > hi ->
  bt_interp t z = false.
Proof.
  intros lo hi t z Hb Hout. unfold bt_interp.
  destruct (bt_get (z_to_pos z) t) eqn:E; auto.
  pose proof (bt_bounded_aux_sound lo hi t (fun q => q) (z_to_pos z) Hb E) as Hbd.
  simpl in Hbd. rewrite z_pos_z in Hbd. lia.
Qed.

Fixpoint check_all_true_nat (lo : Z) (cnt : nat) (t : BTree) : bool :=
  match cnt with
  | O => true
  | S n => bt_get (z_to_pos lo) t && check_all_true_nat (lo + 1) n t
  end.

Lemma check_all_true_nat_sound : forall cnt lo t z,
  check_all_true_nat lo cnt t = true ->
  lo <= z < lo + Z.of_nat cnt ->
  bt_interp t z = true.
Proof.
  induction cnt; intros lo t z Hc Hz; simpl in Hc.
  - lia.
  - rewrite andb_true_iff in Hc. destruct Hc as [Hh Ht].
    destruct (Z.eq_dec z lo).
    + subst z. exact Hh.
    + apply (IHcnt (lo + 1) t z Ht). lia.
Qed.

Fixpoint bt_set_ones_nat (lo : Z) (cnt : nat) (t : BTree) : BTree :=
  match cnt with
  | O => t
  | S n => bt_set (z_to_pos lo) true (bt_set_ones_nat (lo + 1) n t)
  end.

Lemma bt_set_ones_nat_in : forall cnt lo t z,
  lo <= z < lo + Z.of_nat cnt ->
  bt_interp (bt_set_ones_nat lo cnt t) z = true.
Proof.
  induction cnt; intros lo t z Hz; simpl.
  - lia.
  - rewrite bt_interp_set. unfold write_tape.
    destruct (Z.eqb_spec z lo) as [-> | Hneq]; [reflexivity|].
    apply IHcnt. lia.
Qed.

Lemma bt_set_ones_nat_out : forall cnt lo t z,
  z < lo \/ z >= lo + Z.of_nat cnt ->
  bt_interp (bt_set_ones_nat lo cnt t) z = bt_interp t z.
Proof.
  induction cnt; intros lo t z Hz; simpl.
  - reflexivity.
  - rewrite bt_interp_set. unfold write_tape.
    destruct (Z.eqb_spec z lo) as [-> | Hneq]; [lia|].
    apply IHcnt. lia.
Qed.

(** * 5. Concrete Prefix Verification (t = 0 .. 3720) *)

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

Lemma fc0_eq_c0 : cfg_eq (fc_to_cfg fc0) c0.
Proof.
  constructor; simpl; try reflexivity.
  intro z. unfold bt_interp, empty_tape. apply bt_get_empty.
Qed.

Definition fc_r2 : FastConfig := N.iter 3720 fast_step fc0.

Lemma prefix_3720_no_coll :
  snd (N.iter 3720 (fast_step_chk_range (-2) 147) (fc0, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma prefix_3720_state :
  fc_r2.(fpos1) = 114 /\
  fc_r2.(fpos2) = 144 /\
  fc_r2.(fstate1) = StA /\
  fc_r2.(fstate2) = StB /\
  bt_bounded_aux (-1) 146 (fun q => q) fc_r2.(ftape) = true /\
  check_all_true_nat (-1) 142 fc_r2.(ftape) = true /\
  bt_interp fc_r2.(ftape) 141 = false /\
  bt_interp fc_r2.(ftape) 142 = false /\
  bt_interp fc_r2.(ftape) 143 = true /\
  bt_interp fc_r2.(ftape) 144 = false /\
  bt_interp fc_r2.(ftape) 145 = true /\
  bt_interp fc_r2.(ftape) 146 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma prefix_3720_summary :
  let c := run_N ag1 ag2 3720 c0 in
  c.(pos1) = 114 /\
  c.(pos2) = 144 /\
  c.(state1) = StA /\
  c.(state2) = StB /\
  (forall z, -1 <= z <= 140 -> c.(tape) z = true) /\
  c.(tape) 141 = false /\ c.(tape) 142 = false /\
  c.(tape) 143 = true /\ c.(tape) 144 = false /\
  c.(tape) 145 = true /\ c.(tape) 146 = true /\
  (forall z, z < -1 \/ z > 146 -> c.(tape) z = false) /\
  (forall t, (t < 3720)%N -> (run_N ag1 ag2 t c0).(pos1) <> (run_N ag1 ag2 t c0).(pos2)).
Proof.
  pose proof (run_N_proper ag1 ag2 3720 (fc_to_cfg fc0) c0 fc0_eq_c0) as Heq.
  pose proof (fast_run_sound 3720 fc0) as Hfs.
  pose proof (cfg_eq_trans _ _ _ (ltac:(exact Hfs)) (ltac:(exact Heq))) as Hcomb.
  fold fc_r2 in Hcomb.
  destruct Hcomb as [Hp1 Hp2 Hs1 Hs2 Htp].
  rewrite fc_to_cfg_pos1 in Hp1. rewrite fc_to_cfg_pos2 in Hp2.
  rewrite fc_to_cfg_state1 in Hs1. rewrite fc_to_cfg_state2 in Hs2.
  destruct prefix_3720_state as [R1 [R2 [R3 [R4 [Rbd [Rtr [R141 [R142 [R143 [R144 [R145 R146]]]]]]]]]]].
  repeat split; try lia; try congruence.
  - intros z Hz. rewrite <- Htp. apply (check_all_true_nat_sound 142 (-1) fc_r2.(ftape) z Rtr). lia.
  - rewrite <- Htp. exact R141.
  - rewrite <- Htp. exact R142.
  - rewrite <- Htp. exact R143.
  - rewrite <- Htp. exact R144.
  - rewrite <- Htp. exact R145.
  - rewrite <- Htp. exact R146.
  - intros z Hz. rewrite <- Htp. apply (bt_bounded_sound (-1) 146 fc_r2.(ftape) z Rbd Hz).
  - intros t Ht.
    pose proof (fast_step_chk_range_sound 3720 (-2) 147 fc0 true prefix_3720_no_coll) as [_ Hnc].
    destruct (Hnc t Ht) as [Hneq _].
    pose proof (run_N_proper ag1 ag2 t (fc_to_cfg fc0) c0 fc0_eq_c0) as [Tp1 Tp2 _ _ _].
    pose proof (fast_run_sound t fc0) as [Fp1 Fp2 _ _ _].
    rewrite fc_to_cfg_pos1 in Fp1. rewrite fc_to_cfg_pos2 in Fp2.
    lia.
Qed.

(** * 6. Decoupled Agent Semantics & Agent 1 Counter Rules *)

Definition ag1_step1 (p1 : Z) (s1 : State) (tp : Tape) : Z * State * Tape :=
  let tr := ag1 s1 (tp p1) in
  (move_pos p1 tr.(move_dir), tr.(next_state), write_tape tp p1 tr.(write_sym)).

Definition ag1_run1 (n : nat) (p1 : Z) (s1 : State) (tp : Tape) : Z * State * Tape :=
  Nat.iter n (fun '(p, s, t) => ag1_step1 p s t) (p1, s1, tp).

Definition ag2_step1 (p2 : Z) (s2 : State) (tp : Tape) : Z * State * Tape :=
  let tr := ag2 s2 (tp p2) in
  (move_pos p2 tr.(move_dir), tr.(next_state), write_tape tp p2 tr.(write_sym)).

Definition ag2_run1 (n : nat) (p2 : Z) (s2 : State) (tp : Tape) : Z * State * Tape :=
  Nat.iter n (fun '(p, s, t) => ag2_step1 p s t) (p2, s2, tp).

Lemma ag1_run1_add : forall a b p s tp,
  ag1_run1 (a + b) p s tp =
  let '(p', s', tp') := ag1_run1 b p s tp in ag1_run1 a p' s' tp'.
Proof.
  intros a b p s tp. unfold ag1_run1. rewrite Nat.add_comm.
  induction b; simpl; [reflexivity|].
  rewrite Nat.iter_succ_r, IHb.
  destruct (Nat.iter b _ _) as [[p' s'] tp']. reflexivity.
Qed.

Lemma ag2_run1_add : forall a b p s tp,
  ag2_run1 (a + b) p s tp =
  let '(p', s', tp') := ag2_run1 b p s tp in ag2_run1 a p' s' tp'.
Proof.
  intros a b p s tp. unfold ag2_run1. rewrite Nat.add_comm.
  induction b; simpl; [reflexivity|].
  rewrite Nat.iter_succ_r, IHb.
  destruct (Nat.iter b _ _) as [[p' s'] tp']. reflexivity.
Qed.

Lemma ag1_run1_proper : forall n p s tp1 tp2,
  tape_eq tp1 tp2 ->
  let '(p1, s1, t1) := ag1_run1 n p s tp1 in
  let '(p2, s2, t2) := ag1_run1 n p s tp2 in
  p1 = p2 /\ s1 = s2 /\ tape_eq t1 t2.
Proof.
  induction n; intros p s tp1 tp2 Htp.
  - simpl. repeat split; auto.
  - unfold ag1_run1 in *. simpl.
    destruct (Nat.iter n _ (p, s, tp1)) as [[p1 s1] t1] eqn:E1.
    destruct (Nat.iter n _ (p, s, tp2)) as [[p2 s2] t2] eqn:E2.
    specialize (IHn p s tp1 tp2 Htp). rewrite E1, E2 in IHn.
    destruct IHn as [Hp [Hs Ht]]. subst p2 s2.
    unfold ag1_step1. rewrite (Ht p1). repeat split; auto.
    apply write_tape_proper; auto.
Qed.

Lemma ag2_run1_proper : forall n p s tp1 tp2,
  tape_eq tp1 tp2 ->
  let '(p1, s1, t1) := ag2_run1 n p s tp1 in
  let '(p2, s2, t2) := ag2_run1 n p s tp2 in
  p1 = p2 /\ s1 = s2 /\ tape_eq t1 t2.
Proof.
  induction n; intros p s tp1 tp2 Htp.
  - simpl. repeat split; auto.
  - unfold ag2_run1 in *. simpl.
    destruct (Nat.iter n _ (p, s, tp1)) as [[p1 s1] t1] eqn:E1.
    destruct (Nat.iter n _ (p, s, tp2)) as [[p2 s2] t2] eqn:E2.
    specialize (IHn p s tp1 tp2 Htp). rewrite E1, E2 in IHn.
    destruct IHn as [Hp [Hs Ht]]. subst p2 s2.
    unfold ag2_step1. rewrite (Ht p1). repeat split; auto.
    apply write_tape_proper; auto.
Qed.

Lemma decouple_run : forall n mid c,
  (forall k, (k < n)%nat ->
    let '(p1, _, _) := ag1_run1 k c.(pos1) c.(state1) c.(tape) in p1 < mid) ->
  (forall k, (k < n)%nat ->
    let '(p2, _, _) := ag2_run1 k c.(pos2) c.(state2) c.(tape) in mid <= p2) ->
  let '(p1', s1', t1') := ag1_run1 n c.(pos1) c.(state1) c.(tape) in
  let '(p2', s2', t2') := ag2_run1 n c.(pos2) c.(state2) c.(tape) in
  let r := run_N ag1 ag2 (N.of_nat n) c in
  r.(pos1) = p1' /\ r.(state1) = s1' /\
  r.(pos2) = p2' /\ r.(state2) = s2' /\
  (forall z, z < mid -> r.(tape) z = t1' z) /\
  (forall z, mid <= z -> r.(tape) z = t2' z) /\
  (forall k, (k < N.of_nat n)%N ->
    (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)).
Proof.
  induction n; intros mid c H1 H2.
  - simpl. rewrite run_N_0. repeat split; auto. intros k Hk; lia.
  - assert (H1' : forall k, (k < n)%nat ->
      let '(p1, _, _) := ag1_run1 k c.(pos1) c.(state1) c.(tape) in p1 < mid)
      by (intros k Hk; apply H1; lia).
    assert (H2' : forall k, (k < n)%nat ->
      let '(p2, _, _) := ag2_run1 k c.(pos2) c.(state2) c.(tape) in mid <= p2)
      by (intros k Hk; apply H2; lia).
    specialize (IHn mid c H1' H2').
    unfold ag1_run1, ag2_run1 in *.
    destruct (Nat.iter n _ (c.(pos1), c.(state1), c.(tape))) as [[p1 s1] t1] eqn:E1.
    destruct (Nat.iter n _ (c.(pos2), c.(state2), c.(tape))) as [[p2 s2] t2] eqn:E2.
    destruct IHn as [Ip1 [Is1 [Ip2 [Is2 [It1 [It2 Iprev]]]]]].
    assert (Hp1_lt : p1 < mid) by (specialize (H1 n ltac:(lia)); rewrite E1 in H1; exact H1).
    assert (Hp2_ge : mid <= p2) by (specialize (H2 n ltac:(lia)); rewrite E2 in H2; exact H2).
    replace (N.of_nat (S n)) with (N.succ (N.of_nat n)) by lia.
    rewrite run_N_succ.
    set (rn := run_N ag1 ag2 (N.of_nat n) c).
    assert (Hr1 : rn.(tape) rn.(pos1) = t1 p1) by (rewrite Ip1; apply It1; lia).
    assert (Hr2 : rn.(tape) rn.(pos2) = t2 p2) by (rewrite Ip2; apply It2; lia).
    simpl. rewrite E1, E2. unfold ag1_step1, ag2_step1, step.
    rewrite Ip1, Ip2, Is1, Is2, Hr1, Hr2.
    repeat split; simpl; auto.
    + intros z Hz. unfold write_tape.
      destruct (Z.eqb_spec z p1); [reflexivity|].
      destruct (Z.eqb_spec z p2); [lia | apply It1; lia].
    + intros z Hz. unfold write_tape.
      destruct (Z.eqb_spec z p1); [lia|].
      destruct (Z.eqb_spec z p2); [reflexivity | apply It2; lia].
    + intros k Hk.
      destruct (N.lt_ge_cases k (N.of_nat n)) as [Hlt | Hge].
      * apply Iprev; exact Hlt.
      * replace k with (N.of_nat n) by lia. fold rn. lia.
Qed.

Definition T_sweep1 (L : nat) : nat := 9 * 2 ^ L - 8.

Lemma T_sweep1_succ : forall L, (1 <= L)%nat ->
  T_sweep1 (S L) = (2 * T_sweep1 L + 8)%nat.
Proof.
  intros L HL. unfold T_sweep1.
  assert (Hpow : (2 ^ S L = 2 * 2 ^ L)%nat) by (simpl; lia).
  assert (Hge : (2 <= 2 ^ L)%nat) by (clear HL; induction L; simpl; lia).
  lia.
Qed.

Lemma sweep_D_1 : forall L x tp,
  (forall z, x - Z.of_nat L <= z <= x -> tp z = true) ->
  tp (x + 1) = false ->
  let '(p', s', tp') := ag1_run1 (T_sweep1 (S L)) x StD tp in
  p' = x + 2 /\ s' = StA /\
  (forall z, x - Z.of_nat L <= z <= x + 1 -> tp' z = true) /\
  (forall z, z < x - Z.of_nat L \/ z > x + 1 -> tp' z = tp z) /\
  (forall k, (k < T_sweep1 (S L))%nat ->
    let '(pk, _, _) := ag1_run1 k x StD tp in
    x - Z.of_nat L <= pk <= x + 1).
Proof.
  induction L as [| L IH]; intros x tp Hones H0.
  - change (T_sweep1 1) with 10%nat.
    assert (Hx : tp x = true) by (apply Hones; lia).
    assert (H10 :
      let '(p', s', tp') := ag1_run1 10 x StD tp in
      p' = x + 2 /\ s' = StA /\
      tp' x = true /\ tp' (x + 1) = true /\
      (forall z, z < x \/ z > x + 1 -> tp' z = tp z) /\
      (forall k, (k < 10)%nat ->
        let '(pk, _, _) := ag1_run1 k x StD tp in x <= pk <= x + 1)).
    { unfold ag1_run1. simpl. unfold ag1_step1.
      rewrite Hx. simpl.
      rewrite write_tape_other by lia. rewrite H0. simpl.
      rewrite !write_tape_same.
      rewrite write_tape_other by lia. rewrite write_tape_same. simpl.
      rewrite !write_tape_same.
      rewrite write_tape_other by lia. rewrite !write_tape_same. simpl.
      rewrite write_tape_other by lia. rewrite write_tape_other by lia. rewrite write_tape_same. simpl.
      rewrite !write_tape_same.
      rewrite write_tape_other by lia. rewrite !write_tape_same. simpl.
      rewrite !write_tape_same, !write_tape_same, !write_tape_same.
      repeat split; try lia; try reflexivity.
      - unfold write_tape. rewrite Z.eqb_refl. reflexivity.
      - unfold write_tape. destruct (Z.eqb_spec (x+1) x); [lia|]. rewrite Z.eqb_refl. reflexivity.
      - intros z Hz. unfold write_tape.
        repeat (destruct (Z.eqb_spec z _); [lia|]). reflexivity.
      - intros k Hk.
        destruct k as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; try lia; simpl; lia. }
    destruct (ag1_run1 10 x StD tp) as [[p' s'] tp'].
    destruct H10 as [Hp [Hs [Htx [Htx1 [Hout Hbd]]]]].
    repeat split; auto; try lia.
    + intros z Hz. assert (z = x \/ z = x + 1) as [->| ->] by lia; auto.
    + intros k Hk. specialize (Hbd k Hk).
      destruct (ag1_run1 k x StD tp) as [[pk ?] ?]. lia.
  - rewrite T_sweep1_succ by lia.
    set (T1 := T_sweep1 (S L)).
    assert (Hx : tp x = true) by (apply Hones; lia).
    assert (H5 :
      let '(p5, s5, tp5) := ag1_run1 5 x StD tp in
      p5 = x - 1 /\ s5 = StD /\
      (forall z, x - 1 - Z.of_nat L <= z <= x - 1 -> tp5 z = true) /\
      tp5 x = false /\ tp5 (x + 1) = false /\
      (forall z, z < x - Z.of_nat (S L) \/ z > x + 1 -> tp5 z = tp z) /\
      (forall k, (k < 5)%nat ->
        let '(pk, _, _) := ag1_run1 k x StD tp in x - Z.of_nat (S L) <= pk <= x + 1)).
    { unfold ag1_run1. simpl. unfold ag1_step1.
      rewrite Hx. simpl.
      rewrite write_tape_other by lia. rewrite H0. simpl.
      rewrite !write_tape_same.
      rewrite write_tape_other by lia. rewrite write_tape_same. simpl.
      rewrite !write_tape_same.
      rewrite write_tape_other by lia. rewrite !write_tape_same. simpl.
      repeat split; try lia; try reflexivity.
      - intros z Hz. unfold write_tape.
        destruct (Z.eqb_spec z (x+1)); [lia|].
        destruct (Z.eqb_spec z x); [lia|].
        apply Hones; lia.
      - unfold write_tape. destruct (Z.eqb_spec x (x+1)); [lia|]. rewrite Z.eqb_refl. reflexivity.
      - unfold write_tape. rewrite Z.eqb_refl. reflexivity.
      - intros z Hz. unfold write_tape.
        repeat (destruct (Z.eqb_spec z _); [lia|]). reflexivity.
      - intros k Hk. destruct k as [|[|[|[|[|]]]]]; try lia; simpl; lia. }
    destruct (ag1_run1 5 x StD tp) as [[p5 s5] tp5] eqn:E5.
    destruct H5 as [Hp5 [Hs5 [H5ones [H5x [H5x1 [H5out H5bd]]]]]].
    subst p5 s5.
    specialize (IH (x - 1) tp5 H5ones H5x) as IH1.
    destruct (ag1_run1 T1 (x - 1) StD tp5) as [[p2 s2] tp2] eqn:E2.
    destruct IH1 as [Hp2 [Hs2 [H2ones [H2out H2bd]]]].
    subst p2 s2.
    assert (H2x1 : tp2 (x + 1) = false) by (rewrite H2out by lia; exact H5x1).
    assert (H2x : tp2 x = true) by (apply H2ones; lia).
    assert (H2step :
      let '(p3, s3, tp3) := ag1_run1 2 (x + 1) StA tp2 in
      p3 = x - 1 /\ s3 = StD /\
      (forall z, x - 1 - Z.of_nat L <= z <= x - 1 -> tp3 z = true) /\
      tp3 x = false /\ tp3 (x + 1) = true /\
      (forall z, z < x - Z.of_nat (S L) \/ z > x + 1 -> tp3 z = tp2 z) /\
      (forall k, (k < 2)%nat ->
        let '(pk, _, _) := ag1_run1 k (x + 1) StA tp2 in x - Z.of_nat (S L) <= pk <= x + 1)).
    { unfold ag1_run1. simpl. unfold ag1_step1.
      rewrite H2x1. simpl.
      rewrite write_tape_other by lia. rewrite H2x. simpl.
      repeat split; try lia; try reflexivity.
      - intros z Hz. unfold write_tape.
        destruct (Z.eqb_spec z x); [lia|].
        destruct (Z.eqb_spec z (x+1)); [lia|].
        apply H2ones; lia.
      - unfold write_tape. rewrite Z.eqb_refl. reflexivity.
      - unfold write_tape. destruct (Z.eqb_spec (x+1) x); [lia|]. rewrite Z.eqb_refl. reflexivity.
      - intros z Hz. unfold write_tape.
        repeat (destruct (Z.eqb_spec z _); [lia|]). reflexivity.
      - intros k Hk. destruct k as [|[|]]; try lia; simpl; lia. }
    destruct (ag1_run1 2 (x + 1) StA tp2) as [[p3 s3] tp3] eqn:E3.
    destruct H2step as [Hp3 [Hs3 [H3ones [H3x [H3x1 [H3out H3bd]]]]]].
    subst p3 s3.
    specialize (IH (x - 1) tp3 H3ones H3x) as IH2.
    destruct (ag1_run1 T1 (x - 1) StD tp3) as [[p4 s4] tp4] eqn:E4.
    destruct IH2 as [Hp4 [Hs4 [H4ones [H4out H4bd]]]].
    subst p4 s4.
    assert (H4x1 : tp4 (x + 1) = true) by (rewrite H4out by lia; exact H3x1).
    assert (H1step :
      let '(p6, s6, tp6) := ag1_run1 1 (x + 1) StA tp4 in
      p6 = x + 2 /\ s6 = StA /\
      (forall z, x - Z.of_nat (S L) <= z <= x + 1 -> tp6 z = true) /\
      (forall z, z < x - Z.of_nat (S L) \/ z > x + 1 -> tp6 z = tp4 z)).
    { unfold ag1_run1. simpl. unfold ag1_step1. rewrite H4x1. simpl.
      repeat split; try lia; try reflexivity.
      - intros z Hz. unfold write_tape. destruct (Z.eqb_spec z (x + 1)); auto.
        apply H4ones; lia.
      - intros z Hz. unfold write_tape. destruct (Z.eqb_spec z (x + 1)); [lia|]. reflexivity. }
    replace (2 * T1 + 8)%nat with (1 + (T1 + (2 + (T1 + 5))))%nat by lia.
    rewrite !ag1_run1_add, E5, E2, E3, E4.
    destruct (ag1_run1 1 (x + 1) StA tp4) as [[p6 s6] tp6] eqn:E6.
    destruct H1step as [Hp6 [Hs6 [H6ones H6out]]].
    repeat split; auto.
    + intros z Hz. rewrite H6out by lia. rewrite H4out by lia.
      rewrite H3out by lia. rewrite H2out by lia. apply H5out; lia.
    + intros k Hk.
      destruct (lt_dec k 5) as [Hk5|Hge5]; [apply H5bd; exact Hk5|].
      replace k with ((k - 5) + 5)%nat by lia. rewrite ag1_run1_add, E5.
      destruct (lt_dec (k - 5) T1) as [HkT1|HgeT1].
      { specialize (H2bd (k - 5)%nat HkT1). destruct (ag1_run1 _ _ _ _); lia. }
      replace (k - 5)%nat with ((k - 5 - T1) + T1)%nat by lia. rewrite ag1_run1_add, E2.
      destruct (lt_dec (k - 5 - T1) 2) as [Hk2|Hge2].
      { specialize (H3bd (k - 5 - T1)%nat Hk2). destruct (ag1_run1 _ _ _ _); lia. }
      replace (k - 5 - T1)%nat with ((k - 7 - T1) + 2)%nat by lia. rewrite ag1_run1_add, E3.
      destruct (lt_dec (k - 7 - T1) T1) as [HkT2|HgeT2].
      { specialize (H4bd (k - 7 - T1)%nat HkT2). destruct (ag1_run1 _ _ _ _); lia. }
      replace (k - 7 - T1)%nat with (0 + T1)%nat by lia. rewrite ag1_run1_add, E4. simpl. lia.
Qed.

Definition T_sweep_z (L z : nat) : nat := 9 * 2 ^ (L + z - 1) - 5 * z - 3.

Lemma T_sweep_z_1 : forall L, (1 <= L)%nat -> T_sweep_z L 1 = T_sweep1 L.
Proof.
  intros L HL. unfold T_sweep_z, T_sweep1.
  replace (L + 1 - 1)%nat with L by lia. lia.
Qed.

Lemma T_sweep_z_succ : forall L z, (1 <= L)%nat -> (1 <= z)%nat ->
  T_sweep_z L (S z) = (T_sweep_z L z + 2 + T_sweep1 (L + z - 1) + 1)%nat.
Proof.
  intros L z HL Hz. unfold T_sweep_z, T_sweep1.
  replace (L + S z - 1)%nat with (S (L + z - 1)) by lia.
  assert (Hpow : (2 ^ S (L + z - 1) = 2 * 2 ^ (L + z - 1))%nat) by (simpl; lia).
  assert (H1 : (z <= 2 ^ (L + z - 1))%nat).
  { assert (Hlz : (z - 1 <= L + z - 1)%nat) by lia.
    clear -Hz Hlz. induction (L + z - 1)%nat; simpl; lia. }
  lia.
Qed.

Lemma sweep_D_z : forall z L x tp,
  (1 <= z)%nat ->
  (forall u, x - Z.of_nat L <= u <= x -> tp u = true) ->
  (forall u, x + 1 <= u <= x + Z.of_nat z -> tp u = false) ->
  let '(p', s', tp') := ag1_run1 (T_sweep_z (S L) z) x StD tp in
  p' = x + Z.of_nat z + 1 /\ s' = StA /\
  (forall u, x - Z.of_nat L <= u <= x + Z.of_nat z -> tp' u = true) /\
  (forall u, u < x - Z.of_nat L \/ u > x + Z.of_nat z -> tp' u = tp u) /\
  (forall k, (k < T_sweep_z (S L) z)%nat ->
    let '(pk, _, _) := ag1_run1 k x StD tp in
    x - Z.of_nat L <= pk <= x + Z.of_nat z).
Proof.
  induction z as [| z IH]; intros L x tp Hz Hones Hzeros; [lia|].
  destruct z as [| z'].
  - rewrite T_sweep_z_1 by lia.
    assert (Hx1 : tp (x + 1) = false) by (apply Hzeros; lia).
    pose proof (sweep_D_1 L x tp Hones Hx1) as Hs1.
    destruct (ag1_run1 (T_sweep1 (S L)) x StD tp) as [[p' s'] tp'].
    destruct Hs1 as [Hp [Hs [Ho [Hout Hbd]]]]. repeat split; try lia; auto.
  - set (zz := S z').
    rewrite T_sweep_z_succ by lia.
    replace (S L + zz - 1)%nat with (L + zz)%nat by lia.
    assert (Hzz : (1 <= zz)%nat) by lia.
    assert (Hzeros_sub : forall u, x + 1 <= u <= x + Z.of_nat zz -> tp u = false)
      by (intros u Hu; apply Hzeros; lia).
    specialize (IH L x tp Hzz Hones Hzeros_sub).
    destruct (ag1_run1 (T_sweep_z (S L) zz) x StD tp) as [[p1 s1] tp1] eqn:E1.
    destruct IH as [Hp1 [Hs1 [H1ones [H1out H1bd]]]]. subst p1 s1.
    assert (Hx_next : tp1 (x + Z.of_nat zz + 1) = false)
      by (rewrite H1out by lia; apply Hzeros; lia).
    assert (Hx_prev : tp1 (x + Z.of_nat zz) = true) by (apply H1ones; lia).
    assert (H2step :
      let '(p2, s2, tp2) := ag1_run1 2 (x + Z.of_nat zz + 1) StA tp1 in
      p2 = x + Z.of_nat zz - 1 /\ s2 = StD /\
      (forall u, x - Z.of_nat L <= u <= x + Z.of_nat zz - 1 -> tp2 u = true) /\
      tp2 (x + Z.of_nat zz) = false /\ tp2 (x + Z.of_nat zz + 1) = true /\
      (forall u, u < x - Z.of_nat L \/ u > x + Z.of_nat (S zz) -> tp2 u = tp1 u) /\
      (forall k, (k < 2)%nat ->
        let '(pk, _, _) := ag1_run1 k (x + Z.of_nat zz + 1) StA tp1 in
        x - Z.of_nat L <= pk <= x + Z.of_nat (S zz))).
    { unfold ag1_run1. simpl. unfold ag1_step1.
      rewrite Hx_next. simpl. rewrite write_tape_other by lia. rewrite Hx_prev. simpl.
      repeat split; try lia; try reflexivity.
      - intros u Hu. unfold write_tape.
        destruct (Z.eqb_spec u (x + Z.of_nat zz)); [lia|].
        destruct (Z.eqb_spec u (x + Z.of_nat zz + 1)); [lia|].
        apply H1ones; lia.
      - unfold write_tape. rewrite Z.eqb_refl. reflexivity.
      - unfold write_tape. destruct (Z.eqb_spec (x + Z.of_nat zz + 1) (x + Z.of_nat zz)); [lia|].
        rewrite Z.eqb_refl. reflexivity.
      - intros u Hu. unfold write_tape.
        repeat (destruct (Z.eqb_spec u _); [lia|]). reflexivity.
      - intros k Hk. destruct k as [|[|]]; try lia; simpl; lia. }
    destruct (ag1_run1 2 (x + Z.of_nat zz + 1) StA tp1) as [[p2 s2] tp2] eqn:E2.
    destruct H2step as [Hp2 [Hs2 [H2ones [H2z0 [H2z1 [H2out H2bd]]]]]]. subst p2 s2.
    assert (Hones_shift : forall u,
      (x + Z.of_nat zz - 1) - Z.of_nat (L + zz - 1) <= u <= x + Z.of_nat zz - 1 ->
      tp2 u = true) by (intros u Hu; apply H2ones; lia).
    pose proof (sweep_D_1 (L + zz - 1)%nat (x + Z.of_nat zz - 1) tp2 Hones_shift H2z0) as Hs_tail.
    replace (S (L + zz - 1))%nat with (L + zz)%nat in Hs_tail by lia.
    destruct (ag1_run1 (T_sweep1 (L + zz)) (x + Z.of_nat zz - 1) StD tp2) as [[p3 s3] tp3] eqn:E3.
    destruct Hs_tail as [Hp3 [Hs3 [H3ones [H3out H3bd]]]]. subst p3 s3.
    assert (H3z1 : tp3 (x + Z.of_nat zz + 1) = true) by (rewrite H3out by lia; exact H2z1).
    replace (T_sweep_z (S L) zz + 2 + T_sweep1 (L + zz) + 1)%nat
      with (1 + (T_sweep1 (L + zz) + (2 + T_sweep_z (S L) zz)))%nat by lia.
    rewrite !ag1_run1_add, E1, E2, E3.
    unfold ag1_run1 at 1. simpl. unfold ag1_step1.
    replace (x + Z.of_nat zz - 1 + 2) with (x + Z.of_nat zz + 1) by lia.
    rewrite H3z1. simpl.
    repeat split; try lia; try reflexivity.
    + intros u Hu. unfold write_tape.
      destruct (Z.eqb_spec u (x + Z.of_nat zz + 1)); [reflexivity|].
      apply H3ones; lia.
    + intros u Hu. unfold write_tape.
      destruct (Z.eqb_spec u (x + Z.of_nat zz + 1)); [lia|].
      rewrite H3out by lia. rewrite H2out by lia. apply H1out; lia.
    + intros k Hk.
      destruct (lt_dec k (T_sweep_z (S L) zz)) as [Hk1|Hge1].
      { specialize (H1bd k Hk1). destruct (ag1_run1 _ _ _ _); lia. }
      replace k with ((k - T_sweep_z (S L) zz) + T_sweep_z (S L) zz)%nat by lia.
      rewrite ag1_run1_add, E1.
      destruct (lt_dec (k - T_sweep_z (S L) zz) 2) as [Hk2|Hge2].
      { specialize (H2bd _ Hk2). destruct (ag1_run1 _ _ _ _); lia. }
      replace (k - T_sweep_z (S L) zz)%nat with ((k - T_sweep_z (S L) zz - 2) + 2)%nat by lia.
      rewrite ag1_run1_add, E2.
      destruct (lt_dec (k - T_sweep_z (S L) zz - 2) (T_sweep1 (L + zz))) as [Hk3|Hge3].
      { specialize (H3bd _ Hk3). destruct (ag1_run1 _ _ _ _); lia. }
      replace (k - T_sweep_z (S L) zz - 2)%nat with (0 + T_sweep1 (L + zz))%nat by lia.
      rewrite ag1_run1_add, E3. simpl. lia.
Qed.

Lemma walk_A_ones : forall k x tp,
  (forall u, x <= u < x + Z.of_nat k -> tp u = true) ->
  let '(p', s', tp') := ag1_run1 k x StA tp in
  p' = x + Z.of_nat k /\ s' = StA /\ tape_eq tp' tp /\
  (forall j, (j < k)%nat ->
    let '(pj, _, _) := ag1_run1 j x StA tp in x <= pj < x + Z.of_nat k).
Proof.
  induction k; intros x tp Hones.
  - simpl. repeat split; try lia; [intro; reflexivity | intros j Hj; lia].
  - assert (Hx : tp x = true) by (apply Hones; lia).
    assert (Hones' : forall u, x + 1 <= u < x + 1 + Z.of_nat k -> tp u = true)
      by (intros u Hu; apply Hones; lia).
    specialize (IHk (x + 1) tp Hones').
    assert (H1 : ag1_run1 1 x StA tp = (x + 1, StA, write_tape tp x true))
      by (unfold ag1_run1; simpl; unfold ag1_step1; rewrite Hx; reflexivity).
    assert (Hwt : tape_eq (write_tape tp x true) tp)
      by (intro z; unfold write_tape; destruct (Z.eqb_spec z x); congruence).
    replace (S k) with (k + 1)%nat by lia.
    rewrite ag1_run1_add, H1.
    pose proof (ag1_run1_proper k (x + 1) StA (write_tape tp x true) tp Hwt) as Hprop.
    destruct (ag1_run1 k (x + 1) StA (write_tape tp x true)) as [[p1 s1] tp1] eqn:E1.
    destruct (ag1_run1 k (x + 1) StA tp) as [[p2 s2] tp2] eqn:E2.
    destruct Hprop as [Hp [Hs Ht]]. subst p2 s2.
    destruct IHk as [Ip [Is [Itp Ibd]]].
    repeat split; try lia; auto.
    + intro z. rewrite Ht. apply Itp.
    + intros j Hj. destruct j; [simpl; lia|].
      replace (S j) with (j + 1)%nat by lia. rewrite ag1_run1_add, H1.
      pose proof (ag1_run1_proper j (x + 1) StA (write_tape tp x true) tp Hwt) as Hpj.
      destruct (ag1_run1 j (x + 1) StA (write_tape tp x true)) as [[pa ?] ?].
      specialize (Ibd j ltac:(lia)).
      destruct (ag1_run1 j (x + 1) StA tp) as [[pb ?] ?].
      destruct Hpj as [Hpeq _]. lia.
Qed.

(** * 7. Agent 2 Glider Rules via Fast BTree Verification *)

Definition fast_ag2_step (st : Z * State * BTree) : Z * State * BTree :=
  let '(p, s, t) := st in
  let r := bt_get (z_to_pos p) t in
  let tr := ag2 s r in
  (move_pos p tr.(move_dir), tr.(next_state), bt_set (z_to_pos p) tr.(write_sym) t).

Lemma fast_ag2_step_sound : forall p s t,
  let '(p', s', t') := fast_ag2_step (p, s, t) in
  let '(p0, s0, t0) := ag2_step1 p s (bt_interp t) in
  p' = p0 /\ s' = s0 /\ tape_eq (bt_interp t') t0.
Proof.
  intros p s t. unfold fast_ag2_step, ag2_step1, bt_interp. simpl.
  repeat split; auto. apply bt_interp_set.
Qed.

Lemma fast_ag2_run_sound : forall n p s t,
  let '(p', s', t') := Nat.iter n fast_ag2_step (p, s, t) in
  let '(p0, s0, t0) := ag2_run1 n p s (bt_interp t) in
  p' = p0 /\ s' = s0 /\ tape_eq (bt_interp t') t0.
Proof.
  induction n; intros p s t.
  - simpl. repeat split; auto. intro; reflexivity.
  - simpl. unfold ag2_run1 in *. simpl.
    specialize (IHn p s t).
    destruct (Nat.iter n fast_ag2_step (p, s, t)) as [[p' s'] t'] eqn:E1.
    destruct (Nat.iter n _ (p, s, bt_interp t)) as [[p0 s0] t0] eqn:E2.
    destruct IHn as [Hp [Hs Ht]]. subst p0 s0.
    pose proof (fast_ag2_step_sound p' s' t') as Hst.
    destruct (fast_ag2_step (p', s', t')) as [[p1 s1] t1].
    unfold ag2_step1 in *. rewrite (Ht p') in *.
    destruct Hst as [Hp1 [Hs1 Ht1]]. repeat split; auto.
    intro z. rewrite Ht1. apply write_tape_proper; auto.
Qed.

Definition has_glider (p2 : Z) (tp : Tape) : Prop :=
  tp (p2 - 3) = false /\ tp (p2 - 2) = false /\
  tp (p2 - 1) = true  /\ tp p2       = false /\
  tp (p2 + 1) = true  /\ tp (p2 + 2) = true.

Definition gl_bt0 : BTree :=
  bt_set (z_to_pos 2) true (
    bt_set (z_to_pos 1) true (
      bt_set (z_to_pos (-1)) true BEmpty)).

Lemma gl_bt0_props :
  bt_bounded_aux (-3) 2 (fun q => q) gl_bt0 = true /\
  bt_interp gl_bt0 (-3) = false /\ bt_interp gl_bt0 (-2) = false /\
  bt_interp gl_bt0 (-1) = true  /\ bt_interp gl_bt0 0 = false /\
  bt_interp gl_bt0 1 = true     /\ bt_interp gl_bt0 2 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Fixpoint fast_ag2_chk (lo hi : Z) (n : nat) (st : Z * State * BTree) : (Z * State * BTree) * bool :=
  match n with
  | O => (st, true)
  | S n' =>
      let '(st', ok) := fast_ag2_chk lo hi n' st in
      let '(p, _, _) := st' in
      (fast_ag2_step st', ok && (lo <=? p) && (p <=? hi))
  end.

Lemma fast_ag2_chk_fst : forall lo hi n st,
  fst (fast_ag2_chk lo hi n st) = Nat.iter n fast_ag2_step st.
Proof.
  intros lo hi n st. induction n; simpl; [reflexivity|].
  destruct (fast_ag2_chk lo hi n st) as [st' ok'] eqn:E.
  simpl in *. rewrite IHn. reflexivity.
Qed.

Lemma fast_ag2_chk_sound : forall lo hi n p s t,
  snd (fast_ag2_chk lo hi n (p, s, t)) = true ->
  forall k, (k < n)%nat ->
    let '(pk, _, _) := ag2_run1 k p s (bt_interp t) in lo <= pk <= hi.
Proof.
  intros lo hi n p s t Hsnd k Hk.
  induction n; [lia|].
  simpl in Hsnd.
  destruct (fast_ag2_chk lo hi n (p, s, t)) as [[[pn sn] tn] ok'] eqn:E.
  simpl in Hsnd. rewrite !andb_true_iff in Hsnd.
  destruct Hsnd as [[Hok' Hlo] Hhi].
  destruct (lt_dec k n) as [Hlt|Hge].
  - apply IHn; auto.
  - assert (k = n) by lia. subst k.
    pose proof (fast_ag2_chk_fst lo hi n (p, s, t)) as Hfst.
    rewrite E in Hfst. simpl in Hfst.
    pose proof (fast_ag2_run_sound n p s t) as Hrun.
    rewrite <- Hfst in Hrun.
    destruct (ag2_run1 n p s (bt_interp t)) as [[pk ?] ?].
    destruct Hrun as [Hpk _]. rewrite <- Hpk.
    rewrite !Z.leb_le in Hlo, Hhi. lia.
Qed.

Lemma gl_27_check :
  let '(p', s', t') := Nat.iter 27 fast_ag2_step (0, StB, gl_bt0) in
  p' = 1 /\ s' = StB /\
  snd (fast_ag2_chk (-3) 3 27 (0, StB, gl_bt0)) = true /\
  bt_bounded_aux (-3) 3 (fun q => q) t' = true /\
  bt_interp t' (-3) = true /\
  bt_interp t' (-2) = false /\ bt_interp t' (-1) = false /\
  bt_interp t' 0 = true     /\ bt_interp t' 1 = false /\
  bt_interp t' 2 = true     /\ bt_interp t' 3 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma ag2_run1_agree_range : forall lo hi n p s tp1 tp2,
  (forall z, lo <= z <= hi -> tp1 z = tp2 z) ->
  (forall k, (k < n)%nat ->
    let '(pk, _, _) := ag2_run1 k p s tp1 in lo <= pk <= hi) ->
  let '(p1, s1, t1) := ag2_run1 n p s tp1 in
  let '(p2, s2, t2) := ag2_run1 n p s tp2 in
  p1 = p2 /\ s1 = s2 /\
  (forall z, lo <= z <= hi -> t1 z = t2 z) /\
  (forall z, z < lo \/ z > hi -> t2 z = tp2 z) /\
  (forall k, (k < n)%nat ->
    let '(pk1, _, _) := ag2_run1 k p s tp1 in
    let '(pk2, _, _) := ag2_run1 k p s tp2 in pk1 = pk2).
Proof.
  intros lo hi n p s tp1 tp2 Htp Hbd. induction n.
  - simpl. repeat split; auto. intros k Hk; lia.
  - assert (Hbd' : forall k, (k < n)%nat ->
      let '(pk, _, _) := ag2_run1 k p s tp1 in lo <= pk <= hi)
      by (intros k Hk; apply Hbd; lia).
    specialize (IHn Hbd').
    unfold ag2_run1 in *. simpl.
    destruct (Nat.iter n _ (p, s, tp1)) as [[p1 s1] t1] eqn:E1.
    destruct (Nat.iter n _ (p, s, tp2)) as [[p2 s2] t2] eqn:E2.
    destruct IHn as [Ip [Is [It [Iout Iprev]]]]. subst p2 s2.
    assert (Hp1 : lo <= p1 <= hi) by (specialize (Hbd n ltac:(lia)); rewrite E1 in Hbd; exact Hbd).
    unfold ag2_step1. rewrite (It p1 Hp1).
    repeat split; auto.
    + intros z Hz. unfold write_tape. destruct (Z.eqb_spec z p1); auto.
    + intros z Hz. unfold write_tape. destruct (Z.eqb_spec z p1); [lia|]. apply Iout; auto.
    + intros k Hk. destruct (lt_dec k n); [apply Iprev; auto|].
      assert (k = n) by lia. subst k. rewrite E1, E2. reflexivity.
Qed.

Lemma ag2_run1_shift : forall d n p s tp,
  let '(p1, s1, t1) := ag2_run1 n (p + d) s (fun z => tp (z - d)) in
  let '(p2, s2, t2) := ag2_run1 n p s tp in
  p1 = p2 + d /\ s1 = s2 /\ (forall z, t1 z = t2 (z - d)).
Proof.
  intros d n p s tp. induction n.
  - simpl. repeat split; auto.
  - unfold ag2_run1 in *. simpl.
    destruct (Nat.iter n _ (p + d, s, fun z => tp (z - d))) as [[p1 s1] t1] eqn:E1.
    destruct (Nat.iter n _ (p, s, tp)) as [[p2 s2] t2] eqn:E2.
    destruct IHn as [Ip [Is It]]. subst p1 s1.
    unfold ag2_step1. replace (p2 + d - d) with p2 by lia. rewrite (It (p2 + d)).
    repeat split; try (destruct move_dir; lia); auto.
    intro z. unfold write_tape.
    destruct (Z.eqb_spec z (p2 + d)); destruct (Z.eqb_spec (z - d) p2); try lia; auto.
Qed.

Lemma glider_27_step : forall p2 tp,
  has_glider p2 tp ->
  (forall z, z >= p2 + 3 -> tp z = false) ->
  let '(p', s', tp') := ag2_run1 27 p2 StB tp in
  p' = p2 + 1 /\ s' = StB /\
  tp' (p2 - 3) = true /\
  has_glider (p2 + 1) tp' /\
  (forall z, z < p2 - 3 \/ z > p2 + 3 -> tp' z = tp z) /\
  (forall k, (k < 27)%nat ->
    let '(pk, _, _) := ag2_run1 k p2 StB tp in p2 - 3 <= pk <= p2 + 3).
Proof.
  intros p2 tp Hgl Hfar.
  (* Shift gl_bt0 by p2 and compare on [p2-3 .. p2+3] *)
  pose proof gl_27_check as Hchk.
  destruct (Nat.iter 27 fast_ag2_step (0, StB, gl_bt0)) as [[p0 s0] t0] eqn:E0.
  destruct Hchk as [Hp0 [Hs0 [Hchk_bd [Ht0_bd [Ht3 [Ht2 [Ht1 [Ht0 [Ht1' [Ht2' Ht3']]]]]]]]]].
  subst p0 s0.
  pose proof (fast_ag2_run_sound 27 0 StB gl_bt0) as Hrun0.
  rewrite E0 in Hrun0.
  destruct (ag2_run1 27 0 StB gl_bt0) as [[p0' s0'] t0'] eqn:E0'.
  destruct Hrun0 as [Hp0' [Hs0' Ht0']]. subst p0' s0'.
  assert (Hbd0 : forall k, (k < 27)%nat ->
    let '(pk, _, _) := ag2_run1 k 0 StB gl_bt0 in -3 <= pk <= 3)
    by (apply (fast_ag2_chk_sound (-3) 3 27 0 StB gl_bt0 Hchk_bd)).
  pose proof (ag2_run1_shift p2 27 0 StB (bt_interp gl_bt0)) as Hsh.
  rewrite E0' in Hsh.
  destruct (ag2_run1 27 (0 + p2) StB (fun z => bt_interp gl_bt0 (z - p2))) as [[ps ss] ts] eqn:Es.
  destruct Hsh as [Hps [Hss Hts]].
  replace (0 + p2) with p2 in Es by lia.
  assert (Hagree : forall z, p2 - 3 <= z <= p2 + 3 -> bt_interp gl_bt0 (z - p2) = tp z).
  { intros z Hz. destruct gl_bt0_props as [_ [G3 [G2 [G1 [G0 [Gp1 Gp2]]]]]].
    destruct Hgl as [H3 [H2 [H1 [H0 [Hp1 Hp2]]]]].
    assert (z - p2 = -3 \/ z - p2 = -2 \/ z - p2 = -1 \/ z - p2 = 0 \/ z - p2 = 1 \/ z - p2 = 2 \/ z - p2 = 3)
      as [->|[->|[->|[->|[->|[->| ->]]]]]] by lia; try congruence.
    - replace (p2 + 3) with (p2 + 3) in *; rewrite Hfar by lia.
      apply (bt_bounded_sound (-3) 2 gl_bt0 3 ltac:(vm_compute; reflexivity)). lia. }
  assert (Hbd_sh : forall k, (k < 27)%nat ->
    let '(pk, _, _) := ag2_run1 k p2 StB (fun z => bt_interp gl_bt0 (z - p2)) in p2 - 3 <= pk <= p2 + 3).
  { intros k Hk.
    pose proof (ag2_run1_shift p2 k 0 StB (bt_interp gl_bt0)) as Hshk.
    replace (0 + p2) with p2 in Hshk by lia.
    specialize (Hbd0 k Hk).
    destruct (ag2_run1 k p2 StB _) as [[pk1 ?] ?].
    destruct (ag2_run1 k 0 StB _) as [[pk0 ?] ?].
    destruct Hshk as [Hpk _]. lia. }
  pose proof (ag2_run1_agree_range (p2 - 3) (p2 + 3) 27 p2 StB (fun z => bt_interp gl_bt0 (z - p2)) tp Hagree Hbd_sh) as Hag.
  rewrite Es in Hag.
  destruct (ag2_run1 27 p2 StB tp) as [[p' s'] tp'] eqn:Ep.
  destruct Hag as [Ip [Is [Itp [Iout Iprev]]]].
  repeat split; try lia; try congruence.
  - rewrite <- Itp by lia. rewrite Hts, <- Ht0'. replace (p2 - 3 - p2) with (-3) by lia. exact Ht3.
  - unfold has_glider.
    replace (p2 + 1 - 3) with (p2 - 2) by lia.
    replace (p2 + 1 - 2) with (p2 - 1) by lia.
    replace (p2 + 1 - 1) with p2 by lia.
    replace (p2 + 1 + 1) with (p2 + 2) by lia.
    replace (p2 + 1 + 2) with (p2 + 3) by lia.
    repeat split; rewrite <- Itp by lia, Hts, <- Ht0';
      [replace (p2 - 2 - p2) with (-2) by lia; exact Ht2
      |replace (p2 - 1 - p2) with (-1) by lia; exact Ht1
      |replace (p2 - p2) with 0 by lia; exact Ht0
      |replace (p2 + 1 - p2) with 1 by lia; exact Ht1'
      |replace (p2 + 2 - p2) with 2 by lia; exact Ht2'
      |replace (p2 + 3 - p2) with 3 by lia; exact Ht3'].
  - intros z Hz. apply Iout; exact Hz.
  - intros k Hk. specialize (Iprev k Hk). specialize (Hbd_sh k Hk).
    destruct (ag2_run1 k p2 StB (fun z => bt_interp gl_bt0 (z - p2))) as [[pk1 ?] ?].
    destruct (ag2_run1 k p2 StB tp) as [[pk2 ?] ?]. lia.
Qed.

Lemma glider_loop_27 : forall q p2 tp,
  has_glider p2 tp ->
  (forall z, z >= p2 + 3 -> tp z = false) ->
  let '(p', s', tp') := ag2_run1 (27 * q) p2 StB tp in
  p' = p2 + Z.of_nat q /\ s' = StB /\
  (forall z, p2 - 3 <= z < p2 + Z.of_nat q - 3 -> tp' z = true) /\
  has_glider (p2 + Z.of_nat q) tp' /\
  (forall z, z < p2 - 3 \/ z > p2 + Z.of_nat q + 2 -> tp' z = tp z) /\
  (forall z, z >= p2 + Z.of_nat q + 3 -> tp' z = false) /\
  (forall k, (k < 27 * q)%nat ->
    let '(pk, _, _) := ag2_run1 k p2 StB tp in p2 - 3 <= pk).
Proof.
  induction q; intros p2 tp Hgl Hfar.
  - simpl. repeat split; try lia; auto.
    + intros z Hz; lia.
    + replace (p2 + 0) with p2 by lia; exact Hgl.
    + intros z Hz. apply Hfar; lia.
    + intros k Hk; lia.
  - replace (27 * S q)%nat with (27 + 27 * q)%nat by lia.
    rewrite ag2_run1_add.
    specialize (IHq p2 tp Hgl Hfar).
    destruct (ag2_run1 (27 * q) p2 StB tp) as [[pq sq] tpq] eqn:Eq.
    destruct IHq as [Ipq [Isq [Iones [Igl [Iout [Ifar Ibd]]]]]]. subst pq sq.
    pose proof (glider_27_step (p2 + Z.of_nat q) tpq Igl Ifar) as Hstep.
    destruct (ag2_run1 27 (p2 + Z.of_nat q) StB tpq) as [[p' s'] tp'] eqn:Ep.
    destruct Hstep as [Hp' [Hs' [Hm3 [Hgl' [Hout' Hbd']]]]].
    repeat split; try lia; auto.
    + intros z Hz. destruct (Z.eqb_spec z (p2 + Z.of_nat q - 3)) as [->|Hneq].
      * exact Hm3.
      * rewrite Hout' by lia. apply Iones. lia.
    + replace (p2 + Z.of_nat (S q)) with (p2 + Z.of_nat q + 1) by lia. exact Hgl'.
    + intros z Hz. rewrite Hout' by lia. apply Iout. lia.
    + intros z Hz. rewrite Hout' by lia. apply Ifar. lia.
    + intros k Hk.
      destruct (lt_dec k (27 * q)) as [Hkq|Hge].
      * specialize (Ibd k Hkq). destruct (ag2_run1 k p2 StB tp); lia.
      * replace k with ((k - 27 * q) + 27 * q)%nat by lia.
        rewrite ag2_run1_add, Eq.
        specialize (Hbd' (k - 27 * q)%nat ltac:(lia)).
        destruct (ag2_run1 (k - 27 * q) (p2 + Z.of_nat q) StB tpq) as [[pk ?] ?]. lia.
Qed.

(** * 8. Bounce at Gap 30, Round 2 Sweep, Chase, and Final Halt at Gap 32 *)

Definition fc_b30_in : FastConfig := {|
  fpos1 := 0; fpos2 := 30; fstate1 := StA; fstate2 := StB;
  ftape := bt_set_ones_nat (-25) 52 (
             bt_set (z_to_pos 32) true (
               bt_set (z_to_pos 31) true (
                 bt_set (z_to_pos 29) true BEmpty)))
|}.

Definition fc_b30_out : FastConfig := N.iter 160 fast_step fc_b30_in.

Lemma b30_no_coll :
  snd (N.iter 160 (fast_step_chk_range (-1) 40) (fc_b30_in, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b30_out_state :
  fc_b30_out.(fpos1) = 0 /\
  fc_b30_out.(fpos2) = 40 /\
  fc_b30_out.(fstate1) = StD /\
  fc_b30_out.(fstate2) = StB /\
  check_all_true_nat (-25) 26 fc_b30_out.(ftape) = true /\
  bt_interp fc_b30_out.(ftape) 27 = true /\
  bt_interp fc_b30_out.(ftape) 28 = false /\
  bt_interp fc_b30_out.(ftape) 29 = true /\
  bt_interp fc_b30_out.(ftape) 30 = true /\
  bt_interp fc_b30_out.(ftape) 31 = true /\
  bt_interp fc_b30_out.(ftape) 32 = true /\
  bt_interp fc_b30_out.(ftape) 33 = true /\
  bt_interp fc_b30_out.(ftape) 34 = true /\
  bt_interp fc_b30_out.(ftape) 35 = false /\
  bt_interp fc_b30_out.(ftape) 36 = false /\
  bt_interp fc_b30_out.(ftape) 37 = false /\
  bt_interp fc_b30_out.(ftape) 38 = true /\
  bt_interp fc_b30_out.(ftape) 39 = false /\
  bt_interp fc_b30_out.(ftape) 40 = false /\
  (forall z, 1 <= z <= 26 -> bt_interp fc_b30_out.(ftape) z = false).
Proof.
  repeat split; try (vm_compute; reflexivity).
  intros z Hz.
  assert (Hchk : check_all_true_nat 1 26 fc_b30_out.(ftape) = false \/ True) by auto.
  (* Verify 1..26 are false via a simple boolean check *)
  assert (Hzs : (fix chk (lo : Z) (n : nat) (t : BTree) : bool :=
    match n with O => true | S n' => negb (bt_get (z_to_pos lo) t) && chk (lo + 1) n' t end)
    1 26 fc_b30_out.(ftape) = true) by (vm_compute; reflexivity).
  clear Hchk.
  assert (Hgen : forall cnt lo t u,
    (fix chk (l : Z) (n : nat) (tr : BTree) : bool :=
      match n with O => true | S n' => negb (bt_get (z_to_pos l) tr) && chk (l + 1) n' tr end)
      lo cnt t = true ->
    lo <= u < lo + Z.of_nat cnt -> bt_interp t u = false).
  { induction cnt; intros lo t u Hc Hu; [lia|].
    rewrite andb_true_iff in Hc. destruct Hc as [H0 Ht].
    rewrite negb_true_iff in H0.
    destruct (Z.eq_dec u lo); [subst; exact H0 | apply (IHcnt (lo + 1) t u Ht); lia]. }
  apply (Hgen 26 1 fc_b30_out.(ftape) z Hzs). lia.
Qed.

(** Check [adv = 14] steps of solo Agent 2 from [fc_b30_out] *)
Lemma adv14_check :
  let '(p', s', t') := Nat.iter 14 fast_ag2_step (40, StB, fc_b30_out.(ftape)) in
  p' = 38 /\ s' = StB /\
  snd (fast_ag2_chk 36 40 14 (40, StB, fc_b30_out.(ftape))) = true /\
  bt_interp t' 27 = true /\ bt_interp t' 28 = false /\
  bt_interp t' 29 = true /\ bt_interp t' 30 = true /\
  bt_interp t' 31 = true /\ bt_interp t' 32 = true /\
  bt_interp t' 33 = true /\ bt_interp t' 34 = true /\
  bt_interp t' 35 = false /\ bt_interp t' 36 = false /\
  bt_interp t' 37 = true  /\ bt_interp t' 38 = false /\
  bt_interp t' 39 = true  /\ bt_interp t' 40 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Bounce at Gap 32 -> Collision at step 30 *)
Definition fc_h32_in : FastConfig := {|
  fpos1 := 0; fpos2 := 32; fstate1 := StA; fstate2 := StB;
  ftape := bt_set_ones_nat (-2) 31 (
             bt_set (z_to_pos 34) true (
               bt_set (z_to_pos 33) true (
                 bt_set (z_to_pos 31) true BEmpty)))
|}.

Lemma h32_no_coll_29 :
  snd (N.iter 29 (fast_step_chk_range 0 35) (fc_h32_in, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma h32_bounds_29 :
  let fc29 := N.iter 29 fast_step fc_h32_in in
  0 <= fc29.(fpos1) <= 35 /\ 0 <= fc29.(fpos2) <= 35 /\
  (fast_step fc29).(fpos1) = 30 /\ (fast_step fc29).(fpos2) = 30.
Proof. repeat split; vm_compute; lia || reflexivity. Qed.

Lemma halt_32_step : forall x c,
  c.(pos1) = x -> c.(pos2) = x + 32 ->
  c.(state1) = StA -> c.(state2) = StB ->
  (forall z, x <= z <= x + 28 -> c.(tape) z = true) ->
  has_glider (x + 32) c.(tape) ->
  (forall z, z >= x + 35 -> c.(tape) z = false) ->
  (forall k, (k < 30)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  (run_N ag1 ag2 30 c).(pos1) = (run_N ag1 ag2 30 c).(pos2).
Proof.
  intros x c Hp1 Hp2 Hs1 Hs2 Hones Hgl Hfar.
  set (c_sh := shift_cfg (- x) c).
  assert (Hagree : forall z, 0 <= z <= 35 -> (fc_to_cfg fc_h32_in).(tape) z = c_sh.(tape) z).
  { intros z Hz. unfold fc_to_cfg, c_sh, shift_cfg; simpl.
    replace (z - - x) with (x + z) by lia.
    destruct (Z_lt_ge_dec z 29) as [Hlt|Hge].
    - rewrite bt_set_ones_nat_in by lia. symmetry. apply Hones. lia.
    - rewrite bt_set_ones_nat_out by lia.
      destruct Hgl as [G3 [G2 [G1 [G0 [Gp1 Gp2]]]]].
      assert (z = 29 \/ z = 30 \/ z = 31 \/ z = 32 \/ z = 33 \/ z = 34 \/ z = 35)
        as [->|[->|[->|[->|[->|[->| ->]]]]]] by lia.
      + rewrite !bt_interp_set. unfold write_tape. simpl. symmetry.
        replace (x + 29) with (x + 32 - 3) by lia. exact G3.
      + rewrite !bt_interp_set. unfold write_tape. simpl. symmetry.
        replace (x + 30) with (x + 32 - 2) by lia. exact G2.
      + rewrite !bt_interp_set. unfold write_tape. simpl. symmetry.
        replace (x + 31) with (x + 32 - 1) by lia. exact G1.
      + rewrite !bt_interp_set. unfold write_tape. simpl. symmetry.
        replace (x + 32) with (x + 32) by lia. exact G0.
      + rewrite !bt_interp_set. unfold write_tape. simpl. symmetry.
        replace (x + 33) with (x + 32 + 1) by lia. exact Gp1.
      + rewrite !bt_interp_set. unfold write_tape. simpl. symmetry.
        replace (x + 34) with (x + 32 + 2) by lia. exact Gp2.
      + rewrite !bt_interp_set. unfold write_tape, bt_interp. simpl.
        rewrite bt_get_empty. symmetry. apply Hfar. lia. }
  assert (Hbd : forall k, (k < 30)%N ->
    0 <= (run_N ag1 ag2 k (fc_to_cfg fc_h32_in)).(pos1) <= 35 /\
    0 <= (run_N ag1 ag2 k (fc_to_cfg fc_h32_in)).(pos2) <= 35).
  { intros k Hk.
    destruct (N.lt_ge_cases k 29) as [Hk29|Hk29].
    - pose proof (fast_step_chk_range_sound 29 0 35 fc_h32_in true h32_no_coll_29) as [_ Hnc].
      destruct (Hnc k Hk29) as [_ [Hb1 Hb2]].
      pose proof (fast_run_sound k fc_h32_in) as [Fp1 Fp2 _ _ _].
      rewrite fc_to_cfg_pos1 in Fp1. rewrite fc_to_cfg_pos2 in Fp2. lia.
    - assert (k = 29%N) by lia. subst k.
      destruct h32_bounds_29 as [Hb1 [Hb2 _]].
      pose proof (fast_run_sound 29 fc_h32_in) as [Fp1 Fp2 _ _ _].
      rewrite fc_to_cfg_pos1 in Fp1. rewrite fc_to_cfg_pos2 in Fp2. lia. }
  assert (Hp1_sh : (fc_to_cfg fc_h32_in).(pos1) = c_sh.(pos1))
    by (unfold fc_to_cfg, c_sh, shift_cfg; simpl; lia).
  assert (Hp2_sh : (fc_to_cfg fc_h32_in).(pos2) = c_sh.(pos2))
    by (unfold fc_to_cfg, c_sh, shift_cfg; simpl; lia).
  assert (Hs1_sh : (fc_to_cfg fc_h32_in).(state1) = c_sh.(state1)) by (simpl; congruence).
  assert (Hs2_sh : (fc_to_cfg fc_h32_in).(state2) = c_sh.(state2)) by (simpl; congruence).
  destruct (run_N_agree_range ag1 ag2 0 35 30 (fc_to_cfg fc_h32_in) c_sh
              Hp1_sh Hp2_sh Hs1_sh Hs2_sh Hagree Hbd)
    as [Ap1 [Ap2 [_ [_ [_ [_ Aprev]]]]]].
  pose proof (run_N_shift ag1 ag2 (- x) 30 c) as [Shp1 Shp2 _ _ _].
  fold c_sh in Shp1, Shp2.
  rewrite shift_cfg_pos1 in Shp1. rewrite shift_cfg_pos2 in Shp2.
  pose proof (fast_run_sound 30 fc_h32_in) as [Fp1 Fp2 _ _ _].
  rewrite fc_to_cfg_pos1 in Fp1. rewrite fc_to_cfg_pos2 in Fp2.
  destruct h32_bounds_29 as [_ [_ [Hc1 Hc2]]].
  replace (N.iter 30 fast_step fc_h32_in) with (fast_step (N.iter 29 fast_step fc_h32_in))
    in Fp1, Fp2 by (change 30%N with (N.succ 29); apply N.iter_succ).
  split.
  - intros k Hk.
    pose proof (run_N_shift ag1 ag2 (- x) k c) as [K1 K2 _ _ _].
    fold c_sh in K1, K2. rewrite shift_cfg_pos1 in K1. rewrite shift_cfg_pos2 in K2.
    destruct (Aprev k Hk) as [E1 E2].
    destruct (N.lt_ge_cases k 29) as [Hk29|Hk29].
    + pose proof (fast_step_chk_range_sound 29 0 35 fc_h32_in true h32_no_coll_29) as [_ Hnc].
      destruct (Hnc k Hk29) as [Hneq _].
      pose proof (fast_run_sound k fc_h32_in) as [Fk1 Fk2 _ _ _].
      rewrite fc_to_cfg_pos1 in Fk1. rewrite fc_to_cfg_pos2 in Fk2. lia.
    + assert (k = 29%N) by lia. subst k.
      pose proof (fast_run_sound 29 fc_h32_in) as [Fk1 Fk2 _ _ _].
      rewrite fc_to_cfg_pos1 in Fk1. rewrite fc_to_cfg_pos2 in Fk2.
      assert (Hneq29 : (N.iter 29 fast_step fc_h32_in).(fpos1) <> (N.iter 29 fast_step fc_h32_in).(fpos2))
        by (vm_compute; discriminate).
      lia.
  - lia.
Qed.

Lemma chase_27_one : forall x1 x2 c,
  x1 + 32 <= x2 ->
  c.(pos1) = x1 -> c.(pos2) = x2 ->
  c.(state1) = StA -> c.(state2) = StB ->
  (forall z, x1 <= z < x1 + 27 -> c.(tape) z = true) ->
  has_glider x2 c.(tape) ->
  (forall z, z >= x2 + 3 -> c.(tape) z = false) ->
  let r := run_N ag1 ag2 27 c in
  r.(pos1) = x1 + 27 /\ r.(pos2) = x2 + 1 /\
  r.(state1) = StA /\ r.(state2) = StB /\
  (forall z, z < x1 + 27 -> r.(tape) z = c.(tape) z) /\
  (forall z, x1 + 27 <= z < x2 - 3 -> r.(tape) z = c.(tape) z) /\
  (forall z, x2 - 3 <= z < x2 - 2 -> r.(tape) z = true) /\
  has_glider (x2 + 1) r.(tape) /\
  (forall z, z >= x2 + 4 -> r.(tape) z = false) /\
  (forall k, (k < 27)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)).
Proof.
  intros x1 x2 c Hgap Hp1 Hp2 Hs1 Hs2 Hones Hgl Hfar.
  set (mid := x1 + 27).
  assert (H1 : forall k, (k < 27)%nat ->
    let '(p1, _, _) := ag1_run1 k c.(pos1) c.(state1) c.(tape) in p1 < mid).
  { intros k Hk. rewrite Hp1, Hs1.
    pose proof (walk_A_ones 27 x1 c.(tape) Hones) as [_ [_ [_ Hbd]]].
    specialize (Hbd k Hk). destruct (ag1_run1 k x1 StA c.(tape)) as [[pk ?] ?]. lia. }
  assert (H2 : forall k, (k < 27)%nat ->
    let '(p2, _, _) := ag2_run1 k c.(pos2) c.(state2) c.(tape) in mid <= p2).
  { intros k Hk. rewrite Hp2, Hs2.
    pose proof (glider_27_step x2 c.(tape) Hgl ltac:(intros z Hz; apply Hfar; lia)) as [_ [_ [_ [_ [_ Hbd]]]]].
    specialize (Hbd k Hk). destruct (ag2_run1 k x2 StB c.(tape)) as [[pk ?] ?]. lia. }
  pose proof (decouple_run 27 mid c H1 H2) as Hd.
  change (N.of_nat 27) with 27%N in Hd.
  rewrite Hp1, Hs1, Hp2, Hs2 in Hd.
  pose proof (walk_A_ones 27 x1 c.(tape) Hones) as Hw.
  destruct (ag1_run1 27 x1 StA c.(tape)) as [[p1' s1'] t1'].
  destruct Hw as [Hw_p [Hw_s [Hw_t _]]].
  pose proof (glider_27_step x2 c.(tape) Hgl ltac:(intros z Hz; apply Hfar; lia)) as Hg.
  destruct (ag2_run1 27 x2 StB c.(tape)) as [[p2' s2'] t2'].
  destruct Hg as [Hg_p [Hg_s [Hg_m3 [Hg_gl [Hg_out _]]]]].
  destruct Hd as [Dp1 [Ds1 [Dp2 [Ds2 [Dt1 [Dt2 Dnc]]]]]].
  repeat split; try lia; try congruence.
  - intros z Hz. rewrite Dt1 by lia. apply Hw_t.
  - intros z Hz. rewrite Dt2 by lia. apply Hg_out. lia.
  - intros z Hz. rewrite Dt2 by lia. replace z with (x2 - 3) by lia. exact Hg_m3.
  - unfold has_glider in *.
    destruct Hg_gl as [A1 [A2 [A3 [A4 [A5 A6]]]]].
    repeat split; rewrite Dt2 by lia; assumption.
  - intros z Hz. rewrite Dt2 by lia. rewrite Hg_out by lia. apply Hfar. lia.
  - exact Dnc.
Qed.

Lemma chase_27_loop : forall k x1 x2 c,
  x1 + 32 + 26 * Z.of_nat k <= x2 ->
  c.(pos1) = x1 -> c.(pos2) = x2 ->
  c.(state1) = StA -> c.(state2) = StB ->
  (forall z, x1 <= z < x2 - 3 -> c.(tape) z = true) ->
  has_glider x2 c.(tape) ->
  (forall z, z >= x2 + 3 -> c.(tape) z = false) ->
  let r := run_N ag1 ag2 (27 * N.of_nat k) c in
  r.(pos1) = x1 + 27 * Z.of_nat k /\
  r.(pos2) = x2 + Z.of_nat k /\
  r.(state1) = StA /\ r.(state2) = StB /\
  (forall z, x1 + 27 * Z.of_nat k <= z < x2 + Z.of_nat k - 3 -> r.(tape) z = true) /\
  has_glider (x2 + Z.of_nat k) r.(tape) /\
  (forall z, z >= x2 + Z.of_nat k + 3 -> r.(tape) z = false) /\
  (forall t, (t < 27 * N.of_nat k)%N -> (run_N ag1 ag2 t c).(pos1) <> (run_N ag1 ag2 t c).(pos2)).
Proof.
  induction k; intros x1 x2 c Hgap Hp1 Hp2 Hs1 Hs2 Hones Hgl Hfar.
  - simpl. rewrite run_N_0. repeat split; try lia; auto.
    + intros z Hz. apply Hones. lia.
    + replace (x2 + 0) with x2 by lia. exact Hgl.
    + intros z Hz. apply Hfar. lia.
    + intros t Ht; lia.
  - replace (27 * N.of_nat (S k))%N with (27 * N.of_nat k + 27)%N by lia.
    rewrite run_N_add.
    assert (Hones27 : forall z, x1 <= z < x1 + 27 -> c.(tape) z = true)
      by (intros z Hz; apply Hones; lia).
    pose proof (chase_27_one x1 x2 c ltac:(lia) Hp1 Hp2 Hs1 Hs2 Hones27 Hgl Hfar) as Hone.
    set (c1 := run_N ag1 ag2 27 c) in *.
    destruct Hone as [C1p1 [C1p2 [C1s1 [C1s2 [C1l [C1m [C1m3 [C1gl [C1far C1nc]]]]]]]]].
    assert (Hones' : forall z, x1 + 27 <= z < (x2 + 1) - 3 -> c1.(tape) z = true).
    { intros z Hz. destruct (Z.lt_ge_dec z (x2 - 3)).
      - rewrite C1m by lia. apply Hones. lia.
      - apply C1m3. lia. }
    specialize (IHk (x1 + 27) (x2 + 1) c1 ltac:(lia) C1p1 C1p2 C1s1 C1s2 Hones' C1gl C1far).
    destruct IHk as [Ip1 [Ip2 [Is1 [Is2 [Iones [Igl [Ifar Inc]]]]]]].
    repeat split; try lia; auto.
    + intros z Hz. apply Iones. lia.
    + replace (x2 + Z.of_nat (S k)) with (x2 + 1 + Z.of_nat k) by lia. exact Igl.
    + intros z Hz. apply Ifar. lia.
    + apply no_coll_add; [exact C1nc | exact Inc].
Qed.

(** * 9. Main Halting Theorem: exact_T_halt *)

Definition k_close : N := ((2 ^ 141 - 44) / 26)%N.

Lemma k_close_exact : (26 * k_close = 2 ^ 141 - 44)%N.
Proof. vm_compute. reflexivity. Qed.

Definition exact_T_halt : N :=
  (3720 + 160 + (27 * 2 ^ 141 - 121) + 27 * k_close + 30)%N.

Lemma exact_T_halt_val :
  exact_T_halt = 78159823316003962837401627984426228547406259%N.
Proof. vm_compute. reflexivity. Qed.

Theorem cet4_7e43_halts : halts_at_exact ag1 ag2 c0 exact_T_halt.
Proof.
  (* Step 1: Prefix t = 0 .. 3720 *)
  destruct prefix_3720_summary as
    [P1 [P2 [S1 [S2 [Pones [P141 [P142 [P143 [P144 [P145 [P146 [Pfar Pnc]]]]]]]]]]]].
  set (c_r2 := run_N ag1 ag2 3720 c0) in *.

  (* Step 2: Bounce at Gap 30 (160 steps) using shift by 114 *)
  set (c_sh := shift_cfg (-114) c_r2).
  assert (Hagree_b30 : forall z, -25 <= z <= 40 -> (fc_to_cfg fc_b30_in).(tape) z = c_sh.(tape) z).
  { intros z Hz. unfold fc_to_cfg, c_sh, shift_cfg; simpl.
    replace (z - -114) with (z + 114) by lia.
    destruct (Z_lt_ge_dec z 27) as [Hlt|Hge].
    - rewrite bt_set_ones_nat_in by lia. symmetry. apply Pones. lia.
    - rewrite bt_set_ones_nat_out by lia.
      assert (z = 27 \/ z = 28 \/ z = 29 \/ z = 30 \/ z = 31 \/ z = 32 \/ z >= 33)
        as [->|[->|[->|[->|[->|[->|Hz33]]]]]] by lia.
      + rewrite !bt_interp_set. unfold write_tape, bt_interp; simpl; rewrite bt_get_empty. symmetry; exact P141.
      + rewrite !bt_interp_set. unfold write_tape, bt_interp; simpl; rewrite bt_get_empty. symmetry; exact P142.
      + rewrite !bt_interp_set. unfold write_tape; simpl. symmetry; exact P143.
      + rewrite !bt_interp_set. unfold write_tape, bt_interp; simpl; rewrite bt_get_empty. symmetry; exact P144.
      + rewrite !bt_interp_set. unfold write_tape; simpl. symmetry; exact P145.
      + rewrite !bt_interp_set. unfold write_tape; simpl. symmetry; exact P146.
      + rewrite !bt_interp_set. unfold write_tape, bt_interp; simpl; rewrite bt_get_empty.
        symmetry. apply Pfar. lia. }
  assert (Hbd_b30 : forall k, (k < 160)%N ->
    -1 <= (run_N ag1 ag2 k (fc_to_cfg fc_b30_in)).(pos1) <= 40 /\
    -1 <= (run_N ag1 ag2 k (fc_to_cfg fc_b30_in)).(pos2) <= 40).
  { intros k Hk.
    pose proof (fast_step_chk_range_sound 160 (-1) 40 fc_b30_in true b30_no_coll) as [_ Hnc].
    destruct (Hnc k Hk) as [_ [Hb1 Hb2]].
    pose proof (fast_run_sound k fc_b30_in) as [Fp1 Fp2 _ _ _].
    rewrite fc_to_cfg_pos1 in Fp1. rewrite fc_to_cfg_pos2 in Fp2. lia. }
  assert (Hb30_p1 : (fc_to_cfg fc_b30_in).(pos1) = c_sh.(pos1)) by (unfold fc_to_cfg, c_sh, shift_cfg; simpl; lia).
  assert (Hb30_p2 : (fc_to_cfg fc_b30_in).(pos2) = c_sh.(pos2)) by (unfold fc_to_cfg, c_sh, shift_cfg; simpl; lia).
  assert (Hb30_s1 : (fc_to_cfg fc_b30_in).(state1) = c_sh.(state1)) by (simpl; congruence).
  assert (Hb30_s2 : (fc_to_cfg fc_b30_in).(state2) = c_sh.(state2)) by (simpl; congruence).
  destruct (run_N_agree_range ag1 ag2 (-1) 40 160 (fc_to_cfg fc_b30_in) c_sh
              Hb30_p1 Hb30_p2 Hb30_s1 Hb30_s2
              (fun z Hz => Hagree_b30 z ltac:(lia)) Hbd_b30)
    as [Bp1 [Bp2 [Bs1 [Bs2 [Btp [Bout Bprev]]]]]].
  pose proof (run_N_shift ag1 ag2 (-114) 160 c_r2) as [Bsp1 [Bsp2 [Bss1 [Bss2 Bstp]]]].
  fold c_sh in Bsp1, Bsp2, Bss1, Bss2, Bstp.
  rewrite shift_cfg_pos1 in Bsp1. rewrite shift_cfg_pos2 in Bsp2.
  rewrite shift_cfg_state1 in Bss1. rewrite shift_cfg_state2 in Bss2.
  pose proof (fast_run_sound 160 fc_b30_in) as [Fp1 [Fp2 [Fs1 [Fs2 Ftp]]]].
  fold fc_b30_out in Fp1, Fp2, Fs1, Fs2, Ftp.
  rewrite fc_to_cfg_pos1 in Fp1. rewrite fc_to_cfg_pos2 in Fp2.
  rewrite fc_to_cfg_state1 in Fs1. rewrite fc_to_cfg_state2 in Fs2.
  destruct b30_out_state as [O1 [O2 [O3 [O4 [Oones [O27 [O28 [O29 [O30 [O31 [O32 [O33 [O34 [O35 [O36 [O37 [O38 [O39 [O40 Oz]]]]]]]]]]]]]]]]]]].
  set (c_b30 := run_N ag1 ag2 160 c_r2).
  assert (Hb30_nc : forall k, (k < 160)%N -> (run_N ag1 ag2 k c_r2).(pos1) <> (run_N ag1 ag2 k c_r2).(pos2)).
  { intros k Hk.
    pose proof (run_N_shift ag1 ag2 (-114) k c_r2) as [Kp1 Kp2 _ _ _].
    fold c_sh in Kp1, Kp2. rewrite shift_cfg_pos1 in Kp1. rewrite shift_cfg_pos2 in Kp2.
    destruct (Bprev k Hk) as [E1 E2].
    pose proof (fast_step_chk_range_sound 160 (-1) 40 fc_b30_in true b30_no_coll) as [_ Hnc].
    destruct (Hnc k Hk) as [Hneq _].
    pose proof (fast_run_sound k fc_b30_in) as [Fk1 Fk2 _ _ _].
    rewrite fc_to_cfg_pos1 in Fk1. rewrite fc_to_cfg_pos2 in Fk2. lia. }

  (* Key facts about c_b30 *)
  assert (Hc_b30_p1 : c_b30.(pos1) = 114) by lia.
  assert (Hc_b30_p2 : c_b30.(pos2) = 154) by lia.
  assert (Hc_b30_s1 : c_b30.(state1) = StD) by congruence.
  assert (Hc_b30_s2 : c_b30.(state2) = StB) by congruence.
  assert (Hc_b30_ones : forall z, -1 <= z <= 114 -> c_b30.(tape) z = true).
  { intros z Hz. destruct (Z_lt_ge_dec z 113) as [Hlt|Hge].
    - (* z < 113 -> untouched by run_N_agree_range on [-1..40] shifted by 114! *)
      pose proof (Bstp (z - 114)) as H1. simpl in H1. replace (z - 114 - -114) with z in H1 by lia.
      rewrite <- H1. rewrite Bout by lia. unfold c_sh, shift_cfg; simpl.
      replace (z - 114 - -114) with z by lia. apply Pones; lia.
    - pose proof (Bstp (z - 114)) as H1. simpl in H1. replace (z - 114 - -114) with z in H1 by lia.
      rewrite <- H1. rewrite <- Btp by lia. rewrite <- Ftp.
      apply (check_all_true_nat_sound 26 (-25) fc_b30_out.(ftape) (z - 114) Oones). lia. }
  assert (Hc_b30_zeros : forall z, 115 <= z <= 140 -> c_b30.(tape) z = false).
  { intros z Hz.
    pose proof (Bstp (z - 114)) as H1. simpl in H1. replace (z - 114 - -114) with z in H1 by lia.
    rewrite <- H1. rewrite <- Btp by lia. rewrite <- Ftp. apply Oz. lia. }
  assert (Hc_b30_far : forall z, z > 154 -> c_b30.(tape) z = false).
  { intros z Hz.
    pose proof (Bstp (z - 114)) as H1. simpl in H1. replace (z - 114 - -114) with z in H1 by lia.
    rewrite <- H1. rewrite Bout by lia. unfold c_sh, shift_cfg; simpl.
    replace (z - 114 - -114) with z by lia. apply Pfar. lia. }

  (* Step 3: Round 2 Sweep + Sync = (27 * 2^141 - 121) steps *)
  (* Split into: 14 steps (adv14) + 27 * (2^141 - 6) steps + 27 steps *)
  set (T_r2 := (27 * 2 ^ 141 - 121)%N).
  assert (HT_r2_eq : T_r2 = (27 + (27 * (2 ^ 141 - 6) + 14))%N) by (unfold T_r2; lia).

  (* Substep 3A: 14 steps via decouple_run with mid = 149 *)
  (* Note: ag1 runs 14 steps of T_sweep_z 116 26, ag2 runs adv14 *)
  (* Let's bound ag1 on T_sweep_z 116 26: *)
  assert (Hsw26 :
    let '(p1', s1', t1') := ag1_run1 (T_sweep_z 116 26) 114 StD c_b30.(tape) in
    p1' = 141 /\ s1' = StA /\
    (forall u, -1 <= u <= 140 -> t1' u = true) /\
    (forall u, u < -1 \/ u > 140 -> t1' u = c_b30.(tape) u) /\
    (forall k, (k < T_sweep_z 116 26)%nat ->
      let '(pk, _, _) := ag1_run1 k 114 StD c_b30.(tape) in -1 <= pk <= 140)).
  { pose proof (sweep_D_z 26 115 114 c_b30.(tape) ltac:(lia)
                  (fun u Hu => Hc_b30_ones u ltac:(lia))
                  (fun u Hu => Hc_b30_zeros u ltac:(lia))) as H.
    replace (114 - Z.of_nat 115) with (-1) in H by lia.
    replace (114 + Z.of_nat 26) with 140 in H by lia.
    exact H. }

  (* Note: T_sweep_z 116 26 is huge (9 * 2^141 - 133), so we do NOT evaluate it with vm_compute in nat!
     Wait: in Rocq, Nat.iter (9 * 2^141) would be huge if unfolded, so we NEVER unfold it;
     we use decouple_run with N.of_nat? Wait: N.of_nat (T_sweep_z 116 26) only exists as a nat in sweep_D_z!
     Since sweep_D_z is purely symbolic (universally quantified), Lia/Peano never evaluates 2^141 in nat! *)
  assert (Hge_14 : (14 < T_sweep_z 116 26)%nat).
  { unfold T_sweep_z. assert (H2_141 : (1000 <= 2 ^ 141)%nat).
    { change 1000%nat with (1000%nat). clear.
      assert (H10 : (1024 = 2 ^ 10)%nat) by reflexivity.
      assert (Hpow : (2 ^ 10 <= 2 ^ 141)%nat).
      { apply Nat.pow_le_mono_r; lia. }
      lia. }
    replace (116 + 26 - 1)%nat with 141%nat by lia. lia. }

  assert (H3A_1 : forall k, (k < 14)%nat ->
    let '(p1, _, _) := ag1_run1 k c_b30.(pos1) c_b30.(state1) c_b30.(tape) in p1 < 149).
  { intros k Hk. rewrite Hc_b30_p1, Hc_b30_s1.
    destruct (ag1_run1 (T_sweep_z 116 26) 114 StD c_b30.(tape)) as [[? ?] ?].
    destruct Hsw26 as [_ [_ [_ [_ Hbd]]]].
    specialize (Hbd k ltac:(lia)).
    destruct (ag1_run1 k 114 StD c_b30.(tape)) as [[pk ?] ?]. lia. }

  (* For ag2 during 14 steps: compare c_b30.(tape) with fc_b30_out.(ftape) shifted by 114 on [149..155] *)
  assert (Hagree_adv : forall z, 150 <= z <= 154 ->
    bt_interp fc_b30_out.(ftape) (z - 114) = c_b30.(tape) z).
  { intros z Hz.
    
    - replace (155 - 114) with 41 by lia.
      rewrite Hc_b30_far by lia.
      pose proof (Bstp 41) as H1. simpl in H1.
      (* Wait: Bout on fc_b30_out.(ftape) at 41: fc_b30_in was bounded in [-25..32], and 160 steps stayed in [-1..40],
         so fc_b30_out.(ftape) at 41 is false! *)
      assert (H41 : bt_interp fc_b30_out.(ftape) 41 = false).
      { rewrite <- Ftp.
        pose proof (run_N_agree_range ag1 ag2 (-1) 40 160 (fc_to_cfg fc_b30_in) (fc_to_cfg fc_b30_in)
                      eq_refl eq_refl eq_refl eq_refl (fun _ _ => eq_refl) Hbd_b30) as [_ [_ [_ [_ [_ [Hout41 _]]]]]].
        rewrite Hout41 by lia. unfold fc_to_cfg; simpl.
        rewrite bt_set_ones_nat_out by lia.
        rewrite !bt_interp_set. unfold write_tape, bt_interp; simpl.
        repeat (destruct (Z.eqb_spec 41 _); [lia|]). apply bt_get_empty. }
      exact H41.
    - pose proof (Bstp (z - 114)) as H1. simpl in H1. replace (z - 114 - -114) with z in H1 by lia.
      rewrite <- H1. rewrite <- Btp by lia. rewrite <- Ftp. reflexivity. }
  assert (H3A_2 : forall k, (k < 14)%nat ->
    let '(p2, _, _) := ag2_run1 k c_b30.(pos2) c_b30.(state2) c_b30.(tape) in 149 <= p2).
  { intros k Hk. rewrite Hc_b30_p2, Hc_b30_s2.
    destruct adv14_check as [_ [_ [Hchk _]]].
    pose proof (fast_ag2_chk_sound 36 40 14 40 StB fc_b30_out.(ftape) Hchk k Hk) as Hbd0.
    pose proof (ag2_run1_shift 114 k 40 StB (bt_interp fc_b30_out.(ftape))) as Hshk.
    replace (40 + 114) with 154 in Hshk by lia.
    assert (Hbd_sh : forall j, (j < 14)%nat ->
      let '(pj, _, _) := ag2_run1 j 154 StB (fun z => bt_interp fc_b30_out.(ftape) (z - 114)) in 150 <= pj <= 154).
    { intros j Hj.
      pose proof (fast_ag2_chk_sound 36 40 14 40 StB fc_b30_out.(ftape) Hchk j Hj) as Hbdj.
      pose proof (ag2_run1_shift 114 j 40 StB (bt_interp fc_b30_out.(ftape))) as Hshj.
      replace (40 + 114) with 154 in Hshj by lia.
      destruct (ag2_run1 j 154 StB _); destruct (ag2_run1 j 40 StB _); destruct Hshj; lia. }
    pose proof (ag2_run1_agree_range 150 154 14 154 StB
                  (fun z => bt_interp fc_b30_out.(ftape) (z - 114)) c_b30.(tape)
                  Hagree_adv ltac:(intros j Hj; specialize (Hbd_sh j Hj); destruct (ag2_run1 j 154 StB _); lia))
      as [_ [_ [_ [_ Hprev]]]].
    specialize (Hprev k Hk). specialize (Hbd_sh k Hk).
    destruct (ag2_run1 k 154 StB (fun z => bt_interp fc_b30_out.(ftape) (z - 114))) as [[pk1 ?] ?].
    destruct (ag2_run1 k 154 StB c_b30.(tape)) as [[pk2 ?] ?]. lia. }

  pose proof (decouple_run 14 149 c_b30 H3A_1 H3A_2) as H3A.
  change (N.of_nat 14) with 14%N in H3A.
  set (c_3A := run_N ag1 ag2 14 c_b30) in *.
  destruct (ag1_run1 14 c_b30.(pos1) c_b30.(state1) c_b30.(tape)) as [[p1_3A s1_3A] t1_3A] eqn:E1_3A.
  destruct (ag2_run1 14 c_b30.(pos2) c_b30.(state2) c_b30.(tape)) as [[p2_3A s2_3A] t2_3A] eqn:E2_3A.
  destruct H3A as [A3p1 [A3s1 [A3p2 [A3s2 [A3t1 [A3t2 A3nc]]]]]].

  (* Compute ag2 state after adv14 *)
  assert (Hadv14_res :
    p2_3A = 152 /\ s2_3A = StB /\
    (forall z, 141 <= z <= 154 -> t2_3A z = bt_interp (fst (let '(st, _) := (Nat.iter 14 fast_ag2_step (40, StB, fc_b30_out.(ftape)), true) in (snd (let '(a, b, c) := st in (a, b, c)), true))) (z - 114) \/ True)).
  { auto. }
  clear Hadv14_res.
  pose proof adv14_check as Hadv.
  destruct (Nat.iter 14 fast_ag2_step (40, StB, fc_b30_out.(ftape))) as [[p_adv s_adv] t_adv] eqn:Eadv.
  destruct Hadv as [Ha_p [Ha_s [Ha_chk [Ha27 [Ha28 [Ha29 [Ha30 [Ha31 [Ha32 [Ha33 [Ha34 [Ha35 [Ha36 [Ha37 [Ha38 [Ha39 Ha40]]]]]]]]]]]]]]]]].
  subst p_adv s_adv.
  pose proof (fast_ag2_run_sound 14 40 StB fc_b30_out.(ftape)) as Hrun_adv.
  rewrite Eadv in Hrun_adv.
  destruct (ag2_run1 14 40 StB (bt_interp fc_b30_out.(ftape))) as [[p_adv0 s_adv0] t_adv0] eqn:Eadv0.
  destruct Hrun_adv as [Hrp [Hrs Hrt]]. subst p_adv0 s_adv0.
  pose proof (ag2_run1_shift 114 14 40 StB (bt_interp fc_b30_out.(ftape))) as Hsh_adv.
  rewrite Eadv0 in Hsh_adv.
  destruct (ag2_run1 14 (40 + 114) StB (fun z => bt_interp fc_b30_out.(ftape) (z - 114))) as [[ps_adv ss_adv] ts_adv] eqn:Es_adv.
  destruct Hsh_adv as [Hsp [Hss Hst]].
  assert (Hbd_sh14 : forall j, (j < 14)%nat ->
    let '(pj, _, _) := ag2_run1 j 154 StB (fun z => bt_interp fc_b30_out.(ftape) (z - 114)) in 150 <= pj <= 154).
  { intros j Hj.
    pose proof (fast_ag2_chk_sound 36 40 14 40 StB fc_b30_out.(ftape) Ha_chk j Hj) as Hbdj.
    pose proof (ag2_run1_shift 114 j 40 StB (bt_interp fc_b30_out.(ftape))) as Hshj.
    replace (40 + 114) with 154 in Hshj by lia.
    destruct (ag2_run1 j 154 StB _); destruct (ag2_run1 j 40 StB _); destruct Hshj; lia. }
  pose proof (ag2_run1_agree_range 150 154 14 154 StB
                (fun z => bt_interp fc_b30_out.(ftape) (z - 114)) c_b30.(tape)
                Hagree_adv Hbd_sh14) as Hag_adv.
  replace (40 + 114) with 154 in Es_adv by lia. rewrite Es_adv in Hag_adv.
  rewrite Hc_b30_p2, Hc_b30_s2 in E2_3A. rewrite E2_3A in Hag_adv.
  destruct Hag_adv as [Iap [Ias [Iat [Iaout _]]]].

  (* Now c_3A has:
     pos2 = 152, state2 = StB, has_glider 152 c_3A.(tape),
     c_3A.(tape) 141 = true, 142 = false, [143..148] = true, > 154 = false! *)
  assert (Hc3A_p2 : c_3A.(pos2) = 152) by lia.
  assert (Hc3A_s2 : c_3A.(state2) = StB) by congruence.
  assert (Hc3A_gl : has_glider 152 c_3A.(tape)).
  { unfold has_glider. repeat split; rewrite A3t2 by lia, <- Iat by lia, Hst, <- Hrt;
      [exact Ha35 | exact Ha36 | exact Ha37 | exact Ha38 | exact Ha39 | exact Ha40]. }
  assert (Hc3A_far : forall z, z >= 155 -> c_3A.(tape) z = false).
  { intros z Hz. rewrite A3t2 by lia. rewrite Iaout by lia. apply Hc_b30_far. lia. }
  assert (Hc3A_141 : c_3A.(tape) 141 = true /\ c_3A.(tape) 142 = false /\
    (forall z, 143 <= z <= 148 -> c_3A.(tape) z = true)).
  { repeat split.
    - rewrite A3t1 by lia.
      (* 141 < 149: ag1 stayed in [-1..140] during 14 steps! *)
      (* Wait: let's prove ag1_run1 k stays in [-1..140], so tape 141..148 is untouched! *)
      assert (H1_141 : forall j, (j <= 14)%nat ->
        let '(_, _, tj) := ag1_run1 j 114 StD c_b30.(tape) in
        forall z, z >= 141 -> tj z = c_b30.(tape) z).
      { induction j; intros Hj z Hz; [simpl; reflexivity|].
        unfold ag1_run1 in *. simpl.
        destruct (Nat.iter j _ (114, StD, c_b30.(tape))) as [[pj sj] tj] eqn:Ej.
        specialize (IHj ltac:(lia) z Hz).
        assert (Hpj : pj <= 140).
        { destruct Hsw26 as [_ [_ [_ [_ Hbd]]]].
          specialize (Hbd j ltac:(lia)). unfold ag1_run1 in Hbd. rewrite Ej in Hbd. lia. }
        unfold ag1_step1. unfold write_tape. destruct (Z.eqb_spec z pj); [lia | exact IHj]. }
      specialize (H1_141 14%nat ltac:(lia)). rewrite Hc_b30_p1, Hc_b30_s1 in E1_3A.
      rewrite E1_3A in H1_141. rewrite H1_141 by lia.
      pose proof (Bstp (141 - 114)) as H1. simpl in H1. replace (141 - 114 - -114) with 141 in H1 by lia.
      rewrite <- H1, <- Btp by lia, <- Ftp. exact O27.
    - assert (H1_142 : forall j, (j <= 14)%nat ->
        let '(_, _, tj) := ag1_run1 j 114 StD c_b30.(tape) in
        forall z, z >= 141 -> tj z = c_b30.(tape) z).
      { induction j; intros Hj z Hz; [simpl; reflexivity|].
        unfold ag1_run1 in *. simpl.
        destruct (Nat.iter j _ (114, StD, c_b30.(tape))) as [[pj sj] tj] eqn:Ej.
        specialize (IHj ltac:(lia) z Hz).
        assert (Hpj : pj <= 140).
        { destruct Hsw26 as [_ [_ [_ [_ Hbd]]]].
          specialize (Hbd j ltac:(lia)). unfold ag1_run1 in Hbd. rewrite Ej in Hbd. lia. }
        unfold ag1_step1. unfold write_tape. destruct (Z.eqb_spec z pj); [lia | exact IHj]. }
      rewrite A3t1 by lia.
      specialize (H1_142 14%nat ltac:(lia)). rewrite Hc_b30_p1, Hc_b30_s1 in E1_3A.
      rewrite E1_3A in H1_142. rewrite H1_142 by lia.
      pose proof (Bstp (142 - 114)) as H1. simpl in H1. replace (142 - 114 - -114) with 142 in H1 by lia.
      rewrite <- H1, <- Btp by lia, <- Ftp. exact O28.
    - intros z Hz. rewrite A3t1 by lia.
      assert (H1_z : forall j, (j <= 14)%nat ->
        let '(_, _, tj) := ag1_run1 j 114 StD c_b30.(tape) in
        forall u, u >= 141 -> tj u = c_b30.(tape) u).
      { induction j; intros Hj u Hu; [simpl; reflexivity|].
        unfold ag1_run1 in *. simpl.
        destruct (Nat.iter j _ (114, StD, c_b30.(tape))) as [[pj sj] tj] eqn:Ej.
        specialize (IHj ltac:(lia) u Hu).
        assert (Hpj : pj <= 140).
        { destruct Hsw26 as [_ [_ [_ [_ Hbd]]]].
          specialize (Hbd j ltac:(lia)). unfold ag1_run1 in Hbd. rewrite Ej in Hbd. lia. }
        unfold ag1_step1. unfold write_tape. destruct (Z.eqb_spec u pj); [lia | exact IHj]. }
      specialize (H1_z 14%nat ltac:(lia)). rewrite Hc_b30_p1, Hc_b30_s1 in E1_3A.
      rewrite E1_3A in H1_z. rewrite H1_z by lia.
      pose proof (Bstp (z - 114)) as H1. simpl in H1. replace (z - 114 - -114) with z in H1 by lia.
      rewrite <- H1, <- Btp by lia, <- Ftp.
      assert (z - 114 = 29 \/ z - 114 = 30 \/ z - 114 = 31 \/
              z - 114 = 32 \/ z - 114 = 33 \/ z - 114 = 34)
        as [->|[->|[->|[->|[->| ->]]]]] by lia; assumption. }

  (* Substep 3B: Remaining 27 * (2^141 - 5) steps from c_3A, split as:
     27 * (2^141 - 6) steps (mid = 149) + 27 steps (mid = 160) *)
  (* First note: ag1 at c_3A has already run 14 steps of T_sweep_z 116 26,
     and c_3A.(tape) agrees with c_b30.(tape) on z < 149 (actually z <= 148)! *)
  set (q_big := (2 ^ 141 - 6)%nat).
  assert (Hq_big_pos : (27 * q_big = 27 * (2 ^ 141 - 6))%nat) by reflexivity.
  (* Rather than splitting inside ag1, we can prove ag1_run1 (T_full) on c_3A.(tape)
     by noting that on z < 149, ag1_run1 14 c_b30.(tape) = c_3A.(tape)!
     Specifically, let T_rem1 = T_sweep_z 116 26 - 14.
     Wait: ag1_run1 T_rem1 c_3A.(pos1) c_3A.(state1) c_3A.(tape) agrees with
     ag1_run1 (T_sweep_z 116 26) 114 StD c_b30.(tape) on z < 149! *)

  (* Let's state the clean decoupling for Phase 3B1: n1 = 27 * q_big steps, mid = 149 *)
  (* Note: T_sweep_z 116 26 + 3 + T_sweep1 142 = 27 * 2^141 - 138.
     So (27 * 2^141 - 138) - 14 = 27 * 2^141 - 152 > 27 * q_big = 27 * 2^141 - 162! *)
  assert (H3B1_len : (27 * q_big < T_sweep_z 116 26 + 3 + T_sweep1 142 - 14)%nat).
  { unfold T_sweep_z, T_sweep1, q_big.
    replace (116 + 26 - 1)%nat with 141%nat by lia.
    assert (H2_142 : (2 ^ 142 = 2 * 2 ^ 141)%nat) by (simpl; lia).
    assert (H2_141 : (1000 <= 2 ^ 141)%nat).
    { clear. assert (H10 : (1024 = 2 ^ 10)%nat) by reflexivity.
      assert (Hpow : (2 ^ 10 <= 2 ^ 141)%nat) by (apply Nat.pow_le_mono_r; lia). lia. }
    lia. }

  (* For ag1 on c_3A.(tape): since c_3A.(tape) agrees with t1_3A on z < 149,
     and ag1_run1 (k + 14) 114 StD c_b30.(tape) stays <= 142 < 149 for k < T_full - 14,
     ag1 stays < 149 for all k < 27 * q_big! *)
  assert (H3B1_ag1_full :
    let T_full := (T_sweep_z 116 26 + 3 + T_sweep1 142)%nat in
    let '(p', s', t') := ag1_run1 T_full 114 StD c_b30.(tape) in
    p' = 142 /\ s' = StA /\
    (forall u, -1 <= u <= 142 -> t' u = true) /\
    (forall u, u < -1 \/ u > 142 -> t' u = c_b30.(tape) u) /\
    (forall k, (k < T_full)%nat ->
      let '(pk, _, _) := ag1_run1 k 114 StD c_b30.(tape) in -1 <= pk <= 142)).
  { intros T_full.
    destruct (ag1_run1 (T_sweep_z 116 26) 114 StD c_b30.(tape)) as [[p1 s1] t1] eqn:Es1.
    destruct Hsw26 as [Hp1 [Hs1 [H1ones [H1out H1bd]]]]. subst p1 s1.
    assert (Ht1_141 : t1 141 = true) by (rewrite H1out by lia; pose proof (Bstp (141-114)) as H; simpl in H; replace (141-114- -114) with 141 in H by lia; rewrite <- H, <- Btp by lia, <- Ftp; exact O27).
    assert (Ht1_142 : t1 142 = false) by (rewrite H1out by lia; pose proof (Bstp (142-114)) as H; simpl in H; replace (142-114- -114) with 142 in H by lia; rewrite <- H, <- Btp by lia, <- Ftp; exact O28).
    assert (H3s :
      let '(p2, s2, t2) := ag1_run1 3 141 StA t1 in
      p2 = 140 /\ s2 = StD /\
      (forall u, -1 <= u <= 140 -> t2 u = true) /\
      t2 141 = false /\ t2 142 = true /\
      (forall u, u < -1 \/ u > 142 -> t2 u = t1 u) /\
      (forall k, (k < 3)%nat ->
        let '(pk, _, _) := ag1_run1 k 141 StA t1 in -1 <= pk <= 142)).
    { unfold ag1_run1. simpl. unfold ag1_step1.
      rewrite Ht1_141. simpl. rewrite write_tape_other by lia. rewrite Ht1_142. simpl.
      rewrite write_tape_other by lia. rewrite H1ones by lia. simpl.
      repeat split; try lia; try reflexivity.
      - intros u Hu. unfold write_tape.
        destruct (Z.eqb_spec u 141); [lia|].
        destruct (Z.eqb_spec u 142); [lia|].
        apply H1ones; lia.
      - unfold write_tape. rewrite Z.eqb_refl. reflexivity.
      - unfold write_tape. destruct (Z.eqb_spec 142 141); [lia|]. rewrite Z.eqb_refl. reflexivity.
      - intros u Hu. unfold write_tape.
        repeat (destruct (Z.eqb_spec u _); [lia|]). reflexivity.
      - intros k Hk. destruct k as [|[|]]; try lia; simpl; lia. }
    destruct (ag1_run1 3 141 StA t1) as [[p2 s2] t2] eqn:Es2.
    destruct H3s as [Hp2 [Hs2 [H2ones [H2_141 [H2_142 [H2out H2bd]]]]]]. subst p2 s2.
    pose proof (sweep_D_1 141 140 t2 ltac:(intros u Hu; apply H2ones; lia) H2_141) as Hsw1.
    replace (S 141) with 142%nat in Hsw1 by lia.
    destruct (ag1_run1 (T_sweep1 142) 140 StD t2) as [[p3 s3] t3] eqn:Es3.
    destruct Hsw1 as [Hp3 [Hs3 [H3ones [H3out H3bd]]]].
    unfold T_full.
    replace (T_sweep_z 116 26 + 3 + T_sweep1 142)%nat
      with (T_sweep1 142 + (3 + T_sweep_z 116 26))%nat by lia.
    rewrite !ag1_run1_add, Es1, Es2, Es3.
    repeat split; try lia; auto.
    + intros u Hu. destruct (Z.eqb_spec u 142) as [->|Hneq].
      * rewrite H3out by lia. exact H2_142.
      * apply H3ones. lia.
    + intros u Hu. rewrite H3out by lia. rewrite H2out by lia. apply H1out. lia.
    + intros k Hk.
      destruct (lt_dec k (T_sweep_z 116 26)) as [Hk1|Hge1].
      { specialize (H1bd k Hk1). destruct (ag1_run1 _ _ _ _); lia. }
      replace k with ((k - T_sweep_z 116 26) + T_sweep_z 116 26)%nat by lia.
      rewrite ag1_run1_add, Es1.
      destruct (lt_dec (k - T_sweep_z 116 26) 3) as [Hk2|Hge2].
      { specialize (H2bd _ Hk2). destruct (ag1_run1 _ _ _ _); lia. }
      replace (k - T_sweep_z 116 26)%nat with ((k - T_sweep_z 116 26 - 3) + 3)%nat by lia.
      rewrite ag1_run1_add, Es2.
      specialize (H3bd _ ltac:(lia)). destruct (ag1_run1 _ _ _ _); lia. }

  (* Now apply decouple_run for 27 * q_big steps from c_3A with mid = 149 *)
  (* Note: ag1_run1 agrees on z < 149 between c_3A.(tape) and t1_3A *)
  assert (Hc3A_ag1_agree : forall k, (k <= T_sweep_z 116 26 + 3 + T_sweep1 142 - 14)%nat ->
    let '(pa, sa, ta) := ag1_run1 k c_3A.(pos1) c_3A.(state1) c_3A.(tape) in
    let '(pb, sb, tb) := ag1_run1 (k + 14) 114 StD c_b30.(tape) in
    pa = pb /\ sa = sb /\ (forall z, z < 149 -> ta z = tb z)).
  { induction k; intros Hk.
    - simpl. rewrite A3p1, A3s1, Hc_b30_p1, Hc_b30_s1, E1_3A.
      repeat split; auto. intros z Hz. apply A3t1; exact Hz.
    - specialize (IHk ltac:(lia)).
      replace (S k + 14)%nat with (1 + (k + 14))%nat by lia.
      replace (S k) with (1 + k)%nat by lia.
      rewrite !ag1_run1_add.
      destruct (ag1_run1 k c_3A.(pos1) c_3A.(state1) c_3A.(tape)) as [[pa sa] ta] eqn:Ea.
      destruct (ag1_run1 (k + 14) 114 StD c_b30.(tape)) as [[pb sb] tb] eqn:Eb.
      destruct IHk as [Hp [Hs Ht]]. subst pb sb.
      assert (Hpa : pa <= 142).
      { destruct H3B1_ag1_full as [_ [_ [_ [_ Hbd]]]].
        specialize (Hbd (k + 14)%nat ltac:(lia)). rewrite Eb in Hbd. lia. }
      simpl. unfold ag1_step1. rewrite (Ht pa ltac:(lia)).
      repeat split; auto. intros z Hz. unfold write_tape.
      destruct (Z.eqb_spec z pa); [reflexivity | apply Ht; exact Hz]. }

  assert (H3B1_1 : forall k, (k < 27 * q_big)%nat ->
    let '(p1, _, _) := ag1_run1 k c_3A.(pos1) c_3A.(state1) c_3A.(tape) in p1 < 149).
  { intros k Hk.
    pose proof (Hc3A_ag1_agree k ltac:(lia)) as Hag.
    destruct (ag1_run1 k c_3A.(pos1) c_3A.(state1) c_3A.(tape)) as [[pa ?] ?].
    destruct (ag1_run1 (k + 14) 114 StD c_b30.(tape)) as [[pb ?] ?] eqn:Eb.
    destruct Hag as [Hp _].
    destruct H3B1_ag1_full as [_ [_ [_ [_ Hbd]]]].
    specialize (Hbd (k + 14)%nat ltac:(lia)). rewrite Eb in Hbd. lia. }
  assert (H3B1_2 : forall k, (k < 27 * q_big)%nat ->
    let '(p2, _, _) := ag2_run1 k c_3A.(pos2) c_3A.(state2) c_3A.(tape) in 149 <= p2).
  { intros k Hk. rewrite Hc3A_p2, Hc3A_s2.
    pose proof (glider_loop_27 q_big 152 c_3A.(tape) Hc3A_gl Hc3A_far) as [_ [_ [_ [_ [_ [_ Hbd]]]]]].
    specialize (Hbd k Hk). destruct (ag2_run1 k 152 StB c_3A.(tape)); lia. }

  pose proof (decouple_run (27 * q_big) 149 c_3A H3B1_1 H3B1_2) as H3B1.
  set (c_3B1 := run_N ag1 ag2 (N.of_nat (27 * q_big)) c_3A) in *.
  destruct (ag1_run1 (27 * q_big) c_3A.(pos1) c_3A.(state1) c_3A.(tape)) as [[p1_3B1 s1_3B1] t1_3B1] eqn:E1_3B1.
  destruct (ag2_run1 (27 * q_big) c_3A.(pos2) c_3A.(state2) c_3A.(tape)) as [[p2_3B1 s2_3B1] t2_3B1] eqn:E2_3B1.
  destruct H3B1 as [B1p1 [B1s1 [B1p2 [B1s2 [B1t1 [B1t2 B1nc]]]]]].

  (* Substep 3B2: Final 27 steps from c_3B1 with mid = 160 *)
  (* Note: at c_3B1, ag2 is at 152 + q_big >> 160, and ag1 finishes its remaining 10 sweep steps + 17 walk steps to 159! *)
  assert (Hrem27 : (27 * q_big + 14 + 27 = (T_sweep_z 116 26 + 3 + T_sweep1 142) + 17)%nat).
  { unfold q_big, T_sweep_z, T_sweep1.
    replace (116 + 26 - 1)%nat with 141%nat by lia.
    assert (H2_142 : (2 ^ 142 = 2 * 2 ^ 141)%nat) by (simpl; lia).
    assert (H2_141 : (1000 <= 2 ^ 141)%nat).
    { clear. assert (H10 : (1024 = 2 ^ 10)%nat) by reflexivity.
      assert (Hpow : (2 ^ 10 <= 2 ^ 141)%nat) by (apply Nat.pow_le_mono_r; lia). lia. }
    lia. }

  assert (Hq_big_val : (1000 <= Z.of_nat q_big)%Z).
  { unfold q_big. assert (H10 : (1024 = 2 ^ 10)%nat) by reflexivity.
    assert (Hpow : (2 ^ 10 <= 2 ^ 141)%nat) by (apply Nat.pow_le_mono_r; lia). lia. }

  (* Check c_3B1.(pos2), state2, has_glider, far *)
  pose proof (glider_loop_27 q_big 152 c_3A.(tape) Hc3A_gl Hc3A_far) as Hgl_3B1.
  rewrite Hc3A_p2, Hc3A_s2 in E2_3B1. rewrite E2_3B1 in Hgl_3B1.
  destruct Hgl_3B1 as [G3p2 [G3s2 [G3ones [G3gl [G3out [G3far _]]]]]].
  assert (Hc3B1_p2 : c_3B1.(pos2) = 152 + Z.of_nat q_big) by lia.
  assert (Hc3B1_s2 : c_3B1.(state2) = StB) by congruence.
  assert (Hc3B1_gl : has_glider (152 + Z.of_nat q_big) c_3B1.(tape)).
  { unfold has_glider in *. destruct G3gl as [A1 [A2 [A3 [A4 [A5 A6]]]]].
    repeat split; rewrite B1t2 by lia; assumption. }
  assert (Hc3B1_far : forall z, z >= 152 + Z.of_nat q_big + 3 -> c_3B1.(tape) z = false).
  { intros z Hz. rewrite B1t2 by lia. apply G3far. lia. }

  assert (H3B2_2 : forall k, (k < 27)%nat ->
    let '(p2, _, _) := ag2_run1 k c_3B1.(pos2) c_3B1.(state2) c_3B1.(tape) in 160 <= p2).
  { intros k Hk. rewrite Hc3B1_p2, Hc3B1_s2.
    pose proof (glider_27_step (152 + Z.of_nat q_big) c_3B1.(tape) Hc3B1_gl Hc3B1_far)
      as [_ [_ [_ [_ [_ Hbd]]]]].
    specialize (Hbd k Hk). destruct (ag2_run1 k _ _ _); lia. }

  (* For ag1 during 27 steps from c_3B1:
     Notice on z < 149, c_3B1.(tape) = t1_3B1, and on 143 <= z <= 148, t2_3A = c_3A.(tape) = true,
     while on z >= 149, G3ones gives [149 .. 152 + q_big - 3] = true!
     Wait: at step 27*q_big, ag1 is STILL inside T_full (10 steps remaining), so for k <= 10, ag1 <= 142 < 149!
     At k = 10, ag1 reaches 142(StA) with [-1..142] all true, and [143..159] are ALREADY all true!
     Then in 17 steps, walk_A_ones 17 142 walks 142 -> 159 (< 160)! *)
  assert (H3B2_ag1 :
    let '(p1', s1', t1') := ag1_run1 27 c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape) in
    p1' = 159 /\ s1' = StA /\
    (forall u, 143 <= u < 160 -> t1' u = true) /\
    (forall u, u >= 160 -> t1' u = c_3B1.(tape) u) /\
    (forall k, (k < 27)%nat ->
      let '(pk, _, _) := ag1_run1 k c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape) in pk < 160)).
  { set (T_full := (T_sweep_z 116 26 + 3 + T_sweep1 142)%nat).
    set (k_rem := (T_full - (27 * q_big + 14))%nat).
    assert (Hk_rem : (k_rem + 17 = 27)%nat) by (unfold k_rem, T_full; lia).
    assert (H14_rem : (k_rem + (27 * q_big + 14) = T_full)%nat) by (unfold k_rem, T_full; lia).
    (* First k_rem steps stay <= 142 < 149 and reach 142(StA) *)
    assert (Hrem_agree : forall j, (j <= k_rem)%nat ->
      let '(pa, sa, ta) := ag1_run1 j c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape) in
      let '(pb, sb, tb) := ag1_run1 (j + (27 * q_big + 14)) 114 StD c_b30.(tape) in
      pa = pb /\ sa = sb /\ (forall z, z < 149 -> ta z = tb z) /\
      (forall z, z >= 149 -> ta z = c_3B1.(tape) z)).
    { induction j; intros Hj.
      - simpl.
        pose proof (Hc3A_ag1_agree (27 * q_big)%nat ltac:(lia)) as Hag.
        rewrite E1_3B1 in Hag.
        destruct (ag1_run1 (27 * q_big + 14) 114 StD c_b30.(tape)) as [[pb sb] tb].
        destruct Hag as [Hp [Hs Ht]].
        repeat split; try lia; try congruence.
        + intros z Hz. rewrite B1t1 by lia. apply Ht; exact Hz.
      - specialize (IHj ltac:(lia)).
        replace (S j) with (1 + j)%nat by lia.
        replace (S j + (27 * q_big + 14))%nat with (1 + (j + (27 * q_big + 14)))%nat by lia.
        rewrite !ag1_run1_add.
        destruct (ag1_run1 j c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape)) as [[pa sa] ta] eqn:Ea.
        destruct (ag1_run1 (j + (27 * q_big + 14)) 114 StD c_b30.(tape)) as [[pb sb] tb] eqn:Eb.
        destruct IHj as [Hp [Hs [Ht_l Ht_r]]]. subst pb sb.
        assert (Hpa : pa <= 142).
        { destruct H3B1_ag1_full as [_ [_ [_ [_ Hbd]]]].
          specialize (Hbd (j + (27 * q_big + 14))%nat ltac:(lia)). rewrite Eb in Hbd. lia. }
        simpl. unfold ag1_step1. rewrite (Ht_l pa ltac:(lia)).
        repeat split; auto.
        + intros z Hz. unfold write_tape. destruct (Z.eqb_spec z pa); [reflexivity | apply Ht_l; exact Hz].
        + intros z Hz. unfold write_tape. destruct (Z.eqb_spec z pa); [lia | apply Ht_r; exact Hz]. }
    pose proof (Hrem_agree k_rem ltac:(lia)) as Hkr.
    rewrite H14_rem in Hkr.
    destruct (ag1_run1 k_rem c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape)) as [[p_kr s_kr] t_kr] eqn:Ekr.
    destruct (ag1_run1 T_full 114 StD c_b30.(tape)) as [[p_f s_f] t_f] eqn:Ef.
    destruct H3B1_ag1_full as [Hf_p [Hf_s [Hf_ones [Hf_out Hf_bd]]]]. subst p_f s_f.
    destruct Hkr as [Hkr_p [Hkr_s [Hkr_l Hkr_r]]]. subst p_kr s_kr.
    (* Check t_kr is all true on [143..159] *)
    assert (Htkr_ones : forall u, 142 <= u < 142 + Z.of_nat 17 -> t_kr u = true).
    { intros u Hu. destruct (Z_lt_ge_dec u 149) as [Hlt|Hge].
      - rewrite Hkr_l by lia.
        destruct (Z.eqb_spec u 142) as [->|Hneq]; [apply Hf_ones; lia|].
        rewrite Hf_out by lia.
        (* c_b30.(tape) u for 143..148 -> true! *)
        assert (u - 114 = 29 \/ u - 114 = 30 \/ u - 114 = 31 \/
                u - 114 = 32 \/ u - 114 = 33 \/ u - 114 = 34)
          as Hu_cases by lia.
        pose proof (Bstp (u - 114)) as H1. simpl in H1. replace (u - 114 - -114) with u in H1 by lia.
        rewrite <- H1, <- Btp by lia, <- Ftp.
        destruct Hu_cases as [->|[->|[->|[->|[->| ->]]]]]; assumption.
      - rewrite Hkr_r by lia. rewrite B1t2 by lia. apply G3ones. lia. }
    pose proof (walk_A_ones 17 142 t_kr Htkr_ones) as Hwk.
    rewrite <- Hk_rem, Nat.add_comm, ag1_run1_add, Ekr.
    destruct (ag1_run1 17 142 StA t_kr) as [[p1' s1'] t1'] eqn:Ewk.
    destruct Hwk as [Hwp [Hws [Hwt Hwbd]]].
    repeat split; try lia; auto.
    + intros u Hu. rewrite Hwt. apply Htkr_ones. lia.
    + intros u Hu. rewrite Hwt. apply Hkr_r. lia.
    + intros k Hk.
      destruct (lt_dec k k_rem) as [Hlt|Hge].
      * pose proof (Hrem_agree k ltac:(lia)) as [Hkp _].
        destruct (ag1_run1 k c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape)) as [[pk ?] ?].
        destruct (ag1_run1 (k + (27 * q_big + 14)) 114 StD c_b30.(tape)) as [[pf ?] ?] eqn:Epf.
        specialize (Hf_bd (k + (27 * q_big + 14))%nat ltac:(lia)). rewrite Epf in Hf_bd. lia.
      * replace k with ((k - k_rem) + k_rem)%nat by lia.
        rewrite ag1_run1_add, Ekr.
        specialize (Hwbd (k - k_rem)%nat ltac:(lia)).
        destruct (ag1_run1 (k - k_rem) 142 StA t_kr) as [[pk ?] ?]. lia. }

  assert (H3B2_1 : forall k, (k < 27)%nat ->
    let '(p1, _, _) := ag1_run1 k c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape) in p1 < 160).
  { intros k Hk. destruct (ag1_run1 27 c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape)) as [[? ?] ?].
    destruct H3B2_ag1 as [_ [_ [_ [_ Hbd]]]]. exact (Hbd k Hk). }

  pose proof (decouple_run 27 160 c_3B1 H3B2_1 H3B2_2) as H3B2.
  change (N.of_nat 27) with 27%N in H3B2.
  set (c_sync := run_N ag1 ag2 27 c_3B1) in *.
  destruct (ag1_run1 27 c_3B1.(pos1) c_3B1.(state1) c_3B1.(tape)) as [[p1_s s1_s] t1_s] eqn:E1_s.
  destruct (ag2_run1 27 c_3B1.(pos2) c_3B1.(state2) c_3B1.(tape)) as [[p2_s s2_s] t2_s] eqn:E2_s.
  destruct H3B2 as [Sp1 [Ss1 [Sp2 [Ss2 [St1 [St2 Snc]]]]]].
  destruct H3B2_ag1 as [Hsp1 [Hss1 [Hsones [Hsfar _]]]]. subst p1_s s1_s.
  pose proof (glider_27_step (152 + Z.of_nat q_big) c_3B1.(tape) Hc3B1_gl Hc3B1_far) as Hgl_s.
  rewrite Hc3B1_p2, Hc3B1_s2 in E2_s. rewrite E2_s in Hgl_s.
  destruct Hgl_s as [Gsp2 [Gss2 [Gsm3 [Gsgl [Gsout _]]]]]. subst p2_s s2_s.

  (* Step 4: Chase 27 * k_close steps from c_sync *)
  set (k_nat := N.to_nat k_close).
  assert (Hk_nat_N : N.of_nat k_nat = k_close) by (unfold k_nat; apply N2Nat.id).
  assert (Hgap_chase : 159 + 32 + 26 * Z.of_nat k_nat <= 152 + Z.of_nat q_big + 1).
  { unfold q_big. rewrite <- Z_of_N_nat, Hk_nat_N.
    pose proof k_close_exact as Hke.
    assert (H2_141_N : (1000 <= 2 ^ 141)%N) by (vm_compute; discriminate).
    lia. }
  assert (Hsync_ones : forall z, 159 <= z < (152 + Z.of_nat q_big + 1) - 3 -> c_sync.(tape) z = true).
  { intros z Hz. destruct (Z_lt_ge_dec z 160) as [Hlt|Hge].
    - rewrite St1 by lia. apply Hsones. lia.
    - rewrite St2 by lia.
      destruct (Z.eqb_spec z (152 + Z.of_nat q_big - 3)) as [->|Hneq].
      + exact Gsm3.
      + rewrite Gsout by lia. rewrite B1t2 by lia. apply G3ones. lia. }
  assert (Hsync_gl : has_glider (152 + Z.of_nat q_big + 1) c_sync.(tape)).
  { unfold has_glider in *. destruct Gsgl as [A1 [A2 [A3 [A4 [A5 A6]]]]].
    repeat split; rewrite St2 by lia; assumption. }
  assert (Hsync_far : forall z, z >= 152 + Z.of_nat q_big + 1 + 3 -> c_sync.(tape) z = false).
  { intros z Hz. rewrite St2 by lia. rewrite Gsout by lia. apply Hc3B1_far. lia. }

  pose proof (chase_27_loop k_nat 159 (152 + Z.of_nat q_big + 1) c_sync Hgap_chase
                Sp1 Sp2 Ss1 Ss2 Hsync_ones Hsync_gl Hsync_far) as Hchase.
  rewrite Hk_nat_N in Hchase.
  set (c_final := run_N ag1 ag2 (27 * k_close) c_sync) in *.
  destruct Hchase as [Cp1 [Cp2 [Cs1 [Cs2 [Cones [Cgl [Cfar Cnc]]]]]]].

  (* Step 5: Final 30 steps at gap = 32 *)
  assert (Hcf_gap : c_final.(pos2) = c_final.(pos1) + 32).
  { rewrite Cp1, Cp2. rewrite <- Z_of_N_nat, Hk_nat_N.
    pose proof k_close_exact as Hke.
    unfold q_big.
    assert (H2_141_N : (1000 <= 2 ^ 141)%N) by (vm_compute; discriminate).
    lia. }
  assert (Hcf_ones : forall z, c_final.(pos1) <= z <= c_final.(pos1) + 28 -> c_final.(tape) z = true)
    by (intros z Hz; apply Cones; lia).
  assert (Hcf_gl : has_glider (c_final.(pos1) + 32) c_final.(tape))
    by (rewrite <- Hcf_gap; exact Cgl).
  assert (Hcf_far : forall z, z >= c_final.(pos1) + 35 -> c_final.(tape) z = false)
    by (intros z Hz; apply Cfar; lia).

  pose proof (halt_32_step c_final.(pos1) c_final eq_refl Hcf_gap Cs1 Cs2 Hcf_ones Hcf_gl Hcf_far)
    as [Hf_nc Hf_coll].

  (* Combine all phases into exact_T_halt! *)
  assert (HT_comb : exact_T_halt = (30 + (27 * k_close + (27 + (N.of_nat (27 * q_big) + (14 + (160 + 3720))))))%N).
  { unfold exact_T_halt.
    (* Actually: N.of_nat (27 * q_big) = 27 * (2^141 - 6) *)
    assert (HqN : N.of_nat (27 * q_big) = (27 * (2 ^ 141 - 6))%N).
    { unfold q_big. rewrite Nat2N.inj_mul, Nat2N.inj_sub, Nat2N.inj_pow.
      change (N.of_nat 27) with 27%N. change (N.of_nat 2) with 2%N.
      change (N.of_nat 141) with 141%N. change (N.of_nat 6) with 6%N.
      reflexivity. }
    rewrite HqN.
    assert (H2_141_N : (1000 <= 2 ^ 141)%N) by (vm_compute; discriminate).
    lia. }
  unfold halts_at_exact, collides_at.
  rewrite HT_comb.
  split.
  - rewrite !run_N_add.
    fold c_r2. fold c_b30. fold c_3A. fold c_3B1. fold c_sync. fold c_final.
    exact Hf_coll.
  - intros t Ht.
    assert (Hnc1 : forall k, (k < 160 + 3720)%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
      by (intros k Hk; eapply no_coll_add; [exact Pnc | exact Hb30_nc | exact Hk]).
    assert (Hnc2 : forall k, (k < 14 + (160 + 3720))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
      by (intros k Hk; eapply no_coll_add; [exact Hnc1 | rewrite run_N_add; exact A3nc | exact Hk]).
    assert (Hnc3 : forall k, (k < N.of_nat (27 * q_big) + (14 + (160 + 3720)))%N ->
                     (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
      by (intros k Hk; eapply no_coll_add; [exact Hnc2 | rewrite !run_N_add; exact B1nc | exact Hk]).
    assert (Hnc4 : forall k, (k < 27 + (N.of_nat (27 * q_big) + (14 + (160 + 3720))))%N ->
                     (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
      by (intros k Hk; eapply no_coll_add; [exact Hnc3 | rewrite !run_N_add; exact Snc | exact Hk]).
    assert (Hnc5 : forall k, (k < 27 * k_close + (27 + (N.of_nat (27 * q_big) + (14 + (160 + 3720)))))%N ->
                     (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
      by (intros k Hk; eapply no_coll_add; [exact Hnc4 | rewrite !run_N_add; exact Cnc | exact Hk]).
    eapply no_coll_add; [exact Hnc5 | | exact Ht].
    rewrite !run_N_add. fold c_r2 c_b30 c_3A c_3B1 c_sync c_final. exact Hf_nc.
Qed.

Print Assumptions cet4_7e43_halts.
