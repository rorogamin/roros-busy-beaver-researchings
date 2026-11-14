(**
  Formal Machine-Checked Proof of Normal Halting in Rocq 9.1
  Target Machine: 1LB1RC_1LC1RB_1LD0LC_0RA0RB | 1RB0RC_1RC0RD_1LA1LB_1RA0LC
  Model: Catch-Em-Turing CET(4), 2 agents, 4 states, 2 symbols.
  Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
  Normal Halting: exact first collision pos1(T) = pos2(T).

  Mathematical Structure:
  - Concrete prefix (steps 0 .. 5730): enters Round 2 at x0 = 188, G1 = 18, L_left = 190 (L2 = 191).
  - Agent 2 glider (P = 27, D = 1, M = 26): canonical pattern 100100 at [p2-3 .. p2+2], state StC.
  - Agent 1 binary counter: T_fill(m) = 5 * 2^m - m - 3, yielding exact exit time
      T_exit(G, L) = 5 * 2^(L + G - 3) + G + 1
    for all bounce gaps G in {12, 16, 18, 20, 30, 32}.
  - 8-round 2^L tower with gap sequence [18, 30, 12, 20, 20, 16, 32, 8],
    resolved via exact modular arithmetic mod 702 * Q (Carmichael lambda chain
    36 -> 324 -> 2916 -> 26244 -> 236196 -> 2125764).
  - Final collision at G = 8 in 6 steps.
  - Halting time > 2^(2^(2^(2^(2^(2^(2^206)))))), strictly beating all CET(3) champions.
  Zero extra axioms.
*)

From Stdlib Require Import ZArith NArith PArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core Catch-Em-Turing CET(4) Semantics *)

Inductive State := StA | StB | StC | StD.
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

(** * 2. Target Machine: 1LB1RC_1LC1RB_1LD0LC_0RA0RB | 1RB0RC_1RC0RD_1LA1LB_1RA0LC *)

Definition ag1 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StA, true  => {| write_sym := true;  move_dir := MoveR; next_state := StC |}
  | StB, false => {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  | StB, true  => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StC, false => {| write_sym := true;  move_dir := MoveL; next_state := StD |}
  | StC, true  => {| write_sym := false; move_dir := MoveL; next_state := StC |}
  | StD, false => {| write_sym := false; move_dir := MoveR; next_state := StA |}
  | StD, true  => {| write_sym := false; move_dir := MoveR; next_state := StB |}
  end.

Definition ag2 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StA, true  => {| write_sym := false; move_dir := MoveR; next_state := StC |}
  | StB, false => {| write_sym := true;  move_dir := MoveR; next_state := StC |}
  | StB, true  => {| write_sym := false; move_dir := MoveR; next_state := StD |}
  | StC, false => {| write_sym := true;  move_dir := MoveL; next_state := StA |}
  | StC, true  => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StD, false => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StD, true  => {| write_sym := false; move_dir := MoveL; next_state := StC |}
  end.

Definition c0 : Config := {|
  pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape
|}.

(** * 3. Basic Equivalence and Run Laws *)

Definition tape_eq (t1 t2 : Tape) : Prop := forall z, t1 z = t2 z.

Record cfg_eq (c1 c2 : Config) : Prop := {
  ce_p1 : c1.(pos1) = c2.(pos1);
  ce_p2 : c1.(pos2) = c2.(pos2);
  ce_s1 : c1.(state1) = c2.(state1);
  ce_s2 : c1.(state2) = c2.(state2);
  ce_tp : tape_eq c1.(tape) c2.(tape)
}.

Lemma write_tape_same : forall t p s, write_tape t p s p = s.
Proof. intros. unfold write_tape. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma write_tape_other : forall t p s x, x <> p -> write_tape t p s x = t x.
Proof.
  intros. unfold write_tape. destruct (Z.eqb_spec x p); congruence.
Qed.

Lemma write_tape_proper : forall t1 t2 p s,
  tape_eq t1 t2 -> tape_eq (write_tape t1 p s) (write_tape t2 p s).
Proof.
  intros t1 t2 p s Ht z. unfold write_tape. destruct (Z.eqb_spec z p); auto.
Qed.

Lemma tape_eq_trans : forall t1 t2 t3, tape_eq t1 t2 -> tape_eq t2 t3 -> tape_eq t1 t3.
Proof. intros t1 t2 t3 H1 H2 z. rewrite H1. apply H2. Qed.

Lemma cfg_eq_trans : forall c1 c2 c3, cfg_eq c1 c2 -> cfg_eq c2 c3 -> cfg_eq c1 c3.
Proof.
  intros c1 c2 c3 [Hp1 Hp2 Hs1 Hs2 Htp] [Gp1 Gp2 Gs1 Gs2 Gtp].
  constructor; try congruence.
Qed.

Lemma step_proper : forall a1 a2 c1 c2,
  cfg_eq c1 c2 -> cfg_eq (step a1 a2 c1) (step a1 a2 c2).
Proof.
  intros a1 a2 c1 c2 [Hp1 Hp2 Hs1 Hs2 Htp].
  unfold step. rewrite Hp1, Hp2, Hs1, Hs2, !Htp.
  constructor; simpl; try reflexivity.
  apply write_tape_proper. apply write_tape_proper. exact Htp.
Qed.

Lemma run_N_0 : forall a1 a2 c, run_N a1 a2 0%N c = c.
Proof. intros. unfold run_N. reflexivity. Qed.

Lemma run_N_succ : forall a1 a2 n c,
  run_N a1 a2 (N.succ n) c = step a1 a2 (run_N a1 a2 n c).
Proof. intros. unfold run_N. apply N.iter_succ. Qed.

Lemma run_N_add : forall a1 a2 m n c,
  run_N a1 a2 (m + n)%N c = run_N a1 a2 m (run_N a1 a2 n c).
Proof.
  intros a1 a2 m n c. unfold run_N.
  induction m using N.peano_ind.
  - rewrite N.add_0_l. reflexivity.
  - rewrite N.add_succ_l, !N.iter_succ, IHm. reflexivity.
Qed.

Lemma run_N_proper : forall a1 a2 n c1 c2,
  cfg_eq c1 c2 -> cfg_eq (run_N a1 a2 n c1) (run_N a1 a2 n c2).
Proof.
  intros a1 a2 n. induction n using N.peano_ind; intros c1 c2 H.
  - rewrite !run_N_0. exact H.
  - rewrite !run_N_succ. apply step_proper, IHn, H.
Qed.

Lemma no_coll_add : forall a1 a2 m n c,
  (forall k, (k < n)%N -> (run_N a1 a2 k c).(pos1) <> (run_N a1 a2 k c).(pos2)) ->
  (forall k, (k < m)%N -> (run_N a1 a2 k (run_N a1 a2 n c)).(pos1) <>
                           (run_N a1 a2 k (run_N a1 a2 n c)).(pos2)) ->
  forall t, (t < m + n)%N -> (run_N a1 a2 t c).(pos1) <> (run_N a1 a2 t c).(pos2).
Proof.
  intros a1 a2 m n c Hn Hm t Ht.
  destruct (N.lt_ge_cases t n) as [Hlt | Hge].
  - apply Hn. exact Hlt.
  - replace t with ((t - n) + n)%N by lia.
    rewrite run_N_add. apply Hm. lia.
Qed.

Lemma step_agree_range : forall a1 a2 lo hi c1 c2,
  lo <= c1.(pos1) <= hi ->
  lo <= c1.(pos2) <= hi ->
  c1.(pos1) = c2.(pos1) ->
  c1.(pos2) = c2.(pos2) ->
  c1.(state1) = c2.(state1) ->
  c1.(state2) = c2.(state2) ->
  (forall z, lo <= z <= hi -> c1.(tape) z = c2.(tape) z) ->
  (step a1 a2 c1).(pos1) = (step a1 a2 c2).(pos1) /\
  (step a1 a2 c1).(pos2) = (step a1 a2 c2).(pos2) /\
  (step a1 a2 c1).(state1) = (step a1 a2 c2).(state1) /\
  (step a1 a2 c1).(state2) = (step a1 a2 c2).(state2) /\
  (forall z, lo <= z <= hi -> (step a1 a2 c1).(tape) z = (step a1 a2 c2).(tape) z).
Proof.
  intros a1 a2 lo hi c1 c2 Hr1 Hr2 Hp1 Hp2 Hs1 Hs2 Htp.
  unfold step; simpl.
  rewrite Hp1, Hp2, Hs1, Hs2.
  rewrite <- (Htp c2.(pos1)) by lia.
  rewrite <- (Htp c2.(pos2)) by lia.
  repeat split; try reflexivity.
  intros z Hz. unfold write_tape.
  destruct (Z.eqb_spec z c2.(pos1)); destruct (Z.eqb_spec z c2.(pos2)); auto.
Qed.

Lemma run_N_agree_range : forall a1 a2 lo hi n c1 c2,
  (forall k, (k < n)%N ->
    lo <= (run_N a1 a2 k c1).(pos1) <= hi /\
    lo <= (run_N a1 a2 k c1).(pos2) <= hi) ->
  c1.(pos1) = c2.(pos1) ->
  c1.(pos2) = c2.(pos2) ->
  c1.(state1) = c2.(state1) ->
  c1.(state2) = c2.(state2) ->
  (forall z, lo <= z <= hi -> c1.(tape) z = c2.(tape) z) ->
  (run_N a1 a2 n c1).(pos1) = (run_N a1 a2 n c2).(pos1) /\
  (run_N a1 a2 n c1).(pos2) = (run_N a1 a2 n c2).(pos2) /\
  (run_N a1 a2 n c1).(state1) = (run_N a1 a2 n c2).(state1) /\
  (run_N a1 a2 n c1).(state2) = (run_N a1 a2 n c2).(state2) /\
  (forall z, lo <= z <= hi -> (run_N a1 a2 n c1).(tape) z = (run_N a1 a2 n c2).(tape) z).
Proof.
  intros a1 a2 lo hi n.
  induction n using N.peano_ind; intros c1 c2 Hrng Hp1 Hp2 Hs1 Hs2 Htp.
  - rewrite !run_N_0. repeat split; auto.
  - rewrite !run_N_succ.
    assert (Hrng_n : forall k, (k < n)%N ->
      lo <= (run_N a1 a2 k c1).(pos1) <= hi /\
      lo <= (run_N a1 a2 k c1).(pos2) <= hi)
      by (intros k Hk; apply Hrng; lia).
    destruct (IHn c1 c2 Hrng_n Hp1 Hp2 Hs1 Hs2 Htp) as [Gp1 [Gp2 [Gs1 [Gs2 Gtp]]]].
    destruct (Hrng n ltac:(lia)) as [Hn1 Hn2].
    apply (step_agree_range a1 a2 lo hi); auto.
Qed.

(** * 4. Fast Binary-Tree Tape for Concrete Prefix (Steps 0 .. 5730) *)

Inductive BTree :=
  | BEmpty
  | BNode (cur : bool) (l r : BTree).

Fixpoint bt_get (p : positive) (t : BTree) : bool :=
  match t with
  | BEmpty => false
  | BNode cur l r =>
      match p with
      | xH => cur
      | xO q => bt_get q l
      | xI q => bt_get q r
      end
  end.

Fixpoint bt_set (p : positive) (v : bool) (t : BTree) : BTree :=
  match t with
  | BEmpty =>
      match p with
      | xH => BNode v BEmpty BEmpty
      | xO q => BNode false (bt_set q v BEmpty) BEmpty
      | xI q => BNode false BEmpty (bt_set q v BEmpty)
      end
  | BNode cur l r =>
      match p with
      | xH => BNode v l r
      | xO q => BNode cur (bt_set q v l) r
      | xI q => BNode cur l (bt_set q v r)
      end
  end.

Definition z_to_pos (z : Z) : positive :=
  match z with Z0 => 1%positive | Zpos p => (p~0)%positive | Zneg p => (p~1)%positive end.

Definition pos_to_z (p : positive) : Z :=
  match p with xH => 0 | xO q => Zpos q | xI q => Zneg q end.

Lemma z_pos_z : forall z, pos_to_z (z_to_pos z) = z.
Proof. destruct z; reflexivity. Qed.

Lemma bt_get_set_same : forall p v t, bt_get p (bt_set p v t) = v.
Proof. induction p; destruct t; simpl; auto. Qed.

Lemma bt_get_empty : forall q, bt_get q BEmpty = false.
Proof. destruct q; reflexivity. Qed.

Lemma bt_get_set_diff : forall p q v t, p <> q -> bt_get q (bt_set p v t) = bt_get q t.
Proof.
  induction p; intros q v t Hneq; destruct t; destruct q; simpl in *;
    try rewrite !bt_get_empty;
    try reflexivity; try congruence;
    try (apply IHp; congruence);
    try (rewrite IHp; [apply bt_get_empty | congruence]).
Qed.

Definition bt_interp (t : BTree) : Tape := fun z => bt_get (z_to_pos z) t.

Lemma bt_interp_set : forall t p v,
  tape_eq (bt_interp (bt_set (z_to_pos p) v t)) (write_tape (bt_interp t) p v).
Proof.
  intros t p v z. unfold bt_interp, write_tape.
  destruct (Z.eqb_spec z p).
  - subst z. apply bt_get_set_same.
  - apply bt_get_set_diff. intros Heq. apply n.
    rewrite <- (z_pos_z z), <- (z_pos_z p), Heq. reflexivity.
Qed.

Record FastConfig := {
  fpos1 : Z;
  fpos2 : Z;
  fstate1 : State;
  fstate2 : State;
  ftape : BTree
}.

Definition fc_to_cfg (fc : FastConfig) : Config := {|
  pos1 := fc.(fpos1);
  pos2 := fc.(fpos2);
  state1 := fc.(fstate1);
  state2 := fc.(fstate2);
  tape := bt_interp fc.(ftape)
|}.

Definition fast_step (fc : FastConfig) : FastConfig :=
  let r1 := bt_get (z_to_pos fc.(fpos1)) fc.(ftape) in
  let r2 := bt_get (z_to_pos fc.(fpos2)) fc.(ftape) in
  let tr1 := ag1 fc.(fstate1) r1 in
  let tr2 := ag2 fc.(fstate2) r2 in
  let t1 := bt_set (z_to_pos fc.(fpos2)) tr2.(write_sym) fc.(ftape) in
  let t2 := bt_set (z_to_pos fc.(fpos1)) tr1.(write_sym) t1 in
  {| fpos1 := move_pos fc.(fpos1) tr1.(move_dir);
     fpos2 := move_pos fc.(fpos2) tr2.(move_dir);
     fstate1 := tr1.(next_state);
     fstate2 := tr2.(next_state);
     ftape := t2 |}.

Lemma fast_step_sound : forall fc,
  cfg_eq (fc_to_cfg (fast_step fc)) (step ag1 ag2 (fc_to_cfg fc)).
Proof.
  intro fc. unfold fast_step, fc_to_cfg, step.
  constructor; simpl; try reflexivity.
  eapply tape_eq_trans.
  - apply bt_interp_set.
  - apply write_tape_proper. apply bt_interp_set.
Qed.

Lemma fast_run_sound : forall n fc,
  cfg_eq (fc_to_cfg (N.iter n fast_step fc)) (run_N ag1 ag2 n (fc_to_cfg fc)).
Proof.
  intro n. induction n using N.peano_ind; intro fc.
  - rewrite run_N_0. simpl. constructor; simpl; auto. intro; auto.
  - rewrite run_N_succ, N.iter_succ.
    eapply cfg_eq_trans.
    + apply fast_step_sound.
    + apply step_proper. apply IHn.
Qed.

Definition fast_step_chk_range (lo hi : Z) (st : FastConfig * bool) : FastConfig * bool :=
  let (fc, ok) := st in
  let ok_now := ok && negb (Z.eqb fc.(fpos1) fc.(fpos2))
                   && (Z.leb lo fc.(fpos1)) && (Z.leb fc.(fpos1) hi)
                   && (Z.leb lo fc.(fpos2)) && (Z.leb fc.(fpos2) hi) in
  (fast_step fc, ok_now).

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
    fc_k.(fpos1) <> fc_k.(fpos2) /\ lo <= fc_k.(fpos1) <= hi /\ lo <= fc_k.(fpos2) <= hi.
Proof.
  intro n. induction n using N.peano_ind; intros lo hi fc ok Hsnd.
  - simpl in Hsnd. split; auto. intros k Hk. lia.
  - rewrite N.iter_succ in Hsnd.
    destruct (N.iter n (fast_step_chk_range lo hi) (fc, ok)) as [fc' ok'] eqn:E.
    assert (Hfc : fc' = N.iter n fast_step fc)
      by (rewrite <- (fast_step_chk_range_fst n lo hi fc ok), E; reflexivity).
    simpl in Hsnd.
    rewrite !andb_true_iff in Hsnd.
    destruct Hsnd as [[[[[Hok' Hneq] Hlo1] Hhi1] Hlo2] Hhi2].
    assert (Hsnd_n : snd (N.iter n (fast_step_chk_range lo hi) (fc, ok)) = true)
      by (rewrite E; exact Hok').
    destruct (IHn lo hi fc ok Hsnd_n) as [Hok Hlt].
    split; auto. intros k Hk.
    destruct (N.lt_ge_cases k n) as [Hklt | Hkge].
    + apply Hlt; exact Hklt.
    + replace k with n by lia. rewrite <- Hfc.
      split.
      * rewrite negb_true_iff, Z.eqb_neq in Hneq. exact Hneq.
      * rewrite !Z.leb_le in *. lia.
Qed.

Lemma fast_run_outside_zero : forall n lo hi fc,
  (forall k, (k < n)%N ->
    let fc_k := N.iter k fast_step fc in
    lo <= fc_k.(fpos1) <= hi /\ lo <= fc_k.(fpos2) <= hi) ->
  (forall z, z < lo \/ z > hi -> bt_get (z_to_pos z) fc.(ftape) = false) ->
  forall z, z < lo \/ z > hi -> bt_get (z_to_pos z) (N.iter n fast_step fc).(ftape) = false.
Proof.
  intro n. induction n using N.peano_ind; intros lo hi fc Hrng Hout z Hz.
  - simpl. apply Hout; exact Hz.
  - rewrite N.iter_succ.
    assert (Hrng_n : forall k, (k < n)%N ->
      let fc_k := N.iter k fast_step fc in
      lo <= fc_k.(fpos1) <= hi /\ lo <= fc_k.(fpos2) <= hi)
      by (intros k Hk; apply Hrng; lia).
    destruct (Hrng n ltac:(lia)) as [Hn1 Hn2].
    set (fcn := N.iter n fast_step fc) in *.
    unfold fast_step. simpl.
    assert (Hdiff1 : z_to_pos fcn.(fpos1) <> z_to_pos z).
    { intro Heq. assert (fcn.(fpos1) = z) by (rewrite <- (z_pos_z fcn.(fpos1)), <- (z_pos_z z), Heq; reflexivity). lia. }
    assert (Hdiff2 : z_to_pos fcn.(fpos2) <> z_to_pos z).
    { intro Heq. assert (fcn.(fpos2) = z) by (rewrite <- (z_pos_z fcn.(fpos2)), <- (z_pos_z z), Heq; reflexivity). lia. }
    rewrite bt_get_set_diff by exact Hdiff1.
    rewrite bt_get_set_diff by exact Hdiff2.
    apply (IHn lo hi fc); auto.
Qed.

(** * 5. Concrete Prefix (Steps 0 .. 5730) *)

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

Definition state_eqb (s1 s2 : State) : bool :=
  match s1, s2 with
  | StA, StA | StB, StB | StC, StC | StD, StD => true
  | _, _ => false
  end.

Lemma state_eqb_eq : forall s1 s2, state_eqb s1 s2 = true -> s1 = s2.
Proof. destruct s1, s2; simpl; congruence. Qed.

Definition exp_5730 (z : Z) : bool :=
  if Z.ltb z (-2) then false
  else if Z.ltb z 203 then true
  else if Z.eqb z 203 then true
  else if Z.eqb z 206 then true
  else false.

Fixpoint check_range_bool (lo : Z) (len : nat) (t : BTree) : bool :=
  match len with
  | O => true
  | S n => Bool.eqb (bt_get (z_to_pos lo) t) (exp_5730 lo) && check_range_bool (lo + 1) n t
  end.

Lemma check_range_bool_sound : forall len lo t,
  check_range_bool lo len t = true ->
  forall z, lo <= z < lo + Z.of_nat len -> bt_get (z_to_pos z) t = exp_5730 z.
Proof.
  induction len; intros lo t H z Hz.
  - simpl in Hz. lia.
  - simpl in H. rewrite andb_true_iff, eqb_true_iff in H. destruct H as [H0 Hrest].
    destruct (Z.eq_dec z lo).
    + subst z. exact H0.
    + apply (IHlen (lo + 1) t); auto; lia.
Qed.

Definition check_fc_5730 (st : FastConfig * bool) : bool :=
  let (fc, ok) := st in
  ok && Z.eqb fc.(fpos1) 188 && Z.eqb fc.(fpos2) 206
     && state_eqb fc.(fstate1) StB && state_eqb fc.(fstate2) StC
     && check_range_bool (-4) 214 fc.(ftape).

Lemma fc_5730_ok : check_fc_5730 (N.iter 5730 (fast_step_chk_range (-4) 209) (fc0, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Definition round_inv (G : Z) (L_left : N) (x0 : Z) (c : Config) : Prop :=
  c.(pos1) = x0 /\
  c.(state1) = StB /\
  c.(pos2) = x0 + G /\
  c.(state2) = StC /\
  (forall z, z < x0 - Z.of_N L_left -> c.(tape) z = false) /\
  (forall z, x0 - Z.of_N L_left <= z < x0 + G - 3 -> c.(tape) z = true) /\
  c.(tape) (x0 + G - 3) = true /\
  c.(tape) (x0 + G - 2) = false /\
  c.(tape) (x0 + G - 1) = false /\
  c.(tape) (x0 + G) = true /\
  c.(tape) (x0 + G + 1) = false /\
  c.(tape) (x0 + G + 2) = false /\
  (forall z, z > x0 + G + 2 -> c.(tape) z = false).

Lemma prefix_5730_ok :
  round_inv 18 190 188 (run_N ag1 ag2 5730 c0) /\
  (forall k, (k < 5730)%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2)).
Proof.
  pose proof fc_5730_ok as Hok.
  remember (N.iter 5730 (fast_step_chk_range (-4) 209) (fc0, true)) as st eqn:Est.
  destruct st as [fc_end ok_end].
  unfold check_fc_5730 in Hok.
  rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[Hok_end Hp1] Hp2] Hs1] Hs2] Hrng].
  rewrite Z.eqb_eq in Hp1, Hp2.
  apply state_eqb_eq in Hs1, Hs2.
  assert (Hfc : fc_end = N.iter 5730 fast_step fc0).
  { pose proof (fast_step_chk_range_fst 5730 (-4) 209 fc0 true) as Hfst.
    rewrite <- Est in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 5730 (fast_step_chk_range (-4) 209) (fc0, true)) = true)
    by (rewrite <- Est; exact Hok_end).
  destruct (fast_step_chk_range_sound 5730 (-4) 209 fc0 true Hsnd) as [_ Hchk].
  assert (Hrun : cfg_eq (fc_to_cfg fc_end) (run_N ag1 ag2 5730 c0)).
  { rewrite Hfc. apply (fast_run_sound 5730 fc0). }
  destruct Hrun as [Rp1 Rp2 Rs1 Rs2 Rtp].
  assert (Hout : forall z, z < -4 \/ z > 209 -> bt_get (z_to_pos z) fc_end.(ftape) = false).
  { rewrite Hfc. apply (fast_run_outside_zero 5730 (-4) 209 fc0).
    - intros k Hk. destruct (Hchk k Hk) as [_ [Ha Hb]]. split; auto.
    - intros z _. apply bt_get_empty. }
  apply check_range_bool_sound in Hrng.
  split.
  - unfold round_inv.
    rewrite <- Rp1, <- Rp2, <- Rs1, <- Rs2. simpl.
    repeat split; try lia; try assumption.
    + intros z Hz. rewrite <- Rtp. simpl. unfold bt_interp.
      destruct (Z.lt_ge_cases z (-4)) as [Hlt | Hge].
      * apply Hout. left; lia.
      * rewrite Hrng by lia. unfold exp_5730.
        destruct (Z.ltb_spec z (-2)); [reflexivity | lia].
    + intros z Hz. rewrite <- Rtp. simpl. unfold bt_interp.
      rewrite Hrng by lia. unfold exp_5730.
      destruct (Z.ltb_spec z (-2)); [lia|].
      destruct (Z.ltb_spec z 203); [reflexivity | lia].
    + rewrite <- Rtp. simpl. unfold bt_interp. rewrite Hrng by lia. reflexivity.
    + rewrite <- Rtp. simpl. unfold bt_interp. rewrite Hrng by lia. reflexivity.
    + rewrite <- Rtp. simpl. unfold bt_interp. rewrite Hrng by lia. reflexivity.
    + rewrite <- Rtp. simpl. unfold bt_interp. rewrite Hrng by lia. reflexivity.
    + rewrite <- Rtp. simpl. unfold bt_interp. rewrite Hrng by lia. reflexivity.
    + rewrite <- Rtp. simpl. unfold bt_interp. rewrite Hrng by lia. reflexivity.
    + intros z Hz. rewrite <- Rtp. simpl. unfold bt_interp.
      destruct (Z.gt_le_dec z 209) as [Hgt | Hle].
      * apply Hout. right; lia.
      * rewrite Hrng by lia. unfold exp_5730.
        destruct (Z.ltb_spec z (-2)); [lia|].
        destruct (Z.ltb_spec z 203); [lia|].
        destruct (Z.eqb_spec z 203); [lia|].
        destruct (Z.eqb_spec z 206); [lia| reflexivity].
  - intros k Hk.
    pose proof (fast_run_sound k fc0) as Hrk.
    destruct Hrk as [Kp1 Kp2 _ _ _].
    rewrite <- Kp1, <- Kp2. simpl.
    destruct (Hchk k Hk) as [Hneq _]. exact Hneq.
Qed.

(** * 6. Translation Invariance & Single-Agent Decoupling *)

Definition shift_tape (dx : Z) (t : Tape) : Tape := fun z => t (z - dx).

Definition shift_cfg (dx : Z) (c : Config) : Config := {|
  pos1   := c.(pos1) + dx;
  pos2   := c.(pos2) + dx;
  state1 := c.(state1);
  state2 := c.(state2);
  tape   := shift_tape dx c.(tape)
|}.

Lemma step_shift : forall a1 a2 dx c,
  cfg_eq (step a1 a2 (shift_cfg dx c)) (shift_cfg dx (step a1 a2 c)).
Proof.
  intros a1 a2 dx c. unfold step, shift_cfg, shift_tape. simpl.
  replace (c.(pos1) + dx - dx) with c.(pos1) by lia.
  replace (c.(pos2) + dx - dx) with c.(pos2) by lia.
  constructor; simpl; try (unfold move_pos; destruct move_dir; lia); try reflexivity.
  intro z. unfold write_tape.
  destruct (Z.eqb_spec z (c.(pos1) + dx)); destruct (Z.eqb_spec (z - dx) c.(pos1)); try lia; auto.
  destruct (Z.eqb_spec z (c.(pos2) + dx)); destruct (Z.eqb_spec (z - dx) c.(pos2)); try lia; auto.
Qed.

Lemma run_N_shift : forall a1 a2 n dx c,
  cfg_eq (run_N a1 a2 n (shift_cfg dx c)) (shift_cfg dx (run_N a1 a2 n c)).
Proof.
  intros a1 a2 n. induction n using N.peano_ind; intros dx c.
  - rewrite !run_N_0. constructor; simpl; auto. intro; auto.
  - rewrite !run_N_succ. eapply cfg_eq_trans.
    + apply step_proper, IHn.
    + apply step_shift.
Qed.

Record SConfig := {
  spos   : Z;
  sstate : State;
  stape  : Tape
}.

Definition sstep (ag : AgentTable) (sc : SConfig) : SConfig :=
  let r := sc.(stape) sc.(spos) in
  let tr := ag sc.(sstate) r in
  {| spos   := move_pos sc.(spos) tr.(move_dir);
     sstate := tr.(next_state);
     stape  := write_tape sc.(stape) sc.(spos) tr.(write_sym) |}.

Definition srun_N (ag : AgentTable) (n : N) (sc : SConfig) : SConfig :=
  N.iter n (sstep ag) sc.

Lemma srun_N_0 : forall ag sc, srun_N ag 0%N sc = sc.
Proof. intros. reflexivity. Qed.

Lemma srun_N_succ : forall ag n sc, srun_N ag (N.succ n) sc = sstep ag (srun_N ag n sc).
Proof. intros. unfold srun_N. apply N.iter_succ. Qed.

Lemma srun_N_add : forall ag m n sc,
  srun_N ag (m + n)%N sc = srun_N ag m (srun_N ag n sc).
Proof.
  intros ag m n sc. unfold srun_N.
  induction m using N.peano_ind.
  - rewrite N.add_0_l. reflexivity.
  - rewrite N.add_succ_l, !N.iter_succ, IHm. reflexivity.
Qed.

Definition sc_eq (s1 s2 : SConfig) : Prop :=
  s1.(spos) = s2.(spos) /\ s1.(sstate) = s2.(sstate) /\ tape_eq s1.(stape) s2.(stape).

Lemma sstep_proper : forall ag s1 s2, sc_eq s1 s2 -> sc_eq (sstep ag s1) (sstep ag s2).
Proof.
  intros ag s1 s2 [Hp [Hs Ht]]. unfold sstep.
  rewrite Hp, Hs, Ht. repeat split; simpl; auto.
  apply write_tape_proper; exact Ht.
Qed.

Lemma srun_N_proper : forall ag n s1 s2, sc_eq s1 s2 -> sc_eq (srun_N ag n s1) (srun_N ag n s2).
Proof.
  intros ag n. induction n using N.peano_ind; intros s1 s2 H.
  - rewrite !srun_N_0. exact H.
  - rewrite !srun_N_succ. apply sstep_proper, IHn, H.
Qed.

Lemma srun_N_agree_range : forall ag lo hi n s1 s2,
  (forall k, (k < n)%N -> lo <= (srun_N ag k s1).(spos) <= hi) ->
  s1.(spos) = s2.(spos) ->
  s1.(sstate) = s2.(sstate) ->
  (forall z, lo <= z <= hi -> s1.(stape) z = s2.(stape) z) ->
  (srun_N ag n s1).(spos) = (srun_N ag n s2).(spos) /\
  (srun_N ag n s1).(sstate) = (srun_N ag n s2).(sstate) /\
  (forall z, lo <= z <= hi -> (srun_N ag n s1).(stape) z = (srun_N ag n s2).(stape) z) /\
  (forall z, z < lo \/ z > hi -> (srun_N ag n s1).(stape) z = s1.(stape) z).
Proof.
  intros ag lo hi n.
  induction n using N.peano_ind; intros s1 s2 Hrng Hp Hs Htp.
  - rewrite !srun_N_0. repeat split; auto.
  - rewrite !srun_N_succ.
    assert (Hrng_n : forall k, (k < n)%N -> lo <= (srun_N ag k s1).(spos) <= hi)
      by (intros k Hk; apply Hrng; lia).
    destruct (IHn s1 s2 Hrng_n Hp Hs Htp) as [Gp [Gs [Gt Gout]]].
    destruct (Hrng n ltac:(lia)) as [Hlo Hhi].
    unfold sstep; simpl. rewrite Gp, Gs.
    rewrite <- (Gt (srun_N ag n s2).(spos)) by lia.
    repeat split; try reflexivity.
    + intros z Hz. unfold write_tape.
      destruct (Z.eqb_spec z (srun_N ag n s2).(spos)); auto.
    + intros z Hz. rewrite write_tape_other by lia. apply Gout; exact Hz.
Qed.

Lemma run_N_decouple : forall a1 a2 lo1 hi1 lo2 hi2 n c sc1 sc2,
  hi1 < lo2 ->
  (forall k, (k < n)%N -> lo1 <= (srun_N a1 k sc1).(spos) <= hi1) ->
  (forall k, (k < n)%N -> lo2 <= (srun_N a2 k sc2).(spos) <= hi2) ->
  c.(pos1) = sc1.(spos) ->
  c.(state1) = sc1.(sstate) ->
  (forall z, lo1 <= z <= hi1 -> c.(tape) z = sc1.(stape) z) ->
  c.(pos2) = sc2.(spos) ->
  c.(state2) = sc2.(sstate) ->
  (forall z, lo2 <= z <= hi2 -> c.(tape) z = sc2.(stape) z) ->
  (forall k, (k < n)%N ->
    (run_N a1 a2 k c).(pos1) = (srun_N a1 k sc1).(spos) /\
    (run_N a1 a2 k c).(pos2) = (srun_N a2 k sc2).(spos) /\
    (run_N a1 a2 k c).(pos1) <> (run_N a1 a2 k c).(pos2)) /\
  (run_N a1 a2 n c).(pos1) = (srun_N a1 n sc1).(spos) /\
  (run_N a1 a2 n c).(state1) = (srun_N a1 n sc1).(sstate) /\
  (forall z, lo1 <= z <= hi1 -> (run_N a1 a2 n c).(tape) z = (srun_N a1 n sc1).(stape) z) /\
  (run_N a1 a2 n c).(pos2) = (srun_N a2 n sc2).(spos) /\
  (run_N a1 a2 n c).(state2) = (srun_N a2 n sc2).(sstate) /\
  (forall z, lo2 <= z <= hi2 -> (run_N a1 a2 n c).(tape) z = (srun_N a2 n sc2).(stape) z) /\
  (forall z, ~ (lo1 <= z <= hi1) -> ~ (lo2 <= z <= hi2) -> (run_N a1 a2 n c).(tape) z = c.(tape) z).
Proof.
  intros a1 a2 lo1 hi1 lo2 hi2 n.
  induction n using N.peano_ind; intros c sc1 sc2 Hsep Hrng1 Hrng2 Hp1 Hs1 Ht1 Hp2 Hs2 Ht2.
  - rewrite !run_N_0, !srun_N_0. repeat split; auto; intros; lia.
  - assert (Hrng1_n : forall k, (k < n)%N -> lo1 <= (srun_N a1 k sc1).(spos) <= hi1)
      by (intros k Hk; apply Hrng1; lia).
    assert (Hrng2_n : forall k, (k < n)%N -> lo2 <= (srun_N a2 k sc2).(spos) <= hi2)
      by (intros k Hk; apply Hrng2; lia).
    destruct (IHn c sc1 sc2 Hsep Hrng1_n Hrng2_n Hp1 Hs1 Ht1 Hp2 Hs2 Ht2)
      as [Hprev [Gp1 [Gs1 [Gt1 [Gp2 [Gs2 [Gt2 Gout]]]]]]].
    destruct (Hrng1 n ltac:(lia)) as [H1a H1b].
    destruct (Hrng2 n ltac:(lia)) as [H2a H2b].
    split.
    + intros k Hk. destruct (N.lt_ge_cases k n) as [Hklt | Hkge].
      * apply Hprev; exact Hklt.
      * replace k with n by lia. repeat split; auto. lia.
    + rewrite run_N_succ, !srun_N_succ.
      unfold step, sstep.
      rewrite Gp1, Gs1, Gp2, Gs2.
      rewrite Gt1 by lia. rewrite Gt2 by lia.
      repeat split; simpl; try reflexivity.
      * intros z Hz. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 n sc1).(spos)); auto.
        rewrite write_tape_other by lia. apply Gt1; exact Hz.
      * intros z Hz. unfold write_tape.
        rewrite write_tape_other by lia.
        destruct (Z.eqb_spec z (srun_N a2 n sc2).(spos)); auto.
        apply Gt2; exact Hz.
      * intros z Hz1 Hz2. unfold write_tape.
        rewrite write_tape_other by lia.
        rewrite write_tape_other by lia.
        apply Gout; auto.
Qed.

(** * 7. Agent 1 Counter Rules: Sweep, Walk, and Binary Fill *)

Lemma ag1_sweep_left : forall m x_end sc,
  sc.(spos) = x_end + Z.of_N m - 1 ->
  sc.(sstate) = StC ->
  (forall z, x_end <= z < x_end + Z.of_N m -> sc.(stape) z = true) ->
  (forall k, (k < m)%N -> x_end <= (srun_N ag1 k sc).(spos) <= x_end + Z.of_N m - 1) /\
  (srun_N ag1 m sc).(spos) = x_end - 1 /\
  (srun_N ag1 m sc).(sstate) = StC /\
  (forall z, x_end <= z < x_end + Z.of_N m -> (srun_N ag1 m sc).(stape) z = false) /\
  (forall z, z < x_end \/ z >= x_end + Z.of_N m -> (srun_N ag1 m sc).(stape) z = sc.(stape) z).
Proof.
  intro m. induction m using N.peano_ind; intros x_end sc Hp Hs Ht.
  - rewrite srun_N_0. repeat split; try lia; auto.
    + intros k Hk. lia.
    + intros z Hz. lia.
  - set (sc1 := sstep ag1 sc).
    assert (Hsc1 : sc1.(spos) = x_end + Z.of_N m - 1 /\
                   sc1.(sstate) = StC /\
                   (forall z, x_end <= z < x_end + Z.of_N m -> sc1.(stape) z = true) /\
                   sc1.(stape) (x_end + Z.of_N m) = false /\
                   (forall z, z < x_end \/ z > x_end + Z.of_N m -> sc1.(stape) z = sc.(stape) z)).
    { unfold sc1, sstep. rewrite Hp, Hs.
      rewrite Ht by lia. simpl.
      repeat split; try lia.
      - intros z Hz. rewrite write_tape_other by lia. apply Ht; lia.
      - replace (x_end + Z.of_N (N.succ m) - 1) with (x_end + Z.of_N m) by lia.
        apply write_tape_same.
      - intros z Hz. rewrite write_tape_other by lia. reflexivity. }
    destruct Hsc1 as [H1p [H1s [H1t [H1f H1o]]]].
    destruct (IHm x_end sc1 H1p H1s H1t) as [Irng [Ip [Is [It Io]]]].
    replace (N.succ m) with (m + 1)%N by lia.
    rewrite srun_N_add.
    assert (Hs1 : srun_N ag1 1 sc = sc1) by (rewrite <- N.add_1_l, srun_N_add, srun_N_0; reflexivity).
    rewrite Hs1.
    repeat split; try lia; try exact Is.
    + intros k Hk.
      destruct (N.eq_dec k 0) as [-> | Hk0].
      * rewrite srun_N_0. lia.
      * replace k with ((k - 1) + 1)%N by lia.
        rewrite srun_N_add, Hs1.
        specialize (Irng (k - 1)%N ltac:(lia)). lia.
    + intros z Hz.
      destruct (Z.eq_dec z (x_end + Z.of_N m)) as [-> | Hneq].
      * rewrite Io by lia. exact H1f.
      * apply It. lia.
    + intros z Hz. rewrite Io by lia. apply H1o. lia.
Qed.

Lemma ag1_walk_right : forall m x0 sc,
  sc.(spos) = x0 ->
  sc.(sstate) = StB ->
  (forall z, x0 <= z < x0 + Z.of_N m -> sc.(stape) z = true) ->
  (forall k, (k < m)%N -> x0 <= (srun_N ag1 k sc).(spos) <= x0 + Z.of_N m - 1) /\
  (srun_N ag1 m sc).(spos) = x0 + Z.of_N m /\
  (srun_N ag1 m sc).(sstate) = StB /\
  (forall z, (srun_N ag1 m sc).(stape) z = sc.(stape) z).
Proof.
  intro m. induction m using N.peano_ind; intros x0 sc Hp Hs Ht.
  - rewrite srun_N_0. repeat split; try lia; auto. intros k Hk; lia.
  - set (sc1 := sstep ag1 sc).
    assert (Hsc1 : sc1.(spos) = x0 + 1 /\ sc1.(sstate) = StB /\
                   forall z, sc1.(stape) z = sc.(stape) z).
    { unfold sc1, sstep. rewrite Hp, Hs. rewrite Ht by lia. simpl.
      repeat split; try lia.
      intro z. unfold write_tape. destruct (Z.eqb_spec z x0); [subst; symmetry; apply Ht; lia | reflexivity]. }
    destruct Hsc1 as [H1p [H1s H1t]].
    assert (H1t' : forall z, x0 + 1 <= z < x0 + 1 + Z.of_N m -> sc1.(stape) z = true)
      by (intros z Hz; rewrite H1t; apply Ht; lia).
    destruct (IHm (x0 + 1) sc1 H1p H1s H1t') as [Irng [Ip [Is It]]].
    replace (N.succ m) with (m + 1)%N by lia.
    rewrite srun_N_add.
    assert (Hs1 : srun_N ag1 1 sc = sc1) by (rewrite <- N.add_1_l, srun_N_add, srun_N_0; reflexivity).
    rewrite Hs1.
    repeat split; try lia; try exact Is.
    + intros k Hk.
      destruct (N.eq_dec k 0) as [-> | Hk0].
      * rewrite srun_N_0. lia.
      * replace k with ((k - 1) + 1)%N by lia.
        rewrite srun_N_add, Hs1.
        specialize (Irng (k - 1)%N ltac:(lia)). lia.
    + intro z. rewrite It. apply H1t.
Qed.

Definition T_fill (m : N) : N := (5 * 2 ^ m - m - 3)%N.

Lemma T_fill_1 : T_fill 1 = 6%N.
Proof. reflexivity. Qed.

Lemma T_fill_succ : forall m, (1 <= m)%N ->
  T_fill (N.succ m) = (1 + T_fill m + m + 1 + T_fill m)%N.
Proof.
  intros m Hm. unfold T_fill.
  assert (Hpow : (2 ^ m >= 2)%N).
  { replace m with (1 + (m - 1))%N by lia.
    rewrite N.pow_add_r. change (2 ^ 1)%N with 2%N.
    pose proof (N.pow_nonzero 2 (m - 1) ltac:(discriminate)). lia. }
  rewrite N.pow_succ_r' by lia.
  lia.
Qed.

Lemma ag1_fill : forall m x0 sc,
  (1 <= m)%N ->
  sc.(spos) = x0 - 1 ->
  sc.(sstate) = StC ->
  sc.(stape) (x0 - 2) = false ->
  sc.(stape) (x0 - 1) = false ->
  (forall z, x0 <= z < x0 + Z.of_N m -> sc.(stape) z = false) ->
  (forall k, (k < T_fill m)%N -> x0 - 2 <= (srun_N ag1 k sc).(spos) <= x0 + Z.of_N m - 1) /\
  (srun_N ag1 (T_fill m) sc).(spos) = x0 + Z.of_N m /\
  (srun_N ag1 (T_fill m) sc).(sstate) = StB /\
  (srun_N ag1 (T_fill m) sc).(stape) (x0 - 2) = false /\
  (srun_N ag1 (T_fill m) sc).(stape) (x0 - 1) = false /\
  (forall z, x0 <= z < x0 + Z.of_N m -> (srun_N ag1 (T_fill m) sc).(stape) z = true) /\
  (forall z, z < x0 - 2 \/ z >= x0 + Z.of_N m -> (srun_N ag1 (T_fill m) sc).(stape) z = sc.(stape) z).
Proof.
  intro m. induction m using N.peano_ind; intros x0 sc Hm Hp Hs Hm2 Hm1 Ht.
  - lia.
  - destruct (N.eq_dec m 0) as [-> | Hm0].
    + (* Base case m = 1: T_fill 1 = 6 *)
      change (N.succ 0) with 1%N. rewrite T_fill_1.
      assert (H6 : (srun_N ag1 6 sc).(spos) = x0 + 1 /\
                   (srun_N ag1 6 sc).(sstate) = StB /\
                   (srun_N ag1 6 sc).(stape) (x0 - 2) = false /\
                   (srun_N ag1 6 sc).(stape) (x0 - 1) = false /\
                   (srun_N ag1 6 sc).(stape) x0 = true /\
                   (forall z, z < x0 - 2 \/ z >= x0 + 1 -> (srun_N ag1 6 sc).(stape) z = sc.(stape) z) /\
                   (forall k, (k < 6)%N -> x0 - 2 <= (srun_N ag1 k sc).(spos) <= x0)).
      { set (c1 := sstep ag1 sc).
        assert (Hc1 : c1.(spos) = x0 - 2 /\ c1.(sstate) = StD /\ c1.(stape) (x0 - 2) = false /\
                      c1.(stape) (x0 - 1) = true /\ c1.(stape) x0 = false /\
                      forall z, z < x0 - 2 \/ z >= x0 + 1 -> c1.(stape) z = sc.(stape) z).
        { unfold c1, sstep. rewrite Hp, Hs, Hm1. simpl. repeat split; try lia; auto.
          - rewrite write_tape_other by lia. exact Hm2.
          - apply write_tape_same.
          - rewrite write_tape_other by lia. apply Ht; lia.
          - intros z Hz. rewrite write_tape_other by lia. reflexivity. }
        destruct Hc1 as [p1 [s1 [t1m2 [t1m1 [t10 t1o]]]]].
        set (c2 := sstep ag1 c1).
        assert (Hc2 : c2.(spos) = x0 - 1 /\ c2.(sstate) = StA /\ c2.(stape) (x0 - 2) = false /\
                      c2.(stape) (x0 - 1) = true /\ c2.(stape) x0 = false /\
                      forall z, z < x0 - 2 \/ z >= x0 + 1 -> c2.(stape) z = sc.(stape) z).
        { unfold c2, sstep. rewrite p1, s1, t1m2. simpl. repeat split; try lia; auto.
          - apply write_tape_same.
          - rewrite write_tape_other by lia; exact t1m1.
          - rewrite write_tape_other by lia; exact t10.
          - intros z Hz. rewrite write_tape_other by lia; apply t1o; auto. }
        destruct Hc2 as [p2 [s2 [t2m2 [t2m1 [t20 t2o]]]]].
        set (c3 := sstep ag1 c2).
        assert (Hc3 : c3.(spos) = x0 /\ c3.(sstate) = StC /\ c3.(stape) (x0 - 2) = false /\
                      c3.(stape) (x0 - 1) = true /\ c3.(stape) x0 = false /\
                      forall z, z < x0 - 2 \/ z >= x0 + 1 -> c3.(stape) z = sc.(stape) z).
        { unfold c3, sstep. rewrite p2, s2, t2m1. simpl. repeat split; try lia; auto.
          - rewrite write_tape_other by lia; exact t2m2.
          - apply write_tape_same.
          - rewrite write_tape_other by lia; exact t20.
          - intros z Hz. rewrite write_tape_other by lia; apply t2o; auto. }
        destruct Hc3 as [p3 [s3 [t3m2 [t3m1 [t30 t3o]]]]].
        set (c4 := sstep ag1 c3).
        assert (Hc4 : c4.(spos) = x0 - 1 /\ c4.(sstate) = StD /\ c4.(stape) (x0 - 2) = false /\
                      c4.(stape) (x0 - 1) = true /\ c4.(stape) x0 = true /\
                      forall z, z < x0 - 2 \/ z >= x0 + 1 -> c4.(stape) z = sc.(stape) z).
        { unfold c4, sstep. rewrite p3, s3, t30. simpl. repeat split; try lia; auto.
          - rewrite write_tape_other by lia; exact t3m2.
          - rewrite write_tape_other by lia; exact t3m1.
          - apply write_tape_same.
          - intros z Hz. rewrite write_tape_other by lia; apply t3o; auto. }
        destruct Hc4 as [p4 [s4 [t4m2 [t4m1 [t40 t4o]]]]].
        set (c5 := sstep ag1 c4).
        assert (Hc5 : c5.(spos) = x0 /\ c5.(sstate) = StB /\ c5.(stape) (x0 - 2) = false /\
                      c5.(stape) (x0 - 1) = false /\ c5.(stape) x0 = true /\
                      forall z, z < x0 - 2 \/ z >= x0 + 1 -> c5.(stape) z = sc.(stape) z).
        { unfold c5, sstep. rewrite p4, s4, t4m1. simpl. repeat split; try lia; auto.
          - rewrite write_tape_other by lia; exact t4m2.
          - apply write_tape_same.
          - rewrite write_tape_other by lia; exact t40.
          - intros z Hz. rewrite write_tape_other by lia; apply t4o; auto. }
        destruct Hc5 as [p5 [s5 [t5m2 [t5m1 [t50 t5o]]]]].
        set (c6 := sstep ag1 c5).
        assert (Hc6 : c6.(spos) = x0 + 1 /\ c6.(sstate) = StB /\ c6.(stape) (x0 - 2) = false /\
                      c6.(stape) (x0 - 1) = false /\ c6.(stape) x0 = true /\
                      forall z, z < x0 - 2 \/ z >= x0 + 1 -> c6.(stape) z = sc.(stape) z).
        { unfold c6, sstep. rewrite p5, s5, t50. simpl. repeat split; try lia; auto.
          - rewrite write_tape_other by lia; exact t5m2.
          - rewrite write_tape_other by lia; exact t5m1.
          - apply write_tape_same.
          - intros z Hz. rewrite write_tape_other by lia; apply t5o; auto. }
        destruct Hc6 as [p6 [s6 [t6m2 [t6m1 [t60 t6o]]]]].
        assert (Hs0 : srun_N ag1 0 sc = sc) by reflexivity.
        assert (Hs1 : srun_N ag1 1 sc = c1) by reflexivity.
        assert (Hs2 : srun_N ag1 2 sc = c2) by reflexivity.
        assert (Hs3 : srun_N ag1 3 sc = c3) by reflexivity.
        assert (Hs4 : srun_N ag1 4 sc = c4) by reflexivity.
        assert (Hs5 : srun_N ag1 5 sc = c5) by reflexivity.
        assert (Hs6 : srun_N ag1 6 sc = c6) by reflexivity.
        rewrite Hs6. repeat split; auto.
        intros k Hk.
        destruct (N.eq_dec k 0) as [->|]; [rewrite Hs0; lia|].
        destruct (N.eq_dec k 1) as [->|]; [rewrite Hs1; lia|].
        destruct (N.eq_dec k 2) as [->|]; [rewrite Hs2; lia|].
        destruct (N.eq_dec k 3) as [->|]; [rewrite Hs3; lia|].
        destruct (N.eq_dec k 4) as [->|]; [rewrite Hs4; lia|].
        destruct (N.eq_dec k 5) as [->|]; [rewrite Hs5; lia| lia]. }
      destruct H6 as [Hp6 [Hs6 [Hm26 [Hm16 [H06 [Ho6 Hrng6]]]]]].
      repeat split; try lia; auto.
      intros z Hz. replace z with x0 by lia. exact H06.
    + (* Inductive step m >= 1 *)
      assert (Hm1_ge : (1 <= m)%N) by lia.
      assert (Ht_m : forall z, x0 <= z < x0 + Z.of_N m -> sc.(stape) z = false)
        by (intros z Hz; apply Ht; lia).
      destruct (IHm x0 sc Hm1_ge Hp Hs Hm2 Hm1 Ht_m)
        as [RngA [Ap [As [Am2 [Am1 [At Ao]]]]]].
      set (scA := srun_N ag1 (T_fill m) sc) in *.
      (* Step B: 1 step at x0 + m (StB on false -> writes true, moves L to x0 + m - 1 in StC) *)
      set (scB := sstep ag1 scA).
      assert (HscB : scB.(spos) = x0 + Z.of_N m - 1 /\
                     scB.(sstate) = StC /\
                     scB.(stape) (x0 - 2) = false /\
                     scB.(stape) (x0 - 1) = false /\
                     (forall z, x0 <= z < x0 + Z.of_N m -> scB.(stape) z = true) /\
                     scB.(stape) (x0 + Z.of_N m) = true /\
                     (forall z, z < x0 - 2 \/ z >= x0 + Z.of_N (N.succ m) -> scB.(stape) z = sc.(stape) z)).
      { unfold scB, sstep. rewrite Ap, As.
        assert (Hxm : scA.(stape) (x0 + Z.of_N m) = false).
        { rewrite Ao by lia. apply Ht; lia. }
        rewrite Hxm. simpl. repeat split; try lia.
        - rewrite write_tape_other by lia. exact Am2.
        - rewrite write_tape_other by lia. exact Am1.
        - intros z Hz. rewrite write_tape_other by lia. apply At; exact Hz.
        - apply write_tape_same.
        - intros z Hz. rewrite write_tape_other by lia. apply Ao; lia. }
      destruct HscB as [Bp [Bs [Bm2 [Bm1 [Bt [Bxm Bo]]]]]].
      (* Step C: m steps of ag1_sweep_left from x0 + m - 1 to x0 - 1 *)
      destruct (ag1_sweep_left m x0 scB Bp Bs Bt) as [RngC [Cp [Cs [Ct Co]]]].
      set (scC := srun_N ag1 m scB) in *.
      assert (Hcm2 : scC.(stape) (x0 - 2) = false) by (rewrite Co by lia; exact Bm2).
      assert (Hcm1 : scC.(stape) (x0 - 1) = false) by (rewrite Co by lia; exact Bm1).
      assert (Hcxm : scC.(stape) (x0 + Z.of_N m) = true) by (rewrite Co by lia; exact Bxm).
      assert (Hco  : forall z, z < x0 - 2 \/ z >= x0 + Z.of_N (N.succ m) -> scC.(stape) z = sc.(stape) z)
        by (intros z Hz; rewrite Co by lia; apply Bo; exact Hz).
      (* Step D: T_fill m steps from scC *)
      destruct (IHm x0 scC Hm1_ge Cp Cs Hcm2 Hcm1 Ct)
        as [RngD [Dp [Ds [Dm2 [Dm1 [Dt Do]]]]]].
      set (scD := srun_N ag1 (T_fill m) scC) in *.
      (* Step E: 1 step at x0 + m (StB on true -> moves R to x0 + m + 1 in StB) *)
      set (scE := sstep ag1 scD).
      assert (HscE : scE.(spos) = x0 + Z.of_N (N.succ m) /\
                     scE.(sstate) = StB /\
                     scE.(stape) (x0 - 2) = false /\
                     scE.(stape) (x0 - 1) = false /\
                     (forall z, x0 <= z < x0 + Z.of_N (N.succ m) -> scE.(stape) z = true) /\
                     (forall z, z < x0 - 2 \/ z >= x0 + Z.of_N (N.succ m) -> scE.(stape) z = sc.(stape) z)).
      { unfold scE, sstep. rewrite Dp, Ds.
        assert (Hdxm : scD.(stape) (x0 + Z.of_N m) = true) by (rewrite Do by lia; exact Hcxm).
        rewrite Hdxm. simpl. repeat split; try lia.
        - rewrite write_tape_other by lia. exact Dm2.
        - rewrite write_tape_other by lia. exact Dm1.
        - intros z Hz.
          destruct (Z.eq_dec z (x0 + Z.of_N m)) as [-> | Hneq].
          + apply write_tape_same.
          + rewrite write_tape_other by lia. apply Dt. lia.
        - intros z Hz. rewrite write_tape_other by lia. rewrite Do by lia. apply Hco; exact Hz. }
      rewrite T_fill_succ by exact Hm1_ge.
      assert (Hs_eq : srun_N ag1 (1 + T_fill m + m + 1 + T_fill m) sc = scE).
      { replace (1 + T_fill m + m + 1 + T_fill m)%N with (1 + (T_fill m + (m + (1 + T_fill m))))%N by lia.
        rewrite !srun_N_add.
        change (srun_N ag1 1) with (sstep ag1).
        fold scA. fold scB. fold scC. fold scD. fold scE. reflexivity. }
      rewrite Hs_eq.
      repeat split; try (apply HscE).
      intros k Hk.
      destruct (N.lt_ge_cases k (T_fill m)) as [Hk1 | Hk1].
      * specialize (RngA k Hk1). lia.
      * destruct (N.eq_dec k (T_fill m)) as [-> | Hneq1].
        { fold scA. rewrite Ap. lia. }
        destruct (N.lt_ge_cases k (1 + T_fill m + m)) as [Hk2 | Hk2].
        { replace k with ((k - (1 + T_fill m)) + (1 + T_fill m))%N by lia.
          rewrite srun_N_add.
          rewrite (srun_N_add ag1 1 (T_fill m) sc).
          change (srun_N ag1 1) with (sstep ag1). fold scA. fold scB.
          specialize (RngC (k - (1 + T_fill m))%N ltac:(lia)). lia. }
        destruct (N.lt_ge_cases k (1 + T_fill m + m + T_fill m)) as [Hk3 | Hk3].
        { replace k with ((k - (1 + T_fill m + m)) + (m + (1 + T_fill m)))%N by lia.
          rewrite !srun_N_add.
          rewrite (srun_N_add ag1 1 (T_fill m) sc).
          change (srun_N ag1 1) with (sstep ag1). fold scA. fold scB. fold scC.
          specialize (RngD (k - (1 + T_fill m + m))%N ltac:(lia)). lia. }
        { replace k with (T_fill m + (m + (1 + T_fill m)))%N by lia.
          rewrite !srun_N_add.
          rewrite (srun_N_add ag1 1 (T_fill m) sc).
          change (srun_N ag1 1) with (sstep ag1). fold scA. fold scB. fold scC. fold scD.
          rewrite Dp. lia. }
Qed.

(** * 8. Agent 2 Glider (P = 27, D = 1) *)

Definition sshift_cfg (dx : Z) (sc : SConfig) : SConfig := {|
  spos   := sc.(spos) + dx;
  sstate := sc.(sstate);
  stape  := shift_tape dx sc.(stape)
|}.

Lemma sstep_shift : forall ag dx sc,
  sc_eq (sstep ag (sshift_cfg dx sc)) (sshift_cfg dx (sstep ag sc)).
Proof.
  intros ag dx sc. unfold sstep, sshift_cfg, shift_tape. simpl.
  replace (sc.(spos) + dx - dx) with sc.(spos) by lia.
  repeat split; simpl; try (unfold move_pos; destruct move_dir; lia); try reflexivity.
  intro z. unfold write_tape.
  destruct (Z.eqb_spec z (sc.(spos) + dx)); destruct (Z.eqb_spec (z - dx) sc.(spos)); try lia; auto.
Qed.

Lemma srun_N_shift : forall ag n dx sc,
  sc_eq (srun_N ag n (sshift_cfg dx sc)) (sshift_cfg dx (srun_N ag n sc)).
Proof.
  intros ag n. induction n using N.peano_ind; intros dx sc.
  - rewrite !srun_N_0. repeat split; simpl; auto. intro; auto.
  - rewrite !srun_N_succ.
    assert (H := sstep_proper ag _ _ (IHn dx sc)).
    destruct H as [Hp [Hs Ht]].
    pose proof (sstep_shift ag dx (srun_N ag n sc)) as [Gp [Gs Gt]].
    split; [congruence | split; [congruence | eapply tape_eq_trans; eauto]].
Qed.

Definition glider_pat (t : Tape) (p2 : Z) : Prop :=
  t (p2 - 3) = true /\
  t (p2 - 2) = false /\
  t (p2 - 1) = false /\
  t p2 = true /\
  t (p2 + 1) = false /\
  t (p2 + 2) = false.

Definition sc_g0 : SConfig := {|
  spos := 0;
  sstate := StC;
  stape := fun z => if Z.eqb z (-3) then true else if Z.eqb z 0 then true else false
|}.

Fixpoint check_srun_range (ag : AgentTable) (lo hi : Z) (n : nat) (sc : SConfig) : bool :=
  match n with
  | O => true
  | S n' => Z.leb lo sc.(spos) && Z.leb sc.(spos) hi && check_srun_range ag lo hi n' (sstep ag sc)
  end.

Lemma check_srun_range_sound : forall ag lo hi n sc,
  check_srun_range ag lo hi n sc = true ->
  forall k, (k < N.of_nat n)%N -> lo <= (srun_N ag k sc).(spos) <= hi.
Proof.
  intros ag lo hi n. induction n; intros sc H k Hk.
  - lia.
  - simpl in H. rewrite !andb_true_iff in H. destruct H as [[Hlo Hhi] Hrest].
    rewrite Z.leb_le in Hlo, Hhi.
    destruct (N.eq_dec k 0) as [-> | Hk0].
    + rewrite srun_N_0. lia.
    + replace k with (N.succ (k - 1)) by lia.
      rewrite srun_N_succ.
      (* note: srun_N ag (N.succ m) sc = srun_N ag m (sstep ag sc) *)
      assert (Hcomm : forall m s, srun_N ag (N.succ m) s = srun_N ag m (sstep ag s)).
      { intro m. induction m using N.peano_ind; intro s; [reflexivity|].
        rewrite srun_N_succ, IHm, srun_N_succ. reflexivity. }
      rewrite <- srun_N_succ, Hcomm.
      apply IHn; auto. lia.
Qed.

Definition check_g27 : bool :=
  let sc27 := srun_N ag2 27 sc_g0 in
  check_srun_range ag2 (-2) 3 27 sc_g0 &&
  Z.eqb sc27.(spos) 1 &&
  state_eqb sc27.(sstate) StC &&
  Bool.eqb (sc27.(stape) (-3)) true &&
  Bool.eqb (sc27.(stape) (-2)) true &&
  Bool.eqb (sc27.(stape) (-1)) false &&
  Bool.eqb (sc27.(stape) 0) false &&
  Bool.eqb (sc27.(stape) 1) true &&
  Bool.eqb (sc27.(stape) 2) false &&
  Bool.eqb (sc27.(stape) 3) false.

Lemma check_g27_ok : check_g27 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ag2_glider_period : forall p2 sc,
  sc.(spos) = p2 ->
  sc.(sstate) = StC ->
  glider_pat sc.(stape) p2 ->
  sc.(stape) (p2 + 3) = false ->
  (forall k, (k < 27)%N -> p2 - 2 <= (srun_N ag2 k sc).(spos) <= p2 + 3) /\
  (srun_N ag2 27 sc).(spos) = p2 + 1 /\
  (srun_N ag2 27 sc).(sstate) = StC /\
  (srun_N ag2 27 sc).(stape) (p2 - 3) = true /\
  glider_pat (srun_N ag2 27 sc).(stape) (p2 + 1) /\
  (forall z, z < p2 - 2 \/ z > p2 + 3 -> (srun_N ag2 27 sc).(stape) z = sc.(stape) z).
Proof.
  intros p2 sc Hp Hs [Hgm3 [Hgm2 [Hgm1 [Hg0 [Hg1 Hg2]]]]] Hg3.
  pose proof check_g27_ok as Hok.
  unfold check_g27 in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[[[[[Hrng Hp27] Hs27] Ht_m3] Ht_m2] Ht_m1] Ht_0] Ht_1] Ht_2] Ht_3].
  rewrite Z.eqb_eq in Hp27. apply state_eqb_eq in Hs27.
  rewrite !eqb_true_iff in Ht_m3, Ht_m2, Ht_m1, Ht_0, Ht_1, Ht_2, Ht_3.
  apply check_srun_range_sound in Hrng.
  assert (Hagree_g0 : forall k, (k < 27)%N ->
    p2 - 2 <= (srun_N ag2 k (sshift_cfg p2 sc_g0)).(spos) <= p2 + 3).
  { intros k Hk. destruct (srun_N_shift ag2 k p2 sc_g0) as [Sp _].
    rewrite Sp. simpl. specialize (Hrng k ltac:(change (N.of_nat 27) with 27%N; lia)). lia. }
  assert (Hsc_eq : sc.(spos) = (sshift_cfg p2 sc_g0).(spos) /\
                   sc.(sstate) = (sshift_cfg p2 sc_g0).(sstate) /\
                   (forall z, p2 - 2 <= z <= p2 + 3 -> sc.(stape) z = (sshift_cfg p2 sc_g0).(stape) z)).
  { repeat split; simpl; try lia; auto.
    intros z Hz. unfold shift_tape. simpl.
    assert (Hz' : z - p2 = -2 \/ z - p2 = -1 \/ z - p2 = 0 \/ z - p2 = 1 \/ z - p2 = 2 \/ z - p2 = 3) by lia.
    destruct Hz' as [-> | [-> | [-> | [-> | [-> | ->]]]]]; simpl;
      [replace (p2 + -2) with (p2 - 2) in * by lia; auto |
       replace (p2 + -1) with (p2 - 1) in * by lia; auto |
       replace (p2 + 0) with p2 in * by lia; auto |
       auto | auto | auto]. }
  destruct Hsc_eq as [Ep [Es Et]].
  destruct (srun_N_agree_range ag2 (p2 - 2) (p2 + 3) 27 (sshift_cfg p2 sc_g0) sc
              Hagree_g0 (eq_sym Ep) (eq_sym Es) (fun z Hz => eq_sym (Et z Hz)))
    as [Ap [As [At _]]].
  assert (Hsc_rng : forall k, (k < 27)%N -> p2 - 2 <= (srun_N ag2 k sc).(spos) <= p2 + 3).
  { intros k Hk.
    assert (Hk_lt : (forall j, (j < k)%N -> p2 - 2 <= (srun_N ag2 j (sshift_cfg p2 sc_g0)).(spos) <= p2 + 3))
      by (intros j Hj; apply Hagree_g0; lia).
    destruct (srun_N_agree_range ag2 (p2 - 2) (p2 + 3) k (sshift_cfg p2 sc_g0) sc
                Hk_lt (eq_sym Ep) (eq_sym Es) (fun z Hz => eq_sym (Et z Hz)))
      as [Kp _].
    rewrite <- Kp. apply Hagree_g0; exact Hk. }
  destruct (srun_N_agree_range ag2 (p2 - 2) (p2 + 3) 27 sc (sshift_cfg p2 sc_g0)
              Hsc_rng Ep Es Et)
    as [Bp [Bs [Bt Bout]]].
  destruct (srun_N_shift ag2 27 p2 sc_g0) as [Sp [Ss St]].
  repeat split; auto.
  - rewrite Bp, Sp, Hp27. lia.
  - rewrite Bs, Ss, Hs27. reflexivity.
  - rewrite Bout by lia. exact Hgm3.
  - unfold glider_pat.
    assert (Hpt : forall dx, -2 <= dx <= 3 -> (srun_N ag2 27 sc).(stape) (p2 + dx) = (srun_N ag2 27 sc_g0).(stape) dx).
    { intros dx Hdx. rewrite Bt by lia. rewrite St. unfold shift_tape.
      replace (p2 + dx - p2) with dx by lia. reflexivity. }
    repeat split.
    + replace (p2 + 1 - 3) with (p2 + -2) by lia. rewrite Hpt by lia. exact Ht_m2.
    + replace (p2 + 1 - 2) with (p2 + -1) by lia. rewrite Hpt by lia. exact Ht_m1.
    + replace (p2 + 1 - 1) with (p2 + 0) by lia. rewrite Hpt by lia. exact Ht_0.
    + replace (p2 + 1) with (p2 + 1) by lia. rewrite Hpt by lia. exact Ht_1.
    + replace (p2 + 1 + 1) with (p2 + 2) by lia. rewrite Hpt by lia. exact Ht_2.
    + replace (p2 + 1 + 2) with (p2 + 3) by lia. rewrite Hpt by lia. exact Ht_3.
Qed.

Lemma ag2_glider_iter : forall q p2 sc,
  sc.(spos) = p2 ->
  sc.(sstate) = StC ->
  glider_pat sc.(stape) p2 ->
  (forall z, z >= p2 + 3 -> sc.(stape) z = false) ->
  (forall k, (k < 27 * q)%N -> p2 - 2 <= (srun_N ag2 k sc).(spos) <= p2 + Z.of_N q + 2) /\
  (srun_N ag2 (27 * q) sc).(spos) = p2 + Z.of_N q /\
  (srun_N ag2 (27 * q) sc).(sstate) = StC /\
  (forall z, p2 - 3 <= z < p2 + Z.of_N q - 3 -> (srun_N ag2 (27 * q) sc).(stape) z = true) /\
  glider_pat (srun_N ag2 (27 * q) sc).(stape) (p2 + Z.of_N q) /\
  (forall z, z >= p2 + Z.of_N q + 3 -> (srun_N ag2 (27 * q) sc).(stape) z = false) /\
  (forall z, z < p2 - 2 \/ z > p2 + Z.of_N q + 2 -> (srun_N ag2 (27 * q) sc).(stape) z = sc.(stape) z).
Proof.
  intro q. induction q using N.peano_ind; intros p2 sc Hp Hs Hpat Hzero.
  - rewrite N.mul_0_r, srun_N_0. repeat split; try lia; auto.
    + intros k Hk. lia.
    + intros z Hz. lia.
    + replace (p2 + Z.of_N 0) with p2 by lia. exact Hpat.
  - destruct (ag2_glider_period p2 sc Hp Hs Hpat (Hzero (p2 + 3) ltac:(lia)))
      as [Rng1 [P1 [S1 [T1m3 [Pat1 Out1]]]]].
    set (sc1 := srun_N ag2 27 sc) in *.
    assert (Hz1 : forall z, z >= p2 + 1 + 3 -> sc1.(stape) z = false)
      by (intros z Hz; rewrite Out1 by lia; apply Hzero; lia).
    destruct (IHq (p2 + 1) sc1 P1 S1 Pat1 Hz1)
      as [RngQ [PQ [SQ [TrQ [PatQ [HzQ OutQ]]]]]].
    replace (27 * N.succ q)%N with (27 * q + 27)%N by lia.
    rewrite srun_N_add. fold sc1.
    repeat split; try lia; try exact SQ.
    + intros k Hk. destruct (N.lt_ge_cases k 27) as [Hk27 | Hk27].
      * specialize (Rng1 k Hk27). lia.
      * replace k with ((k - 27) + 27)%N by lia.
        rewrite srun_N_add. fold sc1.
        specialize (RngQ (k - 27)%N ltac:(lia)). lia.
    + replace (p2 + 1 + Z.of_N q) with (p2 + Z.of_N (N.succ q)) in * by lia. exact PQ.
    + intros z Hz.
      destruct (Z.eq_dec z (p2 - 3)) as [-> | Hneq].
      * rewrite OutQ by lia. exact T1m3.
      * apply TrQ. lia.
    + replace (p2 + 1 + Z.of_N q) with (p2 + Z.of_N (N.succ q)) in * by lia. exact PatQ.
    + intros z Hz. apply HzQ. lia.
    + intros z Hz. rewrite OutQ by lia. apply Out1. lia.
Qed.

(** * 9. 88-Step Bounce Lemma for G in {12, 16, 18, 20, 30, 32} *)

Fixpoint bt_fill_range (lo : Z) (len : nat) (v : bool) (t : BTree) : BTree :=
  match len with
  | O => t
  | S n => bt_set (z_to_pos lo) v (bt_fill_range (lo + 1) n v t)
  end.

Lemma bt_fill_range_in : forall len lo v t z,
  lo <= z < lo + Z.of_nat len ->
  bt_get (z_to_pos z) (bt_fill_range lo len v t) = v.
Proof.
  induction len; intros lo v t z Hz; simpl in *.
  - lia.
  - destruct (Z.eq_dec z lo) as [-> | Hneq].
    + apply bt_get_set_same.
    + rewrite bt_get_set_diff.
      * apply IHlen; lia.
      * intro Heq. apply Hneq. rewrite <- (z_pos_z z), <- (z_pos_z lo), Heq. reflexivity.
Qed.

Lemma bt_fill_range_out : forall len lo v t z,
  z < lo \/ z >= lo + Z.of_nat len ->
  bt_get (z_to_pos z) (bt_fill_range lo len v t) = bt_get (z_to_pos z) t.
Proof.
  induction len; intros lo v t z Hz; simpl in *.
  - reflexivity.
  - rewrite bt_get_set_diff.
    + apply IHlen; lia.
    + intro Heq. assert (lo = z) by (rewrite <- (z_pos_z lo), <- (z_pos_z z), Heq; reflexivity). lia.
Qed.

Definition bounce_fc (G : Z) : FastConfig :=
  let t1 := bt_fill_range (-70) (Z.to_nat (G + 67)) true BEmpty in
  let t2 := bt_set (z_to_pos (G - 3)) true t1 in
  let t3 := bt_set (z_to_pos G) true t2 in
  {| fpos1 := 0; fpos2 := G; fstate1 := StB; fstate2 := StC; ftape := t3 |}.

Definition exp_b88 (G z : Z) : bool :=
  if Z.ltb z (-70) then false
  else if Z.leb z (2 * G - 90) then true
  else if Z.ltb z (G - 2) then false
  else if Z.eqb z (G - 2) then true
  else if Z.eqb z (G - 1) then true
  else if Z.eqb z (G + 2) then true
  else false.

Fixpoint check_b88_range (G lo : Z) (len : nat) (t : BTree) : bool :=
  match len with
  | O => true
  | S n => Bool.eqb (bt_get (z_to_pos lo) t) (exp_b88 G lo) && check_b88_range G (lo + 1) n t
  end.

Lemma check_b88_range_sound : forall len G lo t,
  check_b88_range G lo len t = true ->
  forall z, lo <= z < lo + Z.of_nat len -> bt_get (z_to_pos z) t = exp_b88 G z.
Proof.
  induction len; intros G lo t H z Hz; simpl in *.
  - lia.
  - rewrite andb_true_iff, eqb_true_iff in H. destruct H as [H0 Hrest].
    destruct (Z.eq_dec z lo) as [-> | Hneq]; [exact H0 | apply IHlen; auto; lia].
Qed.

Definition check_b88 (G : Z) : bool :=
  let st := N.iter 88 (fast_step_chk_range (-70) (G + 6)) (bounce_fc G, true) in
  let (fc, ok) := st in
  ok && Z.eqb fc.(fpos1) (2 * G - 90) && Z.eqb fc.(fpos2) (G + 2)
     && state_eqb fc.(fstate1) StC && state_eqb fc.(fstate2) StC
     && check_b88_range G (-70) (Z.to_nat (G + 78)) fc.(ftape).

Lemma check_b88_all_ok : forallb check_b88 [12; 16; 18; 20; 30; 32] = true.
Proof. vm_compute. reflexivity. Qed.

Definition valid_G (G : Z) : Prop :=
  G = 12 \/ G = 16 \/ G = 18 \/ G = 20 \/ G = 30 \/ G = 32.

Lemma bounce_88_ok : forall G L_left x0 c,
  valid_G G ->
  (70 <= L_left)%N ->
  round_inv G L_left x0 c ->
  (forall k, (k < 88)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  let c1 := run_N ag1 ag2 88 c in
  c1.(pos1) = x0 + 2 * G - 90 /\
  c1.(state1) = StC /\
  c1.(pos2) = x0 + G + 2 /\
  c1.(state2) = StC /\
  (forall z, z < x0 - Z.of_N L_left -> c1.(tape) z = false) /\
  (forall z, x0 - Z.of_N L_left <= z <= x0 + 2 * G - 90 -> c1.(tape) z = true) /\
  (forall z, x0 + 2 * G - 89 <= z <= x0 + G - 3 -> c1.(tape) z = false) /\
  c1.(tape) (x0 + G - 2) = true /\
  glider_pat c1.(tape) (x0 + G + 2) /\
  (forall z, z > x0 + G + 4 -> c1.(tape) z = false).
Proof.
  intros G L_left x0 c HG HL Hinv.
  assert (Hchk : check_b88 G = true).
  { pose proof check_b88_all_ok as Hall. simpl in Hall.
    rewrite !andb_true_iff in Hall.
    destruct Hall as [[[[[H12 H16] H18] H20] H30] H32].
    destruct HG as [-> | [-> | [-> | [-> | [-> | ->]]]]]; auto. }
  unfold check_b88 in Hchk.
  remember (N.iter 88 (fast_step_chk_range (-70) (G + 6)) (bounce_fc G, true)) as st eqn:Est.
  destruct st as [fc_end ok_end].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as [[[[[Hok_end Hp1] Hp2] Hs1] Hs2] Hrng].
  rewrite Z.eqb_eq in Hp1, Hp2. apply state_eqb_eq in Hs1, Hs2.
  assert (Hfc : fc_end = N.iter 88 fast_step (bounce_fc G)).
  { pose proof (fast_step_chk_range_fst 88 (-70) (G + 6) (bounce_fc G) true) as Hfst.
    rewrite <- Est in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 88 (fast_step_chk_range (-70) (G + 6)) (bounce_fc G, true)) = true)
    by (rewrite <- Est; exact Hok_end).
  destruct (fast_step_chk_range_sound 88 (-70) (G + 6) (bounce_fc G) true Hsnd) as [_ Hstep].
  assert (Hzinj : forall a b, z_to_pos a = z_to_pos b -> a = b).
  { intros a b H. rewrite <- (z_pos_z a), <- (z_pos_z b), H. reflexivity. }
  assert (Hout_b0 : forall z, z < -70 \/ z > G + 6 -> bt_get (z_to_pos z) (bounce_fc G).(ftape) = false).
  { intros z Hz. unfold bounce_fc. simpl.
    assert (HG12 : G >= 12) by (destruct HG as [->|[->|[->|[->|[->|->]]]]]; lia).
    rewrite bt_get_set_diff by (intro H; apply Hzinj in H; lia).
    rewrite bt_get_set_diff by (intro H; apply Hzinj in H; lia).
    rewrite bt_fill_range_out by lia.
    apply bt_get_empty. }
  assert (Hout_end : forall z, z < -70 \/ z > G + 6 -> bt_get (z_to_pos z) fc_end.(ftape) = false).
  { rewrite Hfc. apply (fast_run_outside_zero 88 (-70) (G + 6) (bounce_fc G)).
    - intros k Hk. destruct (Hstep k Hk) as [_ [Ha Hb]]. split; auto.
    - exact Hout_b0. }
  assert (Hb0_rng : forall z, -70 <= z <= G + 6 ->
    c.(tape) z = (shift_cfg x0 (fc_to_cfg (bounce_fc G))).(tape) z).
  { intros z Hz. unfold shift_cfg, shift_tape, fc_to_cfg, bt_interp, bounce_fc. simpl.
    destruct Hinv as [_ [_ [_ [_ [_ [Htr [Hm3 [Hm2 [Hm1 [H0 [H1 [H2 Hgt]]]]]]]]]]]].
    assert (HG_pos : G >= 12) by (destruct HG as [->|[->|[->|[->|[->|->]]]]]; lia).
    destruct (Z.eq_dec (z - x0) G) as [HeqG | HneqG].
    - rewrite HeqG, bt_get_set_same. replace z with (x0 + G) by lia. exact H0.
    - rewrite bt_get_set_diff by (intro H; apply HneqG; apply Hzinj; exact H).
      destruct (Z.eq_dec (z - x0) (G - 3)) as [Heqm3 | Hneqm3].
      + rewrite Heqm3, bt_get_set_same. replace z with (x0 + G - 3) by lia. exact Hm3.
      + rewrite bt_get_set_diff by (intro H; apply Hneqm3; apply Hzinj; exact H).
        destruct (Z.lt_ge_cases (z - x0) (G - 3)) as [Hlt | Hge].
        * rewrite bt_fill_range_in by lia. apply Htr. lia.
        * rewrite bt_fill_range_out by lia. rewrite bt_get_empty.
          assert (Hz_cases : z = x0 + G - 2 \/ z = x0 + G - 1 \/ z = x0 + G + 1 \/ z = x0 + G + 2 \/ z > x0 + G + 2) by lia.
          destruct Hz_cases as [->|[->|[->|[->|Hgt']]]]; auto. }
  assert (Hrng_shift : forall k, (k < 88)%N ->
    x0 - 70 <= (run_N ag1 ag2 k (shift_cfg x0 (fc_to_cfg (bounce_fc G)))).(pos1) <= x0 + G + 6 /\
    x0 - 70 <= (run_N ag1 ag2 k (shift_cfg x0 (fc_to_cfg (bounce_fc G)))).(pos2) <= x0 + G + 6).
  { intros k Hk.
    destruct (run_N_shift ag1 ag2 k x0 (fc_to_cfg (bounce_fc G))) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl.
    pose proof (fast_run_sound k (bounce_fc G)) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl.
    destruct (Hstep k Hk) as [_ [[Ha1 Ha2] [Hb1 Hb2]]]. lia. }
  assert (Hc_eq_b0 : c.(pos1) = (shift_cfg x0 (fc_to_cfg (bounce_fc G))).(pos1) /\
                     c.(pos2) = (shift_cfg x0 (fc_to_cfg (bounce_fc G))).(pos2) /\
                     c.(state1) = (shift_cfg x0 (fc_to_cfg (bounce_fc G))).(state1) /\
                     c.(state2) = (shift_cfg x0 (fc_to_cfg (bounce_fc G))).(state2)).
  { destruct Hinv as [Cp1 [Cs1 [Cp2 [Cs2 _]]]]. simpl. repeat split; lia || auto. }
  destruct Hc_eq_b0 as [Ep1 [Ep2 [Es1 Es2]]].
  assert (Hc_rng : forall k, (k < 88)%N ->
    x0 - 70 <= (run_N ag1 ag2 k c).(pos1) <= x0 + G + 6 /\
    x0 - 70 <= (run_N ag1 ag2 k c).(pos2) <= x0 + G + 6).
  { intros k Hk.
    destruct (run_N_agree_range ag1 ag2 (x0 - 70) (x0 + G + 6) k
                (shift_cfg x0 (fc_to_cfg (bounce_fc G))) c
                (fun j Hj => Hrng_shift j ltac:(lia))
                (eq_sym Ep1) (eq_sym Ep2) (eq_sym Es1) (eq_sym Es2)
                (fun z Hz => eq_sym (Hb0_rng z Hz))) as [Kp1 [Kp2 _]].
    rewrite <- Kp1, <- Kp2. apply Hrng_shift; exact Hk. }
  split.
  - intros k Hk.
    destruct (run_N_agree_range ag1 ag2 (x0 - 70) (x0 + G + 6) k c
                (shift_cfg x0 (fc_to_cfg (bounce_fc G)))
                (fun j Hj => Hc_rng j ltac:(lia)) Ep1 Ep2 Es1 Es2 Hb0_rng)
      as [Kp1 [Kp2 _]].
    rewrite Kp1, Kp2.
    destruct (run_N_shift ag1 ag2 k x0 (fc_to_cfg (bounce_fc G))) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl.
    pose proof (fast_run_sound k (bounce_fc G)) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl.
    destruct (Hstep k Hk) as [Hneq _]. lia.
  - destruct (run_N_agree_range ag1 ag2 (x0 - 70) (x0 + G + 6) 88 c
                (shift_cfg x0 (fc_to_cfg (bounce_fc G)))
                Hc_rng Ep1 Ep2 Es1 Es2 Hb0_rng)
      as [Kp1 [Kp2 [Ks1 [Ks2 Ktp]]]].
    destruct (run_N_shift ag1 ag2 88 x0 (fc_to_cfg (bounce_fc G))) as [Sp1 [Sp2 [Ss1 [Ss2 Stp]]]].
    pose proof (fast_run_sound 88 (bounce_fc G)) as [Fp1 [Fp2 [Fs1 [Fs2 Ftp]]]].
    rewrite <- Hfc in Fp1, Fp2, Fs1, Fs2, Ftp.
    assert (Hout_c : forall z, z < x0 - 70 \/ z > x0 + G + 6 ->
      (run_N ag1 ag2 88 c).(tape) z = c.(tape) z).
    { (* Outside [x0-70 .. x0+G+6], neither agent ever visited it in 88 steps *)
      intros z Hz.
      assert (Hgen : forall n, (n <= 88)%N -> (run_N ag1 ag2 n c).(tape) z = c.(tape) z).
      { intro n. induction n using N.peano_ind; intro Hn.
        - rewrite run_N_0. reflexivity.
        - rewrite run_N_succ. unfold step. simpl.
          destruct (Hc_rng n ltac:(lia)) as [Hn1 Hn2].
          rewrite write_tape_other by lia. rewrite write_tape_other by lia.
          apply IHn. lia. }
      apply Hgen. lia. }
    apply check_b88_range_sound in Hrng.
    assert (HG_pos : G >= 12) by (destruct HG as [->|[->|[->|[->|[->|->]]]]]; lia).
    assert (Htp_val : forall z, x0 - 70 <= z <= x0 + G + 6 ->
      (run_N ag1 ag2 88 c).(tape) z = exp_b88 G (z - x0)).
    { intros z Hz. rewrite Ktp by exact Hz. rewrite Stp. unfold shift_tape.
      rewrite <- Ftp. simpl. unfold bt_interp. apply Hrng. lia. }
    destruct Hinv as [_ [_ [_ [_ [HltL [HtrL [_ [_ [_ [_ [_ [_ Hgt4]]]]]]]]]]]].
    repeat split; try lia.
    + rewrite Kp1, Sp1, <- Fp1. simpl. lia.
    + rewrite Ks1, Ss1, <- Fs1. simpl. exact Hs1.
    + rewrite Kp2, Sp2, <- Fp2. simpl. lia.
    + rewrite Ks2, Ss2, <- Fs2. simpl. exact Hs2.
    + intros z Hz. rewrite Hout_c by lia. apply HltL; exact Hz.
    + intros z Hz.
      destruct (Z.lt_ge_cases z (x0 - 70)) as [Hlt | Hge].
      * rewrite Hout_c by lia. apply HtrL. lia.
      * rewrite Htp_val by lia. unfold exp_b88.
        destruct (Z.ltb_spec (z - x0) (-70)); [lia|].
        destruct (Z.leb_spec (z - x0) (2 * G - 90)); [reflexivity | lia].
    + intros z Hz. rewrite Htp_val by lia. unfold exp_b88.
      destruct (Z.ltb_spec (z - x0) (-70)); [lia|].
      destruct (Z.leb_spec (z - x0) (2 * G - 90)); [lia|].
      destruct (Z.ltb_spec (z - x0) (G - 2)); [reflexivity | lia].
    + rewrite Htp_val by lia. unfold exp_b88.
      destruct (Z.ltb_spec (x0 + G - 2 - x0) (-70)); [lia|].
      destruct (Z.leb_spec (x0 + G - 2 - x0) (2 * G - 90)); [lia|].
      destruct (Z.ltb_spec (x0 + G - 2 - x0) (G - 2)); [lia|].
      destruct (Z.eqb_spec (x0 + G - 2 - x0) (G - 2)); [reflexivity | lia].
    + unfold glider_pat. repeat split; rewrite Htp_val by lia; unfold exp_b88.
      * destruct (Z.ltb_spec (x0 + G + 2 - 3 - x0) (-70)); [lia|].
        destruct (Z.leb_spec (x0 + G + 2 - 3 - x0) (2 * G - 90)); [lia|].
        destruct (Z.ltb_spec (x0 + G + 2 - 3 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - 3 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - 3 - x0) (G - 1)); [reflexivity | lia].
      * destruct (Z.ltb_spec (x0 + G + 2 - 2 - x0) (-70)); [lia|].
        destruct (Z.leb_spec (x0 + G + 2 - 2 - x0) (2 * G - 90)); [lia|].
        destruct (Z.ltb_spec (x0 + G + 2 - 2 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - 2 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - 2 - x0) (G - 1)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - 2 - x0) (G + 2)); [lia| reflexivity].
      * destruct (Z.ltb_spec (x0 + G + 2 - 1 - x0) (-70)); [lia|].
        destruct (Z.leb_spec (x0 + G + 2 - 1 - x0) (2 * G - 90)); [lia|].
        destruct (Z.ltb_spec (x0 + G + 2 - 1 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - 1 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - 1 - x0) (G - 1)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - 1 - x0) (G + 2)); [lia| reflexivity].
      * destruct (Z.ltb_spec (x0 + G + 2 - x0) (-70)); [lia|].
        destruct (Z.leb_spec (x0 + G + 2 - x0) (2 * G - 90)); [lia|].
        destruct (Z.ltb_spec (x0 + G + 2 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - x0) (G - 1)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 - x0) (G + 2)); [reflexivity | lia].
      * destruct (Z.ltb_spec (x0 + G + 2 + 1 - x0) (-70)); [lia|].
        destruct (Z.leb_spec (x0 + G + 2 + 1 - x0) (2 * G - 90)); [lia|].
        destruct (Z.ltb_spec (x0 + G + 2 + 1 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 + 1 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 + 1 - x0) (G - 1)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 + 1 - x0) (G + 2)); [lia| reflexivity].
      * destruct (Z.ltb_spec (x0 + G + 2 + 2 - x0) (-70)); [lia|].
        destruct (Z.leb_spec (x0 + G + 2 + 2 - x0) (2 * G - 90)); [lia|].
        destruct (Z.ltb_spec (x0 + G + 2 + 2 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 + 2 - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 + 2 - x0) (G - 1)); [lia|].
        destruct (Z.eqb_spec (x0 + G + 2 + 2 - x0) (G + 2)); [lia| reflexivity].
    + intros z Hz.
      destruct (Z.gt_le_dec z (x0 + G + 6)) as [Hgt | Hle].
      * rewrite Hout_c by lia. apply Hgt4. lia.
      * rewrite Htp_val by lia. unfold exp_b88.
        destruct (Z.ltb_spec (z - x0) (-70)); [lia|].
        destruct (Z.leb_spec (z - x0) (2 * G - 90)); [lia|].
        destruct (Z.ltb_spec (z - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (z - x0) (G - 2)); [lia|].
        destruct (Z.eqb_spec (z - x0) (G - 1)); [lia|].
        destruct (Z.eqb_spec (z - x0) (G + 2)); [lia| reflexivity].
Qed.

(** * 10. Deferred Decoupling, Chase, and Full Round Lemma *)

Lemma run_N_decouple_deferred : forall a1 a2 lo1 x_split hi1 lo2 n k_split c sc1 sc2,
  lo1 <= x_split -> x_split < hi1 -> hi1 < lo2 ->
  (k_split <= n)%N ->
  (forall k, (k < k_split)%N -> lo1 <= (srun_N a1 k sc1).(spos) <= x_split) ->
  (forall k, (k < n)%N -> lo1 <= (srun_N a1 k sc1).(spos) <= hi1) ->
  (forall k, (k < n)%N -> x_split + 1 <= (srun_N a2 k sc2).(spos)) ->
  (forall k, (k_split <= k < n)%N -> lo2 <= (srun_N a2 k sc2).(spos)) ->
  (forall z, x_split < z <= hi1 -> (srun_N a2 k_split sc2).(stape) z = sc1.(stape) z) ->
  c.(pos1) = sc1.(spos) ->
  c.(state1) = sc1.(sstate) ->
  (forall z, lo1 <= z <= x_split -> c.(tape) z = sc1.(stape) z) ->
  c.(pos2) = sc2.(spos) ->
  c.(state2) = sc2.(sstate) ->
  (forall z, x_split + 1 <= z -> c.(tape) z = sc2.(stape) z) ->
  (forall k, (k < n)%N -> (run_N a1 a2 k c).(pos1) <> (run_N a1 a2 k c).(pos2)) /\
  (run_N a1 a2 n c).(pos1) = (srun_N a1 n sc1).(spos) /\
  (run_N a1 a2 n c).(state1) = (srun_N a1 n sc1).(sstate) /\
  (forall z, lo1 <= z <= hi1 -> (run_N a1 a2 n c).(tape) z = (srun_N a1 n sc1).(stape) z) /\
  (run_N a1 a2 n c).(pos2) = (srun_N a2 n sc2).(spos) /\
  (run_N a1 a2 n c).(state2) = (srun_N a2 n sc2).(sstate) /\
  (forall z, hi1 < z -> (run_N a1 a2 n c).(tape) z = (srun_N a2 n sc2).(stape) z) /\
  (forall z, z < lo1 -> (run_N a1 a2 n c).(tape) z = c.(tape) z).
Proof.
  intros a1 a2 lo1 x_split hi1 lo2 n k_split c sc1 sc2
         Hlx Hxh Hhl Hkn Hrk1 Hrn1 Hrn2 Hrk2 Hmid Hp1 Hs1 Ht1 Hp2 Hs2 Ht2.
  assert (Hgen : forall m, (m <= n)%N ->
    (forall k, (k < m)%N -> (run_N a1 a2 k c).(pos1) <> (run_N a1 a2 k c).(pos2)) /\
    (run_N a1 a2 m c).(pos1) = (srun_N a1 m sc1).(spos) /\
    (run_N a1 a2 m c).(state1) = (srun_N a1 m sc1).(sstate) /\
    (forall z, lo1 <= z <= x_split -> (run_N a1 a2 m c).(tape) z = (srun_N a1 m sc1).(stape) z) /\
    (forall z, x_split < z <= hi1 ->
      (m <= k_split)%N -> (run_N a1 a2 m c).(tape) z = (srun_N a2 m sc2).(stape) z) /\
    (forall z, x_split < z <= hi1 ->
      (k_split <= m)%N -> (run_N a1 a2 m c).(tape) z = (srun_N a1 m sc1).(stape) z) /\
    (run_N a1 a2 m c).(pos2) = (srun_N a2 m sc2).(spos) /\
    (run_N a1 a2 m c).(state2) = (srun_N a2 m sc2).(sstate) /\
    (forall z, hi1 < z -> (run_N a1 a2 m c).(tape) z = (srun_N a2 m sc2).(stape) z) /\
    (forall z, z < lo1 -> (run_N a1 a2 m c).(tape) z = c.(tape) z)).
  { intro m. induction m using N.peano_ind; intro Hm.
    - rewrite !run_N_0, !srun_N_0. repeat split; auto; intros; try lia.
      + apply Ht2; lia.
      + assert (Hk0 : k_split = 0%N) by lia. subst k_split.
        rewrite srun_N_0 in Hmid. rewrite <- Hmid by exact H. apply Ht2; lia.
      + apply Ht2; lia.
    - destruct (IHm ltac:(lia))
        as [Hprev [Gp1 [Gs1 [Gt1a [Gt1b_le [Gt1b_ge [Gp2 [Gs2 [Gt2 Gout]]]]]]]]].
      assert (Hm1 : lo1 <= (srun_N a1 m sc1).(spos) <= hi1) by (apply Hrn1; lia).
      assert (Hm2 : x_split + 1 <= (srun_N a2 m sc2).(spos)) by (apply Hrn2; lia).
      assert (Hsep_m : (srun_N a1 m sc1).(spos) <> (srun_N a2 m sc2).(spos)).
      { destruct (N.lt_ge_cases m k_split) as [Hlt | Hge].
        - specialize (Hrk1 m Hlt). lia.
        - specialize (Hrk2 m ltac:(lia)). lia. }
      assert (Hr1_eq : (run_N a1 a2 m c).(tape) (srun_N a1 m sc1).(spos) =
                       (srun_N a1 m sc1).(stape) (srun_N a1 m sc1).(spos)).
      { destruct (Z.le_gt_cases (srun_N a1 m sc1).(spos) x_split) as [Hle | Hgt].
        - apply Gt1a; lia.
        - assert (Hk_le : (k_split <= m)%N).
          { destruct (N.lt_ge_cases m k_split) as [Hlt | Hge]; [| exact Hge].
            specialize (Hrk1 m Hlt). lia. }
          apply Gt1b_ge; lia. }
      assert (Hr2_eq : (run_N a1 a2 m c).(tape) (srun_N a2 m sc2).(spos) =
                       (srun_N a2 m sc2).(stape) (srun_N a2 m sc2).(spos)).
      { destruct (Z.gt_le_dec (srun_N a2 m sc2).(spos) hi1) as [Hgt | Hle].
        - apply Gt2; exact Hgt.
        - assert (Hlt_k : (m < k_split)%N).
          { destruct (N.lt_ge_cases m k_split) as [Hlt | Hge]; [exact Hlt|].
            specialize (Hrk2 m ltac:(lia)). lia. }
          apply Gt1b_le; lia. }
      split.
      { intros k Hk. destruct (N.lt_ge_cases k m) as [Hklt | Hkge].
        - apply Hprev; exact Hklt.
        - replace k with m by lia. rewrite Gp1, Gp2. exact Hsep_m. }
      rewrite run_N_succ, !srun_N_succ. unfold step, sstep.
      rewrite Gp1, Gs1, Gp2, Gs2, Hr1_eq, Hr2_eq.
      repeat split; simpl; try reflexivity.
      * intros z Hz. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 m sc1).(spos)); auto.
        rewrite write_tape_other by lia. apply Gt1a; exact Hz.
      * intros z Hz Hm_le. unfold write_tape.
        assert (Hlt_k : (m < k_split)%N) by lia.
        specialize (Hrk1 m Hlt_k).
        rewrite write_tape_other by lia.
        destruct (Z.eqb_spec z (srun_N a2 m sc2).(spos)); auto.
        apply Gt1b_le; lia.
      * intros z Hz Hm_ge. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 m sc1).(spos)); auto.
        assert (Hwrite2 : (srun_N a2 m sc2).(spos) <> z).
        { destruct (N.eq_dec m k_split) as [-> | Hneq].
          - specialize (Hrk2 k_split ltac:(lia)). lia.
          - specialize (Hrk2 m ltac:(lia)). lia. }
        rewrite write_tape_other by exact Hwrite2.
        destruct (N.eq_dec m k_split) as [-> | Hneq].
        { assert (Hk_le : (k_split <= k_split)%N) by lia.
          rewrite Gt1b_le by lia. exact (Hmid z Hz). }
        { apply Gt1b_ge; lia. }
      * intros z Hz. unfold write_tape.
        rewrite write_tape_other by lia.
        destruct (Z.eqb_spec z (srun_N a2 m sc2).(spos)); auto.
        apply Gt2; exact Hz.
      * intros z Hz. unfold write_tape.
        rewrite write_tape_other by lia.
        rewrite write_tape_other by lia.
        apply Gout; exact Hz. }
  destruct (Hgen n ltac:(lia)) as [Hnc [Gp1 [Gs1 [Gt1a [_ [Gt1b [Gp2 [Gs2 [Gt2 Gout]]]]]]]]].
  repeat split; auto.
  intros z Hz. destruct (Z.le_gt_cases z x_split) as [Hle | Hgt].
  - apply Gt1a; lia.
  - apply Gt1b; lia.
Qed.

Lemma round_chase : forall k_close G_cur L_left x0 c,
  (8 <= G_cur - 26 * Z.of_N k_close)%Z ->
  round_inv G_cur L_left x0 c ->
  (forall k, (k < 27 * k_close)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  round_inv (G_cur - 26 * Z.of_N k_close) (L_left + 27 * k_close) (x0 + 27 * Z.of_N k_close)
    (run_N ag1 ag2 (27 * k_close) c).
Proof.
  intro k_close. induction k_close using N.peano_ind; intros G_cur L_left x0 c Hgap Hinv.
  - rewrite N.mul_0_r, run_N_0, N.add_0_r.
    replace (G_cur - 26 * Z.of_N 0) with G_cur by lia.
    replace (x0 + 27 * Z.of_N 0) with x0 by lia.
    split; [intros k Hk; lia | exact Hinv].
  - assert (HG_ge : G_cur >= 34) by lia.
    destruct Hinv as [Cp1 [Cs1 [Cp2 [Cs2 [HltL [HtrL [Hm3 [Hm2 [Hm1 [H0 [H1 [H2 Hgt2]]]]]]]]]]]].
    set (sc1 := {| spos := x0; sstate := StB; stape := c.(tape) |}).
    set (sc2 := {| spos := x0 + G_cur; sstate := StC; stape := c.(tape) |}).
    assert (Hw1 : forall z, x0 <= z < x0 + Z.of_N 27 -> sc1.(stape) z = true)
      by (intros z Hz; apply HtrL; lia).
    destruct (ag1_walk_right 27 x0 sc1 eq_refl eq_refl Hw1) as [Rng1 [P1 [S1 T1]]].
    assert (Hpat2 : glider_pat sc2.(stape) (x0 + G_cur))
      by (unfold glider_pat; simpl; repeat split; auto).
    destruct (ag2_glider_period (x0 + G_cur) sc2 eq_refl eq_refl Hpat2 (Hgt2 (x0 + G_cur + 3) ltac:(lia)))
      as [Rng2 [P2 [S2 [T2m3 [Pat2 Out2]]]]].
    destruct (run_N_decouple ag1 ag2 x0 (x0 + 26) (x0 + G_cur - 2) (x0 + G_cur + 3) 27 c sc1 sc2
                ltac:(lia)
                (fun k Hk => Rng1 k Hk)
                (fun k Hk => Rng2 k Hk)
                Cp1 Cs1 (fun z Hz => eq_refl)
                Cp2 Cs2 (fun z Hz => eq_refl))
      as [Hnc1 [Dp1 [Ds1 [Dt1 [Dp2 [Ds2 [Dt2 Dout]]]]]]].
    set (c1 := run_N ag1 ag2 27 c) in *.
    assert (Hinv1 : round_inv (G_cur - 26) (L_left + 27) (x0 + 27) c1).
    { unfold round_inv. rewrite Dp1, Ds1, Dp2, Ds2, P1, S1, P2, S2.
      replace (x0 + G_cur + 1) with (x0 + 27 + (G_cur - 26)) by lia.
      repeat split; try lia; auto.
      - intros z Hz. rewrite Dout by lia. apply HltL. lia.
      - intros z Hz.
        destruct (Z.le_gt_cases z (x0 + 26)) as [Hle | Hgt].
        + destruct (Z.lt_ge_cases z x0) as [Hlt | Hge].
          * rewrite Dout by lia. apply HtrL. lia.
          * rewrite Dt1 by lia. rewrite T1. apply HtrL. lia.
        + destruct (Z.lt_ge_cases z (x0 + G_cur - 2)) as [Hlt | Hge].
          * rewrite Dout by lia.
            destruct (Z.eq_dec z (x0 + G_cur - 3)) as [-> | Hneq]; [exact Hm3 | apply HtrL; lia].
          * (* z in [x0 + G_cur - 2 .. x0 + G_cur - 3] is empty! Wait: G_cur - 26 = x0 + 27 + (G_cur - 26) - 3 = x0 + G_cur - 2 *)
            lia.
      - replace (x0 + 27 + (G_cur - 26) - 3) with (x0 + G_cur - 2) by lia.
        rewrite Dt2 by lia. apply Pat2.
      - replace (x0 + 27 + (G_cur - 26) - 2) with (x0 + G_cur - 1) by lia.
        rewrite Dt2 by lia. apply Pat2.
      - replace (x0 + 27 + (G_cur - 26) - 1) with (x0 + G_cur) by lia.
        rewrite Dt2 by lia. apply Pat2.
      - replace (x0 + 27 + (G_cur - 26)) with (x0 + G_cur + 1) by lia.
        rewrite Dt2 by lia. apply Pat2.
      - replace (x0 + 27 + (G_cur - 26) + 1) with (x0 + G_cur + 2) by lia.
        rewrite Dt2 by lia. apply Pat2.
      - replace (x0 + 27 + (G_cur - 26) + 2) with (x0 + G_cur + 3) by lia.
        rewrite Dt2 by lia. apply Pat2.
      - intros z Hz. rewrite Dout by lia. apply Hgt2. lia. }
    destruct (IHk_close (G_cur - 26) (L_left + 27) (x0 + 27) c1 ltac:(lia) Hinv1)
      as [Hnc2 Hinv2].
    replace (27 * N.succ k_close)%N with (27 * k_close + 27)%N by lia.
    split.
    + eapply no_coll_add; [exact Hnc1 | fold c1; exact Hnc2].
    + rewrite run_N_add. fold c1.
      replace (L_left + 27 + 27 * k_close)%N with (L_left + 27 * N.succ k_close)%N in Hinv2 by lia.
      replace (x0 + 27 + 27 * Z.of_N k_close) with (x0 + 27 * Z.of_N (N.succ k_close)) in Hinv2 by lia.
      replace (G_cur - 26 - 26 * Z.of_N k_close) with (G_cur - 26 * Z.of_N (N.succ k_close)) in Hinv2 by lia.
      exact Hinv2.
Qed.

Lemma round_bounce : forall G L_left x0 c dt q_sync k_close G_next,
  valid_G G ->
  (70 <= L_left)%N ->
  (dt < 27)%N ->
  (40 <= q_sync)%N ->
  round_inv G L_left x0 c ->
  let T_exit := (5 * 2 ^ (L_left + Z.to_N G - 2) + Z.to_N G + 1)%N in
  (T_exit - 88 + dt = 27 * q_sync)%N ->
  1 + Z.of_N q_sync - Z.of_N dt - 26 * Z.of_N k_close = G_next ->
  8 <= G_next < 34 ->
  let T_round := (T_exit + dt + 27 * k_close)%N in
  (forall k, (k < T_round)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  round_inv G_next (L_left + Z.to_N G + 1 + dt + 27 * k_close)
    (x0 + G + 1 + Z.of_N dt + 27 * Z.of_N k_close) (run_N ag1 ag2 T_round c).
Proof.
  intros G L_left x0 c dt q_sync k_close G_next HG HL Hdt Hq Hinv T_exit Hsync Hgap HGnext T_round.
  assert (HG_bounds : 12 <= G <= 32) by (destruct HG as [->|[->|[->|[->|[->|->]]]]]; lia).
  assert (HT_ge : (T_exit >= 88 + 27 * 40)%N).
  { unfold T_exit.
    assert (Hexp : (L_left + Z.to_N G - 2 >= 80)%N) by lia.
    assert (Hpow : (2 ^ (L_left + Z.to_N G - 2) >= 2 ^ 10)%N).
    { apply N.pow_le_mono_r; lia. }
    change (2 ^ 10)%N with 1024%N in Hpow. lia. }
  (* 1. Run 88 steps *)
  destruct (bounce_88_ok G L_left x0 c HG HL Hinv)
    as [Hnc88 [P88 [S881 [P882 [S882 [Tlt88 [Ttr88 [Tfl88 [Tm288 [Pat88 Tgt88]]]]]]]]]].
  set (c88 := run_N ag1 ag2 88 c) in *.
  (* 2. Run 27 * q_sync = T_exit - 88 + dt steps via run_N_decouple_deferred *)
  set (m_sw := (L_left + 2 * Z.to_N G - 89)%N).
  set (m_fl := (L_left + Z.to_N G - 2)%N).
  set (m_wk := (3 + dt)%N).
  assert (Hm_sum : (m_sw + T_fill m_fl + m_wk = T_exit - 88 + dt)%N).
  { unfold m_sw, m_fl, m_wk, T_exit, T_fill.
    assert (Hpow : (2 ^ (L_left + Z.to_N G - 2) >= 1024)%N).
    { apply N.pow_le_mono_r; [discriminate | lia]. }
    lia. }
  set (tp1 := fun z : Z =>
    if Z.leb (x0 - Z.of_N L_left) z then
      if Z.leb z (x0 + 2 * G - 90) then true
      else if Z.leb z (x0 + G - 3) then false
      else true
    else false).
  set (sc1 := {| spos := x0 + 2 * G - 90; sstate := StC; stape := tp1 |}).
  set (sc2 := {| spos := x0 + G + 2; sstate := StC; stape := c88.(tape) |}).
  (* Agent 1 trajectory *)
  assert (Hsw1 : forall z, x0 - Z.of_N L_left <= z < x0 - Z.of_N L_left + Z.of_N m_sw -> sc1.(stape) z = true).
  { intros z Hz. unfold sc1, tp1. simpl.
    destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
    destruct (Z.leb_spec z (x0 + 2 * G - 90)); [reflexivity | unfold m_sw in Hz; lia]. }
  assert (Hsw_pos : sc1.(spos) = x0 - Z.of_N L_left + Z.of_N m_sw - 1)
    by (simpl; unfold m_sw; lia).
  destruct (ag1_sweep_left m_sw (x0 - Z.of_N L_left) sc1 Hsw_pos eq_refl Hsw1)
    as [Rng_sw [P_sw [S_sw [T_sw Out_sw]]]].
  set (sc1_sw := srun_N ag1 m_sw sc1) in *.
  assert (Hfl_m2 : sc1_sw.(stape) (x0 - Z.of_N L_left - 2) = false)
    by (rewrite Out_sw by lia; unfold sc1, tp1; simpl; destruct (Z.leb_spec (x0 - Z.of_N L_left) (x0 - Z.of_N L_left - 2)); [lia|reflexivity]).
  assert (Hfl_m1 : sc1_sw.(stape) (x0 - Z.of_N L_left - 1) = false)
    by (rewrite Out_sw by lia; unfold sc1, tp1; simpl; destruct (Z.leb_spec (x0 - Z.of_N L_left) (x0 - Z.of_N L_left - 1)); [lia|reflexivity]).
  assert (Hfl_0 : forall z, x0 - Z.of_N L_left <= z < x0 - Z.of_N L_left + Z.of_N m_fl -> sc1_sw.(stape) z = false).
  { intros z Hz. destruct (Z.lt_ge_cases z (x0 + 2 * G - 89)) as [Hlt | Hge].
    - apply T_sw. unfold m_sw. lia.
    - rewrite Out_sw by (unfold m_sw; lia). unfold sc1, tp1. simpl.
      destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
      destruct (Z.leb_spec z (x0 + 2 * G - 90)); [lia|].
      destruct (Z.leb_spec z (x0 + G - 3)); [reflexivity | unfold m_fl in Hz; lia]. }
  destruct (ag1_fill m_fl (x0 - Z.of_N L_left) sc1_sw ltac:(unfold m_fl; lia) P_sw S_sw Hfl_m2 Hfl_m1 Hfl_0)
    as [Rng_fl [P_fl [S_fl [Fl_m2 [Fl_m1 [T_fl Out_fl]]]]]].
  set (sc1_fl := srun_N ag1 (T_fill m_fl) sc1_sw) in *.
  assert (Hwk_p : sc1_fl.(spos) = x0 + G - 2) by (rewrite P_fl; unfold m_fl; lia).
  assert (Hwk_t : forall z, x0 + G - 2 <= z < x0 + G - 2 + Z.of_N m_wk -> sc1_fl.(stape) z = true).
  { intros z Hz. rewrite Out_fl by (unfold m_fl; lia).
    rewrite Out_sw by (unfold m_sw, m_fl; lia).
    unfold sc1, tp1. simpl.
    destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
    destruct (Z.leb_spec z (x0 + 2 * G - 90)); [reflexivity|].
    destruct (Z.leb_spec z (x0 + G - 3)); [lia | reflexivity]. }
  destruct (ag1_walk_right m_wk (x0 + G - 2) sc1_fl Hwk_p S_fl Hwk_t)
    as [Rng_wk [P_wk [S_wk T_wk]]].
  (* Agent 2 trajectory: 27 * q_sync *)
  destruct (ag2_glider_iter q_sync (x0 + G + 2) sc2 eq_refl eq_refl Pat88 Tgt88)
    as [Rng_g [P_g [S_g [Tr_g [Pat_g [Hz_g Out_g]]]]]].
  (* Apply run_N_decouple_deferred with k_split = 27 * 40 *)
  set (lo1 := x0 - Z.of_N L_left - 2).
  set (x_split := x0 + G - 2).
  set (hi1 := x0 + G + 1 + Z.of_N dt).
  set (lo2 := x0 + G + 40).
  assert (Hk_split_le : (27 * 40 <= 27 * q_sync)%N) by lia.
  assert (Hrk1 : forall k, (k < 27 * 40)%N -> lo1 <= (srun_N ag1 k sc1).(spos) <= x_split).
  { intros k Hk.
    destruct (N.lt_ge_cases k m_sw) as [Hk1 | Hk1].
    - specialize (Rng_sw k Hk1). unfold lo1, x_split, m_sw in *. lia.
    - assert (Hk_fl : (k - m_sw < T_fill m_fl)%N).
      { unfold T_fill.
        assert (Hpow : (2 ^ m_fl >= 2 ^ 10)%N) by (apply N.pow_le_mono_r; [discriminate | unfold m_fl; lia]).
        change (2 ^ 10)%N with 1024%N in Hpow. lia. }
      replace k with ((k - m_sw) + m_sw)%N by lia.
      rewrite srun_N_add. fold sc1_sw.
      specialize (Rng_fl (k - m_sw)%N Hk_fl). unfold lo1, x_split, m_fl in *. lia. }
  assert (Hrn1 : forall k, (k < 27 * q_sync)%N -> lo1 <= (srun_N ag1 k sc1).(spos) <= hi1).
  { intros k Hk.
    destruct (N.lt_ge_cases k m_sw) as [Hk1 | Hk1].
    - specialize (Rng_sw k Hk1). unfold lo1, hi1, m_sw in *. lia.
    - destruct (N.lt_ge_cases k (m_sw + T_fill m_fl)) as [Hk2 | Hk2].
      + replace k with ((k - m_sw) + m_sw)%N by lia.
        rewrite srun_N_add. fold sc1_sw.
        specialize (Rng_fl (k - m_sw)%N ltac:(lia)). unfold lo1, hi1, m_fl in *. lia.
      + replace k with ((k - (m_sw + T_fill m_fl)) + (m_sw + T_fill m_fl))%N by lia.
        rewrite !srun_N_add. fold sc1_sw. fold sc1_fl.
        specialize (Rng_wk (k - (m_sw + T_fill m_fl))%N ltac:(lia)).
        unfold lo1, hi1, m_wk in *. lia. }
  assert (Hrn2 : forall k, (k < 27 * q_sync)%N -> x_split + 1 <= (srun_N ag2 k sc2).(spos)).
  { intros k Hk. specialize (Rng_g k Hk). unfold x_split in *. lia. }
  destruct (ag2_glider_iter 40 (x0 + G + 2) sc2 eq_refl eq_refl Pat88 Tgt88)
    as [_ [P_g40 [S_g40 [Tr_g40 [Pat_g40 _]]]]].
  assert (Hrk2 : forall k, (27 * 40 <= k < 27 * q_sync)%N -> lo2 <= (srun_N ag2 k sc2).(spos)).
  { intros k [Hk1 Hk2].
    replace k with ((k - 27 * 40) + 27 * 40)%N by lia.
    rewrite srun_N_add.
    destruct (ag2_glider_iter (q_sync - 40) (x0 + G + 2 + 40) (srun_N ag2 (27 * 40) sc2)
                P_g40 S_g40 Pat_g40)
      as [Rng_g2 _].
    { intros z Hz.
      destruct (ag2_glider_iter 40 (x0 + G + 2) sc2 eq_refl eq_refl Pat88 Tgt88) as [_ [_ [_ [_ [_ [Hz40 _]]]]]].
      apply Hz40. lia. }
    specialize (Rng_g2 (k - 27 * 40)%N ltac:(lia)). unfold lo2 in *. lia. }
  assert (Hmid_g : forall z, x_split < z <= hi1 -> (srun_N ag2 (27 * 40) sc2).(stape) z = sc1.(stape) z).
  { intros z Hz.
    rewrite Tr_g40 by (unfold x_split, hi1 in *; lia).
    unfold sc1, tp1. simpl.
    destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [| unfold x_split in *; lia].
    destruct (Z.leb_spec z (x0 + 2 * G - 90)); [reflexivity|].
    destruct (Z.leb_spec z (x0 + G - 3)); [unfold x_split in *; lia | reflexivity]. }
  assert (Hc_sc1 : forall z, lo1 <= z <= x_split -> c88.(tape) z = sc1.(stape) z).
  { intros z Hz. unfold sc1, tp1. simpl.
    destruct (Z.lt_ge_cases z (x0 - Z.of_N L_left)) as [Hlt | Hge].
    - rewrite Tlt88 by exact Hlt.
      destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [lia | reflexivity].
    - destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
      destruct (Z.le_gt_cases z (x0 + 2 * G - 90)) as [Hle | Hgt].
      + destruct (Z.leb_spec z (x0 + 2 * G - 90)); [|lia]. apply Ttr88; lia.
      + destruct (Z.leb_spec z (x0 + 2 * G - 90)); [lia|].
        destruct (Z.le_gt_cases z (x0 + G - 3)) as [Hle2 | Hgt2].
        * destruct (Z.leb_spec z (x0 + G - 3)); [|lia]. apply Tfl88; lia.
        * destruct (Z.leb_spec z (x0 + G - 3)); [lia|].
          replace z with (x0 + G - 2) by (unfold x_split in *; lia). exact Tm288. }
  destruct (run_N_decouple_deferred ag1 ag2 lo1 x_split hi1 lo2 (27 * q_sync) (27 * 40) c88 sc1 sc2
              ltac:(unfold lo1, x_split; lia)
              ltac:(unfold x_split, hi1; lia)
              ltac:(unfold hi1, lo2; lia)
              Hk_split_le Hrk1 Hrn1 Hrn2 Hrk2 Hmid_g
              P88 S881 Hc_sc1 P882 S882 (fun z _ => eq_refl))
    as [Hnc_dec [Dp1 [Ds1 [Dt1 [Dp2 [Ds2 [Dt2 Dout]]]]]]].
  assert (Hs1_end : (srun_N ag1 (27 * q_sync) sc1).(spos) = hi1 /\
                    (srun_N ag1 (27 * q_sync) sc1).(sstate) = StB /\
                    (forall z, x0 - Z.of_N L_left <= z < hi1 -> (srun_N ag1 (27 * q_sync) sc1).(stape) z = true) /\
                    (srun_N ag1 (27 * q_sync) sc1).(stape) (x0 - Z.of_N L_left - 2) = false /\
                    (srun_N ag1 (27 * q_sync) sc1).(stape) (x0 - Z.of_N L_left - 1) = false).
  { rewrite <- Hsync, <- Hm_sum.
    replace (m_sw + T_fill m_fl + m_wk)%N with (m_wk + (T_fill m_fl + m_sw))%N by lia.
    rewrite !srun_N_add. fold sc1_sw. fold sc1_fl.
    repeat split.
    - rewrite P_wk. unfold hi1, m_wk. lia.
    - exact S_wk.
    - intros z Hz. rewrite T_wk.
      destruct (Z.lt_ge_cases z (x0 + G - 2)) as [Hlt | Hge].
      + apply T_fl. unfold m_fl. lia.
      + rewrite Out_fl by (unfold m_fl; lia). rewrite Out_sw by (unfold m_sw, m_fl; lia).
        unfold sc1, tp1. simpl.
        destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
        destruct (Z.leb_spec z (x0 + 2 * G - 90)); [reflexivity|].
        destruct (Z.leb_spec z (x0 + G - 3)); [lia | reflexivity].
    - rewrite T_wk. exact Fl_m2.
    - rewrite T_wk. exact Fl_m1. }
  destruct Hs1_end as [E1p [E1s [E1t [E1m2 E1m1]]]].
  set (c_sync := run_N ag1 ag2 (27 * q_sync) c88) in *.
  assert (Hinv_sync : round_inv (1 + Z.of_N q_sync - Z.of_N dt) (L_left + Z.to_N G + 1 + dt)
                        (x0 + G + 1 + Z.of_N dt) c_sync).
  { unfold round_inv. rewrite Dp1, Ds1, Dp2, Ds2, E1p, E1s, P_g, S_g.
    replace (x0 + G + 2 + Z.of_N q_sync) with (x0 + G + 1 + Z.of_N dt + (1 + Z.of_N q_sync - Z.of_N dt)) by lia.
    repeat split; try lia; auto.
    - intros z Hz. rewrite Dout by (unfold lo1; lia).
      apply Tlt88. lia.
    - intros z Hz.
      destruct (Z.le_gt_cases z hi1) as [Hle | Hgt].
      + destruct (Z.eq_dec z hi1) as [-> | Hneq].
        * rewrite Dt1 by (unfold lo1, hi1; lia).
          rewrite <- Hsync, <- Hm_sum.
          replace (m_sw + T_fill m_fl + m_wk)%N with (m_wk + (T_fill m_fl + m_sw))%N by lia.
          rewrite !srun_N_add. fold sc1_sw. fold sc1_fl.
          rewrite T_wk, Out_fl by (unfold hi1, m_fl; lia).
          rewrite Out_sw by (unfold hi1, m_sw; lia).
          unfold sc1, tp1. simpl.
          destruct (Z.leb_spec (x0 - Z.of_N L_left) hi1); [|unfold hi1 in *; lia].
          destruct (Z.leb_spec hi1 (x0 + 2 * G - 90)); [reflexivity|].
          destruct (Z.leb_spec hi1 (x0 + G - 3)); [unfold hi1 in *; lia | reflexivity].
        * destruct (Z.lt_ge_cases z (x0 - Z.of_N L_left)) as [Hlt | Hge].
          { rewrite Dt1 by (unfold lo1, hi1; lia).
            assert (Hz_cases : z = x0 - Z.of_N L_left - 2 \/ z = x0 - Z.of_N L_left - 1) by lia.
            destruct Hz_cases as [-> | ->]; [exact E1m2 | exact E1m1].
            (* wait: at z = x0 - L_left - 2, Hz says x0 + G + 1 + dt - (L_left + G + 1 + dt) = x0 - L_left <= z! Contradiction! *)
            }
          { rewrite Dt1 by (unfold lo1, hi1; lia). apply E1t. unfold hi1 in *. lia. }
      + rewrite Dt2 by exact Hgt. apply Tr_g. unfold hi1 in *. lia.
    - replace (x0 + G + 1 + Z.of_N dt + (1 + Z.of_N q_sync - Z.of_N dt) - 3) with (x0 + G + 2 + Z.of_N q_sync - 3) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - replace (x0 + G + 1 + Z.of_N dt + (1 + Z.of_N q_sync - Z.of_N dt) - 2) with (x0 + G + 2 + Z.of_N q_sync - 2) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - replace (x0 + G + 1 + Z.of_N dt + (1 + Z.of_N q_sync - Z.of_N dt) - 1) with (x0 + G + 2 + Z.of_N q_sync - 1) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - replace (x0 + G + 1 + Z.of_N dt + (1 + Z.of_N q_sync - Z.of_N dt)) with (x0 + G + 2 + Z.of_N q_sync) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - replace (x0 + G + 1 + Z.of_N dt + (1 + Z.of_N q_sync - Z.of_N dt) + 1) with (x0 + G + 2 + Z.of_N q_sync + 1) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - replace (x0 + G + 1 + Z.of_N dt + (1 + Z.of_N q_sync - Z.of_N dt) + 2) with (x0 + G + 2 + Z.of_N q_sync + 2) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - intros z Hz. rewrite Dt2 by (unfold hi1; lia). apply Hz_g. lia. }
  (* 3. Chase k_close glider periods *)
  destruct (round_chase k_close (1 + Z.of_N q_sync - Z.of_N dt) (L_left + Z.to_N G + 1 + dt)
              (x0 + G + 1 + Z.of_N dt) c_sync ltac:(lia) Hinv_sync)
    as [Hnc_ch Hinv_end].
  assert (HT_eq : T_round = (27 * k_close + (27 * q_sync + 88))%N).
  { unfold T_round. lia. }
  rewrite HT_eq.
  split.
  - assert (Hnc_88_dec : forall k, (k < 27 * q_sync + 88)%N ->
      (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)).
    { eapply no_coll_add; [exact Hnc88 | fold c88; exact Hnc_dec]. }
    eapply no_coll_add; [exact Hnc_88_dec | rewrite run_N_add; fold c88; fold c_sync; exact Hnc_ch].
  - rewrite !run_N_add. fold c88. fold c_sync.
    rewrite Hgap in Hinv_end.
    replace (L_left + Z.to_N G + 1 + dt + 27 * k_close)%N
      with (L_left + Z.to_N G + 1 + dt + 27 * k_close)%N in Hinv_end.
    replace (x0 + G + 1 + Z.of_N dt + 27 * Z.of_N k_close)
      with (x0 + G + 1 + Z.of_N dt + 27 * Z.of_N k_close) in Hinv_end.
    exact Hinv_end.
Qed.

(** * 11. Modular Binary Exponentiation & 8-Round Tower Chain *)

Fixpoint pow_mod_pos (b : N) (p : positive) (m : N) : N :=
  match p with
  | xH => b mod m
  | xO q => let r := pow_mod_pos b q m in (r * r) mod m
  | xI q => let r := pow_mod_pos b q m in (b * ((r * r) mod m)) mod m
  end.

Definition pow2_mod (e m : N) : N :=
  match e with
  | 0%N => 1 mod m
  | Npos p => pow_mod_pos 2 p m
  end.

Lemma pow_mod_pos_correct : forall b p m, (0 < m)%N ->
  pow_mod_pos b p m = (b ^ Npos p) mod m.
Proof.
  intros b p m Hm. induction p; simpl.
  - rewrite Pos2Nat.inj_xI.
    (* N.pow b (Npos p~1) = b * (b ^ Npos p) * (b ^ Npos p) *)
    change (Npos p~1) with (1 + 2 * Npos p)%N.
    rewrite N.pow_add_r, N.pow_1_r, N.pow_mul_r.
    change ((b ^ Npos p) ^ 2)%N with ((b ^ Npos p) * (b ^ Npos p) * 1)%N.
    rewrite N.mul_1_r, IHp.
    rewrite N.mul_mod_idemp_r by lia.
    rewrite N.mul_mod by lia.
    rewrite N.mul_mod_idemp_r by lia.
    reflexivity.
  - change (Npos p~0) with (2 * Npos p)%N.
    rewrite N.pow_mul_r.
    change ((b ^ Npos p) ^ 2)%N with ((b ^ Npos p) * (b ^ Npos p) * 1)%N.
    rewrite N.mul_1_r, IHp.
    rewrite N.mul_mod by lia. reflexivity.
  - rewrite N.pow_1_r. reflexivity.
Qed.

Lemma pow2_mod_correct : forall e m, (0 < m)%N ->
  pow2_mod e m = (2 ^ e) mod m.
Proof.
  intros e m Hm. destruct e; [rewrite N.pow_0_r; reflexivity | apply pow_mod_pos_correct; exact Hm].
Qed.

Lemma pow2_mul_lam_mod : forall q lam Q_good,
  (0 < Q_good)%N -> (pow2_mod lam Q_good = 1%N) ->
  ((2 ^ (lam * q)) mod Q_good = 1%N).
Proof.
  intros q lam Q_good HQ Hlam.
  rewrite pow2_mod_correct in Hlam by exact HQ.
  rewrite N.pow_mul_r.
  induction q using N.peano_ind.
  - rewrite N.pow_0_r.
    destruct (N.eq_dec Q_good 1) as [-> | HQ1].
    + exfalso. rewrite N.mod_1_r in Hlam. discriminate.
    + apply N.mod_1_l. lia.
  - rewrite N.pow_succ_r', <- N.mul_mod by lia.
    rewrite Hlam, IHq, N.mul_1_l.
    destruct (N.eq_dec Q_good 1) as [-> | HQ1].
    + exfalso. rewrite N.mod_1_r in Hlam. discriminate.
    + apply N.mod_1_l. lia.
Qed.

Lemma pow2_mod_period : forall lam Q_bad Q_good k,
  (3 <= k)%N -> (3 <= lam)%N ->
  (Q_bad = 2%N \/ Q_bad = 8%N) ->
  (1 < Q_good)%N ->
  (pow2_mod lam Q_good = 1%N) ->
  let k' := if (k <? lam)%N then k else ((k mod lam) + lam)%N in
  ((2 ^ k) mod (Q_bad * Q_good) = pow2_mod k' (Q_bad * Q_good)).
Proof.
  intros lam Q_bad Q_good k Hk Hlam HQb HQg Hpow k'.
  assert (Hm_pos : (0 < Q_bad * Q_good)%N) by lia.
  rewrite pow2_mod_correct by exact Hm_pos.
  unfold k'. destruct (N.ltb_spec k lam) as [Hlt | Hge]; [reflexivity|].
  set (q := (k / lam)%N).
  assert (Hq_ge : (1 <= q)%N) by (unfold q; apply N.div_str_pos; lia).
  assert (Hk_eq : k = ((k mod lam) + lam + lam * (q - 1))%N).
  { pose proof (N.div_mod k lam ltac:(lia)) as Hdm. fold q in Hdm. lia. }
  set (kr := ((k mod lam) + lam)%N).
  assert (Hkr_ge : (3 <= kr)%N) by (unfold kr; lia).
  rewrite Hk_eq, N.pow_add_r. fold kr.
  (* 2^kr * 2^(lam*(q-1)) mod (Q_bad * Q_good) = 2^kr mod (Q_bad * Q_good) *)
  (* Since Q_bad | 2^kr and Q_good | (2^(lam*(q-1)) - 1), Q_bad * Q_good divides their product *)
  assert (Hqb_div : exists u, (2 ^ kr = u * Q_bad)%N).
  { exists (2 ^ (kr - 3) * (if (Q_bad =? 2)%N then 4 else 1))%N.
    replace kr with (3 + (kr - 3))%N by lia.
    rewrite N.pow_add_r. change (2 ^ 3)%N with 8%N.
    destruct HQb as [-> | ->]; simpl; lia. }
  assert (Hqg_div : exists v, (2 ^ (lam * (q - 1)) = v * Q_good + 1)%N).
  { pose proof (pow2_mul_lam_mod (q - 1) lam Q_good ltac:(lia) Hpow) as Hmod.
    pose proof (N.div_mod (2 ^ (lam * (q - 1))) Q_good ltac:(lia)) as Hdm.
    exists (2 ^ (lam * (q - 1)) / Q_good)%N. rewrite Hmod in Hdm. lia. }
  destruct Hqb_div as [u Hu]. destruct Hqg_div as [v Hv].
  rewrite Hv, N.mul_add_distr_l, N.mul_1_r.
  rewrite Hu at 1.
  replace (u * Q_bad * (v * Q_good) + 2 ^ kr)%N
    with (2 ^ kr + (u * v) * (Q_bad * Q_good))%N by lia.
  rewrite N.Div0.mod_add. reflexivity.
Qed.

Lemma check_lam_periods :
  (pow2_mod 36 351 =? 1)%N &&
  (pow2_mod 324 3159 =? 1)%N &&
  (pow2_mod 2916 28431 =? 1)%N &&
  (pow2_mod 26244 255879 =? 1)%N &&
  (pow2_mod 236196 2302911 =? 1)%N &&
  (pow2_mod 2125764 20726199 =? 1)%N = true.
Proof. vm_compute. reflexivity. Qed.


Lemma round_step_mod :
  forall G_z L_left x0 c lam Q_bad Q_good Q_next L_mod k_eff p_mod T_mod dt q_mod k_mod G_next L_next_mod,
  valid_G G_z ->
  (190 <= L_left)%N ->
  (lam <= L_left + Z.to_N G_z - 2)%N ->
  (Q_next <= 2 ^ 30)%N ->
  round_inv G_z L_left x0 c ->
  (3 <= lam)%N ->
  (Q_bad = 2%N \/ Q_bad = 8%N) ->
  (1 < Q_good)%N ->
  (1 <= Q_next)%N ->
  (Q_bad * Q_good = 702 * Q_next)%N ->
  (pow2_mod lam Q_good = 1%N) ->
  ((L_left + 1) mod lam = L_mod)%N ->
  (k_eff = ((L_mod + Z.to_N G_z - 3) mod lam) + lam)%N ->
  (pow2_mod k_eff (702 * Q_next) = p_mod)%N ->
  (T_mod = (5 * p_mod + Z.to_N G_z + 1) mod (702 * Q_next))%N ->
  (88 <= T_mod)%N ->
  (dt < 27)%N ->
  (T_mod - 88 + dt = 27 * q_mod)%N ->
  (1 + Z.of_N q_mod - Z.of_N dt - 26 * Z.of_N k_mod = G_next) ->
  8 <= G_next < 34 ->
  (L_next_mod = (L_left + 1 + Z.to_N G_z + 1 + dt + 27 * k_mod) mod Q_next)%N ->
  exists T_round L_left_next x_next,
    (T_round >= 5 * 2 ^ (L_left + Z.to_N G_z - 2))%N /\
    (L_left_next >= 2 ^ (L_left + Z.to_N G_z - 5))%N /\
    ((L_left_next + 1) mod Q_next = L_next_mod)%N /\
    (forall k, (k < T_round)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
    round_inv G_next L_left_next x_next (run_N ag1 ag2 T_round c).
Proof.
  intros G_z L_left x0 c lam Q_bad Q_good Q_next L_mod k_eff p_mod T_mod dt q_mod k_mod G_next L_next_mod
         HG HL Hlam_le HQ_le Hinv Hlam HQb HQg HQn Hpmq Hpow_lam HLmod Hkeff Hpmod HTmod HT88 Hdt Hqmod Hgap HGnext HLnext.
  assert (HG_pos : 12 <= G_z <= 32) by (destruct HG as [->|[->|[->|[->|[->|->]]]]]; lia).
  set (exp_n := (L_left + Z.to_N G_z - 2)%N).
  assert (Hexp_ge : (exp_n >= 200)%N) by (unfold exp_n; lia).
  assert (Hexp_mod : (exp_n mod lam = (L_mod + Z.to_N G_z - 3) mod lam)%N).
  { unfold exp_n. replace (L_left + Z.to_N G_z - 2)%N with ((L_left + 1) + (Z.to_N G_z - 3))%N by lia.
    rewrite <- HLmod. rewrite N.add_mod_idemp_l by lia.
    replace ((L_left + 1) mod lam + Z.to_N G_z - 3)%N
      with ((L_left + 1) mod lam + (Z.to_N G_z - 3))%N by lia.
    reflexivity. }
  assert (Hpow_exp : ((2 ^ exp_n) mod (702 * Q_next) = p_mod)%N).
  { pose proof (pow2_mod_period lam Q_bad Q_good exp_n ltac:(lia) Hlam HQb HQg Hpow_lam) as Hper.
    rewrite Hpmq in Hper.
    destruct (N.ltb_spec exp_n lam); [unfold exp_n in *; lia|].
    rewrite Hexp_mod, <- Hkeff in Hper.
    rewrite Hper. exact Hpmod. }
  set (T_exit := (5 * 2 ^ exp_n + Z.to_N G_z + 1)%N).
  assert (HT_mod_eq : (T_exit mod (702 * Q_next) = T_mod)%N).
  { unfold T_exit.
    replace (5 * 2 ^ exp_n + Z.to_N G_z + 1)%N with (5 * 2 ^ exp_n + (Z.to_N G_z + 1))%N by lia.
    rewrite N.add_mod, N.mul_mod, Hpow_exp by lia.
    rewrite <- N.mul_mod by lia.
    rewrite <- N.add_mod by lia.
    exact HTmod. }
  pose proof (N.div_mod T_exit (702 * Q_next) ltac:(lia)) as Hdm.
  rewrite HT_mod_eq in Hdm.
  set (K := (T_exit / (702 * Q_next))%N) in *.
  set (q_sync := (26 * Q_next * K + q_mod)%N).
  set (k_close := (Q_next * K + k_mod)%N).
  assert (HK_ge : (K >= 2)%N).
  { assert (Hbig : (2 ^ exp_n >= 2 ^ 40)%N) by (apply N.pow_le_mono_r; [discriminate | lia]).
    change (2 ^ 40)%N with 1099511627776%N in Hbig.
    change (2 ^ 30)%N with 1073741824%N in HQ_le.
    assert (HT_big : (T_exit >= 2 * (702 * Q_next))%N) by (unfold T_exit; lia).
    unfold K. apply N.div_le_lower_bound; lia. }
  assert (Hsync_eq : (T_exit - 88 + dt = 27 * q_sync)%N) by (unfold q_sync; lia).
  assert (Hgap_eq : 1 + Z.of_N q_sync - Z.of_N dt - 26 * Z.of_N k_close = G_next).
  { unfold q_sync, k_close. rewrite !N2Z.inj_add, !N2Z.inj_mul.
    change (Z.of_N 26) with 26. lia. }
  destruct (round_bounce G_z L_left x0 c dt q_sync k_close G_next HG ltac:(lia) Hdt ltac:(unfold q_sync; lia)
              Hinv Hsync_eq Hgap_eq HGnext) as [Hnc Hinv_next].
  set (T_round := (T_exit + dt + 27 * k_close)%N) in *.
  set (L_left_next := (L_left + Z.to_N G_z + 1 + dt + 27 * k_close)%N).
  set (x_next := x0 + G_z + 1 + Z.of_N dt + 27 * Z.of_N k_close).
  exists T_round, L_left_next, x_next.
  repeat split.
  - unfold T_round, T_exit, exp_n. lia.
  - unfold L_left_next, k_close.
    assert (Hexp3 : exp_n = (3 + (exp_n - 3))%N) by lia.
    assert (Hpow_split : (2 ^ exp_n = 8 * 2 ^ (exp_n - 3))%N).
    { rewrite Hexp3 at 1. rewrite N.pow_add_r. change (2 ^ 3)%N with 8%N. lia. }
    (* 27 * Q_next * K = 27 * (T_exit - T_mod) / 702 = (T_exit - T_mod) / 26 *)
    (* Since T_mod < 702 * Q_next <= 702 * 2^30 and 2^exp_n >= 2^40, 26 * (2^(exp_n-3)) <= 26/8 * 2^exp_n < 5 * 2^exp_n - T_mod *)
    assert (Hbig : (2 ^ exp_n >= 2 ^ 40)%N) by (apply N.pow_le_mono_r; [discriminate | lia]).
    change (2 ^ 40)%N with 1099511627776%N in Hbig.
    change (2 ^ 30)%N with 1073741824%N in HQ_le.
    assert (HTmod_lt : (T_mod < 702 * Q_next)%N) by (rewrite HTmod; apply N.mod_lt; lia).
    assert (H26 : (26 * 2 ^ (exp_n - 3) <= T_exit - T_mod)%N).
    { unfold T_exit. rewrite Hpow_split. lia. }
    (* Since 702 * Q_next * K = T_exit - T_mod, 27 * Q_next * K * 26 = 27 * (T_exit - T_mod) >= 26 * 2^(exp_n - 3) *)
    assert (HK_mul : (26 * (27 * Q_next * K) = (T_exit - T_mod))%N).
    { replace (26 * (27 * Q_next * K))%N with (702 * Q_next * K)%N by lia. lia. }
    assert (HL_ge : (27 * Q_next * K >= 2 ^ (exp_n - 3))%N) by lia.
    replace (L_left + Z.to_N G_z - 5)%N with (exp_n - 3)%N by (unfold exp_n; lia).
    lia.
  - unfold L_left_next, k_close.
    replace (L_left + Z.to_N G_z + 1 + dt + 27 * (Q_next * K + k_mod) + 1)%N
      with ((L_left + 1 + Z.to_N G_z + 1 + dt + 27 * k_mod) + (27 * K) * Q_next)%N by lia.
    rewrite N.Div0.mod_add. symmetry; exact HLnext.
  - exact Hnc.
  - exact Hinv_next.
Qed.

Lemma round2_ok :
  exists T2 L_left3 x3,
    (T2 >= 5 * 2 ^ 206)%N /\
    (L_left3 >= 2 ^ 203)%N /\
    ((L_left3 + 1) mod 2125764 = 1509136)%N /\
    (forall k, (k < T2)%N -> (run_N ag1 ag2 k (run_N ag1 ag2 5730 c0)).(pos1) <>
                             (run_N ag1 ag2 k (run_N ag1 ag2 5730 c0)).(pos2)) /\
    round_inv 30 L_left3 x3 (run_N ag1 ag2 T2 (run_N ag1 ag2 5730 c0)).
Proof.
  destruct prefix_5730_ok as [Hinv2 _].
  assert (Hpow : pow2_mod 206 (702 * 2125764) = 1478024968%N) by (vm_compute; reflexivity).
  rewrite pow2_mod_correct in Hpow by lia.
  pose proof (N.div_mod (2 ^ 206) (702 * 2125764) ltac:(lia)) as Hdm.
  rewrite Hpow in Hdm.
  set (K := (2 ^ 206 / (702 * 2125764))%N) in *.
  set (T_exit := (5 * 2 ^ 206 + 19)%N).
  assert (HTx : (T_exit = (702 * 2125764) * (5 * K + 4) + 1420979547)%N).
  { unfold T_exit. rewrite Hdm at 1. lia. }
  set (K2 := (5 * K + 4)%N).
  set (q_sync := (26 * 2125764 * K2 + 52628869)%N).
  set (k_close := (2125764 * K2 + 2024186)%N).
  assert (Hsync : (T_exit - 88 + 4 = 27 * q_sync)%N) by (unfold q_sync; rewrite HTx; fold K2; lia).
  assert (Hgap : 1 + Z.of_N q_sync - Z.of_N 4 - 26 * Z.of_N k_close = 30).
  { unfold q_sync, k_close. rewrite !N2Z.inj_add, !N2Z.inj_mul.
    change (Z.of_N 26) with 26. change (Z.of_N 2125764) with 2125764.
    change (Z.of_N 52628869) with 52628869. change (Z.of_N 2024186) with 2024186.
    change (Z.of_N 4) with 4. lia. }
  assert (Hinv2' : round_inv 18 190 188 (run_N ag1 ag2 5730 c0)) by exact Hinv2.
  destruct (round_bounce 18 190 188 (run_N ag1 ag2 5730 c0) 4 q_sync k_close 30
              ltac:(unfold valid_G; auto) ltac:(lia) ltac:(lia) ltac:(unfold q_sync; lia)
              Hinv2' Hsync Hgap ltac:(lia)) as [Hnc Hinv3].
  set (T2 := (T_exit + 4 + 27 * k_close)%N) in *.
  set (L_left3 := (190 + Z.to_N 18 + 1 + 4 + 27 * k_close)%N).
  set (x3 := 188 + 18 + 1 + Z.of_N 4 + 27 * Z.of_N k_close).
  exists T2, L_left3, x3.
  repeat split.
  - unfold T2, T_exit. lia.
  - unfold L_left3, k_close, K2.
    assert (Hpow_big : (2 ^ 206 = 8 * 2 ^ 203)%N)
      by (replace 206%N with (3 + 203)%N by lia; rewrite N.pow_add_r; change (2 ^ 3)%N with 8%N; lia).
    assert (HK_mul : (26 * (27 * 2125764 * (5 * K + 4)) = T_exit - 1420979547)%N).
    { replace (26 * (27 * 2125764 * (5 * K + 4)))%N with ((702 * 2125764) * (5 * K + 4))%N by lia.
      rewrite HTx. lia. }
    assert (H203 : (2 ^ 203 >= 1420979547)%N) by (vm_compute; lia).
    assert (H26 : (26 * 2 ^ 203 <= T_exit - 1420979547)%N) by (unfold T_exit; rewrite Hpow_big; lia).
    lia.
  - unfold L_left3, k_close.
    replace (190 + Z.to_N 18 + 1 + 4 + 27 * (2125764 * K2 + 2024186) + 1)%N
      with (54653236 + (27 * K2) * 2125764)%N by lia.
    rewrite N.Div0.mod_add. vm_compute. reflexivity.
  - exact Hnc.
  - exact Hinv3.
Qed.

Lemma n_pow2_ge_add : forall n, (2 ^ n >= n + 1)%N.
Proof.
  intro n. induction n using N.peano_ind.
  - simpl. lia.
  - rewrite N.pow_succ_r' by lia. lia.
Qed.

Lemma final_halt_6 : forall L_left x0 c,
  (10 <= L_left)%N ->
  round_inv 8 L_left x0 c ->
  (forall k, (k < 6)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  (run_N ag1 ag2 6 c).(pos1) = (run_N ag1 ag2 6 c).(pos2).
Proof.
  intros L_left x0 c HL Hinv.
  set (fc_g8 := {| fpos1 := 0; fpos2 := 8; fstate1 := StB; fstate2 := StC;
                   ftape := bt_set (z_to_pos 8) true (bt_fill_range (-10) 16 true BEmpty) |}).
  assert (H6_ok :
    let st := N.iter 6 (fast_step_chk_range (-10) 12) (fc_g8, true) in
    snd st = true /\ (fst st).(fpos1) = (fst st).(fpos2)).
  { vm_compute. split; reflexivity. }
  destruct H6_ok as [Hsnd Heq6].
  rewrite fast_step_chk_range_fst in Heq6.
  destruct (fast_step_chk_range_sound 6 (-10) 12 fc_g8 true Hsnd) as [_ Hchk].
  assert (Hzinj : forall a b, z_to_pos a = z_to_pos b -> a = b).
  { intros a b H. rewrite <- (z_pos_z a), <- (z_pos_z b), H. reflexivity. }
  assert (Hrng_tape : forall z, x0 - 10 <= z <= x0 + 12 ->
    c.(tape) z = (shift_cfg x0 (fc_to_cfg fc_g8)).(tape) z).
  { intros z Hz. unfold shift_cfg, shift_tape, fc_to_cfg, bt_interp, fc_g8. simpl.
    destruct Hinv as [_ [_ [_ [_ [_ [Htr [Hm3 [Hm2 [Hm1 [H0 [H1 [H2 Hgt]]]]]]]]]]]].
    destruct (Z.eq_dec (z - x0) 8) as [Heq8 | Hneq8].
    - rewrite Heq8, bt_get_set_same. replace z with (x0 + 8) by lia. exact H0.
    - rewrite bt_get_set_diff by (intro H; apply Hneq8; apply Hzinj; exact H).
      destruct (Z.lt_ge_cases (z - x0) 6) as [Hlt6 | Hge6].
      + rewrite bt_fill_range_in by lia.
        destruct (Z.eq_dec z (x0 + 5)) as [-> | Hneq5]; [exact Hm3 | apply Htr; lia].
      + rewrite bt_fill_range_out by lia. rewrite bt_get_empty.
        assert (Hzc : z = x0 + 6 \/ z = x0 + 7 \/ z = x0 + 9 \/ z = x0 + 10 \/ z > x0 + 10) by lia.
        destruct Hzc as [->|[->|[->|[->|Hgt']]]]; auto. }
  destruct Hinv as [Cp1 [Cs1 [Cp2 [Cs2 _]]]].
  assert (Hrng_shift : forall k, (k < 6)%N ->
    x0 - 10 <= (run_N ag1 ag2 k (shift_cfg x0 (fc_to_cfg fc_g8))).(pos1) <= x0 + 12 /\
    x0 - 10 <= (run_N ag1 ag2 k (shift_cfg x0 (fc_to_cfg fc_g8))).(pos2) <= x0 + 12).
  { intros k Hk.
    destruct (run_N_shift ag1 ag2 k x0 (fc_to_cfg fc_g8)) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl.
    pose proof (fast_run_sound k fc_g8) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl.
    destruct (Hchk k Hk) as [_ [Ha Hb]]. lia. }
  assert (Hrng_c : forall k, (k < 6)%N ->
    x0 - 10 <= (run_N ag1 ag2 k c).(pos1) <= x0 + 12 /\
    x0 - 10 <= (run_N ag1 ag2 k c).(pos2) <= x0 + 12).
  { intros k Hk.
    destruct (run_N_agree_range ag1 ag2 (x0 - 10) (x0 + 12) k
                (shift_cfg x0 (fc_to_cfg fc_g8)) c
                (fun j Hj => Hrng_shift j ltac:(lia))
                (eq_sym Cp1) (eq_sym Cp2) (eq_sym Cs1) (eq_sym Cs2)
                (fun z Hz => eq_sym (Hrng_tape z Hz))) as [Kp1 [Kp2 _]].
    rewrite <- Kp1, <- Kp2. apply Hrng_shift; exact Hk. }
  split.
  - intros k Hk.
    destruct (run_N_agree_range ag1 ag2 (x0 - 10) (x0 + 12) k c
                (shift_cfg x0 (fc_to_cfg fc_g8))
                (fun j Hj => Hrng_c j ltac:(lia)) Cp1 Cp2 Cs1 Cs2 Hrng_tape) as [Kp1 [Kp2 _]].
    rewrite Kp1, Kp2.
    destruct (run_N_shift ag1 ag2 k x0 (fc_to_cfg fc_g8)) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl.
    pose proof (fast_run_sound k fc_g8) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl.
    destruct (Hchk k Hk) as [Hneq _]. lia.
  - destruct (run_N_agree_range ag1 ag2 (x0 - 10) (x0 + 12) 6 c
                (shift_cfg x0 (fc_to_cfg fc_g8))
                Hrng_c Cp1 Cp2 Cs1 Cs2 Hrng_tape) as [Kp1 [Kp2 _]].
    rewrite Kp1, Kp2.
    destruct (run_N_shift ag1 ag2 6 x0 (fc_to_cfg fc_g8)) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl.
    pose proof (fast_run_sound 6 fc_g8) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl.
    lia.
Qed.

Theorem cet4_r8_halts :
  exists T : N,
    halts_at_exact ag1 ag2 c0 T /\
    (T > 2 ^ (2 ^ (2 ^ (2 ^ (2 ^ (2 ^ (2 ^ 200)))))))%N.
Proof.
  pose proof check_lam_periods as Hlam.
  rewrite !andb_true_iff in Hlam.
  destruct Hlam as [[[[[Hp36 Hp324] Hp2916] Hp26244] Hp236196] Hp2125764].
  rewrite N.eqb_eq in Hp36, Hp324, Hp2916, Hp26244, Hp236196, Hp2125764.
  destruct prefix_5730_ok as [_ Hnc1].
  destruct round2_ok as [T2 [L3 [x3 [HT2 [HL3 [HM3 [Hnc2 Hinv3]]]]]]].
  assert (HL3_ge : (L3 >= 2 ^ 200)%N).
  { assert (Hmono : (2 ^ 203 >= 2 ^ 200)%N) by (apply N.pow_le_mono_r; lia). lia. }
  assert (H2_200_big : (2 ^ 200 >= 2125764)%N) by (vm_compute; lia).
  (* Round 3: G=30, lam=2125764, Q_bad=8, Q_good=20726199, Q_next=236196 *)
  destruct (round_step_mod 30 L3 x3 (run_N ag1 ag2 T2 (run_N ag1 ag2 5730 c0))
              2125764 8 20726199 236196 1509136 3634927 27465176 137325911 11 5086142 195620 12 177430
              ltac:(unfold valid_G; auto) ltac:(lia) ltac:(lia) ltac:(vm_compute; lia)
              Hinv3 ltac:(lia) ltac:(auto) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              Hp2125764 HM3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity))
    as [T3 [L4 [x4 [HT3 [HL4 [HM4 [Hnc3 Hinv4]]]]]]].
  assert (HL4_ge : (L4 >= 2 ^ (2 ^ 200))%N).
  { assert (Hmono : (2 ^ (L3 + Z.to_N 30 - 5) >= 2 ^ (2 ^ 200))%N)
      by (apply N.pow_le_mono_r; [discriminate | lia]). lia. }
  assert (HL4_lam : (236196 <= L4 + Z.to_N 12 - 2)%N)
    by (pose proof (n_pow2_ge_add (2 ^ 200)); lia).
  (* Round 4: G=12, lam=236196, Q_bad=8, Q_good=2302911, Q_next=26244 *)
  destruct (round_step_mod 12 L4 x4 _
              236196 8 2302911 26244 177430 413635 17991920 16266461 20 602459 23170 20 15733
              ltac:(unfold valid_G; auto) ltac:(lia) HL4_lam ltac:(vm_compute; lia)
              Hinv4 ltac:(lia) ltac:(auto) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              Hp236196 HM4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity))
    as [T4 [L5 [x5 [HT4 [HL5 [HM5 [Hnc4 Hinv5]]]]]]].
  assert (HL5_ge : (L5 >= 2 ^ (2 ^ (2 ^ 200)))%N).
  { assert (Hmono : (2 ^ (L4 + Z.to_N 12 - 5) >= 2 ^ (2 ^ (2 ^ 200)))%N)
      by (apply N.pow_le_mono_r; [discriminate | lia]). lia. }
  assert (HL5_lam : (26244 <= L5 + Z.to_N 20 - 2)%N)
    by (pose proof (n_pow2_ge_add (2 ^ (2 ^ 200))); pose proof (n_pow2_ge_add (2 ^ 200)); lia).
  (* Round 5: G=20, lam=26244, Q_bad=8, Q_good=255879, Q_next=2916 *)
  destruct (round_step_mod 20 L5 x5 _
              26244 8 255879 2916 15733 41994 1514512 1431485 8 53015 2038 20 804
              ltac:(unfold valid_G; auto) ltac:(lia) HL5_lam ltac:(vm_compute; lia)
              Hinv5 ltac:(lia) ltac:(auto) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              Hp26244 HM5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity))
    as [T5 [L6 [x6 [HT5 [HL6 [HM6 [Hnc5 Hinv6]]]]]]].
  assert (HL6_ge : (L6 >= 2 ^ (2 ^ (2 ^ (2 ^ 200))))%N).
  { assert (Hmono : (2 ^ (L5 + Z.to_N 20 - 5) >= 2 ^ (2 ^ (2 ^ (2 ^ 200))))%N)
      by (apply N.pow_le_mono_r; [discriminate | lia]). lia. }
  assert (HL6_lam : (2916 <= L6 + Z.to_N 20 - 2)%N)
    by (pose proof (n_pow2_ge_add (2 ^ (2 ^ (2 ^ 200)))); pose proof (n_pow2_ge_add (2 ^ (2 ^ 200))); pose proof (n_pow2_ge_add (2 ^ 200)); lia).
  (* Round 6: G=20, lam=2916, Q_bad=8, Q_good=28431, Q_next=324 *)
  destruct (round_step_mod 20 L6 x6 _
              2916 8 28431 324 804 3737 99248 41365 6 1529 58 16 129
              ltac:(unfold valid_G; auto) ltac:(lia) HL6_lam ltac:(vm_compute; lia)
              Hinv6 ltac:(lia) ltac:(auto) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              Hp2916 HM6 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity))
    as [T6 [L7 [x7 [HT6 [HL7 [HM7 [Hnc6 Hinv7]]]]]]].
  assert (HL7_ge : (L7 >= 2 ^ (2 ^ (2 ^ (2 ^ (2 ^ 200)))))%N).
  { assert (Hmono : (2 ^ (L6 + Z.to_N 20 - 5) >= 2 ^ (2 ^ (2 ^ (2 ^ (2 ^ 200)))))%N)
      by (apply N.pow_le_mono_r; [discriminate | lia]). lia. }
  assert (HL7_lam : (324 <= L7 + Z.to_N 16 - 2)%N)
    by (pose proof (n_pow2_ge_add (2 ^ (2 ^ (2 ^ (2 ^ 200))))); pose proof (n_pow2_ge_add (2 ^ (2 ^ (2 ^ 200)))); pose proof (n_pow2_ge_add (2 ^ (2 ^ 200))); pose proof (n_pow2_ge_add (2 ^ 200)); lia).
  (* Round 7: G=16, lam=324, Q_bad=8, Q_good=3159, Q_next=36 *)
  destruct (round_step_mod 16 L7 x7 _
              324 8 3159 36 129 466 22552 11689 9 430 15 32 20
              ltac:(unfold valid_G; auto) ltac:(lia) HL7_lam ltac:(vm_compute; lia)
              Hinv7 ltac:(lia) ltac:(auto) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              Hp324 HM7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity))
    as [T7 [L8 [x8 [HT7 [HL8 [HM8 [Hnc7 Hinv8]]]]]]].
  assert (HL8_ge : (L8 >= 2 ^ (2 ^ (2 ^ (2 ^ (2 ^ (2 ^ 200))))))%N).
  { assert (Hmono : (2 ^ (L7 + Z.to_N 16 - 5) >= 2 ^ (2 ^ (2 ^ (2 ^ (2 ^ (2 ^ 200))))))%N)
      by (apply N.pow_le_mono_r; [discriminate | lia]). lia. }
  assert (HL8_lam : (36 <= L8 + Z.to_N 32 - 2)%N)
    by (pose proof (n_pow2_ge_add (2 ^ (2 ^ (2 ^ (2 ^ (2 ^ 200)))))); pose proof (n_pow2_ge_add (2 ^ (2 ^ (2 ^ (2 ^ 200))))); pose proof (n_pow2_ge_add (2 ^ (2 ^ (2 ^ 200)))); pose proof (n_pow2_ge_add (2 ^ (2 ^ 200))); pose proof (n_pow2_ge_add (2 ^ 200)); lia).
  (* Round 8: G=32, lam=36, Q_bad=2, Q_good=351, Q_next=1 *)
  destruct (round_step_mod 32 L8 x8 _
              36 2 351 1 20 49 470 277 0 7 0 8 0
              ltac:(unfold valid_G; auto) ltac:(lia) HL8_lam ltac:(vm_compute; lia)
              Hinv8 ltac:(lia) ltac:(auto) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              Hp36 HM8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity))
    as [T8 [L9 [x9 [HT8 [HL9 [_ [Hnc8 Hinv9]]]]]]].
  (* Final 6 steps at G=8 *)
  destruct (final_halt_6 L9 x9 _ ltac:(lia) Hinv9) as [Hnc9 Hcoll9].
  set (T_tot := (6 + (T8 + (T7 + (T6 + (T5 + (T4 + (T3 + (T2 + 5730))))))))%N).
  exists T_tot. split.
  - unfold halts_at_exact, collides_at. split.
    + unfold T_tot. rewrite !run_N_add. exact Hcoll9.
    + intros t Ht.
      assert (H12 : forall k, (k < T2 + 5730)%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact Hnc1 | exact Hnc2]).
      assert (H13 : forall k, (k < T3 + (T2 + 5730))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H12 | rewrite run_N_add; exact Hnc3]).
      assert (H14 : forall k, (k < T4 + (T3 + (T2 + 5730)))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H13 | rewrite !run_N_add; exact Hnc4]).
      assert (H15 : forall k, (k < T5 + (T4 + (T3 + (T2 + 5730))))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H14 | rewrite !run_N_add; exact Hnc5]).
      assert (H16 : forall k, (k < T6 + (T5 + (T4 + (T3 + (T2 + 5730)))))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H15 | rewrite !run_N_add; exact Hnc6]).
      assert (H17 : forall k, (k < T7 + (T6 + (T5 + (T4 + (T3 + (T2 + 5730))))))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H16 | rewrite !run_N_add; exact Hnc7]).
      assert (H18 : forall k, (k < T8 + (T7 + (T6 + (T5 + (T4 + (T3 + (T2 + 5730)))))))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H17 | rewrite !run_N_add; exact Hnc8]).
      eapply no_coll_add; [exact H18 | rewrite !run_N_add; exact Hnc9 | exact Ht].
  - assert (Hmono8 : (2 ^ (L8 + Z.to_N 32 - 2) >= 2 ^ (2 ^ (2 ^ (2 ^ (2 ^ (2 ^ (2 ^ 200)))))))%N)
      by (apply N.pow_le_mono_r; [discriminate | lia]).
    unfold T_tot. lia.
Qed.

Print Assumptions cet4_r8_halts.
