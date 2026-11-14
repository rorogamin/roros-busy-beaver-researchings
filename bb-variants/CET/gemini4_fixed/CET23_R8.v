(**
  Formal Machine-Checked Proof of Normal Halting in Rocq 9.1
  Target Machine: 1LB1RA0LB_2RB2LB2RA | 2RB1LA1RB_2LB2RB1LA
  Model: Catch-Em-Turing CET(2,3), 2 agents, 2 states, 3 symbols.
  Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
  Normal Halting: exact first collision pos1(T) = pos2(T).

  Mathematical Structure:
  - Concrete prefix (steps 0 .. 844): enters Round 2 at pos1 = 86 (StA), pos2 = 96 (StB),
    G1 = 10, L_left = 86 (L2 = 87; anchor S2 at -1, S1 on [0..93], glider [94..97] = 2110).
  - Agent 2 glider (P = 9, D = 1, M = 8): canonical pattern 2110 at [p2-2 .. p2+1], state StB.
  - Agent 1 ternary counter: T_fill_3(m) = 3^(m + 1) - m - 3, yielding exact exit time
      T_exit(G, L_left) = 3^(L_left + G + 1) + G - 2
    for bounce gaps G in {8, 10}.
  - 8-round 3^L tower with gap sequence [10, 10, 10, 10, 10, 10, 8, 14],
    resolved via exact modular arithmetic mod 72 * Q (Carmichael lambda chain
    2 -> 4 -> 8 -> 16 -> 32 -> 64).
  - Final collision at G = 14 in 13 steps.
  Zero extra axioms.
*)

From Stdlib Require Import ZArith NArith PArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core Catch-Em-Turing CET(2,3) Semantics *)

Inductive State := StA | StB.
Inductive Sym := S0 | S1 | S2.
Inductive Dir := MoveL | MoveR.

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

(** * 2. Target Machine: 1LB1RA0LB_2RB2LB2RA | 2RB1LA1RB_2LB2RB1LA *)

Definition ag1 (s : State) (v : Sym) : Transition :=
  match s, v with
  | StA, S0 => {| write_sym := S1; move_dir := MoveL; next_state := StB |}
  | StA, S1 => {| write_sym := S1; move_dir := MoveR; next_state := StA |}
  | StA, S2 => {| write_sym := S0; move_dir := MoveL; next_state := StB |}
  | StB, S0 => {| write_sym := S2; move_dir := MoveR; next_state := StB |}
  | StB, S1 => {| write_sym := S2; move_dir := MoveL; next_state := StB |}
  | StB, S2 => {| write_sym := S2; move_dir := MoveR; next_state := StA |}
  end.

Definition ag2 (s : State) (v : Sym) : Transition :=
  match s, v with
  | StA, S0 => {| write_sym := S2; move_dir := MoveR; next_state := StB |}
  | StA, S1 => {| write_sym := S1; move_dir := MoveL; next_state := StA |}
  | StA, S2 => {| write_sym := S1; move_dir := MoveR; next_state := StB |}
  | StB, S0 => {| write_sym := S2; move_dir := MoveL; next_state := StB |}
  | StB, S1 => {| write_sym := S2; move_dir := MoveR; next_state := StB |}
  | StB, S2 => {| write_sym := S1; move_dir := MoveL; next_state := StA |}
  end.

(** * 3. Equivalence and Basic Run Laws *)

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
Proof. intros. unfold write_tape. destruct (Z.eqb_spec x p); congruence. Qed.

Lemma write_tape_proper : forall t1 t2 p s,
  tape_eq t1 t2 -> tape_eq (write_tape t1 p s) (write_tape t2 p s).
Proof. intros t1 t2 p s Ht z. unfold write_tape. destruct (Z.eqb_spec z p); auto. Qed.

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
Proof. intros. reflexivity. Qed.

Lemma run_N_succ : forall a1 a2 n c,
  run_N a1 a2 (N.succ n) c = step a1 a2 (run_N a1 a2 n c).
Proof. intros. unfold run_N. apply N.iter_succ. Qed.

Lemma run_N_add : forall a1 a2 m n c,
  run_N a1 a2 (m + n)%N c = run_N a1 a2 m (run_N a1 a2 n c).
Proof.
  intros a1 a2 m n c. unfold run_N.
  induction m using N.peano_ind; [rewrite N.add_0_l; reflexivity | rewrite N.add_succ_l, !N.iter_succ, IHm; reflexivity].
Qed.

Lemma no_coll_add : forall a1 a2 m n c,
  (forall k, (k < n)%N -> (run_N a1 a2 k c).(pos1) <> (run_N a1 a2 k c).(pos2)) ->
  (forall k, (k < m)%N -> (run_N a1 a2 k (run_N a1 a2 n c)).(pos1) <>
                           (run_N a1 a2 k (run_N a1 a2 n c)).(pos2)) ->
  forall t, (t < m + n)%N -> (run_N a1 a2 t c).(pos1) <> (run_N a1 a2 t c).(pos2).
Proof.
  intros a1 a2 m n c Hn Hm t Ht.
  destruct (N.lt_ge_cases t n) as [Hlt | Hge]; [apply Hn; exact Hlt|].
  replace t with ((t - n) + n)%N by lia. rewrite run_N_add. apply Hm. lia.
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
      lo <= (run_N a1 a2 k c1).(pos2) <= hi) by (intros k Hk; apply Hrng; lia).
    destruct (IHn c1 c2 Hrng_n Hp1 Hp2 Hs1 Hs2 Htp) as [Gp1 [Gp2 [Gs1 [Gs2 Gtp]]]].
    destruct (Hrng n ltac:(lia)) as [Hn1 Hn2].
    apply (step_agree_range a1 a2 lo hi); auto.
Qed.

(** * 4. Fast Binary-Tree Tape and 844-Step Prefix *)

Inductive BTree :=
  | BEmpty
  | BNode (cur : Sym) (l r : BTree).

Fixpoint bt_get (p : positive) (t : BTree) : Sym :=
  match t with
  | BEmpty => S0
  | BNode cur l r =>
      match p with xH => cur | xO q => bt_get q l | xI q => bt_get q r end
  end.

Fixpoint bt_set (p : positive) (v : Sym) (t : BTree) : BTree :=
  match t with
  | BEmpty =>
      match p with
      | xH => BNode v BEmpty BEmpty
      | xO q => BNode S0 (bt_set q v BEmpty) BEmpty
      | xI q => BNode S0 BEmpty (bt_set q v BEmpty)
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

Lemma z_to_pos_inj : forall a b, z_to_pos a = z_to_pos b -> a = b.
Proof. intros a b H. rewrite <- (z_pos_z a), <- (z_pos_z b), H. reflexivity. Qed.

Lemma bt_get_set_same : forall p v t, bt_get p (bt_set p v t) = v.
Proof. induction p; destruct t; simpl; auto. Qed.

Lemma bt_get_empty : forall q, bt_get q BEmpty = S0.
Proof. destruct q; reflexivity. Qed.

Lemma bt_get_set_diff : forall p q v t, p <> q -> bt_get q (bt_set p v t) = bt_get q t.
Proof.
  induction p; intros q v t Hneq; destruct t; destruct q; simpl in *;
    try rewrite !bt_get_empty; try reflexivity; try congruence;
    try (apply IHp; congruence); try (rewrite IHp; [apply bt_get_empty | congruence]).
Qed.

Definition bt_interp (t : BTree) : Tape := fun z => bt_get (z_to_pos z) t.

Lemma bt_interp_set : forall t p v,
  tape_eq (bt_interp (bt_set (z_to_pos p) v t)) (write_tape (bt_interp t) p v).
Proof.
  intros t p v z. unfold bt_interp, write_tape.
  destruct (Z.eqb_spec z p); [subst z; apply bt_get_set_same|].
  apply bt_get_set_diff. intros Heq. apply n. apply z_to_pos_inj; symmetry; exact Heq.
Qed.

Record FastConfig := {
  fpos1 : Z; fpos2 : Z; fstate1 : State; fstate2 : State; ftape : BTree
}.

Definition fc_to_cfg (fc : FastConfig) : Config := {|
  pos1 := fc.(fpos1); pos2 := fc.(fpos2); state1 := fc.(fstate1);
  state2 := fc.(fstate2); tape := bt_interp fc.(ftape)
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
  intro fc. unfold fast_step, fc_to_cfg, step. constructor; simpl; try reflexivity.
  eapply tape_eq_trans; [apply bt_interp_set | apply write_tape_proper, bt_interp_set].
Qed.

Lemma fast_run_sound : forall n fc,
  cfg_eq (fc_to_cfg (N.iter n fast_step fc)) (run_N ag1 ag2 n (fc_to_cfg fc)).
Proof.
  intro n. induction n using N.peano_ind; intro fc.
  - rewrite run_N_0. simpl. constructor; simpl; auto. intro; auto.
  - rewrite run_N_succ, N.iter_succ. eapply cfg_eq_trans; [apply fast_step_sound | apply step_proper, IHn].
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
  intro n. induction n using N.peano_ind; intros lo hi fc ok; [reflexivity|].
  rewrite !N.iter_succ. destruct (N.iter n (fast_step_chk_range lo hi) (fc, ok)) as [fc' ok'] eqn:E.
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
    simpl in Hsnd. rewrite !andb_true_iff in Hsnd.
    destruct Hsnd as [[[[[Hok' Hneq] Hlo1] Hhi1] Hlo2] Hhi2].
    assert (Hsnd_n : snd (N.iter n (fast_step_chk_range lo hi) (fc, ok)) = true) by (rewrite E; exact Hok').
    destruct (IHn lo hi fc ok Hsnd_n) as [Hok Hlt].
    split; auto. intros k Hk.
    destruct (N.lt_ge_cases k n) as [Hklt | Hkge]; [apply Hlt; exact Hklt|].
    replace k with n by lia. rewrite <- Hfc.
    split; [rewrite negb_true_iff, Z.eqb_neq in Hneq; exact Hneq | rewrite !Z.leb_le in *; lia].
Qed.

Lemma fast_run_outside_zero : forall n lo hi fc,
  (forall k, (k < n)%N ->
    let fc_k := N.iter k fast_step fc in
    lo <= fc_k.(fpos1) <= hi /\ lo <= fc_k.(fpos2) <= hi) ->
  (forall z, z < lo \/ z > hi -> bt_get (z_to_pos z) fc.(ftape) = S0) ->
  forall z, z < lo \/ z > hi -> bt_get (z_to_pos z) (N.iter n fast_step fc).(ftape) = S0.
Proof.
  intro n. induction n using N.peano_ind; intros lo hi fc Hrng Hout z Hz.
  - simpl. apply Hout; exact Hz.
  - rewrite N.iter_succ.
    assert (Hrng_n : forall k, (k < n)%N ->
      let fc_k := N.iter k fast_step fc in
      lo <= fc_k.(fpos1) <= hi /\ lo <= fc_k.(fpos2) <= hi) by (intros k Hk; apply Hrng; lia).
    destruct (Hrng n ltac:(lia)) as [Hn1 Hn2].
    set (fcn := N.iter n fast_step fc) in *.
    unfold fast_step. simpl.
    rewrite bt_get_set_diff by (intro H; apply z_to_pos_inj in H; lia).
    rewrite bt_get_set_diff by (intro H; apply z_to_pos_inj in H; lia).
    apply (IHn lo hi fc); auto.
Qed.

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

Definition c0 : Config := fc_to_cfg fc0.

Definition state_eqb (s1 s2 : State) : bool :=
  match s1, s2 with StA, StA | StB, StB => true | _, _ => false end.

Definition sym_eqb (s1 s2 : Sym) : bool :=
  match s1, s2 with S0, S0 | S1, S1 | S2, S2 => true | _, _ => false end.

Lemma state_eqb_eq : forall s1 s2, state_eqb s1 s2 = true -> s1 = s2.
Proof. destruct s1, s2; simpl; congruence. Qed.

Lemma sym_eqb_eq : forall s1 s2, sym_eqb s1 s2 = true -> s1 = s2.
Proof. destruct s1, s2; simpl; congruence. Qed.

Definition exp_844 (z : Z) : Sym :=
  if Z.ltb z (-1) then S0
  else if Z.eqb z (-1) then S2
  else if Z.ltb z 94 then S1
  else if Z.eqb z 94 then S2
  else if Z.eqb z 95 then S1
  else if Z.eqb z 96 then S1
  else S0.

Lemma exp_844_S1 : forall z, 0 <= z < 94 -> exp_844 z = S1.
Proof.
  intros z [H0 H1]. unfold exp_844.
  destruct (Z.ltb_spec z (-1)); [lia|].
  destruct (Z.eqb_spec z (-1)); [lia|].
  destruct (Z.ltb_spec z 94); [reflexivity|lia].
Qed.

Fixpoint check_range_844 (lo : Z) (len : nat) (t : BTree) : bool :=
  match len with
  | O => true
  | S n => sym_eqb (bt_get (z_to_pos lo) t) (exp_844 lo) && check_range_844 (lo + 1) n t
  end.

Lemma check_range_844_sound : forall len lo t,
  check_range_844 lo len t = true ->
  forall z, lo <= z < lo + Z.of_nat len -> bt_get (z_to_pos z) t = exp_844 z.
Proof.
  induction len; intros lo t H z Hz; [simpl in Hz; lia|].
  simpl in H. rewrite andb_true_iff in H. destruct H as [H0 Hrest].
  apply sym_eqb_eq in H0.
  destruct (Z.eq_dec z lo); [subst z; exact H0 | apply (IHlen (lo + 1) t); auto; lia].
Qed.

Definition check_fc_844 (st : FastConfig * bool) : bool :=
  let (fc, ok) := st in
  ok && Z.eqb fc.(fpos1) 86 && Z.eqb fc.(fpos2) 96
     && state_eqb fc.(fstate1) StA && state_eqb fc.(fstate2) StB
     && check_range_844 (-3) 102 fc.(ftape).

Lemma fc_844_ok : check_fc_844 (N.iter 844 (fast_step_chk_range (-3) 98) (fc0, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Definition round_inv (G : Z) (L_left : N) (x0 : Z) (c : Config) : Prop :=
  c.(pos1) = x0 /\
  c.(state1) = StA /\
  c.(pos2) = x0 + G /\
  c.(state2) = StB /\
  (forall z, z < x0 - Z.of_N L_left - 1 -> c.(tape) z = S0) /\
  c.(tape) (x0 - Z.of_N L_left - 1) = S2 /\
  (forall z, x0 - Z.of_N L_left <= z < x0 + G - 2 -> c.(tape) z = S1) /\
  c.(tape) (x0 + G - 2) = S2 /\
  c.(tape) (x0 + G - 1) = S1 /\
  c.(tape) (x0 + G) = S1 /\
  (forall z, z > x0 + G -> c.(tape) z = S0).

Lemma prefix_844_ok :
  round_inv 10 86 86 (run_N ag1 ag2 844 c0) /\
  (forall k, (k < 844)%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2)).
Proof.
  pose proof fc_844_ok as Hok.
  remember (N.iter 844 (fast_step_chk_range (-3) 98) (fc0, true)) as st eqn:Est.
  destruct st as [fc_end ok_end].
  unfold check_fc_844 in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[Hok_end Hp1] Hp2] Hs1] Hs2] Hrng].
  rewrite Z.eqb_eq in Hp1, Hp2. apply state_eqb_eq in Hs1, Hs2.
  assert (Hfc : fc_end = N.iter 844 fast_step fc0).
  { pose proof (fast_step_chk_range_fst 844 (-3) 98 fc0 true) as Hfst.
    rewrite <- Est in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 844 (fast_step_chk_range (-3) 98) (fc0, true)) = true)
    by (rewrite <- Est; exact Hok_end).
  destruct (fast_step_chk_range_sound 844 (-3) 98 fc0 true Hsnd) as [_ Hchk].
  destruct (fast_run_sound 844 fc0) as [Rp1 Rp2 Rs1 Rs2 Rtp].
  rewrite <- Hfc in Rp1, Rp2, Rs1, Rs2, Rtp.
  assert (Hout : forall z, z < -3 \/ z > 98 -> bt_get (z_to_pos z) fc_end.(ftape) = S0).
  { rewrite Hfc. apply (fast_run_outside_zero 844 (-3) 98 fc0).
    - intros k Hk. destruct (Hchk k Hk) as [_ [Ha Hb]]. split; auto.
    - intros z _. apply bt_get_empty. }
  pose proof (check_range_844_sound 102 (-3) fc_end.(ftape) Hrng) as Hrng_all.
  split.
  - assert (Hc0 : c0 = fc_to_cfg fc0) by reflexivity.
    rewrite Hc0. unfold round_inv. rewrite <- Rp1, <- Rp2, <- Rs1, <- Rs2.
    repeat split; try lia; auto.
    + intros z Hz. rewrite <- Rtp. simpl. unfold bt_interp.
      destruct (Z.lt_ge_cases z (-3)) as [Hlt | Hge]; [apply Hout; left; lia|].
      rewrite Hrng_all by lia. unfold exp_844.
      destruct (Z.ltb_spec z (-1)); [reflexivity | lia].
    + intros z Hz. rewrite <- Rtp. simpl. unfold bt_interp. rewrite Hrng_all by lia.
      apply exp_844_S1; lia.
    + intros z Hz. rewrite <- Rtp. simpl. unfold bt_interp.
      destruct (Z.lt_ge_cases z 99) as [Hle | Hgt]; [|apply Hout; right; lia].
      rewrite Hrng_all by lia. unfold exp_844.
      destruct (Z.ltb_spec z (-1)); [lia|].
      destruct (Z.eqb_spec z (-1)); [lia|].
      destruct (Z.ltb_spec z 94); [lia|].
      destruct (Z.eqb_spec z 94); [lia|].
      destruct (Z.eqb_spec z 95); [lia|].
      destruct (Z.eqb_spec z 96); [lia| reflexivity].
  - intros k Hk.
    unfold c0.
    destruct (fast_run_sound k fc0) as [Kp1 Kp2 _ _ _].
    rewrite <- Kp1, <- Kp2. simpl.
    destruct (Hchk k Hk) as [Hneq _]. exact Hneq.
Qed.

(** * 5. Translation Invariance, Decoupling, and Agent 1 Ternary Counter *)

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
  - rewrite !run_N_succ. eapply cfg_eq_trans; [apply step_proper, IHn | apply step_shift].
Qed.

Record SConfig := { spos : Z; sstate : State; stape : Tape }.

Definition sstep (ag : AgentTable) (sc : SConfig) : SConfig :=
  let r := sc.(stape) sc.(spos) in
  let tr := ag sc.(sstate) r in
  {| spos := move_pos sc.(spos) tr.(move_dir); sstate := tr.(next_state);
     stape := write_tape sc.(stape) sc.(spos) tr.(write_sym) |}.

Definition srun_N (ag : AgentTable) (n : N) (sc : SConfig) : SConfig := N.iter n (sstep ag) sc.

Lemma srun_N_0 : forall ag sc, srun_N ag 0%N sc = sc.
Proof. intros. reflexivity. Qed.

Lemma srun_N_succ : forall ag n sc, srun_N ag (N.succ n) sc = sstep ag (srun_N ag n sc).
Proof. intros. unfold srun_N. apply N.iter_succ. Qed.

Lemma srun_N_add : forall ag m n sc, srun_N ag (m + n)%N sc = srun_N ag m (srun_N ag n sc).
Proof.
  intros ag m n sc. unfold srun_N.
  induction m using N.peano_ind; [rewrite N.add_0_l; reflexivity | rewrite N.add_succ_l, !N.iter_succ, IHm; reflexivity].
Qed.

Definition sc_eq (s1 s2 : SConfig) : Prop :=
  s1.(spos) = s2.(spos) /\ s1.(sstate) = s2.(sstate) /\ tape_eq s1.(stape) s2.(stape).

Lemma sstep_proper : forall ag s1 s2, sc_eq s1 s2 -> sc_eq (sstep ag s1) (sstep ag s2).
Proof.
  intros ag s1 s2 [Hp [Hs Ht]]. unfold sstep. rewrite Hp, Hs, Ht.
  repeat split; simpl; auto. apply write_tape_proper; exact Ht.
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
    + intros z Hz. unfold write_tape. destruct (Z.eqb_spec z (srun_N ag n s2).(spos)); auto.
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
    + intros k Hk. destruct (N.lt_ge_cases k n) as [Hklt | Hkge]; [apply Hprev; exact Hklt|].
      replace k with n by lia. repeat split; auto. lia.
    + rewrite run_N_succ, !srun_N_succ. unfold step, sstep.
      rewrite Gp1, Gs1, Gp2, Gs2, Gt1 by lia. rewrite Gt2 by lia.
      repeat split; simpl; try reflexivity.
      * intros z Hz. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 n sc1).(spos)); auto.
        destruct (Z.eqb_spec z (srun_N a2 n sc2).(spos)); [exfalso; lia|].
        apply Gt1; exact Hz.
      * intros z Hz. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 n sc1).(spos)); [exfalso; lia|].
        destruct (Z.eqb_spec z (srun_N a2 n sc2).(spos)); [reflexivity|].
        apply Gt2; exact Hz.
      * intros z Hz1 Hz2. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 n sc1).(spos));
          [exfalso; apply Hz1; lia|].
        destruct (Z.eqb_spec z (srun_N a2 n sc2).(spos));
          [exfalso; apply Hz2; lia|].
        apply Gout; auto.
Qed.

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
      { destruct (N.lt_ge_cases m k_split) as [Hlt | Hge];
          [specialize (Hrk1 m Hlt); lia | specialize (Hrk2 m ltac:(lia)); lia]. }
      assert (Hr1_eq : (run_N a1 a2 m c).(tape) (srun_N a1 m sc1).(spos) =
                       (srun_N a1 m sc1).(stape) (srun_N a1 m sc1).(spos)).
      { destruct (Z.le_gt_cases (srun_N a1 m sc1).(spos) x_split) as [Hle | Hgt]; [apply Gt1a; lia|].
        assert (Hk_le : (k_split <= m)%N)
          by (destruct (N.lt_ge_cases m k_split) as [Hlt | Hge]; [specialize (Hrk1 m Hlt); lia | exact Hge]).
        apply Gt1b_ge; lia. }
      assert (Hr2_eq : (run_N a1 a2 m c).(tape) (srun_N a2 m sc2).(spos) =
                       (srun_N a2 m sc2).(stape) (srun_N a2 m sc2).(spos)).
      { destruct (Z.lt_ge_cases hi1 (srun_N a2 m sc2).(spos)) as [Hgt | Hle]; [apply Gt2; exact Hgt|].
        assert (Hlt_k : (m < k_split)%N)
          by (destruct (N.lt_ge_cases m k_split) as [Hlt | Hge]; [exact Hlt | specialize (Hrk2 m ltac:(lia)); lia]).
        apply Gt1b_le; lia. }
      split.
      { intros k Hk. destruct (N.lt_ge_cases k m) as [Hklt | Hkge]; [apply Hprev; exact Hklt|].
        replace k with m by lia. rewrite Gp1, Gp2. exact Hsep_m. }
      rewrite run_N_succ, !srun_N_succ. unfold step, sstep.
      rewrite Gp1, Gs1, Gp2, Gs2, Hr1_eq, Hr2_eq.
      repeat split; simpl; try reflexivity.
      * intros z Hz. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 m sc1).(spos)); auto.
        destruct (Z.eqb_spec z (srun_N a2 m sc2).(spos)); [exfalso; lia|].
        apply Gt1a; exact Hz.
      * intros z Hz Hm_le. unfold write_tape.
        assert (Hlt_k : (m < k_split)%N) by lia. specialize (Hrk1 m Hlt_k).
        destruct (Z.eqb_spec z (srun_N a1 m sc1).(spos)); [exfalso; lia|].
        destruct (Z.eqb_spec z (srun_N a2 m sc2).(spos)); auto. apply Gt1b_le; lia.
      * intros z Hz Hm_ge. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 m sc1).(spos)); auto.
        destruct (N.lt_ge_cases k_split (N.succ m)) as [Hlt | Hge].
        { destruct (Z.eqb_spec z (srun_N a2 m sc2).(spos));
            [exfalso; assert (Hlo2 : lo2 <= (srun_N a2 m sc2).(spos))
              by (apply Hrk2; split; lia); lia|].
          apply Gt1b_ge; lia. }
        { assert (Heq : k_split = N.succ m) by lia. subst k_split.
          destruct (Z.eqb_spec z (srun_N a2 m sc2).(spos)).
          { rewrite e.
            assert (Hs := Hmid (spos (srun_N a2 m sc2)) ltac:(lia)).
            symmetry in Hs. rewrite Hs.
            rewrite srun_N_succ. unfold sstep. simpl.
            rewrite write_tape_same. reflexivity. }
          { rewrite (Gt1b_le z Hz ltac:(lia)).
            symmetry.
            transitivity (stape (srun_N a2 (N.succ m) sc2) z).
            - rewrite srun_N_succ. unfold sstep. simpl.
              rewrite write_tape_other by exact n. reflexivity.
            - apply Hmid; exact Hz. } }
      * intros z Hz. unfold write_tape.
        destruct (Z.eqb_spec z (srun_N a1 m sc1).(spos)); [exfalso; lia|].
        destruct (Z.eqb_spec z (srun_N a2 m sc2).(spos)); auto. apply Gt2; exact Hz.
      * intros z Hz. unfold write_tape.
        apply Gout; exact Hz. }
  destruct (Hgen n ltac:(lia)) as [Hnc [Gp1 [Gs1 [Gt1a [_ [Gt1b [Gp2 [Gs2 [Gt2 Gout]]]]]]]]].
  repeat split; auto.
  intros z Hz. destruct (Z.le_gt_cases z x_split) as [Hle | Hgt]; [apply Gt1a; lia | apply Gt1b; lia].
Qed.

Lemma ag1_sweep_left : forall m x_end sc,
  sc.(spos) = x_end + Z.of_N m - 1 ->
  sc.(sstate) = StB ->
  (forall z, x_end <= z < x_end + Z.of_N m -> sc.(stape) z = S1) ->
  (forall k, (k < m)%N -> x_end <= (srun_N ag1 k sc).(spos) <= x_end + Z.of_N m - 1) /\
  (srun_N ag1 m sc).(spos) = x_end - 1 /\
  (srun_N ag1 m sc).(sstate) = StB /\
  (forall z, x_end <= z < x_end + Z.of_N m -> (srun_N ag1 m sc).(stape) z = S2) /\
  (forall z, z < x_end \/ z >= x_end + Z.of_N m -> (srun_N ag1 m sc).(stape) z = sc.(stape) z).
Proof.
  intro m. induction m using N.peano_ind; intros x_end sc Hp Hs Ht.
  - rewrite srun_N_0. repeat split; try lia; auto; intros; lia.
  - set (sc1 := sstep ag1 sc).
    assert (Hsc1 : sc1.(spos) = x_end + Z.of_N m - 1 /\ sc1.(sstate) = StB /\
                   (forall z, x_end <= z < x_end + Z.of_N m -> sc1.(stape) z = S1) /\
                   sc1.(stape) (x_end + Z.of_N m) = S2 /\
                   (forall z, z < x_end \/ z > x_end + Z.of_N m -> sc1.(stape) z = sc.(stape) z)).
    { unfold sc1, sstep. rewrite Hp, Hs, Ht by lia. simpl. repeat split; try lia.
      - intros z Hz. apply Ht; lia.
      - replace (x_end + Z.of_N (N.succ m) - 1) with (x_end + Z.of_N m) by lia. apply write_tape_same.
      - intros z Hz. reflexivity. }
    destruct Hsc1 as [H1p [H1s [H1t [H1f H1o]]]].
    destruct (IHm x_end sc1 H1p H1s H1t) as [Irng [Ip [Is [It Io]]]].
    replace (N.succ m) with (m + 1)%N by lia. rewrite srun_N_add.
    assert (Hs1 : srun_N ag1 1 sc = sc1) by (rewrite <- N.add_1_l, srun_N_add, srun_N_0; reflexivity).
    rewrite Hs1. repeat split; try lia; try exact Is.
    + intros k Hk. destruct (N.eq_dec k 0) as [-> | Hk0]; [rewrite srun_N_0; lia|].
      replace k with ((k - 1) + 1)%N by lia. rewrite srun_N_add, Hs1.
      specialize (Irng (k - 1)%N ltac:(lia)). lia.
    + intros z Hz. destruct (Z.eq_dec z (x_end + Z.of_N m)) as [-> | Hneq]; [rewrite Io by lia; exact H1f | apply It; lia].
    + intros z Hz. rewrite Io by lia. apply H1o. lia.
Qed.

Lemma ag1_walk_right : forall m x0 sc,
  sc.(spos) = x0 ->
  sc.(sstate) = StA ->
  (forall z, x0 <= z < x0 + Z.of_N m -> sc.(stape) z = S1) ->
  (forall k, (k < m)%N -> x0 <= (srun_N ag1 k sc).(spos) <= x0 + Z.of_N m - 1) /\
  (srun_N ag1 m sc).(spos) = x0 + Z.of_N m /\
  (srun_N ag1 m sc).(sstate) = StA /\
  (forall z, (srun_N ag1 m sc).(stape) z = sc.(stape) z).
Proof.
  intro m. induction m using N.peano_ind; intros x0 sc Hp Hs Ht.
  - rewrite srun_N_0. repeat split; try lia; auto. intros k Hk; lia.
  - set (sc1 := sstep ag1 sc).
    assert (Hsc1 : sc1.(spos) = x0 + 1 /\ sc1.(sstate) = StA /\ forall z, sc1.(stape) z = sc.(stape) z).
    { unfold sc1, sstep. rewrite Hp, Hs, Ht by lia. simpl. repeat split; try lia.
      intro z. unfold write_tape. destruct (Z.eqb_spec z x0); [subst; symmetry; apply Ht; lia | reflexivity]. }
    destruct Hsc1 as [H1p [H1s H1t]].
    assert (H1t' : forall z, x0 + 1 <= z < x0 + 1 + Z.of_N m -> sc1.(stape) z = S1)
      by (intros z Hz; rewrite H1t; apply Ht; lia).
    destruct (IHm (x0 + 1) sc1 H1p H1s H1t') as [Irng [Ip [Is It]]].
    replace (N.succ m) with (m + 1)%N by lia. rewrite srun_N_add.
    assert (Hs1 : srun_N ag1 1 sc = sc1) by (rewrite <- N.add_1_l, srun_N_add, srun_N_0; reflexivity).
    rewrite Hs1. repeat split; try lia; try exact Is.
    + intros k Hk. destruct (N.eq_dec k 0) as [-> | Hk0]; [rewrite srun_N_0; lia|].
      replace k with ((k - 1) + 1)%N by lia. rewrite srun_N_add, Hs1.
      specialize (Irng (k - 1)%N ltac:(lia)). lia.
    + intro z. rewrite It. apply H1t.
Qed.

Definition T_fill_3 (m : N) : N := (3 ^ (m + 1) - m - 3)%N.

Lemma T_fill_3_1 : T_fill_3 1 = 5%N.
Proof. reflexivity. Qed.

Lemma T_fill_3_succ : forall m, (1 <= m)%N ->
  T_fill_3 (N.succ m) = (3 * T_fill_3 m + 2 * m + 5)%N.
Proof.
  intros m Hm. unfold T_fill_3.
  assert (Hpow : (3 ^ (m + 1) >= 9)%N).
  { replace (m + 1)%N with (2 + (m - 1))%N by lia.
    rewrite N.pow_add_r. change (3 ^ 2)%N with 9%N.
    pose proof (N.pow_nonzero 3 (m - 1) ltac:(discriminate)). lia. }
  replace (N.succ m + 1)%N with (N.succ (m + 1)) by lia.
  rewrite N.pow_succ_r' by lia. lia.
Qed.

Lemma ag1_fill_3 : forall m x0 sc,
  (1 <= m)%N ->
  sc.(spos) = x0 ->
  sc.(sstate) = StA ->
  sc.(stape) (x0 - 1) = S2 ->
  (forall z, x0 <= z < x0 + Z.of_N m -> sc.(stape) z = S2) ->
  (forall k, (k < T_fill_3 m)%N -> x0 - 1 <= (srun_N ag1 k sc).(spos) <= x0 + Z.of_N m - 1) /\
  (srun_N ag1 (T_fill_3 m) sc).(spos) = x0 + Z.of_N m /\
  (srun_N ag1 (T_fill_3 m) sc).(sstate) = StA /\
  (srun_N ag1 (T_fill_3 m) sc).(stape) (x0 - 1) = S2 /\
  (forall z, x0 <= z < x0 + Z.of_N m -> (srun_N ag1 (T_fill_3 m) sc).(stape) z = S1) /\
  (forall z, z < x0 - 1 \/ z >= x0 + Z.of_N m -> (srun_N ag1 (T_fill_3 m) sc).(stape) z = sc.(stape) z).
Proof.
  intro m. induction m using N.peano_ind; intros x0 sc Hm Hp Hs Hm1 Ht; [lia|].
  destruct (N.eq_dec m 0) as [-> | Hm0].
  - change (N.succ 0) with 1%N. rewrite T_fill_3_1.
    set (c1 := sstep ag1 sc).
    assert (Hc1 : c1.(spos) = x0 - 1 /\ c1.(sstate) = StB /\ c1.(stape) (x0 - 1) = S2 /\ c1.(stape) x0 = S0 /\
                  forall z, z < x0 - 1 \/ z >= x0 + 1 -> c1.(stape) z = sc.(stape) z).
    { unfold c1, sstep. rewrite Hp, Hs, Ht by lia. simpl. repeat split; try lia; auto.
      - exact Hm1.
      - apply write_tape_same.
      - intros z Hz. reflexivity. }
    destruct Hc1 as [p1 [s1 [t1m [t10 t1o]]]].
    set (c2 := sstep ag1 c1).
    assert (Hc2 : c2.(spos) = x0 /\ c2.(sstate) = StA /\ c2.(stape) (x0 - 1) = S2 /\ c2.(stape) x0 = S0 /\
                  forall z, z < x0 - 1 \/ z >= x0 + 1 -> c2.(stape) z = sc.(stape) z).
    { unfold c2, sstep. rewrite p1, s1, t1m. simpl. repeat split; try lia; auto.
      - apply write_tape_same.
      - rewrite write_tape_other by lia; exact t10.
      - intros z Hz. rewrite write_tape_other by lia; apply t1o; auto. }
    destruct Hc2 as [p2 [s2 [t2m [t20 t2o]]]].
    set (c3 := sstep ag1 c2).
    assert (Hc3 : c3.(spos) = x0 - 1 /\ c3.(sstate) = StB /\ c3.(stape) (x0 - 1) = S2 /\ c3.(stape) x0 = S1 /\
                  forall z, z < x0 - 1 \/ z >= x0 + 1 -> c3.(stape) z = sc.(stape) z).
    { unfold c3, sstep. rewrite p2, s2, t20. simpl. repeat split; try lia; auto.
      - rewrite write_tape_other by lia; exact t2m.
      - apply write_tape_same.
      - intros z Hz. rewrite write_tape_other by lia; apply t2o; auto. }
    destruct Hc3 as [p3 [s3 [t3m [t30 t3o]]]].
    set (c4 := sstep ag1 c3).
    assert (Hc4 : c4.(spos) = x0 /\ c4.(sstate) = StA /\ c4.(stape) (x0 - 1) = S2 /\ c4.(stape) x0 = S1 /\
                  forall z, z < x0 - 1 \/ z >= x0 + 1 -> c4.(stape) z = sc.(stape) z).
    { unfold c4, sstep. rewrite p3, s3, t3m. simpl. repeat split; try lia; auto.
      - apply write_tape_same.
      - rewrite write_tape_other by lia; exact t30.
      - intros z Hz. rewrite write_tape_other by lia; apply t3o; auto. }
    destruct Hc4 as [p4 [s4 [t4m [t40 t4o]]]].
    set (c5 := sstep ag1 c4).
    assert (Hc5 : c5.(spos) = x0 + 1 /\ c5.(sstate) = StA /\ c5.(stape) (x0 - 1) = S2 /\ c5.(stape) x0 = S1 /\
                  forall z, z < x0 - 1 \/ z >= x0 + 1 -> c5.(stape) z = sc.(stape) z).
    { unfold c5, sstep. rewrite p4, s4, t40. simpl. repeat split; try lia; auto.
      - rewrite write_tape_other by lia; exact t4m.
      - apply write_tape_same.
      - intros z Hz. rewrite write_tape_other by lia; apply t4o; auto. }
    destruct Hc5 as [p5 [s5 [t5m [t50 t5o]]]].
    assert (Hs0 : srun_N ag1 0 sc = sc) by reflexivity.
    assert (Hs1 : srun_N ag1 1 sc = c1) by reflexivity.
    assert (Hs2 : srun_N ag1 2 sc = c2) by reflexivity.
    assert (Hs3 : srun_N ag1 3 sc = c3) by reflexivity.
    assert (Hs4 : srun_N ag1 4 sc = c4) by reflexivity.
    assert (Hs5 : srun_N ag1 5 sc = c5) by reflexivity.
    rewrite Hs5. repeat split; auto.
    + intros k Hk.
      destruct (N.eq_dec k 0) as [->|]; [rewrite Hs0; lia|].
      destruct (N.eq_dec k 1) as [->|]; [rewrite Hs1; lia|].
      destruct (N.eq_dec k 2) as [->|]; [rewrite Hs2; lia|].
      destruct (N.eq_dec k 3) as [->|]; [rewrite Hs3; lia|].
      destruct (N.eq_dec k 4) as [->|]; [rewrite Hs4; lia | lia].
    + intros z Hz. replace z with x0 by lia. exact t50.
  - assert (Hm1_ge : (1 <= m)%N) by lia.
    assert (Ht_m : forall z, x0 <= z < x0 + Z.of_N m -> sc.(stape) z = S2) by (intros z Hz; apply Ht; lia).
    destruct (IHm x0 sc Hm1_ge Hp Hs Hm1 Ht_m) as [RngA [Ap [As [Am1 [At Ao]]]]].
    set (scA := srun_N ag1 (T_fill_3 m) sc) in *.
    set (scB := sstep ag1 scA).
    assert (HscB : scB.(spos) = x0 + Z.of_N m - 1 /\ scB.(sstate) = StB /\ scB.(stape) (x0 - 1) = S2 /\
                   (forall z, x0 <= z < x0 + Z.of_N m -> scB.(stape) z = S1) /\
                   scB.(stape) (x0 + Z.of_N m) = S0 /\
                   forall z, z < x0 - 1 \/ z >= x0 + Z.of_N (N.succ m) -> scB.(stape) z = sc.(stape) z).
    { unfold scB, sstep. rewrite Ap, As, Ao, Ht by lia. simpl. repeat split; try lia.
      - exact Am1.
      - intros z Hz. apply At; exact Hz.
      - apply write_tape_same.
      - intros z Hz. apply Ao; lia. }
    destruct HscB as [Bp [Bs [Bm1 [Bt [Bxm Bo]]]]].
    destruct (ag1_sweep_left m x0 scB Bp Bs Bt) as [RngC [Cp [Cs [Ct Co]]]].
    set (scC := srun_N ag1 m scB) in *.
    set (scD := sstep ag1 scC).
    assert (HscD : scD.(spos) = x0 /\ scD.(sstate) = StA /\ scD.(stape) (x0 - 1) = S2 /\
                   (forall z, x0 <= z < x0 + Z.of_N m -> scD.(stape) z = S2) /\
                   scD.(stape) (x0 + Z.of_N m) = S0 /\
                   forall z, z < x0 - 1 \/ z >= x0 + Z.of_N (N.succ m) -> scD.(stape) z = sc.(stape) z).
    { unfold scD, sstep. rewrite Cp, Cs, Co, Bm1 by lia. simpl. repeat split; try lia.
      - apply write_tape_same.
      - intros z Hz. apply Ct; exact Hz.
      - rewrite write_tape_other by lia, Co by lia; exact Bxm.
      - intros z Hz. rewrite write_tape_other by lia, Co by lia; apply Bo; exact Hz. }
    destruct HscD as [Dp [Ds [Dm1 [Dt [Dxm Do]]]]].
    destruct (IHm x0 scD Hm1_ge Dp Ds Dm1 Dt) as [RngE [Ep [Es [Em1 [Et Eo]]]]].
    set (scE := srun_N ag1 (T_fill_3 m) scD) in *.
    set (scF := sstep ag1 scE).
    assert (HscF : scF.(spos) = x0 + Z.of_N m - 1 /\ scF.(sstate) = StB /\ scF.(stape) (x0 - 1) = S2 /\
                   (forall z, x0 <= z < x0 + Z.of_N m -> scF.(stape) z = S1) /\
                   scF.(stape) (x0 + Z.of_N m) = S1 /\
                   forall z, z < x0 - 1 \/ z >= x0 + Z.of_N (N.succ m) -> scF.(stape) z = sc.(stape) z).
    { unfold scF, sstep. rewrite Ep, Es, Eo, Dxm by lia. simpl. repeat split; try lia.
      - rewrite write_tape_other by lia; exact Em1.
      - intros z Hz. rewrite write_tape_other by lia; apply Et; exact Hz.
      - apply write_tape_same.
      - intros z Hz. rewrite write_tape_other by lia, Eo by lia; apply Do; exact Hz. }
    destruct HscF as [Fp [Fs [Fm1 [Ft [Fxm Fo]]]]].
    destruct (ag1_sweep_left m x0 scF Fp Fs Ft) as [RngG [Gp [Gs [Gt Go]]]].
    set (scG := srun_N ag1 m scF) in *.
    set (scH := sstep ag1 scG).
    assert (HscH : scH.(spos) = x0 /\ scH.(sstate) = StA /\ scH.(stape) (x0 - 1) = S2 /\
                   (forall z, x0 <= z < x0 + Z.of_N m -> scH.(stape) z = S2) /\
                   scH.(stape) (x0 + Z.of_N m) = S1 /\
                   forall z, z < x0 - 1 \/ z >= x0 + Z.of_N (N.succ m) -> scH.(stape) z = sc.(stape) z).
    { unfold scH, sstep. rewrite Gp, Gs, Go, Fm1 by lia. simpl. repeat split; try lia.
      - apply write_tape_same.
      - intros z Hz. rewrite write_tape_other by lia; apply Gt; exact Hz.
      - rewrite write_tape_other by lia, Go by lia; exact Fxm.
      - intros z Hz. rewrite write_tape_other by lia, Go by lia; apply Fo; exact Hz. }
    destruct HscH as [Hp' [Hs' [Hm1' [Ht' [Hxm' Ho']]]]].
    destruct (IHm x0 scH Hm1_ge Hp' Hs' Hm1' Ht') as [RngI [Ip [Is [Im1 [It Io]]]]].
    set (scI := srun_N ag1 (T_fill_3 m) scH) in *.
    set (scJ := sstep ag1 scI).
    assert (HscJ : scJ.(spos) = x0 + Z.of_N (N.succ m) /\ scJ.(sstate) = StA /\ scJ.(stape) (x0 - 1) = S2 /\
                   (forall z, x0 <= z < x0 + Z.of_N (N.succ m) -> scJ.(stape) z = S1) /\
                   forall z, z < x0 - 1 \/ z >= x0 + Z.of_N (N.succ m) -> scJ.(stape) z = sc.(stape) z).
    { unfold scJ, sstep. rewrite Ip, Is, Io, Hxm' by lia. simpl. repeat split; try lia.
      - rewrite write_tape_other by lia; exact Im1.
      - intros z Hz. destruct (Z.eq_dec z (x0 + Z.of_N m)) as [-> | Hneq];
          [apply write_tape_same | rewrite write_tape_other by lia; apply It; lia].
      - intros z Hz. rewrite write_tape_other by lia, Io by lia; apply Ho'; exact Hz. }
    rewrite T_fill_3_succ by exact Hm1_ge.
    set (k_tot := (3 * T_fill_3 m + 2 * m + 5)%N).
    assert (Hk_eq : k_tot = (1 + (T_fill_3 m + (1 + (m + (1 + (T_fill_3 m + (1 + (m + (1 + T_fill_3 m)))))))))%N)
      by (unfold k_tot; lia).
    rewrite Hk_eq, !srun_N_add.
    change (srun_N ag1 1) with (sstep ag1).
    fold scA scB scC scD scE scF scG scH scI scJ.
    repeat split; try (apply HscJ).
    intros k Hk. unfold k_tot in Hk.
    destruct (N.lt_ge_cases k (T_fill_3 m)) as [Hk1|Hk1]; [specialize (RngA k Hk1); lia|].
    destruct (N.eq_dec k (T_fill_3 m)) as [->|]; [fold scA; rewrite Ap; lia|].
    destruct (N.lt_ge_cases k (1 + T_fill_3 m + m)) as [Hk2|Hk2].
    { replace k with ((k - (1 + T_fill_3 m)) + (1 + T_fill_3 m))%N by lia.
      rewrite srun_N_add, (srun_N_add ag1 1 (T_fill_3 m) sc).
      change (srun_N ag1 1) with (sstep ag1). fold scA scB.
      specialize (RngC (k - (1 + T_fill_3 m))%N ltac:(lia)); lia. }
    destruct (N.eq_dec k (1 + T_fill_3 m + m)) as [->|].
    { replace (1 + T_fill_3 m + m)%N with (m + (1 + T_fill_3 m))%N by lia.
      rewrite srun_N_add, (srun_N_add ag1 1 (T_fill_3 m) sc).
      change (srun_N ag1 1) with (sstep ag1). fold scA scB scC. rewrite Cp; lia. }
    destruct (N.lt_ge_cases k (2 + T_fill_3 m + m + T_fill_3 m)) as [Hk3|Hk3].
    { replace k with ((k - (2 + T_fill_3 m + m)) + (1 + (m + (1 + T_fill_3 m))))%N by lia.
      rewrite !srun_N_add, (srun_N_add ag1 1 (T_fill_3 m) sc).
      change (srun_N ag1 1) with (sstep ag1). fold scA scB scC scD.
      specialize (RngE (k - (2 + T_fill_3 m + m))%N ltac:(lia)); lia. }
    destruct (N.eq_dec k (2 + T_fill_3 m + m + T_fill_3 m)) as [->|].
    { replace (2 + T_fill_3 m + m + T_fill_3 m)%N with (T_fill_3 m + (1 + (m + (1 + T_fill_3 m))))%N by lia.
      rewrite !srun_N_add, (srun_N_add ag1 1 (T_fill_3 m) sc).
      change (srun_N ag1 1) with (sstep ag1). fold scA scB scC scD scE. rewrite Ep; lia. }
    destruct (N.lt_ge_cases k (3 + 2 * T_fill_3 m + 2 * m)) as [Hk4|Hk4].
    { replace k with ((k - (3 + 2 * T_fill_3 m + m)) + (1 + (T_fill_3 m + (1 + (m + (1 + T_fill_3 m))))))%N by lia.
      rewrite !srun_N_add, (srun_N_add ag1 1 (T_fill_3 m) sc).
      change (srun_N ag1 1) with (sstep ag1). fold scA scB scC scD scE scF.
      specialize (RngG (k - (3 + 2 * T_fill_3 m + m))%N ltac:(lia)); lia. }
    destruct (N.eq_dec k (3 + 2 * T_fill_3 m + 2 * m)) as [->|].
    { replace (3 + 2 * T_fill_3 m + 2 * m)%N with (m + (1 + (T_fill_3 m + (1 + (m + (1 + T_fill_3 m))))))%N by lia.
      rewrite !srun_N_add, (srun_N_add ag1 1 (T_fill_3 m) sc).
      change (srun_N ag1 1) with (sstep ag1). fold scA scB scC scD scE scF scG. rewrite Gp; lia. }
    destruct (N.lt_ge_cases k (4 + 3 * T_fill_3 m + 2 * m)) as [Hk5|Hk5].
    { replace k with ((k - (4 + 2 * T_fill_3 m + 2 * m)) + (1 + (m + (1 + (T_fill_3 m + (1 + (m + (1 + T_fill_3 m))))))))%N by lia.
      rewrite !srun_N_add, (srun_N_add ag1 1 (T_fill_3 m) sc).
      change (srun_N ag1 1) with (sstep ag1). fold scA scB scC scD scE scF scG scH.
      specialize (RngI (k - (4 + 2 * T_fill_3 m + 2 * m))%N ltac:(lia)); lia. }
    { replace k with (T_fill_3 m + (1 + (m + (1 + (T_fill_3 m + (1 + (m + (1 + T_fill_3 m))))))))%N by lia.
      rewrite !srun_N_add, (srun_N_add ag1 1 (T_fill_3 m) sc).
      change (srun_N ag1 1) with (sstep ag1). fold scA scB scC scD scE scF scG scH scI.
      rewrite Ip; lia. }
Qed.

(** * 6. Agent 2 Glider (P = 9, D = 1) *)

Definition sshift_cfg (dx : Z) (sc : SConfig) : SConfig := {|
  spos := sc.(spos) + dx; sstate := sc.(sstate); stape := shift_tape dx sc.(stape)
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
    assert (H := sstep_proper ag _ _ (IHn dx sc)). destruct H as [Hp [Hs Ht]].
    pose proof (sstep_shift ag dx (srun_N ag n sc)) as [Gp [Gs Gt]].
    split; [congruence | split; [congruence | eapply tape_eq_trans; eauto]].
Qed.

Definition glider_pat (t : Tape) (p2 : Z) : Prop :=
  t (p2 - 2) = S2 /\ t (p2 - 1) = S1 /\ t p2 = S1 /\ t (p2 + 1) = S0.

Definition sc_g0 : SConfig := {|
  spos := 0; sstate := StB;
  stape := fun z => if Z.eqb z (-2) then S2 else if Z.eqb z (-1) then S1 else if Z.eqb z 0 then S1 else S0
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
  intros ag lo hi n. induction n; intros sc H k Hk; [lia|].
  simpl in H. rewrite !andb_true_iff in H. destruct H as [[Hlo Hhi] Hrest].
  rewrite Z.leb_le in Hlo, Hhi.
  destruct (N.eq_dec k 0) as [-> | Hk0]; [rewrite srun_N_0; lia|].
  replace k with (N.succ (k - 1)) by lia. rewrite srun_N_succ.
  assert (Hcomm : forall m s, srun_N ag (N.succ m) s = srun_N ag m (sstep ag s)).
  { intro m. induction m using N.peano_ind; intro s; [reflexivity | rewrite srun_N_succ, IHm, srun_N_succ; reflexivity]. }
  rewrite <- srun_N_succ, Hcomm. apply IHn; auto; lia.
Qed.

Definition check_g9 : bool :=
  let sc9 := srun_N ag2 9 sc_g0 in
  check_srun_range ag2 (-2) 1 9 sc_g0 &&
  Z.eqb sc9.(spos) 1 && state_eqb sc9.(sstate) StB &&
  sym_eqb (sc9.(stape) (-2)) S1 && sym_eqb (sc9.(stape) (-1)) S2 &&
  sym_eqb (sc9.(stape) 0) S1 && sym_eqb (sc9.(stape) 1) S1 && sym_eqb (sc9.(stape) 2) S0.

Lemma check_g9_ok : check_g9 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ag2_glider_period : forall p2 sc,
  sc.(spos) = p2 -> sc.(sstate) = StB -> glider_pat sc.(stape) p2 -> sc.(stape) (p2 + 2) = S0 ->
  (forall k, (k < 9)%N -> p2 - 2 <= (srun_N ag2 k sc).(spos) <= p2 + 1) /\
  (srun_N ag2 9 sc).(spos) = p2 + 1 /\
  (srun_N ag2 9 sc).(sstate) = StB /\
  (srun_N ag2 9 sc).(stape) (p2 - 2) = S1 /\
  glider_pat (srun_N ag2 9 sc).(stape) (p2 + 1) /\
  (forall z, z < p2 - 2 \/ z > p2 + 1 -> (srun_N ag2 9 sc).(stape) z = sc.(stape) z).
Proof.
  intros p2 sc Hp Hs [Hgm2 [Hgm1 [Hg0 Hg1]]] Hg2.
  pose proof check_g9_ok as Hok. unfold check_g9 in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[[[Hrng Hp9] Hs9] Ht_m2] Ht_m1] Ht_0] Ht_1] Ht_2].
  rewrite Z.eqb_eq in Hp9. apply state_eqb_eq in Hs9.
  apply sym_eqb_eq in Ht_m2, Ht_m1, Ht_0, Ht_1, Ht_2.
  apply check_srun_range_sound in Hrng.
  assert (Hagree_g0 : forall k, (k < 9)%N -> p2 - 2 <= (srun_N ag2 k (sshift_cfg p2 sc_g0)).(spos) <= p2 + 1).
  { intros k Hk. destruct (srun_N_shift ag2 k p2 sc_g0) as [Sp _].
    rewrite Sp. simpl. specialize (Hrng k ltac:(change (N.of_nat 9) with 9%N; lia)). lia. }
  assert (Hsc_eq : sc.(spos) = (sshift_cfg p2 sc_g0).(spos) /\
                   sc.(sstate) = (sshift_cfg p2 sc_g0).(sstate) /\
                   (forall z, p2 - 2 <= z <= p2 + 1 -> sc.(stape) z = (sshift_cfg p2 sc_g0).(stape) z)).
  { repeat split; simpl; try lia; auto.
    intros z Hz. unfold shift_tape. simpl.
    assert (Hz' : z - p2 = -2 \/ z - p2 = -1 \/ z - p2 = 0 \/ z - p2 = 1) by lia.
    destruct Hz' as [-> | [-> | [-> | ->]]]; simpl;
      [replace (p2 + -2) with (p2 - 2) in * by lia; auto |
       replace (p2 + -1) with (p2 - 1) in * by lia; auto |
       replace (p2 + 0) with p2 in * by lia; auto | auto]. }
  destruct Hsc_eq as [Ep [Es Et]].
  assert (Hsc_rng : forall k, (k < 9)%N -> p2 - 2 <= (srun_N ag2 k sc).(spos) <= p2 + 1).
  { intros k Hk.
    destruct (srun_N_agree_range ag2 (p2 - 2) (p2 + 1) k (sshift_cfg p2 sc_g0) sc
                (fun j Hj => Hagree_g0 j ltac:(lia)) (eq_sym Ep) (eq_sym Es) (fun z Hz => eq_sym (Et z Hz)))
      as [Kp _].
    rewrite <- Kp. apply Hagree_g0; exact Hk. }
  destruct (srun_N_agree_range ag2 (p2 - 2) (p2 + 1) 9 sc (sshift_cfg p2 sc_g0) Hsc_rng Ep Es Et)
    as [Bp [Bs [Bt Bout]]].
  destruct (srun_N_shift ag2 9 p2 sc_g0) as [Sp [Ss St]].
  repeat split; auto.
  - rewrite Bp, Sp, Hp9. lia.
  - rewrite Bs, Ss, Hs9. reflexivity.
  - rewrite Bt by lia, St. unfold shift_tape. replace (p2 - 2 - p2) with (-2) by lia. exact Ht_m2.
  - unfold glider_pat.
    assert (Hpt : forall dx, -2 <= dx <= 1 -> (srun_N ag2 9 sc).(stape) (p2 + dx) = (srun_N ag2 9 sc_g0).(stape) dx).
    { intros dx Hdx. rewrite Bt by lia, St. unfold shift_tape. replace (p2 + dx - p2) with dx by lia. reflexivity. }
    repeat split.
    + replace (p2 + 1 - 2) with (p2 + -1) by lia. rewrite Hpt by lia. exact Ht_m1.
    + replace (p2 + 1 - 1) with (p2 + 0) by lia. rewrite Hpt by lia. exact Ht_0.
    + rewrite Hpt by lia. exact Ht_1.
    + rewrite Bout by lia. exact Hg2.
Qed.

Lemma ag2_glider_iter : forall q p2 sc,
  sc.(spos) = p2 -> sc.(sstate) = StB -> glider_pat sc.(stape) p2 ->
  (forall z, z >= p2 + 1 -> sc.(stape) z = S0) ->
  (forall k, (k < 9 * q)%N -> p2 - 2 <= (srun_N ag2 k sc).(spos) <= p2 + Z.of_N q) /\
  (srun_N ag2 (9 * q) sc).(spos) = p2 + Z.of_N q /\
  (srun_N ag2 (9 * q) sc).(sstate) = StB /\
  (forall z, p2 - 2 <= z < p2 + Z.of_N q - 2 -> (srun_N ag2 (9 * q) sc).(stape) z = S1) /\
  glider_pat (srun_N ag2 (9 * q) sc).(stape) (p2 + Z.of_N q) /\
  (forall z, z >= p2 + Z.of_N q + 1 -> (srun_N ag2 (9 * q) sc).(stape) z = S0) /\
  (forall z, z < p2 - 2 \/ z > p2 + Z.of_N q + 1 -> (srun_N ag2 (9 * q) sc).(stape) z = sc.(stape) z).
Proof.
  intro q. induction q using N.peano_ind; intros p2 sc Hp Hs Hpat Hzero.
  - rewrite N.mul_0_r, srun_N_0. repeat split; try lia; auto; [intros k Hk; lia | intros z Hz; lia | replace (p2 + Z.of_N 0) with p2 by lia; exact Hpat].
  - destruct (ag2_glider_period p2 sc Hp Hs Hpat (Hzero (p2 + 2) ltac:(lia))) as [Rng1 [P1 [S1 [T1m2 [Pat1 Out1]]]]].
    set (sc1 := srun_N ag2 9 sc) in *.
    assert (Hz1 : forall z, z >= p2 + 1 + 1 -> sc1.(stape) z = S0) by (intros z Hz; rewrite Out1 by lia; apply Hzero; lia).
    destruct (IHq (p2 + 1) sc1 P1 S1 Pat1 Hz1) as [RngQ [PQ [SQ [TrQ [PatQ [HzQ OutQ]]]]]].
    replace (9 * N.succ q)%N with (9 * q + 9)%N by lia. rewrite srun_N_add. fold sc1.
    repeat split; try lia; try exact SQ.
    + intros k Hk. destruct (N.lt_ge_cases k 9) as [Hk9 | Hk9]; [specialize (Rng1 k Hk9); lia|].
      replace k with ((k - 9) + 9)%N by lia. rewrite srun_N_add. fold sc1.
      specialize (RngQ (k - 9)%N ltac:(lia)). lia.
    + replace (p2 + 1 + Z.of_N q) with (p2 + Z.of_N (N.succ q)) in * by lia. exact PQ.
    + intros z Hz. destruct (Z.eq_dec z (p2 - 2)) as [-> | Hneq]; [rewrite OutQ by lia; exact T1m2 | apply TrQ; lia].
    + replace (p2 + 1 + Z.of_N q) with (p2 + Z.of_N (N.succ q)) in * by lia. exact PatQ.
    + intros z Hz. apply HzQ. lia.
    + intros z Hz. rewrite OutQ by lia. apply Out1. lia.
Qed.

(** * 7. 27-Step Bounce Lemma for G in {8, 10} *)

Fixpoint bt_fill_range (lo : Z) (len : nat) (v : Sym) (t : BTree) : BTree :=
  match len with
  | O => t
  | S n => bt_set (z_to_pos lo) v (bt_fill_range (lo + 1) n v t)
  end.

Lemma bt_fill_range_in : forall len lo v t z,
  lo <= z < lo + Z.of_nat len ->
  bt_get (z_to_pos z) (bt_fill_range lo len v t) = v.
Proof.
  induction len; intros lo v t z Hz; simpl in *; [lia|].
  destruct (Z.eq_dec z lo) as [-> | Hneq]; [apply bt_get_set_same|].
  rewrite bt_get_set_diff; [apply IHlen; lia | intro Heq; apply Hneq, z_to_pos_inj; exact Heq].
Qed.

Lemma bt_fill_range_out : forall len lo v t z,
  z < lo \/ z >= lo + Z.of_nat len ->
  bt_get (z_to_pos z) (bt_fill_range lo len v t) = bt_get (z_to_pos z) t.
Proof.
  induction len; intros lo v t z Hz; simpl in *; [reflexivity|].
  rewrite bt_get_set_diff; [apply IHlen; lia | intro Heq; apply z_to_pos_inj in Heq; lia].
Qed.

Definition bounce_fc (G : Z) : FastConfig :=
  let t1 := bt_fill_range (-20) (Z.to_nat (G + 18)) S1 BEmpty in
  let t2 := bt_set (z_to_pos (G - 2)) S2 t1 in
  let t3 := bt_set (z_to_pos (G - 1)) S1 t2 in
  let t4 := bt_set (z_to_pos G) S1 t3 in
  {| fpos1 := 0; fpos2 := G; fstate1 := StA; fstate2 := StB; ftape := t4 |}.

Definition exp_b27 (G z : Z) : Sym :=
  if Z.ltb z (-20) then S0
  else if Z.leb z (2 * G - 29) then S1
  else if Z.ltb z (G - 1) then S2
  else if Z.eqb z (G - 1) then S1
  else if Z.eqb z G then S1
  else if Z.eqb z (G + 1) then S2
  else if Z.eqb z (G + 2) then S1
  else if Z.eqb z (G + 3) then S1
  else S0.

Fixpoint check_b27_range (G lo : Z) (len : nat) (t : BTree) : bool :=
  match len with
  | O => true
  | S n => sym_eqb (bt_get (z_to_pos lo) t) (exp_b27 G lo) && check_b27_range G (lo + 1) n t
  end.

Lemma check_b27_range_sound : forall len G lo t,
  check_b27_range G lo len t = true ->
  forall z, lo <= z < lo + Z.of_nat len -> bt_get (z_to_pos z) t = exp_b27 G z.
Proof.
  induction len; intros G lo t H z Hz; simpl in *; [lia|].
  rewrite andb_true_iff in H. destruct H as [H0 Hrest]. apply sym_eqb_eq in H0.
  destruct (Z.eq_dec z lo) as [-> | Hneq]; [exact H0 | apply IHlen; auto; lia].
Qed.

Definition check_b27 (G : Z) : bool :=
  let st := N.iter 27 (fast_step_chk_range (-20) (G + 5)) (bounce_fc G, true) in
  let (fc, ok) := st in
  ok && Z.eqb fc.(fpos1) (2 * G - 29) && Z.eqb fc.(fpos2) (G + 3)
     && state_eqb fc.(fstate1) StB && state_eqb fc.(fstate2) StB
     && check_b27_range G (-20) (Z.to_nat (G + 26)) fc.(ftape).

Lemma check_b27_all_ok : forallb check_b27 [8; 10] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bounce_27_ok : forall G L_left x0 c,
  (G = 8 \/ G = 10) ->
  (20 <= L_left)%N ->
  round_inv G L_left x0 c ->
  (forall k, (k < 27)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  let c1 := run_N ag1 ag2 27 c in
  c1.(pos1) = x0 + 2 * G - 29 /\
  c1.(state1) = StB /\
  c1.(pos2) = x0 + G + 3 /\
  c1.(state2) = StB /\
  (forall z, z < x0 - Z.of_N L_left - 1 -> c1.(tape) z = S0) /\
  c1.(tape) (x0 - Z.of_N L_left - 1) = S2 /\
  (forall z, x0 - Z.of_N L_left <= z <= x0 + 2 * G - 29 -> c1.(tape) z = S1) /\
  (forall z, x0 + 2 * G - 28 <= z <= x0 + G - 2 -> c1.(tape) z = S2) /\
  c1.(tape) (x0 + G - 1) = S1 /\
  c1.(tape) (x0 + G) = S1 /\
  glider_pat c1.(tape) (x0 + G + 3) /\
  (forall z, z > x0 + G + 3 -> c1.(tape) z = S0).
Proof.
  intros G L_left x0 c HG HL Hinv.
  assert (Hchk : check_b27 G = true).
  { pose proof check_b27_all_ok as Hall. simpl in Hall. rewrite !andb_true_iff in Hall.
    destruct Hall as [[H8 H10] _]. destruct HG as [-> | ->]; auto. }
  unfold check_b27 in Hchk.
  remember (N.iter 27 (fast_step_chk_range (-20) (G + 5)) (bounce_fc G, true)) as st eqn:Est.
  destruct st as [fc_end ok_end]. rewrite !andb_true_iff in Hchk.
  destruct Hchk as [[[[[Hok_end Hp1] Hp2] Hs1] Hs2] Hrng].
  rewrite Z.eqb_eq in Hp1, Hp2. apply state_eqb_eq in Hs1, Hs2.
  assert (Hfc : fc_end = N.iter 27 fast_step (bounce_fc G))
    by (pose proof (fast_step_chk_range_fst 27 (-20) (G + 5) (bounce_fc G) true) as Hfst; rewrite <- Est in Hfst; exact Hfst).
  assert (Hsnd : snd (N.iter 27 (fast_step_chk_range (-20) (G + 5)) (bounce_fc G, true)) = true)
    by (rewrite <- Est; exact Hok_end).
  destruct (fast_step_chk_range_sound 27 (-20) (G + 5) (bounce_fc G) true Hsnd) as [_ Hstep].
  assert (Hb0_rng : forall z, x0 - 20 <= z <= x0 + G + 5 ->
    c.(tape) z = (shift_cfg x0 (fc_to_cfg (bounce_fc G))).(tape) z).
  { intros z Hz. unfold shift_cfg, shift_tape, fc_to_cfg, bt_interp, bounce_fc. simpl.
    destruct Hinv as [_ [_ [_ [_ [_ [_ [Htr [Hm2 [Hm1 [H0 Hgt]]]]]]]]]]].
    assert (HG_pos : G = 8 \/ G = 10) by exact HG.
    destruct (Z.eq_dec (z - x0) G) as [->|]; [rewrite bt_get_set_same; replace z with (x0 + G) by lia; exact H0|].
    rewrite bt_get_set_diff by (intro H; apply z_to_pos_inj in H; congruence).
    destruct (Z.eq_dec (z - x0) (G - 1)) as [->|]; [rewrite bt_get_set_same; replace z with (x0 + G - 1) by lia; exact Hm1|].
    rewrite bt_get_set_diff by (intro H; apply z_to_pos_inj in H; congruence).
    destruct (Z.eq_dec (z - x0) (G - 2)) as [->|]; [rewrite bt_get_set_same; replace z with (x0 + G - 2) by lia; exact Hm2|].
    rewrite bt_get_set_diff by (intro H; apply z_to_pos_inj in H; congruence).
    destruct (Z.lt_ge_cases (z - x0) (G - 2)) as [Hlt | Hge].
    - rewrite bt_fill_range_in by lia. apply Htr. lia.
    - rewrite bt_fill_range_out by lia. rewrite bt_get_empty. apply Hgt. lia. }
  destruct Hinv as [Cp1 [Cs1 [Cp2 [Cs2 [HltL [Hanc [HtrL [_ [_ [_ Hgt0]]]]]]]]]].
  assert (Hrng_shift : forall k, (k < 27)%N ->
    x0 - 20 <= (run_N ag1 ag2 k (shift_cfg x0 (fc_to_cfg (bounce_fc G)))).(pos1) <= x0 + G + 5 /\
    x0 - 20 <= (run_N ag1 ag2 k (shift_cfg x0 (fc_to_cfg (bounce_fc G)))).(pos2) <= x0 + G + 5).
  { intros k Hk. destruct (run_N_shift ag1 ag2 k x0 (fc_to_cfg (bounce_fc G))) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl. pose proof (fast_run_sound k (bounce_fc G)) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl. destruct (Hstep k Hk) as [_ [Ha Hb]]. lia. }
  assert (Hc_rng : forall k, (k < 27)%N ->
    x0 - 20 <= (run_N ag1 ag2 k c).(pos1) <= x0 + G + 5 /\
    x0 - 20 <= (run_N ag1 ag2 k c).(pos2) <= x0 + G + 5).
  { intros k Hk.
    destruct (run_N_agree_range ag1 ag2 (x0 - 20) (x0 + G + 5) k
                (shift_cfg x0 (fc_to_cfg (bounce_fc G))) c
                (fun j Hj => Hrng_shift j ltac:(lia))
                (eq_sym Cp1) (eq_sym Cp2) (eq_sym Cs1) (eq_sym Cs2)
                (fun z Hz => eq_sym (Hb0_rng z Hz))) as [Kp1 [Kp2 _]].
    rewrite <- Kp1, <- Kp2. apply Hrng_shift; exact Hk. }
  split.
  - intros k Hk.
    destruct (run_N_agree_range ag1 ag2 (x0 - 20) (x0 + G + 5) k c
                (shift_cfg x0 (fc_to_cfg (bounce_fc G)))
                (fun j Hj => Hc_rng j ltac:(lia)) Cp1 Cp2 Cs1 Cs2 Hb0_rng) as [Kp1 [Kp2 _]].
    rewrite Kp1, Kp2. destruct (run_N_shift ag1 ag2 k x0 (fc_to_cfg (bounce_fc G))) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl. pose proof (fast_run_sound k (bounce_fc G)) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl. destruct (Hstep k Hk) as [Hneq _]. lia.
  - destruct (run_N_agree_range ag1 ag2 (x0 - 20) (x0 + G + 5) 27 c
                (shift_cfg x0 (fc_to_cfg (bounce_fc G))) Hc_rng Cp1 Cp2 Cs1 Cs2 Hb0_rng)
      as [Kp1 [Kp2 [Ks1 [Ks2 Ktp]]]].
    destruct (run_N_shift ag1 ag2 27 x0 (fc_to_cfg (bounce_fc G))) as [Sp1 [Sp2 [Ss1 [Ss2 Stp]]]].
    pose proof (fast_run_sound 27 (bounce_fc G)) as [Fp1 [Fp2 [Fs1 [Fs2 Ftp]]]].
    rewrite <- Hfc in Fp1, Fp2, Fs1, Fs2, Ftp.
    assert (Hout_c : forall z, z < x0 - 20 \/ z > x0 + G + 5 -> (run_N ag1 ag2 27 c).(tape) z = c.(tape) z).
    { intros z Hz.
      assert (Hgen : forall n, (n <= 27)%N -> (run_N ag1 ag2 n c).(tape) z = c.(tape) z).
      { intro n. induction n using N.peano_ind; intro Hn; [rewrite run_N_0; reflexivity|].
        rewrite run_N_succ. unfold step. simpl. destruct (Hc_rng n ltac:(lia)) as [Hn1 Hn2].
        rewrite write_tape_other by lia, write_tape_other by lia. apply IHn. lia. }
      apply Hgen. lia. }
    apply check_b27_range_sound in Hrng.
    assert (Htp_val : forall z, x0 - 20 <= z <= x0 + G + 5 -> (run_N ag1 ag2 27 c).(tape) z = exp_b27 G (z - x0)).
    { intros z Hz. rewrite Ktp by exact Hz, Stp. unfold shift_tape. rewrite <- Ftp. simpl. unfold bt_interp. apply Hrng. lia. }
    assert (HG_pos : G = 8 \/ G = 10) by exact HG.
    repeat split; try lia.
    + rewrite Kp1, Sp1, <- Fp1. simpl. lia.
    + rewrite Ks1, Ss1, <- Fs1. simpl. exact Hs1.
    + rewrite Kp2, Sp2, <- Fp2. simpl. lia.
    + rewrite Ks2, Ss2, <- Fs2. simpl. exact Hs2.
    + intros z Hz. rewrite Hout_c by lia. apply HltL; exact Hz.
    + rewrite Hout_c by lia. exact Hanc.
    + intros z Hz. destruct (Z.lt_ge_cases z (x0 - 20)) as [Hlt | Hge]; [rewrite Hout_c by lia; apply HtrL; lia|].
      rewrite Htp_val by lia. unfold exp_b27.
      destruct (Z.ltb_spec (z - x0) (-20)); [lia|].
      destruct (Z.leb_spec (z - x0) (2 * G - 29)); [reflexivity | lia].
    + intros z Hz. rewrite Htp_val by lia. unfold exp_b27.
      destruct (Z.ltb_spec (z - x0) (-20)); [lia|].
      destruct (Z.leb_spec (z - x0) (2 * G - 29)); [lia|].
      destruct (Z.ltb_spec (z - x0) (G - 1)); [reflexivity | lia].
    + rewrite Htp_val by lia. unfold exp_b27.
      destruct (Z.ltb_spec (x0 + G - 1 - x0) (-20)); [lia|].
      destruct (Z.leb_spec (x0 + G - 1 - x0) (2 * G - 29)); [lia|].
      destruct (Z.ltb_spec (x0 + G - 1 - x0) (G - 1)); [lia|].
      destruct (Z.eqb_spec (x0 + G - 1 - x0) (G - 1)); [reflexivity | lia].
    + rewrite Htp_val by lia. unfold exp_b27.
      destruct (Z.ltb_spec (x0 + G - x0) (-20)); [lia|].
      destruct (Z.leb_spec (x0 + G - x0) (2 * G - 29)); [lia|].
      destruct (Z.ltb_spec (x0 + G - x0) (G - 1)); [lia|].
      destruct (Z.eqb_spec (x0 + G - x0) (G - 1)); [lia|].
      destruct (Z.eqb_spec (x0 + G - x0) G); [reflexivity | lia].
    + unfold glider_pat. repeat split; rewrite Htp_val by lia; unfold exp_b27;
        repeat match goal with
        | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b); try lia
        | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); try lia
        | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); try lia
        end; reflexivity.
    + intros z Hz. destruct (Z.lt_ge_cases (x0 + G + 5) z) as [Hgt | Hle]; [rewrite Hout_c by lia; apply Hgt0; lia|].
      rewrite Htp_val by lia. unfold exp_b27.
      repeat match goal with
      | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b); try lia
      | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); try lia
      | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); try lia
      end; reflexivity.
Qed.

(** * 8. Chase, Full Round Lemma, Modular Exponentiation, and 8-Round Tower *)

Lemma round_chase : forall k_close G_cur L_left x0 c,
  (8 <= G_cur - 8 * Z.of_N k_close)%Z ->
  round_inv G_cur L_left x0 c ->
  (forall k, (k < 9 * k_close)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  round_inv (G_cur - 8 * Z.of_N k_close) (L_left + 9 * k_close) (x0 + 9 * Z.of_N k_close)
    (run_N ag1 ag2 (9 * k_close) c).
Proof.
  intro k_close. induction k_close using N.peano_ind; intros G_cur L_left x0 c Hgap Hinv.
  - rewrite N.mul_0_r, run_N_0, N.add_0_r.
    replace (G_cur - 8 * Z.of_N 0) with G_cur by lia.
    replace (x0 + 9 * Z.of_N 0) with x0 by lia.
    split; [intros k Hk; lia | exact Hinv].
  - assert (HG_ge : G_cur >= 16) by lia.
    destruct Hinv as [Cp1 [Cs1 [Cp2 [Cs2 [HltL [Hanc [HtrL [Hm2 [Hm1 [H0 Hgt0]]]]]]]]]].
    set (sc1 := {| spos := x0; sstate := StA; stape := c.(tape) |}).
    set (sc2 := {| spos := x0 + G_cur; sstate := StB; stape := c.(tape) |}).
    assert (Hw1 : forall z, x0 <= z < x0 + Z.of_N 9 -> sc1.(stape) z = S1) by (intros z Hz; apply HtrL; lia).
    destruct (ag1_walk_right 9 x0 sc1 eq_refl eq_refl Hw1) as [Rng1 [P1 [S1 T1]]].
    assert (Hpat2 : glider_pat sc2.(stape) (x0 + G_cur)) by (unfold glider_pat; simpl; repeat split; auto).
    destruct (ag2_glider_period (x0 + G_cur) sc2 eq_refl eq_refl Hpat2 (Hgt0 (x0 + G_cur + 2) ltac:(lia)))
      as [Rng2 [P2 [S2 [T2m2 [Pat2 Out2]]]]].
    destruct (run_N_decouple ag1 ag2 x0 (x0 + 8) (x0 + G_cur - 2) (x0 + G_cur + 1) 9 c sc1 sc2
                ltac:(lia) (fun k Hk => Rng1 k Hk) (fun k Hk => Rng2 k Hk)
                Cp1 Cs1 (fun z Hz => eq_refl) Cp2 Cs2 (fun z Hz => eq_refl))
      as [Hnc1 [Dp1 [Ds1 [Dt1 [Dp2 [Ds2 [Dt2 Dout]]]]]]].
    set (c1 := run_N ag1 ag2 9 c) in *.
    assert (Hinv1 : round_inv (G_cur - 8) (L_left + 9) (x0 + 9) c1).
    { unfold round_inv. rewrite Dp1, Ds1, Dp2, Ds2, P1, S1, P2, S2.
      replace (x0 + G_cur + 1) with (x0 + 9 + (G_cur - 8)) by lia.
      repeat split; try lia; auto.
      - intros z Hz. rewrite Dout by lia. apply HltL. lia.
      - rewrite Dout by lia. exact Hanc.
      - intros z Hz. destruct (Z.le_gt_cases z (x0 + 8)) as [Hle | Hgt].
        + destruct (Z.lt_ge_cases z x0) as [Hlt | Hge]; [rewrite Dout by lia; apply HtrL; lia | rewrite Dt1 by lia, T1; apply HtrL; lia].
        + destruct (Z.lt_ge_cases z (x0 + G_cur - 2)) as [Hlt | Hge]; [rewrite Dout by lia; apply HtrL; lia|].
          replace z with (x0 + G_cur - 2) by lia. rewrite Dt2 by lia. exact T2m2.
      - replace (x0 + 9 + (G_cur - 8) - 2) with (x0 + G_cur + 1 - 2) by lia. rewrite Dt2 by lia. apply Pat2.
      - replace (x0 + 9 + (G_cur - 8) - 1) with (x0 + G_cur + 1 - 1) by lia. rewrite Dt2 by lia. apply Pat2.
      - replace (x0 + 9 + (G_cur - 8)) with (x0 + G_cur + 1) by lia. rewrite Dt2 by lia. apply Pat2.
      - intros z Hz. rewrite Dout by lia. apply Hgt0. lia. }
    destruct (IHk_close (G_cur - 8) (L_left + 9) (x0 + 9) c1 ltac:(lia) Hinv1) as [Hnc2 Hinv2].
    replace (9 * N.succ k_close)%N with (9 * k_close + 9)%N by lia.
    split; [eapply no_coll_add; [exact Hnc1 | fold c1; exact Hnc2]|].
    rewrite run_N_add. fold c1.
    replace (L_left + 9 + 9 * k_close)%N with (L_left + 9 * N.succ k_close)%N in Hinv2 by lia.
    replace (x0 + 9 + 9 * Z.of_N k_close) with (x0 + 9 * Z.of_N (N.succ k_close)) in Hinv2 by lia.
    replace (G_cur - 8 - 8 * Z.of_N k_close) with (G_cur - 8 * Z.of_N (N.succ k_close)) in Hinv2 by lia.
    exact Hinv2.
Qed.

Lemma round_bounce : forall G L_left x0 c dt q_sync k_close G_next,
  (G = 8 \/ G = 10) ->
  (20 <= L_left)%N ->
  (dt < 9)%N ->
  (20 <= q_sync)%N ->
  round_inv G L_left x0 c ->
  let T_exit := (3 ^ (L_left + Z.to_N G + 1) + Z.to_N G - 2)%N in
  (T_exit - 27 + dt = 9 * q_sync)%N ->
  2 + Z.of_N q_sync - Z.of_N dt - 8 * Z.of_N k_close = G_next ->
  8 <= G_next < 16 ->
  let T_round := (T_exit + dt + 9 * k_close)%N in
  (forall k, (k < T_round)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  round_inv G_next (L_left + Z.to_N G + 1 + dt + 9 * k_close)
    (x0 + G + 1 + Z.of_N dt + 9 * Z.of_N k_close) (run_N ag1 ag2 T_round c).
Proof.
  intros G L_left x0 c dt q_sync k_close G_next HG HL Hdt Hq Hinv T_exit Hsync Hgap HGnext T_round.
  assert (HG_b : G = 8 \/ G = 10) by exact HG.
  assert (HT_ge : (T_exit >= 27 + 9 * 20)%N).
  { unfold T_exit. assert (Hpow : (3 ^ (L_left + Z.to_N G + 1) >= 3 ^ 10)%N) by (apply N.pow_le_mono_r; [discriminate | lia]).
    change (3 ^ 10)%N with 59049%N in Hpow. lia. }
  destruct (bounce_27_ok G L_left x0 c HG HL Hinv)
    as [Hnc27 [P27 [S271 [P272 [S272 [Tlt27 [Tanc27 [Ttr27 [Tfl27 [Tm127 [T027 [Pat27 Tgt27]]]]]]]]]]]].
  set (c27 := run_N ag1 ag2 27 c) in *.
  set (m_sw := (L_left + 2 * Z.to_N G - 28)%N).
  set (m_fl := (L_left + Z.to_N G - 1)%N).
  set (m_wk := (2 + dt)%N).
  assert (Hm_sum : (m_sw + 1 + T_fill_3 m_fl + m_wk = T_exit - 27 + dt)%N).
  { unfold m_sw, m_fl, m_wk, T_exit, T_fill_3.
    replace (m_fl + 1)%N with (L_left + Z.to_N G + 1)%N by (unfold m_fl; lia).
    assert (Hpow : (3 ^ (L_left + Z.to_N G + 1) >= 59049)%N).
    { apply N.pow_le_mono_r; [discriminate | lia]. }
    unfold m_fl in *. lia. }
  set (tp1 := fun z : Z =>
    if Z.eqb z (x0 - Z.of_N L_left - 1) then S2
    else if Z.leb (x0 - Z.of_N L_left) z then
      if Z.leb z (x0 + 2 * G - 29) then S1
      else if Z.leb z (x0 + G - 2) then S2
      else S1
    else S0).
  set (sc1 := {| spos := x0 + 2 * G - 29; sstate := StB; stape := tp1 |}).
  set (sc2 := {| spos := x0 + G + 3; sstate := StB; stape := c27.(tape) |}).
  assert (Hsw1 : forall z, x0 - Z.of_N L_left <= z < x0 - Z.of_N L_left + Z.of_N m_sw -> sc1.(stape) z = S1).
  { intros z Hz. unfold sc1, tp1. simpl.
    destruct (Z.eqb_spec z (x0 - Z.of_N L_left - 1)); [lia|].
    destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
    destruct (Z.leb_spec z (x0 + 2 * G - 29)); [reflexivity | unfold m_sw in Hz; lia]. }
  assert (Hsw_pos : sc1.(spos) = x0 - Z.of_N L_left + Z.of_N m_sw - 1) by (simpl; unfold m_sw; lia).
  destruct (ag1_sweep_left m_sw (x0 - Z.of_N L_left) sc1 Hsw_pos eq_refl Hsw1)
    as [Rng_sw [P_sw [S_sw [T_sw Out_sw]]]].
  set (sc1_sw := srun_N ag1 m_sw sc1) in *.
  set (sc1_anc := sstep ag1 sc1_sw).
  assert (Hanc_step : sc1_anc.(spos) = x0 - Z.of_N L_left /\ sc1_anc.(sstate) = StA /\
                      sc1_anc.(stape) (x0 - Z.of_N L_left - 1) = S2 /\
                      (forall z, x0 - Z.of_N L_left <= z < x0 - Z.of_N L_left + Z.of_N m_fl -> sc1_anc.(stape) z = S2) /\
                      (forall z, z < x0 - Z.of_N L_left - 1 \/ z >= x0 - Z.of_N L_left + Z.of_N m_fl -> sc1_anc.(stape) z = sc1_sw.(stape) z)).
  { unfold sc1_anc, sstep. rewrite P_sw, S_sw.
    assert (Hm1_eq : sc1_sw.(stape) (x0 - Z.of_N L_left - 1) = S2).
    { rewrite Out_sw by lia. unfold sc1, tp1. simpl. rewrite Z.eqb_refl. reflexivity. }
    rewrite Hm1_eq. simpl. repeat split; try lia.
    - apply write_tape_same.
    - intros z Hz. 
      destruct (Z.lt_ge_cases z (x0 + 2 * G - 28)) as [Hlt | Hge]; [apply T_sw; unfold m_sw; lia|].
      rewrite Out_sw by (unfold m_sw; lia). unfold sc1, tp1. simpl.
      destruct (Z.eqb_spec z (x0 - Z.of_N L_left - 1)); [lia|].
      destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
      destruct (Z.leb_spec z (x0 + 2 * G - 29)); [lia|].
      destruct (Z.leb_spec z (x0 + G - 2)); [reflexivity | unfold m_fl in Hz; lia].
    - intros z Hz. reflexivity. }
  destruct Hanc_step as [Pa_sw [Sa_sw [Am1_sw [At_sw Ao_sw]]]].
  destruct (ag1_fill_3 m_fl (x0 - Z.of_N L_left) sc1_anc ltac:(unfold m_fl; lia) Pa_sw Sa_sw Am1_sw At_sw)
    as [Rng_fl [P_fl [S_fl [Fl_m1 [T_fl Out_fl]]]]].
  set (sc1_fl := srun_N ag1 (T_fill_3 m_fl) sc1_anc) in *.
  assert (Hwk_p : sc1_fl.(spos) = x0 + G - 1) by (rewrite P_fl; unfold m_fl; lia).
  assert (Hwk_t : forall z, x0 + G - 1 <= z < x0 + G - 1 + Z.of_N m_wk -> sc1_fl.(stape) z = S1).
  { intros z Hz. rewrite Out_fl by (unfold m_fl; lia). rewrite Ao_sw by (unfold m_fl; lia).
    rewrite Out_sw by (unfold m_sw, m_fl; lia). unfold sc1, tp1. simpl.
    destruct (Z.eqb_spec z (x0 - Z.of_N L_left - 1)); [lia|].
    destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
    destruct (Z.leb_spec z (x0 + 2 * G - 29)); [reflexivity|].
    destruct (Z.leb_spec z (x0 + G - 2)); [lia | reflexivity]. }
  destruct (ag1_walk_right m_wk (x0 + G - 1) sc1_fl Hwk_p S_fl Hwk_t) as [Rng_wk [P_wk [S_wk T_wk]]].
  destruct (ag2_glider_iter q_sync (x0 + G + 3) sc2 eq_refl eq_refl Pat27 Tgt27)
    as [Rng_g [P_g [S_g [Tr_g [Pat_g [Hz_g Out_g]]]]]].
  set (lo1 := x0 - Z.of_N L_left - 1).
  set (x_split := x0 + G - 2).
  set (hi1 := x0 + G + 1 + Z.of_N dt).
  set (lo2 := x0 + G + 15).
  assert (Hk_split_le : (9 * 20 <= 9 * q_sync)%N) by lia.
  assert (Hrk1 : forall k, (k < 9 * 20)%N -> lo1 <= (srun_N ag1 k sc1).(spos) <= x_split).
  { intros k Hk.
    destruct (N.lt_ge_cases k m_sw) as [Hk1 | Hk1]; [specialize (Rng_sw k Hk1); unfold lo1, x_split, m_sw in *; lia|].
    destruct (N.eq_dec k m_sw) as [-> | Hneq]; [rewrite P_sw; unfold lo1, x_split; lia|].
    assert (Hk_fl : (k - (m_sw + 1) < T_fill_3 m_fl)%N).
    { unfold T_fill_3. assert (Hpow : (3 ^ (m_fl + 1) >= 59049)%N) by (apply N.pow_le_mono_r; [discriminate | unfold m_fl; lia]).
      unfold m_fl in *. lia. }
    replace k with ((k - (m_sw + 1)) + (1 + m_sw))%N by lia.
    rewrite !srun_N_add. change (srun_N ag1 1) with (sstep ag1). fold sc1_sw sc1_anc.
    specialize (Rng_fl (k - (m_sw + 1))%N Hk_fl). unfold lo1, x_split, m_fl in *. lia. }
  assert (Hrn1 : forall k, (k < 9 * q_sync)%N -> lo1 <= (srun_N ag1 k sc1).(spos) <= hi1).
  { intros k Hk.
    destruct (N.lt_ge_cases k m_sw) as [Hk1 | Hk1]; [specialize (Rng_sw k Hk1); unfold lo1, hi1, m_sw in *; lia|].
    destruct (N.eq_dec k m_sw) as [-> | Hneq]; [rewrite P_sw; unfold lo1, hi1; lia|].
    destruct (N.lt_ge_cases k (m_sw + 1 + T_fill_3 m_fl)) as [Hk2 | Hk2].
    - replace k with ((k - (m_sw + 1)) + (1 + m_sw))%N by lia.
      rewrite !srun_N_add. change (srun_N ag1 1) with (sstep ag1). fold sc1_sw sc1_anc.
      specialize (Rng_fl (k - (m_sw + 1))%N ltac:(lia)). unfold lo1, hi1, m_fl in *. lia.
    - replace k with ((k - (m_sw + 1 + T_fill_3 m_fl)) + (T_fill_3 m_fl + (1 + m_sw)))%N by lia.
      rewrite !srun_N_add. change (srun_N ag1 1) with (sstep ag1). fold sc1_sw sc1_anc sc1_fl.
      specialize (Rng_wk (k - (m_sw + 1 + T_fill_3 m_fl))%N ltac:(lia)). unfold lo1, hi1, m_wk in *. lia. }
  assert (Hrn2 : forall k, (k < 9 * q_sync)%N -> x_split + 1 <= (srun_N ag2 k sc2).(spos))
    by (intros k Hk; specialize (Rng_g k Hk); unfold x_split in *; lia).
  destruct (ag2_glider_iter 20 (x0 + G + 3) sc2 eq_refl eq_refl Pat27 Tgt27)
    as [_ [P_g20 [S_g20 [Tr_g20 [Pat_g20 [Hz_g20 _]]]]]].
  assert (Hrk2 : forall k, (9 * 20 <= k < 9 * q_sync)%N -> lo2 <= (srun_N ag2 k sc2).(spos)).
  { intros k [Hk1 Hk2]. replace k with ((k - 9 * 20) + 9 * 20)%N by lia. rewrite srun_N_add.
    destruct (ag2_glider_iter (q_sync - 20) (x0 + G + 3 + 20) (srun_N ag2 (9 * 20) sc2)
                P_g20 S_g20 Pat_g20 Hz_g20) as [Rng_g2 _].
    specialize (Rng_g2 (k - 9 * 20)%N ltac:(lia)). unfold lo2 in *. lia. }
  assert (Hmid_g : forall z, x_split < z <= hi1 -> (srun_N ag2 (9 * 20) sc2).(stape) z = sc1.(stape) z).
  { intros z Hz.
    destruct (Z.lt_ge_cases z (x0 + G + 1)) as [Hlt | Hge].
    - assert (Hout2 : z < x0 + G + 3 - 2) by lia.
      destruct (ag2_glider_iter 20 (x0 + G + 3) sc2 eq_refl eq_refl Pat27 Tgt27) as [_ [_ [_ [_ [_ [_ Out20]]]]]].
      rewrite Out20 by lia. simpl.
      assert (Hzc : z = x0 + G - 1 \/ z = x0 + G) by (unfold x_split in *; lia).
      destruct Hzc as [-> | ->]; [rewrite Tm127 | rewrite T027]; unfold sc1, tp1; simpl;
        destruct (Z.eqb_spec _ _); try lia; destruct (Z.leb_spec _ _); try lia;
        destruct (Z.leb_spec _ _); try lia; destruct (Z.leb_spec _ _); try lia; reflexivity.
    - rewrite Tr_g20 by (unfold hi1 in *; lia). unfold sc1, tp1. simpl.
      destruct (Z.eqb_spec z (x0 - Z.of_N L_left - 1)); [lia|].
      destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
      destruct (Z.leb_spec z (x0 + 2 * G - 29)); [reflexivity|].
      destruct (Z.leb_spec z (x0 + G - 2)); [lia | reflexivity]. }
  assert (Hc_sc1 : forall z, lo1 <= z <= x_split -> c27.(tape) z = sc1.(stape) z).
  { intros z Hz. unfold sc1, tp1. simpl.
    destruct (Z.eq_dec z (x0 - Z.of_N L_left - 1)) as [-> | Hneq].
    - rewrite Z.eqb_refl. exact Tanc27.
    - destruct (Z.eqb_spec z (x0 - Z.of_N L_left - 1)); [lia|].
      destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|unfold lo1 in *; lia].
      destruct (Z.le_gt_cases z (x0 + 2 * G - 29)) as [Hle | Hgt].
      + destruct (Z.leb_spec z (x0 + 2 * G - 29)); [|lia]. apply Ttr27; lia.
      + destruct (Z.leb_spec z (x0 + 2 * G - 29)); [lia|].
        destruct (Z.leb_spec z (x0 + G - 2)); [apply Tfl27; unfold x_split in *; lia | unfold x_split in *; lia]. }
  destruct (run_N_decouple_deferred ag1 ag2 lo1 x_split hi1 lo2 (9 * q_sync) (9 * 20) c27 sc1 sc2
              ltac:(unfold lo1, x_split; lia) ltac:(unfold x_split, hi1; lia) ltac:(unfold hi1, lo2; lia)
              Hk_split_le Hrk1 Hrn1 Hrn2 Hrk2 Hmid_g
              P27 S271 Hc_sc1 P272 S272 (fun z _ => eq_refl))
    as [Hnc_dec [Dp1 [Ds1 [Dt1 [Dp2 [Ds2 [Dt2 Dout]]]]]]].
  assert (Hs1_end : (srun_N ag1 (9 * q_sync) sc1).(spos) = hi1 /\
                    (srun_N ag1 (9 * q_sync) sc1).(sstate) = StA /\
                    (srun_N ag1 (9 * q_sync) sc1).(stape) (x0 - Z.of_N L_left - 1) = S2 /\
                    (forall z, x0 - Z.of_N L_left <= z < hi1 -> (srun_N ag1 (9 * q_sync) sc1).(stape) z = S1)).
  { rewrite <- Hsync, <- Hm_sum.
    replace (m_sw + 1 + T_fill_3 m_fl + m_wk)%N with (m_wk + (T_fill_3 m_fl + (1 + m_sw)))%N by lia.
    rewrite !srun_N_add. change (srun_N ag1 1) with (sstep ag1). fold sc1_sw sc1_anc sc1_fl.
    repeat split.
    - rewrite P_wk. unfold hi1, m_wk. lia.
    - exact S_wk.
    - rewrite T_wk. exact Fl_m1.
    - intros z Hz. rewrite T_wk.
      destruct (Z.lt_ge_cases z (x0 + G - 1)) as [Hlt | Hge]; [apply T_fl; unfold m_fl; lia|].
      rewrite Out_fl by (unfold m_fl; lia). rewrite Ao_sw by (unfold m_fl; lia).
      rewrite Out_sw by (unfold m_sw, m_fl; lia). unfold sc1, tp1. simpl.
      destruct (Z.eqb_spec z (x0 - Z.of_N L_left - 1)); [lia|].
      destruct (Z.leb_spec (x0 - Z.of_N L_left) z); [|lia].
      destruct (Z.leb_spec z (x0 + 2 * G - 29)); [reflexivity|].
      destruct (Z.leb_spec z (x0 + G - 2)); [lia | reflexivity]. }
  destruct Hs1_end as [E1p [E1s [E1anc E1t]]].
  set (c_sync := run_N ag1 ag2 (9 * q_sync) c27) in *.
  assert (Hinv_sync : round_inv (2 + Z.of_N q_sync - Z.of_N dt) (L_left + Z.to_N G + 1 + dt)
                        (x0 + G + 1 + Z.of_N dt) c_sync).
  { unfold round_inv. rewrite Dp1, Ds1, Dp2, Ds2, E1p, E1s, P_g, S_g.
    replace (x0 + G + 3 + Z.of_N q_sync) with (x0 + G + 1 + Z.of_N dt + (2 + Z.of_N q_sync - Z.of_N dt)) by lia.
    repeat split; try lia; auto.
    - intros z Hz. rewrite Dout by (unfold lo1; lia). apply Tlt27. lia.
    - replace (x0 + G + 1 + Z.of_N dt - Z.of_N (L_left + Z.to_N G + 1 + dt) - 1)
        with (x0 - Z.of_N L_left - 1) by lia.
      rewrite Dt1 by (unfold lo1, hi1; lia). exact E1anc.
    - intros z Hz.
      destruct (Z.le_gt_cases z hi1) as [Hle | Hgt].
      + destruct (Z.eq_dec z hi1) as [-> | Hneq].
        * rewrite Dt1 by (unfold lo1, hi1; lia).
          rewrite <- Hsync, <- Hm_sum.
          replace (m_sw + 1 + T_fill_3 m_fl + m_wk)%N with (m_wk + (T_fill_3 m_fl + (1 + m_sw)))%N by lia.
          rewrite !srun_N_add. change (srun_N ag1 1) with (sstep ag1). fold sc1_sw sc1_anc sc1_fl.
          rewrite T_wk, Out_fl by (unfold hi1, m_fl; lia).
          rewrite Ao_sw by (unfold hi1, m_fl; lia).
          rewrite Out_sw by (unfold hi1, m_sw; lia).
          unfold sc1, tp1. simpl.
          destruct (Z.eqb_spec hi1 (x0 - Z.of_N L_left - 1)); [unfold hi1 in *; lia|].
          destruct (Z.leb_spec (x0 - Z.of_N L_left) hi1); [|unfold hi1 in *; lia].
          destruct (Z.leb_spec hi1 (x0 + 2 * G - 29)); [reflexivity|].
          destruct (Z.leb_spec hi1 (x0 + G - 2)); [unfold hi1 in *; lia | reflexivity].
        * rewrite Dt1 by (unfold lo1, hi1; lia). apply E1t. unfold hi1 in *. lia.
      + rewrite Dt2 by exact Hgt. apply Tr_g. unfold hi1 in *. lia.
    - replace (x0 + G + 1 + Z.of_N dt + (2 + Z.of_N q_sync - Z.of_N dt) - 2) with (x0 + G + 3 + Z.of_N q_sync - 2) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - replace (x0 + G + 1 + Z.of_N dt + (2 + Z.of_N q_sync - Z.of_N dt) - 1) with (x0 + G + 3 + Z.of_N q_sync - 1) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - replace (x0 + G + 1 + Z.of_N dt + (2 + Z.of_N q_sync - Z.of_N dt)) with (x0 + G + 3 + Z.of_N q_sync) by lia.
      rewrite Dt2 by (unfold hi1; lia). apply Pat_g.
    - intros z Hz. rewrite Dt2 by (unfold hi1; lia). apply Hz_g. lia. }
  destruct (round_chase k_close (2 + Z.of_N q_sync - Z.of_N dt) (L_left + Z.to_N G + 1 + dt)
              (x0 + G + 1 + Z.of_N dt) c_sync ltac:(lia) Hinv_sync) as [Hnc_ch Hinv_end].
  assert (HT_eq : T_round = (9 * k_close + (9 * q_sync + 27))%N) by (unfold T_round; lia).
  rewrite HT_eq.
  split.
  - assert (Hnc_27_dec : forall k, (k < 9 * q_sync + 27)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2))
      by (eapply no_coll_add; [exact Hnc27 | fold c27; exact Hnc_dec]).
    eapply no_coll_add; [exact Hnc_27_dec | rewrite run_N_add; fold c27 c_sync; exact Hnc_ch].
  - rewrite !run_N_add. fold c27 c_sync. rewrite Hgap in Hinv_end. exact Hinv_end.
Qed.

(** * 9. Modular Ternary Exponentiation & 8-Round Tower *)

Fixpoint pow_mod_pos (b : N) (p : positive) (m : N) : N :=
  match p with
  | xH => b mod m
  | xO q => let r := pow_mod_pos b q m in (r * r) mod m
  | xI q => let r := pow_mod_pos b q m in (b * ((r * r) mod m)) mod m
  end.

Definition pow3_mod (e m : N) : N :=
  match e with 0%N => 1 mod m | Npos p => pow_mod_pos 3 p m end.

Lemma pow_mod_pos_correct : forall b p m, (0 < m)%N -> pow_mod_pos b p m = (b ^ Npos p) mod m.
Proof.
  intros b p m Hm. induction p; simpl.
  - change (Npos p~1) with (1 + 2 * Npos p)%N.
    rewrite N.pow_add_r, N.pow_1_r, N.pow_mul_r.
    change ((b ^ Npos p) ^ 2)%N with ((b ^ Npos p) * (b ^ Npos p) * 1)%N.
    rewrite N.mul_1_r, IHp, N.mul_mod_idemp_r by lia.
    rewrite N.mul_mod by lia. rewrite N.mul_mod_idemp_r by lia. reflexivity.
  - change (Npos p~0) with (2 * Npos p)%N. rewrite N.pow_mul_r.
    change ((b ^ Npos p) ^ 2)%N with ((b ^ Npos p) * (b ^ Npos p) * 1)%N.
    rewrite N.mul_1_r, IHp, N.mul_mod by lia. reflexivity.
  - rewrite N.pow_1_r. reflexivity.
Qed.

Lemma pow3_mod_correct : forall e m, (0 < m)%N -> pow3_mod e m = (3 ^ e) mod m.
Proof.
  intros e m Hm. destruct e; [rewrite N.pow_0_r; reflexivity | apply pow_mod_pos_correct; exact Hm].
Qed.

Lemma pow3_mul_lam_mod : forall q lam Q_good,
  (0 < Q_good)%N -> (pow3_mod lam Q_good = 1%N) ->
  ((3 ^ (lam * q)) mod Q_good = 1%N).
Proof.
  intros q lam Q_good HQ Hlam. rewrite pow3_mod_correct in Hlam by exact HQ. rewrite N.pow_mul_r.
  induction q using N.peano_ind.
  - rewrite N.pow_0_r. destruct (N.eq_dec Q_good 1) as [-> | HQ1];
      [exfalso; rewrite N.mod_1_r in Hlam; discriminate | apply N.mod_1_l; lia].
  - rewrite N.pow_succ_r', <- N.mul_mod by lia. rewrite Hlam, IHq, N.mul_1_l.
    destruct (N.eq_dec Q_good 1) as [-> | HQ1];
      [exfalso; rewrite N.mod_1_r in Hlam; discriminate | apply N.mod_1_l; lia].
Qed.

Lemma pow3_mod_period : forall lam Q_good k,
  (2 <= k)%N -> (2 <= lam)%N -> (1 < Q_good)%N -> (pow3_mod lam Q_good = 1%N) ->
  let k' := if (k <? lam)%N then k else ((k mod lam) + lam)%N in
  ((3 ^ k) mod (9 * Q_good) = pow3_mod k' (9 * Q_good)).
Proof.
  intros lam Q_good k Hk Hlam HQg Hpow k'.
  assert (Hm_pos : (0 < 9 * Q_good)%N) by lia.
  rewrite pow3_mod_correct by exact Hm_pos.
  unfold k'. destruct (N.ltb_spec k lam) as [Hlt | Hge]; [reflexivity|].
  set (q := (k / lam)%N).
  assert (Hq_ge : (1 <= q)%N) by (unfold q; apply N.div_str_pos; lia).
  assert (Hk_eq : k = ((k mod lam) + lam + lam * (q - 1))%N)
    by (pose proof (N.div_mod k lam ltac:(lia)) as Hdm; fold q in Hdm; lia).
  set (kr := ((k mod lam) + lam)%N).
  assert (Hkr_ge : (2 <= kr)%N) by (unfold kr; lia).
  rewrite Hk_eq, N.pow_add_r. fold kr.
  assert (Hqb_div : exists u, (3 ^ kr = u * 9)%N).
  { exists (3 ^ (kr - 2))%N. replace kr with (2 + (kr - 2))%N by lia.
    rewrite N.pow_add_r. change (3 ^ 2)%N with 9%N. lia. }
  assert (Hqg_div : exists v, (3 ^ (lam * (q - 1)) = v * Q_good + 1)%N).
  { pose proof (pow3_mul_lam_mod (q - 1) lam Q_good ltac:(lia) Hpow) as Hmod.
    pose proof (N.div_mod (3 ^ (lam * (q - 1))) Q_good ltac:(lia)) as Hdm.
    exists (3 ^ (lam * (q - 1)) / Q_good)%N. rewrite Hmod in Hdm. lia. }
  destruct Hqb_div as [u Hu]. destruct Hqg_div as [v Hv].
  rewrite Hv, N.mul_add_distr_l, N.mul_1_r, Hu at 1.
  replace (u * 9 * (v * Q_good) + 3 ^ kr)%N with (3 ^ kr + (u * v) * (9 * Q_good))%N by lia.
  rewrite N.Div0.mod_add. reflexivity.
Qed.

Lemma check_lam3_periods :
  (pow3_mod 2 8 =? 1)%N && (pow3_mod 4 16 =? 1)%N && (pow3_mod 8 32 =? 1)%N &&
  (pow3_mod 16 64 =? 1)%N && (pow3_mod 32 128 =? 1)%N && (pow3_mod 64 256 =? 1)%N = true.
Proof. vm_compute. reflexivity. Qed.

Lemma round_step_mod :
  forall G_z L_left x0 c lam Q_next L_mod k_eff p_mod T_mod T_adj dt q_mod k_mod G_next L_next_mod,
  (G_z = 8 \/ G_z = 10) ->
  (86 <= L_left)%N ->
  (lam <= L_left + Z.to_N G_z + 1)%N ->
  (Q_next <= 64)%N ->
  round_inv G_z L_left x0 c ->
  (2 <= lam)%N ->
  (pow3_mod lam (8 * Q_next) = 1%N) ->
  (L_left mod lam = L_mod)%N ->
  (k_eff = ((L_mod + Z.to_N G_z + 1) mod lam) + lam)%N ->
  (pow3_mod k_eff (72 * Q_next) = p_mod)%N ->
  (T_mod = (p_mod + Z.to_N G_z - 2) mod (72 * Q_next))%N ->
  (T_adj = if (T_mod <? 27)%N then (T_mod + 72 * Q_next)%N else T_mod) ->
  (dt < 9)%N ->
  (T_adj - 27 + dt = 9 * q_mod)%N ->
  (2 + Z.of_N q_mod - Z.of_N dt - 8 * Z.of_N k_mod = G_next) ->
  8 <= G_next < 16 ->
  (L_next_mod = (L_left + Z.to_N G_z + 1 + dt + 9 * k_mod) mod Q_next)%N ->
  exists T_round L_left_next x_next,
    (T_round >= 3 ^ (L_left + Z.to_N G_z + 1))%N /\
    (L_left_next >= 3 ^ (L_left + Z.to_N G_z - 2))%N /\
    (L_left_next mod Q_next = L_next_mod)%N /\
    (forall k, (k < T_round)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
    round_inv G_next L_left_next x_next (run_N ag1 ag2 T_round c).
Proof.
  intros G_z L_left x0 c lam Q_next L_mod k_eff p_mod T_mod T_adj dt q_mod k_mod G_next L_next_mod
         HG HL Hlam_le HQ_le Hinv Hlam Hpow_lam HLmod Hkeff Hpmod HTmod HTadj Hdt Hqmod Hgap HGnext HLnext.
  assert (HG_pos : G_z = 8 \/ G_z = 10) by exact HG.
  set (exp_n := (L_left + Z.to_N G_z + 1)%N).
  assert (Hexp_ge : (exp_n >= 90)%N) by (unfold exp_n; lia).
  assert (Hexp_mod : (exp_n mod lam = (L_mod + Z.to_N G_z + 1) mod lam)%N).
  { unfold exp_n. rewrite <- HLmod. rewrite <- N.add_mod_idemp_l by lia.
    replace (L_left + (Z.to_N G_z + 1))%N with (L_left + Z.to_N G_z + 1)%N by lia.
    replace (L_left mod lam + Z.to_N G_z + 1)%N with (L_left mod lam + (Z.to_N G_z + 1))%N by lia.
    rewrite N.add_mod_idemp_l by lia. reflexivity. }
  assert (Hpow_exp : ((3 ^ exp_n) mod (72 * Q_next) = p_mod)%N).
  { pose proof (pow3_mod_period lam (8 * Q_next) exp_n ltac:(lia) Hlam ltac:(lia) Hpow_lam) as Hper.
    replace (9 * (8 * Q_next))%N with (72 * Q_next)%N in Hper by lia.
    destruct (N.ltb_spec exp_n lam); [unfold exp_n in *; lia|].
    rewrite Hexp_mod, <- Hkeff in Hper. rewrite Hper. exact Hpmod. }
  set (T_exit := (3 ^ exp_n + Z.to_N G_z - 2)%N).
  assert (HT_mod_eq : (T_exit mod (72 * Q_next) = T_mod)%N).
  { unfold T_exit. replace (3 ^ exp_n + Z.to_N G_z - 2)%N with (3 ^ exp_n + (Z.to_N G_z - 2))%N by lia.
    rewrite N.add_mod, Hpow_exp by lia. rewrite <- N.add_mod by lia. exact HTmod. }
  pose proof (N.div_mod T_exit (72 * Q_next) ltac:(lia)) as Hdm. rewrite HT_mod_eq in Hdm.
  set (K := (T_exit / (72 * Q_next))%N) in *.
  assert (HK_ge : (K >= 3)%N).
  { assert (Hbig : (3 ^ exp_n >= 3 ^ 20)%N) by (apply N.pow_le_mono_r; [discriminate | lia]).
    change (3 ^ 20)%N with 3486784401%N in Hbig.
    assert (HT_big : (T_exit >= 3 * (72 * Q_next))%N) by (unfold T_exit; lia).
    unfold K. apply N.div_le_lower_bound; lia. }
  set (K' := if (T_mod <? 27)%N then (K - 1)%N else K).
  assert (HT_adj_eq : (T_exit = (72 * Q_next) * K' + T_adj)%N).
  { unfold K', T_adj. destruct (N.ltb_spec T_mod 27); lia. }
  assert (HK'_ge : (K' >= 2)%N) by (unfold K'; destruct (N.ltb_spec T_mod 27); lia).
  set (q_sync := (8 * Q_next * K' + q_mod)%N).
  set (k_close := (Q_next * K' + k_mod)%N).
  assert (Hsync_eq : (T_exit - 27 + dt = 9 * q_sync)%N) by (unfold q_sync; rewrite HT_adj_eq; lia).
  assert (Hgap_eq : 2 + Z.of_N q_sync - Z.of_N dt - 8 * Z.of_N k_close = G_next).
  { unfold q_sync, k_close. rewrite !N2Z.inj_add, !N2Z.inj_mul. change (Z.of_N 8) with 8. lia. }
  destruct (round_bounce G_z L_left x0 c dt q_sync k_close G_next HG ltac:(lia) Hdt ltac:(unfold q_sync; lia)
              Hinv Hsync_eq Hgap_eq HGnext) as [Hnc Hinv_next].
  set (T_round := (T_exit + dt + 9 * k_close)%N) in *.
  set (L_left_next := (L_left + Z.to_N G_z + 1 + dt + 9 * k_close)%N).
  set (x_next := x0 + G_z + 1 + Z.of_N dt + 9 * Z.of_N k_close).
  exists T_round, L_left_next, x_next.
  repeat split.
  - unfold T_round, T_exit, exp_n. lia.
  - unfold L_left_next, k_close.
    assert (Hexp3 : exp_n = (3 + (exp_n - 3))%N) by lia.
    assert (Hpow_split : (3 ^ exp_n = 27 * 3 ^ (exp_n - 3))%N)
      by (rewrite Hexp3 at 1; rewrite N.pow_add_r; change (3 ^ 3)%N with 27%N; lia).
    assert (Hbig : (3 ^ exp_n >= 3 ^ 20)%N) by (apply N.pow_le_mono_r; [discriminate | lia]).
    change (3 ^ 20)%N with 3486784401%N in Hbig.
    assert (HTmod_lt : (T_mod < 72 * Q_next)%N) by (rewrite HTmod; apply N.mod_lt; lia).
    assert (HTadj_lt : (T_adj < 2 * (72 * Q_next))%N) by (unfold T_adj; destruct (N.ltb_spec T_mod 27); lia).
    assert (HK_mul : (8 * (9 * Q_next * K') = T_exit - T_adj)%N)
      by (replace (8 * (9 * Q_next * K'))%N with (72 * Q_next * K')%N by lia; lia).
    assert (H8 : (8 * 3 ^ (exp_n - 3) <= T_exit - T_adj)%N) by (unfold T_exit; rewrite Hpow_split; lia).
    replace (L_left + Z.to_N G_z - 2)%N with (exp_n - 3)%N by (unfold exp_n; lia).
    lia.
  - unfold L_left_next, k_close.
    replace (L_left + Z.to_N G_z + 1 + dt + 9 * (Q_next * K' + k_mod))%N
      with ((L_left + Z.to_N G_z + 1 + dt + 9 * k_mod) + (9 * K') * Q_next)%N by lia.
    rewrite N.Div0.mod_add. symmetry; exact HLnext.
  - exact Hnc.
  - exact Hinv_next.
Qed.

Lemma round2_ok :
  exists T2 L3 x3,
    (T2 >= 3 ^ 97)%N /\ (L3 >= 3 ^ 94)%N /\ (L3 mod 64 = 38)%N /\
    (forall k, (k < T2)%N -> (run_N ag1 ag2 k (run_N ag1 ag2 844 c0)).(pos1) <>
                             (run_N ag1 ag2 k (run_N ag1 ag2 844 c0)).(pos2)) /\
    round_inv 10 L3 x3 (run_N ag1 ag2 T2 (run_N ag1 ag2 844 c0)).
Proof.
  destruct prefix_844_ok as [Hinv2 _].
  assert (Hpow : pow3_mod 97 4608 = 2691%N) by (vm_compute; reflexivity).
  rewrite pow3_mod_correct in Hpow by lia.
  pose proof (N.div_mod (3 ^ 97) 4608 ltac:(lia)) as Hdm. rewrite Hpow in Hdm.
  set (K := (3 ^ 97 / 4608)%N) in *.
  set (T_exit := (3 ^ 97 + 8)%N).
  assert (HTx : (T_exit = 4608 * K + 2699)%N) by (unfold T_exit; lia).
  set (q_sync := (512 * K + 297)%N).
  set (k_close := (64 * K + 36)%N).
  assert (Hsync : (T_exit - 27 + 1 = 9 * q_sync)%N) by (unfold q_sync; rewrite HTx; lia).
  assert (Hgap : 2 + Z.of_N q_sync - Z.of_N 1 - 8 * Z.of_N k_close = 10).
  { unfold q_sync, k_close. rewrite !N2Z.inj_add, !N2Z.inj_mul.
    change (Z.of_N 8) with 8. change (Z.of_N 512) with 512. change (Z.of_N 64) with 64.
    change (Z.of_N 297) with 297. change (Z.of_N 36) with 36. change (Z.of_N 1) with 1. lia. }
  destruct (round_bounce 10 86 86 (run_N ag1 ag2 844 c0) 1 q_sync k_close 10
              ltac:(auto) ltac:(lia) ltac:(lia) ltac:(unfold q_sync; lia) Hinv2 Hsync Hgap ltac:(lia)) as [Hnc Hinv3].
  set (T2 := (T_exit + 1 + 9 * k_close)%N) in *.
  set (L3 := (86 + Z.to_N 10 + 1 + 1 + 9 * k_close)%N).
  set (x3 := 86 + 10 + 1 + Z.of_N 1 + 9 * Z.of_N k_close).
  exists T2, L3, x3. repeat split.
  - unfold T2, T_exit. lia.
  - unfold L3, k_close.
    assert (Hpow_split : (3 ^ 97 = 27 * 3 ^ 94)%N) by (replace 97%N with (3 + 94)%N by lia; rewrite N.pow_add_r; change (3 ^ 3)%N with 27%N; lia).
    assert (HK_mul : (8 * (9 * 64 * K) = T_exit - 2699)%N) by (replace (8 * (9 * 64 * K))%N with (4608 * K)%N by lia; lia).
    assert (H94 : (3 ^ 94 >= 2699)%N) by (vm_compute; lia).
    assert (H8 : (8 * 3 ^ 94 <= T_exit - 2699)%N) by (unfold T_exit; rewrite Hpow_split; lia).
    lia.
  - unfold L3, k_close.
    replace (86 + Z.to_N 10 + 1 + 1 + 9 * (64 * K + 36))%N with (422 + (9 * K) * 64)%N by lia.
    rewrite N.Div0.mod_add. vm_compute. reflexivity.
  - exact Hnc.
  - exact Hinv3.
Qed.

Lemma final_halt_13 : forall L_left x0 c,
  (10 <= L_left)%N ->
  round_inv 14 L_left x0 c ->
  (forall k, (k < 13)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  (run_N ag1 ag2 13 c).(pos1) = (run_N ag1 ag2 13 c).(pos2).
Proof.
  intros L_left x0 c HL Hinv.
  set (fc_g14 := {| fpos1 := 0; fpos2 := 14; fstate1 := StA; fstate2 := StB;
                    ftape := bt_set (z_to_pos 14) S1 (bt_set (z_to_pos 13) S1 (bt_set (z_to_pos 12) S2 (bt_fill_range (-10) 22 S1 BEmpty))) |}).
  assert (H13_ok :
    let st := N.iter 13 (fast_step_chk_range (-10) 16) (fc_g14, true) in
    snd st = true /\ (fst st).(fpos1) = (fst st).(fpos2)).
  { vm_compute. split; reflexivity. }
  destruct H13_ok as [Hsnd Heq13]. rewrite fast_step_chk_range_fst in Heq13.
  destruct (fast_step_chk_range_sound 13 (-10) 16 fc_g14 true Hsnd) as [_ Hchk].
  assert (Hrng_tape : forall z, x0 - 10 <= z <= x0 + 16 ->
    c.(tape) z = (shift_cfg x0 (fc_to_cfg fc_g14)).(tape) z).
  { intros z Hz. unfold shift_cfg, shift_tape, fc_to_cfg, bt_interp, fc_g14. simpl.
    destruct Hinv as [_ [_ [_ [_ [_ [_ [Htr [Hm2 [Hm1 [H0 Hgt]]]]]]]]]]].
    destruct (Z.eq_dec (z - x0) 14) as [->|]; [rewrite bt_get_set_same; replace z with (x0 + 14) by lia; exact H0|].
    rewrite bt_get_set_diff by (intro H; apply z_to_pos_inj in H; congruence).
    destruct (Z.eq_dec (z - x0) 13) as [->|]; [rewrite bt_get_set_same; replace z with (x0 + 13) by lia; exact Hm1|].
    rewrite bt_get_set_diff by (intro H; apply z_to_pos_inj in H; congruence).
    destruct (Z.eq_dec (z - x0) 12) as [->|]; [rewrite bt_get_set_same; replace z with (x0 + 12) by lia; exact Hm2|].
    rewrite bt_get_set_diff by (intro H; apply z_to_pos_inj in H; congruence).
    destruct (Z.lt_ge_cases (z - x0) 12) as [Hlt | Hge]; [rewrite bt_fill_range_in by lia; apply Htr; lia|].
    rewrite bt_fill_range_out by lia. rewrite bt_get_empty. apply Hgt. lia. }
  destruct Hinv as [Cp1 [Cs1 [Cp2 [Cs2 _]]]].
  assert (Hrng_shift : forall k, (k < 13)%N ->
    x0 - 10 <= (run_N ag1 ag2 k (shift_cfg x0 (fc_to_cfg fc_g14))).(pos1) <= x0 + 16 /\
    x0 - 10 <= (run_N ag1 ag2 k (shift_cfg x0 (fc_to_cfg fc_g14))).(pos2) <= x0 + 16).
  { intros k Hk. destruct (run_N_shift ag1 ag2 k x0 (fc_to_cfg fc_g14)) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl. pose proof (fast_run_sound k fc_g14) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl. destruct (Hchk k Hk) as [_ [Ha Hb]]. lia. }
  assert (Hrng_c : forall k, (k < 13)%N ->
    x0 - 10 <= (run_N ag1 ag2 k c).(pos1) <= x0 + 16 /\
    x0 - 10 <= (run_N ag1 ag2 k c).(pos2) <= x0 + 16).
  { intros k Hk.
    destruct (run_N_agree_range ag1 ag2 (x0 - 10) (x0 + 16) k (shift_cfg x0 (fc_to_cfg fc_g14)) c
                (fun j Hj => Hrng_shift j ltac:(lia)) (eq_sym Cp1) (eq_sym Cp2) (eq_sym Cs1) (eq_sym Cs2)
                (fun z Hz => eq_sym (Hrng_tape z Hz))) as [Kp1 [Kp2 _]].
    rewrite <- Kp1, <- Kp2. apply Hrng_shift; exact Hk. }
  split.
  - intros k Hk.
    destruct (run_N_agree_range ag1 ag2 (x0 - 10) (x0 + 16) k c (shift_cfg x0 (fc_to_cfg fc_g14))
                (fun j Hj => Hrng_c j ltac:(lia)) Cp1 Cp2 Cs1 Cs2 Hrng_tape) as [Kp1 [Kp2 _]].
    rewrite Kp1, Kp2. destruct (run_N_shift ag1 ag2 k x0 (fc_to_cfg fc_g14)) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl. pose proof (fast_run_sound k fc_g14) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl. destruct (Hchk k Hk) as [Hneq _]. lia.
  - destruct (run_N_agree_range ag1 ag2 (x0 - 10) (x0 + 16) 13 c (shift_cfg x0 (fc_to_cfg fc_g14))
                Hrng_c Cp1 Cp2 Cs1 Cs2 Hrng_tape) as [Kp1 [Kp2 _]].
    rewrite Kp1, Kp2. destruct (run_N_shift ag1 ag2 13 x0 (fc_to_cfg fc_g14)) as [Sp1 [Sp2 _]].
    rewrite Sp1, Sp2. simpl. pose proof (fast_run_sound 13 fc_g14) as [Fp1 [Fp2 _]].
    rewrite <- Fp1, <- Fp2. simpl. lia.
Qed.

Lemma n_pow3_ge_add : forall n, (3 ^ n >= n + 1)%N.
Proof.
  intro n. induction n using N.peano_ind; [simpl; lia | rewrite N.pow_succ_r' by lia; lia].
Qed.

Theorem cet23_r8_halts :
  exists T : N,
    halts_at_exact ag1 ag2 c0 T /\
    (T > 3 ^ (3 ^ (3 ^ (3 ^ (3 ^ (3 ^ (3 ^ 90)))))))%N.
Proof.
  pose proof check_lam3_periods as Hlam. rewrite !andb_true_iff in Hlam.
  destruct Hlam as [[[[[Hp2 Hp4] Hp8] Hp16] Hp32] Hp64].
  rewrite N.eqb_eq in Hp2, Hp4, Hp8, Hp16, Hp32, Hp64.
  destruct prefix_844_ok as [_ Hnc1].
  destruct round2_ok as [T2 [L3 [x3 [HT2 [HL3 [HM3 [Hnc2 Hinv3]]]]]]].
  assert (HL3_ge : (L3 >= 3 ^ 90)%N) by (assert (H : (3 ^ 94 >= 3 ^ 90)%N) by (apply N.pow_le_mono_r; lia); lia).
  assert (H3_90_big : (3 ^ 90 >= 86)%N) by (vm_compute; lia).
  (* Round 3: G=10, lam=64, Q_next=32 *)
  destruct (round_step_mod 10 L3 x3 _ 64 32 38 113 2115 2123 2123 1 233 28 10 14
              ltac:(auto) ltac:(lia) ltac:(lia) ltac:(lia) Hinv3 ltac:(lia) Hp64 HM3
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity))
    as [T3 [L4 [x4 [HT3 [HL4 [HM4 [Hnc3 Hinv4]]]]]]].
  assert (HL4_ge : (L4 >= 3 ^ (3 ^ 90))%N)
    by (assert (H : (3 ^ (L3 + Z.to_N 10 - 2) >= 3 ^ (3 ^ 90))%N) by (apply N.pow_le_mono_r; [discriminate | lia]); lia).
  assert (HL4_lam : (32 <= L4 + Z.to_N 10 + 1)%N) by (pose proof (n_pow3_ge_add (3 ^ 90)); lia).
  (* Round 4: G=10, lam=32, Q_next=16 *)
  destruct (round_step_mod 10 L4 x4 _ 32 16 14 57 675 683 683 1 73 8 10 2
              ltac:(auto) ltac:(lia) HL4_lam ltac:(lia) Hinv4 ltac:(lia) Hp32 HM4
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity))
    as [T4 [L5 [x5 [HT4 [HL5 [HM5 [Hnc4 Hinv5]]]]]]].
  assert (HL5_ge : (L5 >= 3 ^ (3 ^ (3 ^ 90)))%N)
    by (assert (H : (3 ^ (L4 + Z.to_N 10 - 2) >= 3 ^ (3 ^ (3 ^ 90)))%N) by (apply N.pow_le_mono_r; [discriminate | lia]); lia).
  assert (HL5_lam : (16 <= L5 + Z.to_N 10 + 1)%N)
    by (pose proof (n_pow3_ge_add (3 ^ (3 ^ 90))); pose proof (n_pow3_ge_add (3 ^ 90)); lia).
  (* Round 5: G=10, lam=16, Q_next=8 *)
  destruct (round_step_mod 10 L5 x5 _ 16 8 2 29 531 539 539 1 57 6 10 4
              ltac:(auto) ltac:(lia) HL5_lam ltac:(lia) Hinv5 ltac:(lia) Hp16 HM5
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity))
    as [T5 [L6 [x6 [HT5 [HL6 [HM6 [Hnc5 Hinv6]]]]]]].
  assert (HL6_ge : (L6 >= 3 ^ (3 ^ (3 ^ (3 ^ 90))))%N)
    by (assert (H : (3 ^ (L5 + Z.to_N 10 - 2) >= 3 ^ (3 ^ (3 ^ (3 ^ 90))))%N) by (apply N.pow_le_mono_r; [discriminate | lia]); lia).
  assert (HL6_lam : (8 <= L6 + Z.to_N 10 + 1)%N)
    by (pose proof (n_pow3_ge_add (3 ^ (3 ^ (3 ^ 90)))); pose proof (n_pow3_ge_add (3 ^ (3 ^ 90))); pose proof (n_pow3_ge_add (3 ^ 90)); lia).
  (* Round 6: G=10, lam=8, Q_next=4 *)
  destruct (round_step_mod 10 L6 x6 _ 8 4 4 15 171 179 179 1 17 1 10 1
              ltac:(auto) ltac:(lia) HL6_lam ltac:(lia) Hinv6 ltac:(lia) Hp8 HM6
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity))
    as [T6 [L7 [x7 [HT6 [HL7 [HM7 [Hnc6 Hinv7]]]]]]].
  assert (HL7_ge : (L7 >= 3 ^ (3 ^ (3 ^ (3 ^ (3 ^ 90)))))%N)
    by (assert (H : (3 ^ (L6 + Z.to_N 10 - 2) >= 3 ^ (3 ^ (3 ^ (3 ^ (3 ^ 90)))))%N) by (apply N.pow_le_mono_r; [discriminate | lia]); lia).
  assert (HL7_lam : (4 <= L7 + Z.to_N 10 + 1)%N)
    by (pose proof (n_pow3_ge_add (3 ^ (3 ^ (3 ^ (3 ^ 90))))); pose proof (n_pow3_ge_add (3 ^ (3 ^ (3 ^ 90)))); pose proof (n_pow3_ge_add (3 ^ (3 ^ 90))); pose proof (n_pow3_ge_add (3 ^ 90)); lia).
  (* Round 7: G=10, lam=4, Q_next=2 *)
  destruct (round_step_mod 10 L7 x7 _ 4 2 1 4 81 89 89 1 7 0 8 1
              ltac:(auto) ltac:(lia) HL7_lam ltac:(lia) Hinv7 ltac:(lia) Hp4 HM7
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity))
    as [T7 [L8 [x8 [HT7 [HL8 [HM8 [Hnc7 Hinv8]]]]]]].
  assert (HL8_ge : (L8 >= 3 ^ (3 ^ (3 ^ (3 ^ (3 ^ (3 ^ 90))))))%N)
    by (assert (H : (3 ^ (L7 + Z.to_N 10 - 2) >= 3 ^ (3 ^ (3 ^ (3 ^ (3 ^ (3 ^ 90))))))%N) by (apply N.pow_le_mono_r; [discriminate | lia]); lia).
  assert (HL8_lam : (2 <= L8 + Z.to_N 8 + 1)%N)
    by (pose proof (n_pow3_ge_add (3 ^ (3 ^ (3 ^ (3 ^ (3 ^ 90)))))); pose proof (n_pow3_ge_add (3 ^ (3 ^ (3 ^ (3 ^ 90))))); pose proof (n_pow3_ge_add (3 ^ (3 ^ (3 ^ 90)))); pose proof (n_pow3_ge_add (3 ^ (3 ^ 90))); pose proof (n_pow3_ge_add (3 ^ 90)); lia).
  (* Round 8: G=8, lam=2, Q_next=1 *)
  destruct (round_step_mod 8 L8 x8 _ 2 1 1 2 9 15 87 3 7 0 14 0
              ltac:(auto) ltac:(lia) HL8_lam ltac:(lia) Hinv8 ltac:(lia) Hp2 HM8
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity))
    as [T8 [L9 [x9 [HT8 [HL9 [_ [Hnc8 Hinv9]]]]]]].
  destruct (final_halt_13 L9 x9 _ ltac:(lia) Hinv9) as [Hnc9 Hcoll9].
  set (T_tot := (13 + (T8 + (T7 + (T6 + (T5 + (T4 + (T3 + (T2 + 844))))))))%N).
  exists T_tot. split.
  - unfold halts_at_exact, collides_at. split.
    + unfold T_tot. rewrite !run_N_add. exact Hcoll9.
    + intros t Ht.
      assert (H12 : forall k, (k < T2 + 844)%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact Hnc1 | exact Hnc2]).
      assert (H13 : forall k, (k < T3 + (T2 + 844))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H12 | rewrite run_N_add; exact Hnc3]).
      assert (H14 : forall k, (k < T4 + (T3 + (T2 + 844)))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H13 | rewrite !run_N_add; exact Hnc4]).
      assert (H15 : forall k, (k < T5 + (T4 + (T3 + (T2 + 844))))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H14 | rewrite !run_N_add; exact Hnc5]).
      assert (H16 : forall k, (k < T6 + (T5 + (T4 + (T3 + (T2 + 844)))))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H15 | rewrite !run_N_add; exact Hnc6]).
      assert (H17 : forall k, (k < T7 + (T6 + (T5 + (T4 + (T3 + (T2 + 844))))))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H16 | rewrite !run_N_add; exact Hnc7]).
      assert (H18 : forall k, (k < T8 + (T7 + (T6 + (T5 + (T4 + (T3 + (T2 + 844)))))))%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
        by (eapply no_coll_add; [exact H17 | rewrite !run_N_add; exact Hnc8]).
      eapply no_coll_add; [exact H18 | rewrite !run_N_add; exact Hnc9 | exact Ht].
  - assert (Hmono8 : (3 ^ (L8 + Z.to_N 8 + 1) >= 3 ^ (3 ^ (3 ^ (3 ^ (3 ^ (3 ^ (3 ^ 90)))))))%N)
      by (apply N.pow_le_mono_r; [discriminate | lia]).
    unfold T_tot. lia.
Qed.

Print Assumptions cet23_r8_halts.
