(**
  Formal Machine-Checked Proof of Normal Halting in Rocq 9.1
  Target Machine: 0LB---_1LC1RB_0RB0LC | 0RB0LC_1RC1LB_1LB1RA
  Model: Catch-Em-Turing CET(3), 2 agents, 3 states, 2 symbols.
  Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
  Normal Halting: exact first collision pos1(T) = pos2(T).

  Proves:
  1. For ANY transition placed in the unreachable slot (StA, true) (`---`),
     the machine NEVER executes (StA, true) at any step t >= 0.
  2. The machine collides at exact step T_halt = (2^1379 - 8)/3 + 5497
     = 4397873831...56397857 (415 digits, ~4.398e414 steps).
  3. For all 0 <= t < T_halt, pos1(t) <> pos2(t) (strictly first collision).
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

(** * 2. Target Machine Definition: 0LB---_1LC1RB_0RB0LC | 0RB0LC_1RC1LB_1LB1RA *)

Definition ag1_with (undef : Transition) (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := false; move_dir := MoveL; next_state := StB |}
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
  | StA, false => {| write_sym := false; move_dir := MoveR; next_state := StB |}
  | StA, true  => {| write_sym := false; move_dir := MoveL; next_state := StC |}
  | StB, false => {| write_sym := true;  move_dir := MoveR; next_state := StC |}
  | StB, true  => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StC, false => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StC, true  => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  end.

Definition c0 : Config := {|
  pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape
|}.

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
Proof.
  intros. unfold write_tape. destruct (Z.eqb_spec x p); congruence.
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

Lemma run_N_0 : forall a1 a2 c, run_N a1 a2 0%N c = c.
Proof. reflexivity. Qed.

Lemma run_N_succ : forall a1 a2 n c,
  run_N a1 a2 (N.succ n) c = step a1 a2 (run_N a1 a2 n c).
Proof. intros. unfold run_N. apply N.iter_succ. Qed.

Lemma run_N_add : forall a1 a2 p q c,
  run_N a1 a2 (p + q) c = run_N a1 a2 p (run_N a1 a2 q c).
Proof. intros. unfold run_N. apply N.iter_add. Qed.

(** Splitting collision-freeness over two time intervals *)
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

(** * 4. Proof that (StA, true) (`---`) is Never Reached *)

Lemma ag1_leaves_A : forall undef c,
  (c.(state1) = StB \/ c.(state1) = StC) ->
  let c' := step (ag1_with undef) ag2 c in
  c'.(state1) = StB \/ c'.(state1) = StC.
Proof.
  intros undef c [H | H]; unfold step, ag1_with; rewrite H;
    destruct (c.(tape) c.(pos1)); simpl; auto.
Qed.

Lemma ag1_undef_irrelevant_BC : forall undef c,
  (c.(state1) = StB \/ c.(state1) = StC) ->
  step (ag1_with undef) ag2 c = step ag1 ag2 c.
Proof.
  intros undef c [H | H]; unfold step, ag1, ag1_with; rewrite H; reflexivity.
Qed.

Lemma run_N_undef_irrelevant : forall undef t,
  (run_N (ag1_with undef) ag2 t c0 = run_N ag1 ag2 t c0) /\
  ((t >= 1)%N ->
    (run_N ag1 ag2 t c0).(state1) = StB \/ (run_N ag1 ag2 t c0).(state1) = StC) /\
  ~ ((run_N (ag1_with undef) ag2 t c0).(state1) = StA /\
     (run_N (ag1_with undef) ag2 t c0).(tape) (run_N (ag1_with undef) ag2 t c0).(pos1) = true).
Proof.
  intros undef t. induction t using N.peano_ind.
  - rewrite !run_N_0. repeat split; [lia |].
    unfold c0, empty_tape. simpl. intros [_ H]. discriminate.
  - rewrite !run_N_succ. destruct IHt as [Heq [HBC Hnr]].
    destruct (N.eq_0_gt_0_cases t) as [Ht0 | Htgt0].
    + subst t. rewrite !run_N_0. unfold step, ag1, ag1_with, c0, empty_tape. simpl.
      repeat split; auto. intros [H _]. discriminate.
    + assert (Hbc : (run_N ag1 ag2 t c0).(state1) = StB \/ (run_N ag1 ag2 t c0).(state1) = StC).
      { apply HBC. lia. }
      assert (Hstep : step (ag1_with undef) ag2 (run_N (ag1_with undef) ag2 t c0) =
                      step ag1 ag2 (run_N ag1 ag2 t c0)).
      { rewrite Heq. apply ag1_undef_irrelevant_BC. exact Hbc. }
      pose proof (ag1_leaves_A default_undef (run_N ag1 ag2 t c0) Hbc) as Hbc'.
      change (ag1_with default_undef) with ag1 in Hbc'.
      repeat split; auto.
      intros [HA _]. rewrite Hstep in HA. destruct Hbc' as [HB | HC]; rewrite HA in *; discriminate.
Qed.

(** * 5. Fast Reflected Evaluator (BTree Tape) *)

Inductive BTree := BEmpty | BNode : bool -> BTree -> BTree -> BTree.

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

Lemma pos_z_pos : forall p, z_to_pos (pos_to_z p) = p.
Proof. destruct p; reflexivity. Qed.

Lemma z_pos_z : forall z, pos_to_z (z_to_pos z) = z.
Proof. destruct z; reflexivity. Qed.

Lemma bt_get_set_same : forall p v t, bt_get p (bt_set p v t) = v.
Proof.
  induction p; destruct t; simpl; auto.
Qed.

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

Lemma tape_eq_trans : forall t1 t2 t3, tape_eq t1 t2 -> tape_eq t2 t3 -> tape_eq t1 t3.
Proof. intros t1 t2 t3 H1 H2 z. rewrite H1. apply H2. Qed.

Lemma cfg_eq_trans : forall c1 c2 c3, cfg_eq c1 c2 -> cfg_eq c2 c3 -> cfg_eq c1 c3.
Proof.
  intros c1 c2 c3 [Hp1 Hp2 Hs1 Hs2 Htp] [Gp1 Gp2 Gs1 Gs2 Gtp].
  constructor; try congruence.
Qed.

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

(** * 6. Concrete Prefix Verification (Steps 0 .. 6872) *)

Definition fast_step_chk_ge (lo : Z) (st : FastConfig * bool) : FastConfig * bool :=
  let (fc, ok) := st in
  let fc' := fast_step fc in
  (fc', ok && negb (fc'.(fpos1) =? fc'.(fpos2))
            && (lo <=? fc'.(fpos1)) && (lo <=? fc'.(fpos2))).

Lemma fast_step_chk_ge_fst : forall n lo fc ok,
  fst (N.iter n (fast_step_chk_ge lo) (fc, ok)) = N.iter n fast_step fc.
Proof.
  intro n. induction n using N.peano_ind; intros lo fc ok.
  - reflexivity.
  - rewrite !N.iter_succ.
    destruct (N.iter n (fast_step_chk_ge lo) (fc, ok)) as [fc' ok'] eqn:E.
    simpl. assert (fc' = N.iter n fast_step fc) by (rewrite <- (IHn lo fc ok), E; reflexivity).
    subst fc'. reflexivity.
Qed.

Lemma fast_step_chk_ge_sound : forall n lo fc ok,
  snd (N.iter n (fast_step_chk_ge lo) (fc, ok)) = true ->
  ok = true /\
  forall k, (1 <= k <= n)%N ->
    let fc_k := N.iter k fast_step fc in
    fc_k.(fpos1) <> fc_k.(fpos2) /\ lo <= fc_k.(fpos1) /\ lo <= fc_k.(fpos2).
Proof.
  intro n. induction n using N.peano_ind; intros lo fc ok Hsnd.
  - simpl in Hsnd. split; [exact Hsnd | intros k Hk; lia].
  - rewrite N.iter_succ in Hsnd.
    destruct (N.iter n (fast_step_chk_ge lo) (fc, ok)) as [fc' ok'] eqn:E.
    assert (Hfc : fc' = N.iter n fast_step fc) by (rewrite <- (fast_step_chk_ge_fst n lo fc ok), E; reflexivity).
    simpl in Hsnd. rewrite !andb_true_iff in Hsnd.
    destruct Hsnd as [[[Hok' Hneq] Hlo1] Hlo2].
    assert (Hsnd_n : snd (N.iter n (fast_step_chk_ge lo) (fc, ok)) = true) by (rewrite E; exact Hok').
    destruct (IHn lo fc ok Hsnd_n) as [Hok Hlt].
    split; [exact Hok |].
    intros k Hk.
    destruct (N.lt_ge_cases k (N.succ n)) as [Hlt_k | Hge_k].
    + apply Hlt. lia.
    + replace k with (N.succ n) by lia. rewrite N.iter_succ, <- Hfc.
      repeat split.
      * rewrite negb_true_iff, Z.eqb_neq in Hneq. exact Hneq.
      * rewrite Z.leb_le in Hlo1. exact Hlo1.
      * rewrite Z.leb_le in Hlo2. exact Hlo2.
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

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

Lemma fc0_eq_c0 : cfg_eq (fc_to_cfg fc0) c0.
Proof.
  constructor; simpl; auto.
  intro z. unfold bt_interp, empty_tape. simpl. apply bt_get_empty.
Qed.

Definition check_fc_6872 (st : FastConfig * bool) : bool :=
  let (fc, ok) := st in
  ok &&
  (fc.(fpos1) =? -2) &&
  (fc.(fpos2) =? 1720) &&
  (match fc.(fstate1), fc.(fstate2) with StC, StA => true | _, _ => false end) &&
  bt_bounded_aux 1374 1720 (fun q => q) fc.(ftape) &&
  check_all_true_nat 1374 (Z.to_nat (1721 - 1374)) fc.(ftape).

Lemma fc_6872_ok : check_fc_6872 (N.iter 6872 (fast_step_chk_ge (-2)) (fc0, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma check_states_CA : forall s1 s2,
  (match s1, s2 with StC, StA => true | _, _ => false end = true) ->
  s1 = StC /\ s2 = StA.
Proof. destruct s1, s2; simpl; intros H; try discriminate; auto. Qed.

Lemma state_6872 :
  let c := run_N ag1 ag2 6872 c0 in
  c.(pos1) = -2 /\ c.(pos2) = 1720 /\ c.(state1) = StC /\ c.(state2) = StA /\
  (forall z, z <= 1373 -> c.(tape) z = false) /\
  (forall z, 1374 <= z <= 1720 -> c.(tape) z = true) /\
  (forall z, 1721 <= z -> c.(tape) z = false) /\
  (forall t, (t < 6872)%N -> (run_N ag1 ag2 t c0).(pos1) <> (run_N ag1 ag2 t c0).(pos2)).
Proof.
  pose proof fc_6872_ok as Hok.
  remember (N.iter 6872 (fast_step_chk_ge (-2)) (fc0, true)) as st eqn:E.
  destruct st as [fc_end ok_end].
  unfold check_fc_6872 in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[Hok_b Hp1] Hp2] Hst] Hbd] Htr].
  rewrite Z.eqb_eq in Hp1, Hp2.
  apply check_states_CA in Hst. destruct Hst as [Hs1 Hs2].
  assert (Hfc : fc_end = N.iter 6872 fast_step fc0).
  { pose proof (fast_step_chk_ge_fst 6872 (-2) fc0 true) as Hfst.
    rewrite <- E in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 6872 (fast_step_chk_ge (-2)) (fc0, true)) = true).
  { rewrite <- E. exact Hok_b. }
  clear E Hok_b.
  pose proof (fast_run_sound 6872 fc0) as Hrun.
  pose proof (run_N_proper ag1 ag2 6872 _ _ fc0_eq_c0) as Hprop.
  assert (Heq : cfg_eq (fc_to_cfg fc_end) (run_N ag1 ag2 6872 c0)).
  { rewrite Hfc. eapply cfg_eq_trans; [exact Hrun | exact Hprop]. }
  clear Hfc Hrun Hprop.
  destruct Heq as [Ep1 Ep2 Es1 Es2 Etp].
  change (pos1 (fc_to_cfg fc_end)) with fc_end.(fpos1) in Ep1.
  change (pos2 (fc_to_cfg fc_end)) with fc_end.(fpos2) in Ep2.
  change (state1 (fc_to_cfg fc_end)) with fc_end.(fstate1) in Es1.
  change (state2 (fc_to_cfg fc_end)) with fc_end.(fstate2) in Es2.
  change (tape (fc_to_cfg fc_end)) with (bt_interp fc_end.(ftape)) in Etp.
  intro c. subst c.
  split; [rewrite <- Ep1; exact Hp1 |].
  split; [rewrite <- Ep2; exact Hp2 |].
  split; [rewrite <- Es1; exact Hs1 |].
  split; [rewrite <- Es2; exact Hs2 |].
  split; [intros z Hz; rewrite <- Etp; eapply bt_bounded_sound; [exact Hbd | lia] |].
  split; [intros z Hz; rewrite <- Etp; eapply check_all_true_nat_sound; [exact Htr |];
          change (Z.of_nat (Z.to_nat (1721 - 1374))) with 347; lia |].
  split; [intros z Hz; rewrite <- Etp; eapply bt_bounded_sound; [exact Hbd | lia] |].
  intros t Ht.
  destruct (N.eq_0_gt_0_cases t) as [Ht0 | Htgt0].
  - subst t. rewrite run_N_0. unfold c0; simpl; lia.
  - destruct (fast_step_chk_ge_sound 6872 (-2) fc0 true Hsnd) as [_ Hchk].
    assert (Hk : (1 <= t <= 6872)%N) by lia.
    destruct (Hchk t Hk) as [Hneq _].
    pose proof (fast_run_sound t fc0) as Hrt.
    pose proof (run_N_proper ag1 ag2 t _ _ fc0_eq_c0) as Hpt.
    assert (Heqt : cfg_eq (fc_to_cfg (N.iter t fast_step fc0)) (run_N ag1 ag2 t c0))
      by (eapply cfg_eq_trans; eauto).
    destruct Heqt as [Tp1 Tp2 _ _ _].
    change (pos1 (fc_to_cfg (N.iter t fast_step fc0))) with (N.iter t fast_step fc0).(fpos1) in Tp1.
    change (pos2 (fc_to_cfg (N.iter t fast_step fc0))) with (N.iter t fast_step fc0).(fpos2) in Tp2.
    lia.
Qed.

(** * 7. Single-Agent Execution and Spatial Decoupling *)

Record SingleCfg := {
  spos   : Z;
  sstate : State;
  stape  : Tape
}.

Definition sstep (ag : AgentTable) (sc : SingleCfg) : SingleCfg :=
  let r := sc.(stape) sc.(spos) in
  let tr := ag sc.(sstate) r in
  {| spos   := move_pos sc.(spos) tr.(move_dir);
     sstate := tr.(next_state);
     stape  := write_tape sc.(stape) sc.(spos) tr.(write_sym) |}.

Definition srun (ag : AgentTable) (n : N) (sc : SingleCfg) : SingleCfg :=
  N.iter n (sstep ag) sc.

Lemma srun_0 : forall ag sc, srun ag 0%N sc = sc.
Proof. reflexivity. Qed.

Lemma srun_succ : forall ag n sc, srun ag (N.succ n) sc = sstep ag (srun ag n sc).
Proof. intros. unfold srun. apply N.iter_succ. Qed.

Lemma srun_add : forall ag p q sc, srun ag (p + q) sc = srun ag p (srun ag q sc).
Proof. intros. unfold srun. apply N.iter_add. Qed.

Record scfg_eq (s1 s2 : SingleCfg) : Prop := {
  se_p : s1.(spos) = s2.(spos);
  se_s : s1.(sstate) = s2.(sstate);
  se_t : tape_eq s1.(stape) s2.(stape)
}.

Lemma sstep_proper : forall ag s1 s2, scfg_eq s1 s2 -> scfg_eq (sstep ag s1) (sstep ag s2).
Proof.
  intros ag s1 s2 [Hp Hs Ht]. unfold sstep.
  rewrite Hp, Hs, (Ht s2.(spos)).
  constructor; simpl; auto. apply write_tape_proper. exact Ht.
Qed.

Lemma srun_proper : forall ag n s1 s2, scfg_eq s1 s2 -> scfg_eq (srun ag n s1) (srun ag n s2).
Proof.
  intros ag n. induction n using N.peano_ind; intros s1 s2 H.
  - rewrite !srun_0. exact H.
  - rewrite !srun_succ. apply sstep_proper. apply IHn. exact H.
Qed.

Lemma run_decouple : forall a1 a2 B1 B2 n c sc1 sc2,
  B1 < B2 ->
  c.(pos1) = sc1.(spos) -> c.(state1) = sc1.(sstate) ->
  c.(pos2) = sc2.(spos) -> c.(state2) = sc2.(sstate) ->
  (forall z, z <= B1 -> c.(tape) z = sc1.(stape) z) ->
  (forall z, B2 <= z -> c.(tape) z = sc2.(stape) z) ->
  (forall k, (k < n)%N -> (srun a1 k sc1).(spos) <= B1) ->
  (forall k, (k < n)%N -> B2 <= (srun a2 k sc2).(spos)) ->
  let c' := run_N a1 a2 n c in
  c'.(pos1) = (srun a1 n sc1).(spos) /\
  c'.(state1) = (srun a1 n sc1).(sstate) /\
  c'.(pos2) = (srun a2 n sc2).(spos) /\
  c'.(state2) = (srun a2 n sc2).(sstate) /\
  (forall z, z <= B1 -> c'.(tape) z = (srun a1 n sc1).(stape) z) /\
  (forall z, B2 <= z -> c'.(tape) z = (srun a2 n sc2).(stape) z) /\
  (forall z, B1 < z < B2 -> c'.(tape) z = c.(tape) z) /\
  (forall k, (k < n)%N -> (run_N a1 a2 k c).(pos1) <> (run_N a1 a2 k c).(pos2)).
Proof.
  intros a1 a2 B1 B2 n c sc1 sc2 Hsep Hp1 Hs1 Hp2 Hs2 Ht1 Ht2 Hbd1 Hbd2.
  induction n using N.peano_ind.
  - rewrite run_N_0, !srun_0. repeat split; auto; intros k Hk; lia.
  - assert (Hbd1' : forall k, (k < n)%N -> (srun a1 k sc1).(spos) <= B1) by (intros; apply Hbd1; lia).
    assert (Hbd2' : forall k, (k < n)%N -> B2 <= (srun a2 k sc2).(spos)) by (intros; apply Hbd2; lia).
    destruct (IHn Hbd1' Hbd2') as [Ep1 [Es1 [Ep2 [Es2 [Et1 [Et2 [Emid Hnc]]]]]]].
    rewrite run_N_succ, !srun_succ.
    set (cn := run_N a1 a2 n c) in *.
    set (u1 := srun a1 n sc1) in *.
    set (u2 := srun a2 n sc2) in *.
    assert (Hu1 : u1.(spos) <= B1) by (apply Hbd1; lia).
    assert (Hu2 : B2 <= u2.(spos)) by (apply Hbd2; lia).
    assert (Hr1 : cn.(tape) cn.(pos1) = u1.(stape) u1.(spos)) by (rewrite Ep1; apply Et1; lia).
    assert (Hr2 : cn.(tape) cn.(pos2) = u2.(stape) u2.(spos)) by (rewrite Ep2; apply Et2; lia).
    unfold step, sstep. rewrite Hr1, Hr2, Ep1, Ep2, Es1, Es2.
    repeat split; simpl; auto.
    + intros z Hz.
      destruct (Z.eq_dec z u1.(spos)).
      * subst z. rewrite !write_tape_same. reflexivity.
      * rewrite !write_tape_other by lia. apply Et1; auto.
    + intros z Hz.
      destruct (Z.eq_dec z u1.(spos)); [lia |].
      rewrite write_tape_other by auto.
      destruct (Z.eq_dec z u2.(spos)).
      * subst z. rewrite !write_tape_same. reflexivity.
      * rewrite !write_tape_other by auto. apply Et2; auto.
    + intros z Hz.
      rewrite write_tape_other by lia. rewrite write_tape_other by lia. apply Emid; auto.
    + intros k Hk. destruct (N.lt_ge_cases k n) as [Hlt | Hge].
      * apply Hnc; exact Hlt.
      * replace k with n by lia. change (run_N a1 a2 n c) with cn. rewrite Ep1, Ep2. lia.
Qed.

(** * 8. Binary Counter (Agent 1) and Glider (Agent 2) Inductions *)

Lemma srun_1 : forall ag sc, srun ag 1%N sc = sstep ag sc.
Proof. reflexivity. Qed.

Ltac splits := repeat match goal with |- _ /\ _ => split | |- let _ := _ in _ /\ _ => cbv zeta; split end.
Ltac step1_eval := rewrite srun_1; unfold sstep, ag1, ag1_with, ag2, move_pos.
Ltac proj_eval := cbn [spos sstate stape write_sym move_dir next_state].

Fixpoint S_rec (m : nat) : N :=
  match m with
  | O => 1%N
  | S k => (2 * S_rec k + N.of_nat k + 2)%N
  end.

Lemma S_rec_1375 : S_rec 1375 = (2 ^ 1377 - 1378)%N.
Proof. vm_compute. reflexivity. Qed.

Lemma ag1_wipe_left : forall m sc,
  sc.(spos) = -2 + Z.of_nat m ->
  sc.(sstate) = StC ->
  (forall z, -1 <= z <= -2 + Z.of_nat m -> sc.(stape) z = true) ->
  (forall k, (k < N.of_nat m)%N -> -1 <= (srun ag1 k sc).(spos) <= -2 + Z.of_nat m) /\
  let sc' := srun ag1 (N.of_nat m) sc in
  sc'.(spos) = -2 /\
  sc'.(sstate) = StC /\
  (forall z, -1 <= z <= -2 + Z.of_nat m -> sc'.(stape) z = false) /\
  (forall z, z < -1 \/ z > -2 + Z.of_nat m -> sc'.(stape) z = sc.(stape) z).
Proof.
  induction m; intros sc Hp Hs Ht.
  - rewrite srun_0. simpl in *. splits; try exact Hs; try lia; intros; auto; lia.
  - rewrite Nat2Z.inj_succ in *. rewrite Nat2N.inj_succ.
    replace (N.succ (N.of_nat m)) with (N.of_nat m + 1)%N by lia.
    set (sc1 := srun ag1 1%N sc).
    assert (H1 : sc1.(spos) = -2 + Z.of_nat m /\ sc1.(sstate) = StC /\
                 sc1.(stape) (-1 + Z.of_nat m) = false /\
                 (forall z, z <> -1 + Z.of_nat m -> sc1.(stape) z = sc.(stape) z)).
    { unfold sc1. step1_eval.
      replace (-2 + Z.succ (Z.of_nat m)) with (-1 + Z.of_nat m) in Hp by lia.
      rewrite Hp, Hs. rewrite Ht by lia. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same |].
      intros z Hz. apply write_tape_other. auto. }
    destruct H1 as [H1p [H1s [H1f H1o]]].
    assert (H1t : forall z, -1 <= z <= -2 + Z.of_nat m -> sc1.(stape) z = true).
    { intros z Hz. rewrite H1o by lia. apply Ht. lia. }
    destruct (IHm sc1 H1p H1s H1t) as [IHbd [IHp [IHs [IHt IHo]]]].
    splits.
    + intros k Hk. destruct (N.eq_0_gt_0_cases k) as [Hk0 | Hkgt].
      * subst k. rewrite srun_0, Hp. lia.
      * replace k with ((k - 1) + 1)%N by lia.
        rewrite srun_add. change (srun ag1 1 sc) with sc1.
        assert (Hk' : (k - 1 < N.of_nat m)%N) by lia.
        pose proof (IHbd (k - 1)%N Hk'). lia.
    + rewrite srun_add. exact IHp.
    + rewrite srun_add. exact IHs.
    + intros z Hz. rewrite srun_add.
      destruct (Z.eq_dec z (-1 + Z.of_nat m)).
      * subst z. rewrite IHo by lia. exact H1f.
      * apply IHt. lia.
    + intros z Hz. rewrite srun_add, IHo by lia. apply H1o. lia.
Qed.

Lemma ag1_counter : forall m sc,
  sc.(spos) = -2 ->
  sc.(sstate) = StC ->
  (forall z, -2 <= z <= -2 + Z.of_nat m -> sc.(stape) z = false) ->
  (forall k, (k < S_rec m)%N -> -2 <= (srun ag1 k sc).(spos) <= -2 + Z.of_nat m) /\
  let sc' := srun ag1 (S_rec m) sc in
  sc'.(spos) = -1 + Z.of_nat m /\
  sc'.(sstate) = StB /\
  sc'.(stape) (-2) = false /\
  (forall z, -1 <= z <= -2 + Z.of_nat m -> sc'.(stape) z = true) /\
  (forall z, z < -2 \/ z > -2 + Z.of_nat m -> sc'.(stape) z = sc.(stape) z).
Proof.
  induction m; intros sc Hp Hs Ht.
  - simpl S_rec. unfold srun. simpl N.iter. unfold sstep, ag1, ag1_with, move_pos.
    rewrite Hp, Hs, (Ht (-2)) by lia. simpl.
    splits.
    + intros k Hk. assert (k = 0%N) by lia. subst k. simpl. lia.
    + lia.
    + reflexivity.
    + reflexivity.
    + intros z Hz. lia.
    + intros z Hz. apply write_tape_other. lia.
  - change (S_rec (S m)) with (2 * S_rec m + N.of_nat m + 2)%N.
    rewrite Nat2Z.inj_succ in *.
    assert (Ht_m : forall z, -2 <= z <= -2 + Z.of_nat m -> sc.(stape) z = false)
      by (intros z Hz; apply Ht; lia).
    destruct (IHm sc Hp Hs Ht_m) as [Bd1 [P1 [S1 [F1 [T1 O1]]]]].
    set (t1 := S_rec m) in *.
    set (sc1 := srun ag1 t1 sc) in *.
    (* Step 2: 1 step at pos = -1 + m, StB, reading false *)
    set (sc2 := srun ag1 1%N sc1).
    assert (H2 : sc2.(spos) = -2 + Z.of_nat m /\ sc2.(sstate) = StC /\
                 sc2.(stape) (-1 + Z.of_nat m) = true /\
                 (forall z, z <> -1 + Z.of_nat m -> sc2.(stape) z = sc1.(stape) z)).
    { unfold sc2. step1_eval. rewrite P1, S1, O1 by lia.
      rewrite (Ht (-1 + Z.of_nat m)) by lia. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same |].
      intros z Hz. apply write_tape_other. auto. }
    destruct H2 as [P2 [S2 [W2 O2]]].
    (* Step 3: wipe left m steps *)
    assert (Ht2 : forall z, -1 <= z <= -2 + Z.of_nat m -> sc2.(stape) z = true)
      by (intros z Hz; rewrite O2 by lia; apply T1; auto).
    destruct (ag1_wipe_left m sc2 P2 S2 Ht2) as [Bd3 [P3 [S3 [T3 O3]]]].
    set (sc3 := srun ag1 (N.of_nat m) sc2) in *.
    (* Step 4: counter m steps again *)
    assert (Ht3 : forall z, -2 <= z <= -2 + Z.of_nat m -> sc3.(stape) z = false).
    { intros z Hz. destruct (Z.eq_dec z (-2)).
      - subst z. rewrite O3 by lia. rewrite O2 by lia. exact F1.
      - apply T3. lia. }
    destruct (IHm sc3 P3 S3 Ht3) as [Bd4 [P4 [S4 [F4 [T4 O4]]]]].
    set (sc4 := srun ag1 t1 sc3) in *.
    (* Step 5: 1 step at pos = -1 + m, StB, reading true *)
    set (sc5 := srun ag1 1%N sc4).
    assert (H5 : sc5.(spos) = -1 + Z.succ (Z.of_nat m) /\ sc5.(sstate) = StB /\
                 sc5.(stape) (-1 + Z.of_nat m) = true /\
                 (forall z, z <> -1 + Z.of_nat m -> sc5.(stape) z = sc4.(stape) z)).
    { unfold sc5. step1_eval.
      rewrite P4, S4.
      assert (Hr4 : sc4.(stape) (-1 + Z.of_nat m) = true).
      { rewrite O4 by lia. rewrite O3 by lia. exact W2. }
      rewrite Hr4. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same |].
      intros z Hz. apply write_tape_other. auto. }
    destruct H5 as [P5 [S5 [W5 O5]]].
    assert (Htot : (2 * t1 + N.of_nat m + 2 = 1 + (t1 + (N.of_nat m + (1 + t1))))%N)
      by (unfold t1; lia).
    rewrite Htot.
    assert (Hsc5 : srun ag1 (1 + (t1 + (N.of_nat m + (1 + t1)))) sc = sc5).
    { rewrite !srun_add. reflexivity. }
    splits.
    + intros k Hk.
      destruct (N.lt_ge_cases k t1) as [Hk1 | Hge1].
      * pose proof (Bd1 k Hk1). lia.
      * destruct (N.lt_ge_cases k (1 + t1)) as [Hk2 | Hge2].
        -- replace k with t1 by lia. change (srun ag1 t1 sc) with sc1. rewrite P1. lia.
        -- destruct (N.lt_ge_cases k (N.of_nat m + (1 + t1))) as [Hk3 | Hge3].
           ++ replace k with ((k - (1 + t1)) + (1 + t1))%N by lia.
              rewrite !srun_add.
              change (srun ag1 1 (srun ag1 t1 sc)) with sc2.
              pose proof (Bd3 (k - (1 + t1))%N ltac:(lia)). lia.
           ++ destruct (N.lt_ge_cases k (t1 + (N.of_nat m + (1 + t1)))) as [Hk4 | Hge4].
              ** replace k with ((k - (N.of_nat m + (1 + t1))) + (N.of_nat m + (1 + t1)))%N by lia.
                 rewrite !srun_add.
                 change (srun ag1 (N.of_nat m) (srun ag1 1 (srun ag1 t1 sc))) with sc3.
                 pose proof (Bd4 (k - (N.of_nat m + (1 + t1)))%N ltac:(lia)). lia.
              ** replace k with (t1 + (N.of_nat m + (1 + t1)))%N by lia.
                 rewrite !srun_add.
                 change (srun ag1 t1 (srun ag1 (N.of_nat m) (srun ag1 1 (srun ag1 t1 sc)))) with sc4.
                 rewrite P4. lia.
    + rewrite Hsc5. exact P5.
    + rewrite Hsc5. exact S5.
    + rewrite Hsc5, O5 by lia. exact F4.
    + intros z Hz. rewrite Hsc5.
      destruct (Z.eq_dec z (-1 + Z.of_nat m)).
      * subst z. exact W5.
      * rewrite O5 by auto. apply T4. lia.
    + intros z Hz. rewrite Hsc5, O5 by lia.
      rewrite O4 by lia. rewrite O3 by lia. rewrite O2 by lia. apply O1. lia.
Qed.

(** * 8b. Translation Invariance, Locality, and Reflected Agent 2 Cycle *)

Definition agree_ge (lo : Z) (t1 t2 : Tape) : Prop :=
  forall z, lo <= z -> t1 z = t2 z.

Lemma srun_agree_ge : forall ag lo n s1 s2,
  s1.(spos) = s2.(spos) -> s1.(sstate) = s2.(sstate) ->
  agree_ge lo s1.(stape) s2.(stape) ->
  (forall k, (k < n)%N -> lo <= (srun ag k s1).(spos)) ->
  let u1 := srun ag n s1 in
  let u2 := srun ag n s2 in
  u1.(spos) = u2.(spos) /\ u1.(sstate) = u2.(sstate) /\
  agree_ge lo u1.(stape) u2.(stape) /\
  (forall z, z < lo -> u1.(stape) z = s1.(stape) z).
Proof.
  intros ag lo n s1 s2 Hp Hs Hag Hbd.
  induction n using N.peano_ind.
  - rewrite !srun_0. cbv zeta. splits; auto.
  - assert (Hbd' : forall k, (k < n)%N -> lo <= (srun ag k s1).(spos)) by (intros; apply Hbd; lia).
    destruct (IHn Hbd') as [Ep [Es [Eag Elt]]].
    rewrite !srun_succ.
    set (u1 := srun ag n s1) in *. set (u2 := srun ag n s2) in *.
    assert (Hu : lo <= u1.(spos)) by (apply Hbd; lia).
    assert (Hr : u1.(stape) u1.(spos) = u2.(stape) u2.(spos)) by (rewrite <- Ep; apply Eag; auto).
    unfold sstep. rewrite Ep, Es, <- Ep, Hr, Ep.
    cbv zeta. splits; simpl; auto.
    + intros z Hz. unfold write_tape. destruct (Z.eqb_spec z u2.(spos)); auto; apply Eag; auto.
    + intros z Hz. rewrite write_tape_other by lia. apply Elt; auto.
Qed.

Lemma run_N_agree_ge : forall a1 a2 lo n c1 c2,
  c1.(pos1) = c2.(pos1) -> c1.(pos2) = c2.(pos2) ->
  c1.(state1) = c2.(state1) -> c1.(state2) = c2.(state2) ->
  agree_ge lo c1.(tape) c2.(tape) ->
  (forall k, (k < n)%N -> lo <= (run_N a1 a2 k c1).(pos1) /\ lo <= (run_N a1 a2 k c1).(pos2)) ->
  let r1 := run_N a1 a2 n c1 in
  let r2 := run_N a1 a2 n c2 in
  r1.(pos1) = r2.(pos1) /\ r1.(pos2) = r2.(pos2) /\
  r1.(state1) = r2.(state1) /\ r1.(state2) = r2.(state2) /\
  agree_ge lo r1.(tape) r2.(tape) /\
  (forall z, z < lo -> r1.(tape) z = c1.(tape) z) /\
  (forall k, (k < n)%N -> (run_N a1 a2 k c1).(pos1) = (run_N a1 a2 k c2).(pos1) /\
                          (run_N a1 a2 k c1).(pos2) = (run_N a1 a2 k c2).(pos2)).
Proof.
  intros a1 a2 lo n c1 c2 Hp1 Hp2 Hs1 Hs2 Hag Hbd.
  induction n using N.peano_ind.
  - rewrite !run_N_0. cbv zeta. splits; auto. intros k Hk; lia.
  - assert (Hbd' : forall k, (k < n)%N -> lo <= (run_N a1 a2 k c1).(pos1) /\ lo <= (run_N a1 a2 k c1).(pos2))
      by (intros; apply Hbd; lia).
    destruct (IHn Hbd') as [Ep1 [Ep2 [Es1 [Es2 [Eag [Elt Hprev]]]]]].
    rewrite !run_N_succ.
    set (r1 := run_N a1 a2 n c1) in *. set (r2 := run_N a1 a2 n c2) in *.
    destruct (Hbd n ltac:(lia)) as [H1 H2].
    change (run_N a1 a2 n c1) with r1 in H1, H2.
    assert (Hr1 : r1.(tape) r1.(pos1) = r2.(tape) r2.(pos1)) by (rewrite <- Ep1; apply Eag; auto).
    assert (Hr2 : r1.(tape) r1.(pos2) = r2.(tape) r2.(pos2)) by (rewrite <- Ep2; apply Eag; auto).
    unfold step. rewrite Hr1, Hr2, Ep1, Ep2, Es1, Es2.
    cbv zeta. splits; simpl; auto.
    + intros z Hz. unfold write_tape.
      destruct (Z.eqb_spec z r2.(pos1)); auto;
      destruct (Z.eqb_spec z r2.(pos2)); auto;
      apply Eag; auto.
    + intros z Hz. rewrite !write_tape_other by (rewrite <- ?Ep1, <- ?Ep2; lia). apply Elt; auto.
    + intros k Hk. destruct (N.lt_ge_cases k n) as [Hlt | Hge].
      * apply Hprev; exact Hlt.
      * replace k with n by lia. split; [exact Ep1 | exact Ep2].
Qed.

Definition shift_tape (d : Z) (t : Tape) : Tape := fun z => t (z - d).
Definition shift_sc (d : Z) (sc : SingleCfg) : SingleCfg :=
  {| spos := sc.(spos) + d; sstate := sc.(sstate); stape := shift_tape d sc.(stape) |}.
Definition shift_cfg (d : Z) (c : Config) : Config :=
  {| pos1 := c.(pos1) + d; pos2 := c.(pos2) + d;
     state1 := c.(state1); state2 := c.(state2); tape := shift_tape d c.(tape) |}.

Lemma sstep_shift : forall ag d sc,
  scfg_eq (shift_sc d (sstep ag sc)) (sstep ag (shift_sc d sc)).
Proof.
  intros ag d sc. unfold shift_sc, sstep, shift_tape, move_pos. simpl.
  replace (spos sc + d - d) with (spos sc) by lia.
  constructor; simpl; try destruct (move_dir _); try lia; auto.
  intro z. unfold write_tape. destruct (Z.eqb_spec (z - d) (spos sc)), (Z.eqb_spec z (spos sc + d)); auto; lia.
Qed.

Lemma srun_shift : forall ag d n sc,
  scfg_eq (shift_sc d (srun ag n sc)) (srun ag n (shift_sc d sc)).
Proof.
  intros ag d n sc. induction n using N.peano_ind.
  - rewrite !srun_0. constructor; simpl; auto. intro; auto.
  - rewrite !srun_succ.
    assert (Hs : scfg_eq (shift_sc d (sstep ag (srun ag n sc))) (sstep ag (shift_sc d (srun ag n sc))))
      by apply sstep_shift.
    pose proof (sstep_proper ag _ _ IHn) as [Ap As At].
    destruct Hs as [Bp Bs Bt].
    constructor; try congruence.
Qed.

Lemma step_shift : forall a1 a2 d c,
  cfg_eq (shift_cfg d (step a1 a2 c)) (step a1 a2 (shift_cfg d c)).
Proof.
  intros a1 a2 d c. unfold shift_cfg, step, shift_tape, move_pos. simpl.
  replace (pos1 c + d - d) with (pos1 c) by lia.
  replace (pos2 c + d - d) with (pos2 c) by lia.
  constructor; simpl;
    try destruct (move_dir (a1 _ _)); try destruct (move_dir (a2 _ _)); try lia; auto.
  try (intro z; unfold write_tape;
       destruct (Z.eqb_spec (z - d) (pos1 c)), (Z.eqb_spec z (pos1 c + d)),
                (Z.eqb_spec (z - d) (pos2 c)), (Z.eqb_spec z (pos2 c + d)); auto; lia).
Qed.

Lemma run_N_shift : forall a1 a2 d n c,
  cfg_eq (shift_cfg d (run_N a1 a2 n c)) (run_N a1 a2 n (shift_cfg d c)).
Proof.
  intros a1 a2 d n c. induction n using N.peano_ind.
  - rewrite !run_N_0. constructor; simpl; auto. intro; auto.
  - rewrite !run_N_succ.
    eapply cfg_eq_trans; [apply step_shift | apply step_proper; exact IHn].
Qed.

Record FastSingle := { fspos : Z; fsstate : State; fstape : BTree }.

Definition fs_to_sc (fs : FastSingle) : SingleCfg :=
  {| spos := fs.(fspos); sstate := fs.(fsstate); stape := bt_interp fs.(fstape) |}.

Definition fast_sstep (ag : AgentTable) (fs : FastSingle) : FastSingle :=
  let r := bt_get (z_to_pos fs.(fspos)) fs.(fstape) in
  let tr := ag fs.(fsstate) r in
  {| fspos := move_pos fs.(fspos) tr.(move_dir);
     fsstate := tr.(next_state);
     fstape := bt_set (z_to_pos fs.(fspos)) tr.(write_sym) fs.(fstape) |}.

Lemma fast_sstep_sound : forall ag fs,
  scfg_eq (fs_to_sc (fast_sstep ag fs)) (sstep ag (fs_to_sc fs)).
Proof.
  intros ag fs. unfold fast_sstep, fs_to_sc, sstep.
  constructor; simpl; try reflexivity. apply bt_interp_set.
Qed.

Lemma fast_srun_sound : forall ag n fs,
  scfg_eq (fs_to_sc (N.iter n (fast_sstep ag) fs)) (srun ag n (fs_to_sc fs)).
Proof.
  intros ag n. induction n using N.peano_ind; intro fs.
  - rewrite srun_0. simpl. constructor; simpl; auto. intro; auto.
  - rewrite srun_succ, N.iter_succ.
    pose proof (fast_sstep_sound ag (N.iter n (fast_sstep ag) fs)) as [Ap As At].
    pose proof (sstep_proper ag _ _ (IHn fs)) as [Bp Bs Bt].
    constructor; try congruence.
Qed.

Lemma ag2_cycle8 : forall X sc,
  sc.(spos) = X ->
  sc.(sstate) = StA ->
  (forall z, X <= z -> sc.(stape) z = false) ->
  (forall k, (k < 8)%N -> X <= (srun ag2 k sc).(spos)) /\
  let sc' := srun ag2 8 sc in
  sc'.(spos) = X + 2 /\
  sc'.(sstate) = StA /\
  (forall z, z < X -> sc'.(stape) z = sc.(stape) z) /\
  (forall z, X <= z < X + 2 -> sc'.(stape) z = true) /\
  (forall z, X + 2 <= z -> sc'.(stape) z = false).
Proof.
  intros X sc Hp0 Hs0 Ht0.
  remember (srun ag2 1 sc) as sc1 eqn:E1.
  assert (H1 : sc1.(spos) = X + 1 /\ sc1.(sstate) = StB /\ forall z, sc1.(stape) z = sc.(stape) z).
  { rewrite E1, srun_1. unfold sstep, ag2, move_pos. rewrite Hp0, Hs0, (Ht0 X ltac:(lia)). proj_eval.
    splits; [lia | reflexivity |].
    intro z. destruct (Z.eq_dec z X); [subst z; rewrite write_tape_same; symmetry; apply Ht0; lia | apply write_tape_other; auto]. }
  destruct H1 as [P1 [S1 T1]].
  remember (srun ag2 2 sc) as sc2 eqn:E2.
  assert (H2 : sc2.(spos) = X + 2 /\ sc2.(sstate) = StC /\ sc2.(stape) (X + 1) = true /\
               forall z, z <> X + 1 -> sc2.(stape) z = sc1.(stape) z).
  { assert (Hs : sc2 = sstep ag2 sc1) by (rewrite E2, E1; change 2%N with (N.succ 1); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos. rewrite P1, S1, T1, (Ht0 (X + 1) ltac:(lia)). proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H2 as [P2 [S2 [W2 O2]]].
  remember (srun ag2 3 sc) as sc3 eqn:E3.
  assert (H3 : sc3.(spos) = X + 1 /\ sc3.(sstate) = StB /\ sc3.(stape) (X + 2) = true /\
               forall z, z <> X + 2 -> sc3.(stape) z = sc2.(stape) z).
  { assert (Hs : sc3 = sstep ag2 sc2) by (rewrite E3, E2; change 3%N with (N.succ 2); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos. rewrite P2, S2, O2, T1, (Ht0 (X + 2) ltac:(lia)) by lia. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H3 as [P3 [S3 [W3 O3]]].
  remember (srun ag2 4 sc) as sc4 eqn:E4.
  assert (H4 : sc4.(spos) = X /\ sc4.(sstate) = StB /\ forall z, sc4.(stape) z = sc3.(stape) z).
  { assert (Hs : sc4 = sstep ag2 sc3) by (rewrite E4, E3; change 4%N with (N.succ 3); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr3 : sc3.(stape) (X + 1) = true) by (rewrite O3 by lia; exact W2).
    rewrite P3, S3, Hr3. proj_eval.
    splits; [lia | reflexivity |].
    intro z. destruct (Z.eq_dec z (X + 1)); [subst z; rewrite write_tape_same; symmetry; exact Hr3 | apply write_tape_other; auto]. }
  destruct H4 as [P4 [S4 T4]].
  remember (srun ag2 5 sc) as sc5 eqn:E5.
  assert (H5 : sc5.(spos) = X + 1 /\ sc5.(sstate) = StC /\ sc5.(stape) X = true /\
               forall z, z <> X -> sc5.(stape) z = sc4.(stape) z).
  { assert (Hs : sc5 = sstep ag2 sc4) by (rewrite E5, E4; change 5%N with (N.succ 4); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr4 : sc4.(stape) X = false) by (rewrite T4, O3, O2, T1 by lia; apply Ht0; lia).
    rewrite P4, S4, Hr4. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H5 as [P5 [S5 [W5 O5]]].
  remember (srun ag2 6 sc) as sc6 eqn:E6.
  assert (H6 : sc6.(spos) = X + 2 /\ sc6.(sstate) = StA /\ forall z, sc6.(stape) z = sc5.(stape) z).
  { assert (Hs : sc6 = sstep ag2 sc5) by (rewrite E6, E5; change 6%N with (N.succ 5); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr5 : sc5.(stape) (X + 1) = true) by (rewrite O5, T4, O3 by lia; exact W2).
    rewrite P5, S5, Hr5. proj_eval.
    splits; [lia | reflexivity |].
    intro z. destruct (Z.eq_dec z (X + 1)); [subst z; rewrite write_tape_same; symmetry; exact Hr5 | apply write_tape_other; auto]. }
  destruct H6 as [P6 [S6 T6]].
  remember (srun ag2 7 sc) as sc7 eqn:E7.
  assert (H7 : sc7.(spos) = X + 1 /\ sc7.(sstate) = StC /\ sc7.(stape) (X + 2) = false /\
               forall z, z <> X + 2 -> sc7.(stape) z = sc6.(stape) z).
  { assert (Hs : sc7 = sstep ag2 sc6) by (rewrite E7, E6; change 7%N with (N.succ 6); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr6 : sc6.(stape) (X + 2) = true) by (rewrite T6, O5, T4 by lia; exact W3).
    rewrite P6, S6, Hr6. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H7 as [P7 [S7 [W7 O7]]].
  remember (srun ag2 8 sc) as sc8 eqn:E8.
  assert (H8 : sc8.(spos) = X + 2 /\ sc8.(sstate) = StA /\ forall z, sc8.(stape) z = sc7.(stape) z).
  { assert (Hs : sc8 = sstep ag2 sc7) by (rewrite E8, E7; change 8%N with (N.succ 7); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr7 : sc7.(stape) (X + 1) = true) by (rewrite O7, T6, O5, T4, O3 by lia; exact W2).
    rewrite P7, S7, Hr7. proj_eval.
    splits; [lia | reflexivity |].
    intro z. destruct (Z.eq_dec z (X + 1)); [subst z; rewrite write_tape_same; symmetry; exact Hr7 | apply write_tape_other; auto]. }
  destruct H8 as [P8 [S8 T8]].
  cbv zeta.
  splits.
  - intros k Hk.
    assert (Hk_c : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%N) by lia.
    destruct Hk_c as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [rewrite srun_0; lia | rewrite <- E1; lia | rewrite <- E2; lia | rewrite <- E3; lia |
       rewrite <- E4; lia | rewrite <- E5; lia | rewrite <- E6; lia | rewrite <- E7; lia].
  - exact P8.
  - exact S8.
  - intros z Hz. rewrite T8, O7, T6, O5, T4, O3, O2, T1 by lia. reflexivity.
  - intros z Hz. rewrite T8, O7, T6 by lia.
    destruct (Z.eq_dec z X).
    + subst z. exact W5.
    + rewrite O5, T4, O3 by lia. replace z with (X + 1) by lia. exact W2.
  - intros z Hz. rewrite T8. destruct (Z.eq_dec z (X + 2)).
    + subst z. exact W7.
    + rewrite O7, T6, O5, T4, O3, O2, T1 by lia. apply Ht0. lia.
Qed.

Lemma ag2_glider : forall K lo X sc,
  lo <= X ->
  sc.(spos) = X ->
  sc.(sstate) = StA ->
  (forall z, lo <= z < X -> sc.(stape) z = true) ->
  (forall z, X <= z -> sc.(stape) z = false) ->
  (forall k, (k < 8 * K)%N -> X <= (srun ag2 k sc).(spos)) /\
  let sc' := srun ag2 (8 * K) sc in
  sc'.(spos) = X + 2 * Z.of_N K /\
  sc'.(sstate) = StA /\
  (forall z, z < lo -> sc'.(stape) z = sc.(stape) z) /\
  (forall z, lo <= z < X + 2 * Z.of_N K -> sc'.(stape) z = true) /\
  (forall z, X + 2 * Z.of_N K <= z -> sc'.(stape) z = false).
Proof.
  intro K. induction K using N.peano_ind; intros lo X sc Hlo Hp Hs Hlt Hge.
  - rewrite N.mul_0_r, srun_0. cbv zeta. splits; [intros; lia | lia | exact Hs | auto | |].
    + intros z Hz. apply Hlt. lia.
    + intros z Hz. apply Hge. lia.
  - replace (8 * N.succ K)%N with (8 + 8 * K)%N by lia.
    rewrite N2Z.inj_succ.
    destruct (IHK lo X sc Hlo Hp Hs Hlt Hge) as [IHbd [IHp [IHs [IHbelow [IHlt IHge]]]]].
    set (scK := srun ag2 (8 * K) sc) in *.
    set (XK := X + 2 * Z.of_N K) in *.
    destruct (ag2_cycle8 XK scK IHp IHs IHge) as [Cybd [Cyp [Cys [Cyold [Cynew Cyge]]]]].
    cbv zeta. splits.
    + intros k Hk. destruct (N.lt_ge_cases k (8 * K)%N) as [Hk1 | Hk2].
      * apply IHbd; exact Hk1.
      * replace k with ((k - 8 * K) + 8 * K)%N by lia.
        rewrite srun_add. change (srun ag2 (8 * K) sc) with scK.
        pose proof (Cybd (k - 8 * K)%N ltac:(lia)). lia.
    + rewrite srun_add. change (srun ag2 (8 * K) sc) with scK. rewrite Cyp. unfold XK. lia.
    + rewrite srun_add. change (srun ag2 (8 * K) sc) with scK. exact Cys.
    + intros z Hz. rewrite srun_add. change (srun ag2 (8 * K) sc) with scK.
      rewrite Cyold by (unfold XK; lia). apply IHbelow; auto.
    + intros z Hz. rewrite srun_add. change (srun ag2 (8 * K) sc) with scK.
      destruct (Z.lt_ge_cases z XK).
      * rewrite Cyold by auto. apply IHlt; unfold XK in *; lia.
      * apply Cynew. unfold XK in *. lia.
    + intros z Hz. rewrite srun_add. change (srun ag2 (8 * K) sc) with scK.
      apply Cyge. unfold XK in *. lia.
Qed.

(** * 9. Full Execution Trace from t = 0 to Exact Collision at T_halt *)

Lemma ag1_walk_ones : forall n X sc,
  sc.(spos) = X ->
  sc.(sstate) = StB ->
  (forall z, X <= z < X + Z.of_nat n -> sc.(stape) z = true) ->
  (forall k, (k < N.of_nat n)%N -> X <= (srun ag1 k sc).(spos) <= X + Z.of_nat n - 1) /\
  let sc' := srun ag1 (N.of_nat n) sc in
  sc'.(spos) = X + Z.of_nat n /\
  sc'.(sstate) = StB /\
  (forall z, sc'.(stape) z = sc.(stape) z).
Proof.
  induction n; intros X sc Hp Hs Ht.
  - rewrite srun_0. simpl in *. cbv zeta. splits; [intros; lia | lia | exact Hs | auto].
  - rewrite Nat2Z.inj_succ, Nat2N.inj_succ.
    replace (N.succ (N.of_nat n)) with (N.of_nat n + 1)%N by lia.
    remember (srun ag1 1 sc) as sc1 eqn:E1.
    assert (H1 : sc1.(spos) = X + 1 /\ sc1.(sstate) = StB /\ forall z, sc1.(stape) z = sc.(stape) z).
    { rewrite E1, srun_1. unfold sstep, ag1, ag1_with, move_pos.
      rewrite Hp, Hs, (Ht X ltac:(lia)). proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z X); [subst z; rewrite write_tape_same; symmetry; apply Ht; lia | apply write_tape_other; auto]. }
    destruct H1 as [P1 [S1 T1]].
    assert (Ht1 : forall z, X + 1 <= z < (X + 1) + Z.of_nat n -> sc1.(stape) z = true).
    { intros z Hz. rewrite T1. apply Ht. lia. }
    destruct (IHn (X + 1) sc1 P1 S1 Ht1) as [IHbd [IHp [IHs IHt]]].
    cbv zeta. rewrite srun_add, <- E1.
    splits.
    + intros k Hk. destruct (N.eq_0_gt_0_cases k) as [Hk0 | Hkgt].
      * subst k. rewrite srun_0, Hp. lia.
      * replace k with ((k - 1) + 1)%N by lia.
        rewrite srun_add, <- E1.
        pose proof (IHbd (k - 1)%N ltac:(lia)). lia.
    + rewrite IHp. lia.
    + exact IHs.
    + intro z. rewrite IHt, T1. reflexivity.
Qed.

Lemma ag2_init_2 : forall sc,
  sc.(spos) = 1720 ->
  sc.(sstate) = StA ->
  sc.(stape) 1719 = true ->
  sc.(stape) 1720 = true ->
  (forall k, (k < 2)%N -> 1719 <= (srun ag2 k sc).(spos)) /\
  let sc' := srun ag2 2 sc in
  sc'.(spos) = 1720 /\
  sc'.(sstate) = StA /\
  sc'.(stape) 1719 = true /\
  sc'.(stape) 1720 = false /\
  (forall z, z <> 1720 -> sc'.(stape) z = sc.(stape) z).
Proof.
  intros sc Hp Hs H19 H20.
  remember (srun ag2 1 sc) as sc1 eqn:E1.
  assert (H1 : sc1.(spos) = 1719 /\ sc1.(sstate) = StC /\ sc1.(stape) 1720 = false /\
               forall z, z <> 1720 -> sc1.(stape) z = sc.(stape) z).
  { rewrite E1, srun_1. unfold sstep, ag2, move_pos. rewrite Hp, Hs, H20. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H1 as [P1 [S1 [W1 O1]]].
  remember (srun ag2 2 sc) as sc2 eqn:E2.
  assert (H2 : sc2.(spos) = 1720 /\ sc2.(sstate) = StA /\ forall z, sc2.(stape) z = sc1.(stape) z).
  { assert (Hs2 : sc2 = sstep ag2 sc1) by (rewrite E2, E1; change 2%N with (N.succ 1); apply srun_succ).
    rewrite Hs2. unfold sstep, ag2, move_pos.
    assert (Hr1 : sc1.(stape) 1719 = true) by (rewrite O1 by lia; exact H19).
    rewrite P1, S1, Hr1. proj_eval.
    splits; [lia | reflexivity |].
    intro z. destruct (Z.eq_dec z 1719); [subst z; rewrite write_tape_same; symmetry; exact Hr1 | apply write_tape_other; auto]. }
  destruct H2 as [P2 [S2 T2]].
  cbv zeta. splits.
  - intros k Hk. assert (Hk_c : (k = 0 \/ k = 1)%N) by lia.
    destruct Hk_c as [-> | ->]; [rewrite srun_0; lia | rewrite <- E1; lia].
  - exact P2.
  - exact S2.
  - rewrite T2, O1 by lia. exact H19.
  - rewrite T2. exact W1.
  - intros z Hz. rewrite T2, O1 by auto. reflexivity.
Qed.

Definition K1 : N := (2 ^ 1374 - 172)%N.
Definition t_counter_sync : N := (S_rec 1375 + 4)%N.
Definition t_sync : N := (6872 + t_counter_sync)%N.
Definition jump_k : N := ((2 ^ 1375 - 2) / 6 - 20)%N.

Definition exact_halt_steps : N :=
  4397873831233679476816168179015300135585816001365597076883499356690186665385757906829986274227835544781589115804990020413062659163948473486133675604097473928756884549654396397906013959496506245396903094169696422471083393132585725532096421646923803885258657692727834993829094468258866647860150169182807287464686057402414864462182908171851541944008194384506196934762792580650559766666192331422423922540542059256397857%N.

Lemma K1_rel : t_counter_sync = (8 * K1 + 2)%N.
Proof. vm_compute. reflexivity. Qed.

Lemma pos2_sync_eq : 1720 + 2 * Z.of_N K1 = Z.of_N (2 ^ 1375) + 1376.
Proof. vm_compute. reflexivity. Qed.

Lemma sync_gap_eq : (Z.of_N (2 ^ 1375) + 1376) - 1378 = 120 + 6 * Z.of_N jump_k.
Proof. vm_compute. reflexivity. Qed.

Lemma total_steps_eq : (159 + (8 * jump_k + t_sync))%N = exact_halt_steps.
Proof. vm_compute. reflexivity. Qed.

Lemma bridge_to_sync :
  let c := run_N ag1 ag2 t_sync c0 in
  c.(pos1) = 1378 /\
  c.(pos2) = Z.of_N (2 ^ 1375) + 1376 /\
  c.(state1) = StB /\
  c.(state2) = StA /\
  (forall z, c.(pos1) <= z < c.(pos2) -> c.(tape) z = true) /\
  (forall z, c.(pos2) <= z -> c.(tape) z = false) /\
  (forall t, (t < t_sync)%N -> (run_N ag1 ag2 t c0).(pos1) <> (run_N ag1 ag2 t c0).(pos2)).
Proof.
  pose proof state_6872 as H6872.
  cbv zeta in H6872.
  remember (run_N ag1 ag2 6872 c0) as c6872 eqn:Ec6872.
  destruct H6872 as [Hp1 [Hp2 [Hs1 [Hs2 [Hz1373 [Htr [Hz1721 Hnc6872]]]]]]].
  set (sc1 := {| spos := -2; sstate := StC; stape := c6872.(tape) |}).
  set (sc2 := {| spos := 1720; sstate := StA; stape := c6872.(tape) |}).
  (* Agent 1 trace: ag1_counter 1375 + ag1_walk_ones 4 *)
  assert (Hc1_base : forall z, -2 <= z <= -2 + Z.of_nat 1375 -> sc1.(stape) z = false)
    by (intros z Hz; apply Hz1373; lia).
  destruct (ag1_counter 1375 sc1 eq_refl eq_refl Hc1_base) as [C1bd [C1p [C1s [C1f [C1t C1o]]]]].
  remember (srun ag1 (S_rec 1375) sc1) as sc1_mid eqn:Esc1_mid.
  assert (Hw1_base : forall z, 1374 <= z < 1374 + Z.of_nat 4 -> sc1_mid.(stape) z = true).
  { intros z Hz. rewrite C1o by (change (Z.of_nat 1375) with 1375; lia).
    apply Htr. lia. }
  assert (C1p' : sc1_mid.(spos) = 1374) by (rewrite C1p; change (Z.of_nat 1375) with 1375; lia).
  destruct (ag1_walk_ones 4 1374 sc1_mid C1p' C1s Hw1_base) as [W1bd [W1p [W1s W1t]]].
  assert (Hag1_bd : forall k, (k < t_counter_sync)%N -> (srun ag1 k sc1).(spos) <= 1377).
  { intros k Hk. unfold t_counter_sync in Hk.
    destruct (N.lt_ge_cases k (S_rec 1375)) as [Hk1 | Hk2].
    - pose proof (C1bd k Hk1). change (Z.of_nat 1375) with 1375 in *. lia.
    - replace k with ((k - S_rec 1375) + S_rec 1375)%N by lia.
      rewrite srun_add, <- Esc1_mid.
      pose proof (W1bd (k - S_rec 1375)%N ltac:(change (N.of_nat 4) with 4%N; lia)).
      change (Z.of_nat 4) with 4 in *. lia. }
  (* Agent 2 trace: ag2_init_2 + ag2_glider K1 1720 1720 *)
  destruct (ag2_init_2 sc2 eq_refl eq_refl (Htr 1719 ltac:(lia)) (Htr 1720 ltac:(lia)))
    as [I2bd [I2p [I2s [I2_19 [I2_20 I2o]]]]].
  remember (srun ag2 2 sc2) as sc2_mid eqn:Esc2_mid.
  assert (Hg2_lt : forall z, 1720 <= z < 1720 -> sc2_mid.(stape) z = true) by (intros; lia).
  assert (Hg2_ge : forall z, 1720 <= z -> sc2_mid.(stape) z = false).
  { intros z Hz. destruct (Z.eq_dec z 1720); [subst z; exact I2_20 |].
    rewrite I2o by auto. apply Hz1721. lia. }
  destruct (ag2_glider K1 1720 1720 sc2_mid ltac:(lia) I2p I2s Hg2_lt Hg2_ge)
    as [G2bd [G2p [G2s [G2below [G2tr G2ge]]]]].
  assert (Hag2_bd : forall k, (k < t_counter_sync)%N -> 1719 <= (srun ag2 k sc2).(spos)).
  { intros k Hk. rewrite K1_rel in Hk.
    destruct (N.lt_ge_cases k 2%N) as [Hk1 | Hk2].
    - apply I2bd; exact Hk1.
    - replace k with ((k - 2) + 2)%N by lia.
      rewrite srun_add, <- Esc2_mid.
      pose proof (G2bd (k - 2)%N ltac:(lia)). lia. }
  (* Combine via run_decouple *)
  assert (Hsep_b : 1377 < 1719) by lia.
  assert (Hdp1 : c6872.(pos1) = sc1.(spos)) by (unfold sc1; cbn [spos]; exact Hp1).
  assert (Hds1 : c6872.(state1) = sc1.(sstate)) by (unfold sc1; cbn [sstate]; exact Hs1).
  assert (Hdp2 : c6872.(pos2) = sc2.(spos)) by (unfold sc2; cbn [spos]; exact Hp2).
  assert (Hds2 : c6872.(state2) = sc2.(sstate)) by (unfold sc2; cbn [sstate]; exact Hs2).
  assert (Hdt1 : forall z, z <= 1377 -> c6872.(tape) z = sc1.(stape) z) by (intros; unfold sc1; cbn [stape]; reflexivity).
  assert (Hdt2 : forall z, 1719 <= z -> c6872.(tape) z = sc2.(stape) z) by (intros; unfold sc2; cbn [stape]; reflexivity).
  destruct (run_decouple ag1 ag2 1377 1719 t_counter_sync c6872 sc1 sc2
              Hsep_b Hdp1 Hds1 Hdp2 Hds2 Hdt1 Hdt2 Hag1_bd Hag2_bd)
    as [Dp1 [Ds1 [Dp2 [Ds2 [Dt1 [Dt2 [Dmid Dnc]]]]]]].
  assert (Hts_eq : t_sync = (t_counter_sync + 6872)%N) by (unfold t_sync; lia).
  cbv zeta. rewrite Hts_eq, run_N_add, <- Ec6872.
  assert (Hpos1 : (run_N ag1 ag2 t_counter_sync c6872).(pos1) = 1378).
  { rewrite Dp1. unfold t_counter_sync. replace (S_rec 1375 + 4)%N with (N.of_nat 4 + S_rec 1375)%N by (change (N.of_nat 4) with 4%N; lia).
    rewrite srun_add, <- Esc1_mid, W1p. change (Z.of_nat 4) with 4. lia. }
  assert (Hpos2 : (run_N ag1 ag2 t_counter_sync c6872).(pos2) = Z.of_N (2 ^ 1375) + 1376).
  { rewrite Dp2, K1_rel, srun_add, <- Esc2_mid, G2p, pos2_sync_eq. reflexivity. }
  splits.
  - exact Hpos1.
  - exact Hpos2.
  - rewrite Ds1. unfold t_counter_sync. replace (S_rec 1375 + 4)%N with (N.of_nat 4 + S_rec 1375)%N by (change (N.of_nat 4) with 4%N; lia).
    rewrite srun_add, <- Esc1_mid. exact W1s.
  - rewrite Ds2, K1_rel, srun_add, <- Esc2_mid. exact G2s.
  - intros z [Hz1 Hz2]. rewrite Hpos1 in Hz1. rewrite Hpos2 in Hz2.
    destruct (Z.lt_ge_cases z 1719) as [HzA | HzB].
    + rewrite Dmid by lia. apply Htr. lia.
    + rewrite Dt2 by lia. rewrite K1_rel, srun_add, <- Esc2_mid.
      destruct (Z.eq_dec z 1719).
      * subst z. rewrite G2below by lia. exact I2_19.
      * apply G2tr. rewrite pos2_sync_eq. lia.
  - intros z Hz. rewrite Hpos2 in Hz.
    assert (Hzge : 1719 <= z).
    { rewrite <- pos2_sync_eq in Hz. pose proof (N2Z.is_nonneg K1). lia. }
    rewrite Dt2 by lia. rewrite K1_rel, srun_add, <- Esc2_mid.
    apply G2ge. rewrite pos2_sync_eq. exact Hz.
  - intros t Ht.
    assert (Hnc_orig : forall k, (k < t_counter_sync)%N ->
              (run_N ag1 ag2 k (run_N ag1 ag2 6872 c0)).(pos1) <>
              (run_N ag1 ag2 k (run_N ag1 ag2 6872 c0)).(pos2))
      by (rewrite <- Ec6872; exact Dnc).
    eapply (no_coll_add ag1 ag2 t_counter_sync 6872 c0 Hnc6872 Hnc_orig t Ht).
Qed.

Lemma chase_cycle8 : forall P1 P2 c,
  c.(pos1) = P1 -> c.(state1) = StB ->
  c.(pos2) = P2 -> c.(state2) = StA ->
  P1 + 10 <= P2 ->
  (forall z, P1 <= z < P2 -> c.(tape) z = true) ->
  (forall z, P2 <= z -> c.(tape) z = false) ->
  (forall k, (k < 8)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  let c' := run_N ag1 ag2 8 c in
  c'.(pos1) = P1 + 8 /\ c'.(state1) = StB /\
  c'.(pos2) = P2 + 2 /\ c'.(state2) = StA /\
  (forall z, P1 + 8 <= z < P2 + 2 -> c'.(tape) z = true) /\
  (forall z, P2 + 2 <= z -> c'.(tape) z = false).
Proof.
  intros P1 P2 c Hp1 Hs1 Hp2 Hs2 Hsep Htlt Htge.
  set (sc1 := {| spos := P1; sstate := StB; stape := c.(tape) |}).
  set (sc2 := {| spos := P2; sstate := StA; stape := c.(tape) |}).
  assert (Hw1 : forall z, P1 <= z < P1 + Z.of_nat 8 -> sc1.(stape) z = true)
    by (intros z Hz; apply Htlt; change (Z.of_nat 8) with 8 in Hz; lia).
  destruct (ag1_walk_ones 8 P1 sc1 eq_refl eq_refl Hw1) as [Wbd [Wp [Ws Wt]]].
  destruct (ag2_cycle8 P2 sc2 eq_refl eq_refl Htge) as [Cbd [Cp [Cs [Cold [Cnew Cge]]]]].
  assert (Hbd1 : forall k, (k < 8)%N -> (srun ag1 k sc1).(spos) <= P1 + 7).
  { intros k Hk. change 8%N with (N.of_nat 8) in Hk. pose proof (Wbd k Hk).
    change (Z.of_nat 8) with 8 in *. lia. }
  assert (Hsep_c : P1 + 7 < P2) by lia.
  assert (Hdp1 : c.(pos1) = sc1.(spos)) by (unfold sc1; cbn [spos]; exact Hp1).
  assert (Hds1 : c.(state1) = sc1.(sstate)) by (unfold sc1; cbn [sstate]; exact Hs1).
  assert (Hdp2 : c.(pos2) = sc2.(spos)) by (unfold sc2; cbn [spos]; exact Hp2).
  assert (Hds2 : c.(state2) = sc2.(sstate)) by (unfold sc2; cbn [sstate]; exact Hs2).
  assert (Hdt1 : forall z, z <= P1 + 7 -> c.(tape) z = sc1.(stape) z) by (intros; unfold sc1; cbn [stape]; reflexivity).
  assert (Hdt2 : forall z, P2 <= z -> c.(tape) z = sc2.(stape) z) by (intros; unfold sc2; cbn [stape]; reflexivity).
  destruct (run_decouple ag1 ag2 (P1 + 7) P2 8 c sc1 sc2 Hsep_c Hdp1 Hds1 Hdp2 Hds2 Hdt1 Hdt2 Hbd1 Cbd)
    as [Dp1 [Ds1 [Dp2 [Ds2 [Dt1 [Dt2 [Dmid Dnc]]]]]]].
  cbv zeta. splits.
  - exact Dnc.
  - rewrite Dp1. change 8%N with (N.of_nat 8). rewrite Wp. change (Z.of_nat 8) with 8. lia.
  - rewrite Ds1. change 8%N with (N.of_nat 8). exact Ws.
  - rewrite Dp2. exact Cp.
  - rewrite Ds2. exact Cs.
  - intros z [Hz1 Hz2]. destruct (Z.lt_ge_cases z P2).
    + rewrite Dmid by lia. apply Htlt. lia.
    + rewrite Dt2 by lia. apply Cnew. lia.
  - intros z Hz. rewrite Dt2 by lia. apply Cge. exact Hz.
Qed.

Lemma chase_loop : forall j P1 P2 c,
  c.(pos1) = P1 -> c.(state1) = StB ->
  c.(pos2) = P2 -> c.(state2) = StA ->
  P2 - P1 = 120 + 6 * Z.of_N j ->
  (forall z, P1 <= z < P2 -> c.(tape) z = true) ->
  (forall z, P2 <= z -> c.(tape) z = false) ->
  (forall k, (k < 8 * j)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  let c' := run_N ag1 ag2 (8 * j) c in
  c'.(pos1) = P1 + 8 * Z.of_N j /\ c'.(state1) = StB /\
  c'.(pos2) = P2 + 2 * Z.of_N j /\ c'.(state2) = StA /\
  c'.(pos2) - c'.(pos1) = 120 /\
  (forall z, c'.(pos1) <= z < c'.(pos2) -> c'.(tape) z = true) /\
  (forall z, c'.(pos2) <= z -> c'.(tape) z = false).
Proof.
  intro j. induction j using N.peano_ind; intros P1 P2 c Hp1 Hs1 Hp2 Hs2 Hgap Htlt Htge.
  - rewrite N.mul_0_r, run_N_0. cbv zeta. splits; [intros; lia | lia | exact Hs1 | lia | exact Hs2 | lia | |].
    + intros z Hz. apply Htlt. lia.
    + intros z Hz. apply Htge. lia.
  - rewrite N2Z.inj_succ in Hgap.
    destruct (chase_cycle8 P1 P2 c Hp1 Hs1 Hp2 Hs2 ltac:(pose proof (N2Z.is_nonneg j); lia) Htlt Htge)
      as [Cnc [Cp1 [Cs1 [Cp2 [Cs2 [Ctlt Ctge]]]]]].
    set (c8 := run_N ag1 ag2 8 c) in *.
    destruct (IHj (P1 + 8) (P2 + 2) c8 Cp1 Cs1 Cp2 Cs2 ltac:(lia) Ctlt Ctge)
      as [Lnc [Lp1 [Ls1 [Lp2 [Ls2 [Lgap [Ltlt Ltge]]]]]]].
    replace (8 * N.succ j)%N with (8 * j + 8)%N by lia.
    cbv zeta. rewrite run_N_add. change (run_N ag1 ag2 8 c) with c8.
    rewrite N2Z.inj_succ.
    splits.
    + intros k Hk. eapply no_coll_add; [exact Cnc | exact Lnc | exact Hk].
    + rewrite Lp1. lia.
    + exact Ls1.
    + rewrite Lp2. lia.
    + exact Ls2.
    + exact Lgap.
    + exact Ltlt.
    + exact Ltge.
Qed.

Fixpoint bt_set_ones (lo : Z) (cnt : nat) (t : BTree) : BTree :=
  match cnt with
  | O => t
  | S n => bt_set_ones (lo + 1) n (bt_set (z_to_pos lo) true t)
  end.

Definition fc_final120 : FastConfig := {|
  fpos1 := -120; fpos2 := 0; fstate1 := StB; fstate2 := StA;
  ftape := bt_set_ones (-120) 120 BEmpty
|}.

Definition check_final_159 : bool :=
  let st158 := N.iter 158 (fast_step_chk_ge (-120)) (fc_final120, true) in
  let fc159 := fast_step (fst st158) in
  snd st158 &&
  (fc159.(fpos1) =? fc159.(fpos2)) &&
  check_all_true_nat (-120) 120 fc_final120.(ftape) &&
  bt_bounded_aux (-120) (-1) (fun q => q) fc_final120.(ftape).

Lemma final_159_ok : check_final_159 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma shift_cfg_pos1 : forall d c, (shift_cfg d c).(pos1) = c.(pos1) + d.
Proof. intros; reflexivity. Qed.

Lemma shift_cfg_pos2 : forall d c, (shift_cfg d c).(pos2) = c.(pos2) + d.
Proof. intros; reflexivity. Qed.

Lemma fc_to_cfg_pos1 : forall fc, (fc_to_cfg fc).(pos1) = fc.(fpos1).
Proof. intros; reflexivity. Qed.

Lemma fc_to_cfg_pos2 : forall fc, (fc_to_cfg fc).(pos2) = fc.(fpos2).
Proof. intros; reflexivity. Qed.

Lemma final_159 : forall c,
  c.(pos1) = c.(pos2) - 120 ->
  c.(state1) = StB ->
  c.(state2) = StA ->
  (forall z, c.(pos1) <= z < c.(pos2) -> c.(tape) z = true) ->
  (forall z, c.(pos2) <= z -> c.(tape) z = false) ->
  (run_N ag1 ag2 159 c).(pos1) = (run_N ag1 ag2 159 c).(pos2) /\
  forall t, (t < 159)%N -> (run_N ag1 ag2 t c).(pos1) <> (run_N ag1 ag2 t c).(pos2).
Proof.
  intros c Hsep Hs1 Hs2 Htlt Htge.
  pose proof final_159_ok as Hok. unfold check_final_159 in Hok.
  rewrite !andb_true_iff in Hok. destruct Hok as [[[Hsnd Hcol] Htr] Hbd].
  rewrite Z.eqb_eq in Hcol.
  destruct (fast_step_chk_ge_sound 158 (-120) fc_final120 true Hsnd) as [_ Hchk].
  assert (Hfc159 : fast_step (fst (N.iter 158 (fast_step_chk_ge (-120)) (fc_final120, true))) =
                   N.iter 159 fast_step fc_final120).
  { rewrite fast_step_chk_ge_fst. change 159%N with (N.succ 158). rewrite N.iter_succ. reflexivity. }
  rewrite Hfc159 in Hcol.
  remember (N.iter 159 fast_step fc_final120) as fc159 eqn:Efc159.
  assert (Hbd_cf : forall k, (k < 159)%N ->
            (-120 <= (run_N ag1 ag2 k (fc_to_cfg fc_final120)).(pos1) /\
             -120 <= (run_N ag1 ag2 k (fc_to_cfg fc_final120)).(pos2)) /\
            (run_N ag1 ag2 k (fc_to_cfg fc_final120)).(pos1) <>
            (run_N ag1 ag2 k (fc_to_cfg fc_final120)).(pos2)).
  { intros k Hk.
    pose proof (fast_run_sound k fc_final120) as [Rp1 Rp2 _ _ _].
    rewrite fc_to_cfg_pos1 in Rp1. rewrite fc_to_cfg_pos2 in Rp2.
    rewrite <- Rp1, <- Rp2.
    destruct (N.eq_0_gt_0_cases k) as [-> | Hkgt].
    - cbn [N.iter]. unfold fc_final120. cbn [fpos1 fpos2]. lia.
    - destruct (Hchk k ltac:(lia)) as [Hn [Hb1 Hb2]]. lia. }
  assert (Hbd_only : forall k, (k < 159)%N ->
            -120 <= (run_N ag1 ag2 k (fc_to_cfg fc_final120)).(pos1) /\
            -120 <= (run_N ag1 ag2 k (fc_to_cfg fc_final120)).(pos2))
    by (intros k Hk; apply (Hbd_cf k Hk)).
  assert (Hag : agree_ge (-120) (fc_to_cfg fc_final120).(tape) (shift_cfg (- c.(pos2)) c).(tape)).
  { intros z Hz. unfold fc_to_cfg, shift_cfg, shift_tape. cbn [tape ftape].
    destruct (Z.lt_ge_cases z 0).
    - rewrite (check_all_true_nat_sound 120 (-120) fc_final120.(ftape) z Htr) by (change (Z.of_nat 120) with 120; lia).
      symmetry. apply Htlt. lia.
    - rewrite (bt_bounded_sound (-120) (-1) fc_final120.(ftape) z Hbd) by lia.
      symmetry. apply Htge. lia. }
  assert (Hap1 : (fc_to_cfg fc_final120).(pos1) = (shift_cfg (- c.(pos2)) c).(pos1))
    by (unfold fc_to_cfg, shift_cfg, fc_final120; cbn [pos1 fpos1]; lia).
  assert (Hap2 : (fc_to_cfg fc_final120).(pos2) = (shift_cfg (- c.(pos2)) c).(pos2))
    by (unfold fc_to_cfg, shift_cfg, fc_final120; cbn [pos2 fpos2]; lia).
  assert (Has1 : (fc_to_cfg fc_final120).(state1) = (shift_cfg (- c.(pos2)) c).(state1))
    by (unfold fc_to_cfg, shift_cfg, fc_final120; cbn [state1 fstate1]; congruence).
  assert (Has2 : (fc_to_cfg fc_final120).(state2) = (shift_cfg (- c.(pos2)) c).(state2))
    by (unfold fc_to_cfg, shift_cfg, fc_final120; cbn [state2 fstate2]; congruence).
  destruct (run_N_agree_ge ag1 ag2 (-120) 159 (fc_to_cfg fc_final120) (shift_cfg (- c.(pos2)) c)
              Hap1 Hap2 Has1 Has2 Hag Hbd_only)
    as [Ap1 [Ap2 [_ [_ [_ [_ Aprev]]]]]].
  pose proof (run_N_shift ag1 ag2 (- c.(pos2)) 159 c) as [Sp1 Sp2 _ _ _].
  rewrite shift_cfg_pos1 in Sp1.
  rewrite shift_cfg_pos2 in Sp2.
  pose proof (fast_run_sound 159 fc_final120) as [F159p1 F159p2 _ _ _].
  rewrite <- Efc159 in F159p1, F159p2.
  rewrite fc_to_cfg_pos1 in F159p1. rewrite fc_to_cfg_pos2 in F159p2.
  split.
  - assert (Hlhs : (run_N ag1 ag2 159 c).(pos1) + - c.(pos2) = fc159.(fpos1))
      by (rewrite Sp1, <- Ap1, <- F159p1; reflexivity).
    assert (Hrhs : (run_N ag1 ag2 159 c).(pos2) + - c.(pos2) = fc159.(fpos2))
      by (rewrite Sp2, <- Ap2, <- F159p2; reflexivity).
    lia.
  - intros t Ht.
    pose proof (run_N_shift ag1 ag2 (- c.(pos2)) t c) as [Tp1 Tp2 _ _ _].
    rewrite shift_cfg_pos1 in Tp1.
    rewrite shift_cfg_pos2 in Tp2.
    destruct (Aprev t Ht) as [Bp1 Bp2].
    destruct (Hbd_cf t Ht) as [_ Hnc].
    lia.
Qed.

Theorem star_cet3_halts : forall undef : Transition,
  halts_at_exact (ag1_with undef) ag2 c0 exact_halt_steps.
Proof.
  intro undef.
  pose proof bridge_to_sync as Hbr.
  cbv zeta in Hbr.
  remember (run_N ag1 ag2 t_sync c0) as cs eqn:Ecs.
  destruct Hbr as [Bp1 [Bp2 [Bs1 [Bs2 [Btlt [Btge Bnc]]]]]].
  rewrite Bp1, Bp2 in Btlt. rewrite Bp2 in Btge.
  destruct (chase_loop jump_k 1378 (Z.of_N (2 ^ 1375) + 1376) cs Bp1 Bs1 Bp2 Bs2 sync_gap_eq Btlt Btge)
    as [Lnc [Lp1 [Ls1 [Lp2 [Ls2 [Lgap [Ltlt Ltge]]]]]]].
  remember (run_N ag1 ag2 (8 * jump_k) cs) as cl eqn:Ecl.
  assert (Hcl_gap : cl.(pos1) = cl.(pos2) - 120) by lia.
  destruct (final_159 cl Hcl_gap Ls1 Ls2 Ltlt Ltge) as [Fcol Fnc].
  assert (Hcol : collides_at ag1 ag2 c0 exact_halt_steps).
  { unfold collides_at. rewrite <- total_steps_eq, !run_N_add, <- Ecs, <- Ecl.
    exact Fcol. }
  assert (Hnc : forall t, (t < exact_halt_steps)%N -> ~ collides_at ag1 ag2 c0 t).
  { intros t Ht. unfold collides_at. rewrite <- total_steps_eq in Ht.
    assert (Hmid : forall k, (k < 8 * jump_k + t_sync)%N ->
              (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2)).
    { intros k Hk. eapply no_coll_add; [exact Bnc | | exact Hk].
      rewrite <- Ecs. exact Lnc. }
    eapply no_coll_add; [exact Hmid | | exact Ht].
    intro k. rewrite run_N_add, <- Ecs, <- Ecl. exact (Fnc k). }
  split.
  - unfold collides_at. destruct (run_N_undef_irrelevant undef exact_halt_steps) as [Heq _].
    rewrite Heq. exact Hcol.
  - intros t Ht Hc. unfold collides_at in Hc.
    destruct (run_N_undef_irrelevant undef t) as [Heq _].
    rewrite Heq in Hc. exact (Hnc t Ht Hc).
Qed.

Print Assumptions star_cet3_halts.
