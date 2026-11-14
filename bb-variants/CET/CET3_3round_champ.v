(**
  Formal Machine-Checked Proof of Normal Halting in Rocq 9.1
  Target Machine: 0LB---_1LC1RB_0RB0LC | 1RC1LC_1RA0RA_1LB0LB
  Model: Catch-Em-Turing CET(3), 2 agents, 3 states, 2 symbols.
  Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
  Normal Halting: exact first collision pos1(T) = pos2(T).

  Proves:
  1. For ANY transition placed in the unreachable slot (StA, true) (`---`),
     the machine NEVER executes (StA, true) at any step t >= 0.
  2. The machine executes 3 full binary-counter-vs-glider rounds with gap
     sequence [10, 10, 8] and collides at exact step
       T_halt = 70411 + 2^4697 + 15*K2 + 2^(4714 + 15*K2) + 15*K3
     where K2 = (2^4697 - 242) / 210 and K3 = (2^(4714 + 15*K2) - 128) / 210
     (~ 10^(10^1412.53) steps), decisively beating the previous CET(3) bound
     (~ 10^(10^13.45) steps).
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

(** * 2. Target Machine Definition: 0LB---_1LC1RB_0RB0LC | 1RC1LC_1RA0RA_1LB0LB *)

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
  | StA, false => {| write_sym := true;  move_dir := MoveR; next_state := StC |}
  | StA, true  => {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  | StB, false => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StB, true  => {| write_sym := false; move_dir := MoveR; next_state := StA |}
  | StC, false => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StC, true  => {| write_sym := false; move_dir := MoveL; next_state := StB |}
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

Fixpoint check_all_false_nat (lo : Z) (cnt : nat) (t : BTree) : bool :=
  match cnt with
  | O => true
  | S n => negb (bt_get (z_to_pos lo) t) && check_all_false_nat (lo + 1) n t
  end.

Lemma check_all_false_nat_sound : forall cnt lo t z,
  check_all_false_nat lo cnt t = true ->
  lo <= z < lo + Z.of_nat cnt ->
  bt_interp t z = false.
Proof.
  induction cnt; intros lo t z Hc Hz; simpl in Hc.
  - lia.
  - rewrite andb_true_iff in Hc. destruct Hc as [Hh Ht].
    rewrite negb_true_iff in Hh.
    destruct (Z.eq_dec z lo).
    + subst z. exact Hh.
    + apply (IHcnt (lo + 1) t z Ht). lia.
Qed.

(** * 6. Concrete Prefix Verification (Steps 0 .. 70429) *)

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

Lemma fc0_eq_c0 : cfg_eq (fc_to_cfg fc0) c0.
Proof.
  constructor; simpl; auto.
  intro z. unfold bt_interp, empty_tape. simpl. apply bt_get_empty.
Qed.

Definition check_fc_70429 (st : FastConfig * bool) : bool :=
  let (fc, ok) := st in
  ok &&
  (fc.(fpos1) =? 4657) &&
  (fc.(fpos2) =? 4697) &&
  (match fc.(fstate1), fc.(fstate2) with StC, StC => true | _, _ => false end) &&
  bt_bounded_aux (-1) 4698 (fun q => q) fc.(ftape) &&
  check_all_true_nat (-1) 4659%nat fc.(ftape) &&
  check_all_false_nat 4658 36%nat fc.(ftape) &&
  bt_get (z_to_pos 4694) fc.(ftape) &&
  negb (bt_get (z_to_pos 4695) fc.(ftape)) &&
  negb (bt_get (z_to_pos 4696) fc.(ftape)) &&
  negb (bt_get (z_to_pos 4697) fc.(ftape)) &&
  bt_get (z_to_pos 4698) fc.(ftape).

Lemma fc_70429_ok : check_fc_70429 (N.iter 70429 (fast_step_chk_ge (-2)) (fc0, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma check_states_CC : forall s1 s2,
  (match s1, s2 with StC, StC => true | _, _ => false end = true) ->
  s1 = StC /\ s2 = StC.
Proof. destruct s1, s2; simpl; intros H; try discriminate; auto. Qed.

Lemma state_70429 :
  let c := run_N ag1 ag2 70429 c0 in
  c.(pos1) = 4657 /\ c.(pos2) = 4697 /\ c.(state1) = StC /\ c.(state2) = StC /\
  c.(tape) (-2) = false /\
  (forall z, -1 <= z <= 4657 -> c.(tape) z = true) /\
  (forall z, 4658 <= z <= 4693 -> c.(tape) z = false) /\
  c.(tape) 4694 = true /\
  c.(tape) 4695 = false /\
  c.(tape) 4696 = false /\
  c.(tape) 4697 = false /\
  c.(tape) 4698 = true /\
  (forall z, 4699 <= z -> c.(tape) z = false) /\
  (forall t, (t < 70429)%N -> (run_N ag1 ag2 t c0).(pos1) <> (run_N ag1 ag2 t c0).(pos2)).
Proof.
  pose proof fc_70429_ok as Hok.
  remember (N.iter 70429 (fast_step_chk_ge (-2)) (fc0, true)) as st eqn:E.
  destruct st as [fc_end ok_end].
  unfold check_fc_70429 in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[[[[[[[Hok_b Hp1] Hp2] Hst] Hbd] Htr] Hfl] Ht94] Hf95] Hf96] Hf97] Ht98].
  rewrite Z.eqb_eq in Hp1, Hp2.
  rewrite negb_true_iff in Hf95, Hf96, Hf97.
  apply check_states_CC in Hst. destruct Hst as [Hs1 Hs2].
  assert (Hfc : fc_end = N.iter 70429 fast_step fc0).
  { pose proof (fast_step_chk_ge_fst 70429 (-2) fc0 true) as Hfst.
    rewrite <- E in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 70429 (fast_step_chk_ge (-2)) (fc0, true)) = true)
    by (rewrite <- E; exact Hok_b).
  clear E Hok_b.
  pose proof (fast_run_sound 70429 fc0) as Hrun.
  pose proof (run_N_proper ag1 ag2 70429 _ _ fc0_eq_c0) as Hprop.
  assert (Heq : cfg_eq (fc_to_cfg fc_end) (run_N ag1 ag2 70429 c0))
    by (rewrite Hfc; eapply cfg_eq_trans; [exact Hrun | exact Hprop]).
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
  split; [rewrite <- Etp; eapply bt_bounded_sound; [exact Hbd | lia] |].
  split; [intros z Hz; rewrite <- Etp; eapply check_all_true_nat_sound; [exact Htr |];
          change (Z.of_nat 4659%nat) with 4659; lia |].
  split; [intros z Hz; rewrite <- Etp; eapply check_all_false_nat_sound; [exact Hfl |];
          change (Z.of_nat 36%nat) with 36; lia |].
  split; [rewrite <- Etp; exact Ht94 |].
  split; [rewrite <- Etp; exact Hf95 |].
  split; [rewrite <- Etp; exact Hf96 |].
  split; [rewrite <- Etp; exact Hf97 |].
  split; [rewrite <- Etp; exact Ht98 |].
  split; [intros z Hz; rewrite <- Etp; eapply bt_bounded_sound; [exact Hbd | lia] |].
  intros t Ht.
  destruct (N.eq_0_gt_0_cases t) as [Ht0 | Htgt0].
  - subst t. rewrite run_N_0. unfold c0; simpl; lia.
  - destruct (fast_step_chk_ge_sound 70429 (-2) fc0 true Hsnd) as [_ Hchk].
    destruct (Hchk t ltac:(lia)) as [Hneq _].
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

Lemma S_rec_closed : forall m : nat,
  Z.of_N (S_rec m) = 2 ^ (Z.of_nat m + 2) - Z.of_nat m - 3.
Proof.
  induction m.
  - reflexivity.
  - change (S_rec (S m)) with (2 * S_rec m + N.of_nat m + 2)%N.
    rewrite !N2Z.inj_add, N2Z.inj_mul, nat_N_Z, Nat2Z.inj_succ.
    rewrite IHm.
    assert (Hp : 2 ^ (Z.succ (Z.of_nat m) + 2) = 2 * 2 ^ (Z.of_nat m + 2)).
    { replace (Z.succ (Z.of_nat m) + 2) with (1 + (Z.of_nat m + 2)) by lia.
      rewrite Z.pow_add_r by lia. reflexivity. }
    rewrite Hp. simpl Z.of_N. lia.
Qed.

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
    set (sc2 := srun ag1 1%N sc1).
    assert (H2 : sc2.(spos) = -2 + Z.of_nat m /\ sc2.(sstate) = StC /\
                 sc2.(stape) (-1 + Z.of_nat m) = true /\
                 (forall z, z <> -1 + Z.of_nat m -> sc2.(stape) z = sc1.(stape) z)).
    { unfold sc2. step1_eval. rewrite P1, S1, O1 by lia.
      rewrite (Ht (-1 + Z.of_nat m)) by lia. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same |].
      intros z Hz. apply write_tape_other. auto. }
    destruct H2 as [P2 [S2 [W2 O2]]].
    assert (Ht2 : forall z, -1 <= z <= -2 + Z.of_nat m -> sc2.(stape) z = true)
      by (intros z Hz; rewrite O2 by lia; apply T1; auto).
    destruct (ag1_wipe_left m sc2 P2 S2 Ht2) as [Bd3 [P3 [S3 [T3 O3]]]].
    set (sc3 := srun ag1 (N.of_nat m) sc2) in *.
    assert (Ht3 : forall z, -2 <= z <= -2 + Z.of_nat m -> sc3.(stape) z = false).
    { intros z Hz. destruct (Z.eq_dec z (-2)).
      - subst z. rewrite O3 by lia. rewrite O2 by lia. exact F1.
      - apply T3. lia. }
    destruct (IHm sc3 P3 S3 Ht3) as [Bd4 [P4 [S4 [F4 [T4 O4]]]]].
    set (sc4 := srun ag1 t1 sc3) in *.
    set (sc5 := srun ag1 1%N sc4).
    assert (H5 : sc5.(spos) = -1 + Z.succ (Z.of_nat m) /\ sc5.(sstate) = StB /\
                 sc5.(stape) (-1 + Z.of_nat m) = true /\
                 (forall z, z <> -1 + Z.of_nat m -> sc5.(stape) z = sc4.(stape) z)).
    { unfold sc5. step1_eval.
      rewrite P4, S4.
      assert (Hr4 : sc4.(stape) (-1 + Z.of_nat m) = true)
        by (rewrite O4 by lia; rewrite O3 by lia; exact W2).
      rewrite Hr4. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same |].
      intros z Hz. apply write_tape_other. auto. }
    destruct H5 as [P5 [S5 [W5 O5]]].
    assert (Htot : (2 * t1 + N.of_nat m + 2 = 1 + (t1 + (N.of_nat m + (1 + t1))))%N)
      by (unfold t1; lia).
    rewrite Htot.
    assert (Hsc5 : srun ag1 (1 + (t1 + (N.of_nat m + (1 + t1)))) sc = sc5)
      by (rewrite !srun_add; reflexivity).
    splits.
    + intros k Hk.
      destruct (N.lt_ge_cases k t1) as [Hk1 | Hge1].
      * pose proof (Bd1 k Hk1). lia.
      * destruct (N.lt_ge_cases k (1 + t1)) as [Hk2 | Hge2].
        -- replace k with t1 by lia. change (srun ag1 t1 sc) with sc1. rewrite P1. lia.
        -- destruct (N.lt_ge_cases k (N.of_nat m + (1 + t1))) as [Hk3 | Hge3].
           ++ replace k with ((k - (1 + t1)) + (1 + t1))%N by lia.
              rewrite !srun_add. change (srun ag1 1 (srun ag1 t1 sc)) with sc2.
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
    assert (Ht1 : forall z, X + 1 <= z < (X + 1) + Z.of_nat n -> sc1.(stape) z = true)
      by (intros z Hz; rewrite T1; apply Ht; lia).
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

Definition fs_ag2_0 : FastSingle := {|
  fspos := 0; fsstate := StC; fstape := bt_set (z_to_pos 1) true BEmpty
|}.

Definition check_ag2_15 : bool :=
  let fs := N.iter 15 (fast_sstep ag2) fs_ag2_0 in
  (fs.(fspos) =? 1) &&
  (match fs.(fsstate) with StC => true | _ => false end) &&
  bt_get (z_to_pos (-2)) fs.(fstape) &&
  negb (bt_get (z_to_pos (-1)) fs.(fstape)) &&
  negb (bt_get (z_to_pos 0) fs.(fstape)) &&
  negb (bt_get (z_to_pos 1) fs.(fstape)) &&
  bt_get (z_to_pos 2) fs.(fstape) &&
  bt_bounded_aux (-2) 2 (fun q => q) fs.(fstape).

Lemma ag2_15_ok : check_ag2_15 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ag2_cycle15 : forall X sc,
  sc.(spos) = X ->
  sc.(sstate) = StC ->
  sc.(stape) (X - 2) = false ->
  sc.(stape) (X - 1) = false ->
  sc.(stape) X = false ->
  sc.(stape) (X + 1) = true ->
  (forall z, X + 2 <= z -> sc.(stape) z = false) ->
  (forall k, (k < 15)%N -> X - 2 <= (srun ag2 k sc).(spos)) /\
  let sc' := srun ag2 15 sc in
  sc'.(spos) = X + 1 /\
  sc'.(sstate) = StC /\
  (forall z, z < X - 2 -> sc'.(stape) z = sc.(stape) z) /\
  sc'.(stape) (X - 2) = true /\
  sc'.(stape) (X - 1) = false /\
  sc'.(stape) X = false /\
  sc'.(stape) (X + 1) = false /\
  sc'.(stape) (X + 2) = true /\
  (forall z, X + 3 <= z -> sc'.(stape) z = false).
Proof.
  intros X sc Hp Hs Hm2 Hm1 H0 H1 Hge.
  set (sc_base := fs_to_sc fs_ag2_0).
  assert (Hbase_ge : agree_ge (-2) sc_base.(stape) (shift_sc (- X) sc).(stape)).
  { intros z Hz. unfold sc_base, fs_to_sc, fs_ag2_0, shift_sc, shift_tape, bt_interp. cbn [stape fstape].
    destruct (Z.eqb_spec z 1).
    - subst z. replace (1 - - X) with (X + 1) by lia. rewrite bt_get_set_same. symmetry; exact H1.
    - assert (Hz_b : bt_get (z_to_pos z) (bt_set (z_to_pos 1) true BEmpty) = false).
      { rewrite bt_get_set_diff; [apply bt_get_empty |].
        intro Heq. apply n. rewrite <- (z_pos_z z), <- (z_pos_z 1), Heq. reflexivity. }
      rewrite Hz_b.
      assert (Hz_cases : z = -2 \/ z = -1 \/ z = 0 \/ 2 <= z) by lia.
      destruct Hz_cases as [-> | [-> | [-> | H2]]].
      + replace (-2 - - X) with (X - 2) by lia. symmetry; exact Hm2.
      + replace (-1 - - X) with (X - 1) by lia. symmetry; exact Hm1.
      + replace (0 - - X) with X by lia. symmetry; exact H0.
      + symmetry; apply Hge; lia. }
  assert (Hbase_bd : forall k, (k < 15)%N -> -2 <= (srun ag2 k sc_base).(spos)).
  { intros k Hk.
    pose proof (fast_srun_sound ag2 k fs_ag2_0) as [Sp _ _].
    change (srun ag2 k sc_base) with (srun ag2 k (fs_to_sc fs_ag2_0)).
    rewrite <- Sp. change (spos (fs_to_sc (N.iter k (fast_sstep ag2) fs_ag2_0))) with (N.iter k (fast_sstep ag2) fs_ag2_0).(fspos).
    assert (Hk_cases : (k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7\/k=8\/k=9\/k=10\/k=11\/k=12\/k=13\/k=14)%N) by lia.
    repeat match goal with H : (_ \/ _)%N |- _ => destruct H as [-> | H] end;
      try subst k; vm_compute; discriminate. }
  destruct (srun_agree_ge ag2 (-2) 15 sc_base (shift_sc (- X) sc)
              ltac:(simpl; lia) ltac:(simpl; congruence) Hbase_ge Hbase_bd)
    as [Ap [As [Aag _]]].
  pose proof ag2_15_ok as Hok. unfold check_ag2_15 in Hok.
  remember (N.iter 15 (fast_sstep ag2) fs_ag2_0) as fs15 eqn:Efs15.
  rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[[[Bp Bs] Bm2] Bm1] B0] B1] B2] Bbd].
  rewrite Z.eqb_eq in Bp. rewrite negb_true_iff in Bm1, B0, B1.
  assert (Bs' : fs15.(fsstate) = StC) by (destruct (fs15.(fsstate)); try discriminate; reflexivity).
  pose proof (fast_srun_sound ag2 15 fs_ag2_0) as [F15p F15s F15t].
  rewrite <- Efs15 in F15p, F15s, F15t.
  cbn [spos sstate stape fs_to_sc] in F15p, F15s, F15t.
  cbv zeta.
  assert (Hbd_orig : forall k, (k < 15)%N -> X - 2 <= (srun ag2 k sc).(spos)).
  { intros k Hk.
    assert (Hbd_k : forall j, (j < k)%N -> -2 <= (srun ag2 j sc_base).(spos))
      by (intros j Hj; apply Hbase_bd; lia).
    destruct (srun_agree_ge ag2 (-2) k sc_base (shift_sc (- X) sc)
                ltac:(simpl; lia) ltac:(simpl; congruence) Hbase_ge Hbd_k) as [Kp _].
    pose proof (srun_shift ag2 (- X) k sc) as [Sp _ _].
    simpl in Sp. pose proof (Hbase_bd k Hk). lia. }
  assert (Hread : forall z, -2 <= z -> (srun ag2 15 sc).(stape) (X + z) = bt_interp fs15.(fstape) z).
  { intros z Hz. pose proof (srun_shift ag2 (- X) 15 sc) as [_ _ St].
    specialize (St z). unfold shift_sc, shift_tape in St. simpl in St.
    replace (z - - X) with (X + z) in St by lia.
    rewrite <- St, <- (Aag z Hz). symmetry. exact (F15t z). }
  splits.
  - exact Hbd_orig.
  - pose proof (srun_shift ag2 (- X) 15 sc) as [Sp _ _]. simpl in Sp. lia.
  - pose proof (srun_shift ag2 (- X) 15 sc) as [_ Ss _]. simpl in Ss. congruence.
  - intros z Hz.
    destruct (srun_agree_ge ag2 (X - 2) 15 sc sc eq_refl eq_refl ltac:(intros ? _; reflexivity) Hbd_orig)
      as [_ [_ [_ Hlt]]].
    apply Hlt; exact Hz.
  - replace (X - 2) with (X + (-2)) by lia. rewrite Hread by lia. exact Bm2.
  - replace (X - 1) with (X + (-1)) by lia. rewrite Hread by lia. exact Bm1.
  - replace X with (X + 0) by lia. rewrite Hread by lia. exact B0.
  - rewrite Hread by lia. exact B1.
  - rewrite Hread by lia. exact B2.
  - intros z Hz. replace z with (X + (z - X)) by lia. rewrite Hread by lia.
    eapply bt_bounded_sound; [exact Bbd | lia].
Qed.

Lemma ag2_glider : forall K lo X sc,
  lo <= X - 2 ->
  sc.(spos) = X ->
  sc.(sstate) = StC ->
  (forall z, lo <= z < X - 2 -> sc.(stape) z = true) ->
  sc.(stape) (X - 2) = false ->
  sc.(stape) (X - 1) = false ->
  sc.(stape) X = false ->
  sc.(stape) (X + 1) = true ->
  (forall z, X + 2 <= z -> sc.(stape) z = false) ->
  (forall k, (k < 15 * K)%N -> X - 2 <= (srun ag2 k sc).(spos)) /\
  let sc' := srun ag2 (15 * K) sc in
  sc'.(spos) = X + Z.of_N K /\
  sc'.(sstate) = StC /\
  (forall z, z < lo -> sc'.(stape) z = sc.(stape) z) /\
  (forall z, lo <= z < X + Z.of_N K - 2 -> sc'.(stape) z = true) /\
  sc'.(stape) (X + Z.of_N K - 2) = false /\
  sc'.(stape) (X + Z.of_N K - 1) = false /\
  sc'.(stape) (X + Z.of_N K) = false /\
  sc'.(stape) (X + Z.of_N K + 1) = true /\
  (forall z, X + Z.of_N K + 2 <= z -> sc'.(stape) z = false).
Proof.
  intro K. induction K using N.peano_ind; intros lo X sc Hlo Hp Hs Hlt Hm2 Hm1 H0 H1 Hge.
  - rewrite N.mul_0_r, srun_0. cbv zeta. splits; [intros; lia | lia | exact Hs | auto | | | | | |];
      try (intros z Hz; apply Hlt; lia);
      try (replace (X + 0 - 2) with (X - 2) by lia; exact Hm2);
      try (replace (X + 0 - 1) with (X - 1) by lia; exact Hm1);
      try (replace (X + 0) with X by lia; exact H0);
      try (replace (X + 0 + 1) with (X + 1) by lia; exact H1);
      try (intros z Hz; apply Hge; lia).
  - replace (15 * N.succ K)%N with (15 + 15 * K)%N by lia.
    rewrite N2Z.inj_succ.
    destruct (IHK lo X sc Hlo Hp Hs Hlt Hm2 Hm1 H0 H1 Hge)
      as [IHbd [IHp [IHs [IHbelow [IHlt [IHm2 [IHm1 [IH0 [IH1 IHge']]]]]]]]].
    set (scK := srun ag2 (15 * K) sc) in *.
    set (XK := X + Z.of_N K) in *.
    destruct (ag2_cycle15 XK scK IHp IHs IHm2 IHm1 IH0 IH1 IHge')
      as [Cybd [Cyp [Cys [Cyold [Cym2 [Cym1 [Cy0 [Cy1 [Cy2 Cyge]]]]]]]]].
    cbv zeta. splits.
    + intros k Hk. destruct (N.lt_ge_cases k (15 * K)%N) as [Hk1 | Hk2].
      * apply IHbd; exact Hk1.
      * replace k with ((k - 15 * K) + 15 * K)%N by lia.
        rewrite srun_add. change (srun ag2 (15 * K) sc) with scK.
        pose proof (Cybd (k - 15 * K)%N ltac:(lia)). unfold XK in *. lia.
    + rewrite srun_add. change (srun ag2 (15 * K) sc) with scK. rewrite Cyp. unfold XK. lia.
    + rewrite srun_add. change (srun ag2 (15 * K) sc) with scK. exact Cys.
    + intros z Hz. rewrite srun_add. change (srun ag2 (15 * K) sc) with scK.
      rewrite Cyold by (unfold XK; lia). apply IHbelow; auto.
    + intros z Hz. rewrite srun_add. change (srun ag2 (15 * K) sc) with scK.
      destruct (Z.lt_ge_cases z (XK - 2)).
      * rewrite Cyold by auto. apply IHlt. unfold XK in *. lia.
      * replace z with (XK - 2) by (unfold XK in *; lia). exact Cym2.
    + rewrite srun_add. change (srun ag2 (15 * K) sc) with scK.
      replace (X + Z.succ (Z.of_N K) - 2) with (XK - 1) by (unfold XK; lia). exact Cym1.
    + rewrite srun_add. change (srun ag2 (15 * K) sc) with scK.
      replace (X + Z.succ (Z.of_N K) - 1) with XK by (unfold XK; lia). exact Cy0.
    + rewrite srun_add. change (srun ag2 (15 * K) sc) with scK.
      replace (X + Z.succ (Z.of_N K)) with (XK + 1) by (unfold XK; lia). exact Cy1.
    + rewrite srun_add. change (srun ag2 (15 * K) sc) with scK.
      replace (X + Z.succ (Z.of_N K) + 1) with (XK + 2) by (unfold XK; lia). exact Cy2.
    + intros z Hz. rewrite srun_add. change (srun ag2 (15 * K) sc) with scK.
      apply Cyge. unfold XK in *. lia.
Qed.

(** * 9. Generic Round Counter + Chase + Bounce + Final Collision *)

Lemma round_decouple_and_chase :
  forall c (X1 X2 : Z) (W : nat) (n_cyc K : N) (G_next : Z),
  148 <= X1 ->
  X1 + 40 = X2 ->
  (W <= 10)%nat ->
  (12 <= n_cyc)%N ->
  G_next >= 8 ->
  N.of_nat (Z.to_nat (X1 + 2)) + S_rec (Z.to_nat (X2 - 2)) + N.of_nat W = (15 * n_cyc)%N ->
  X2 + Z.of_N n_cyc - ((X2 - 3) + Z.of_nat W) = G_next + 14 * Z.of_N K ->
  c.(pos1) = X1 -> c.(state1) = StC ->
  c.(pos2) = X2 -> c.(state2) = StC ->
  c.(tape) (-2) = false ->
  (forall z, -1 <= z <= X1 -> c.(tape) z = true) ->
  (forall z, X1 + 1 <= z <= X2 - 4 -> c.(tape) z = false) ->
  c.(tape) (X2 - 3) = true ->
  c.(tape) (X2 - 2) = false ->
  c.(tape) (X2 - 1) = false ->
  c.(tape) X2 = false ->
  c.(tape) (X2 + 1) = true ->
  (forall z, X2 + 2 <= z -> c.(tape) z = false) ->
  let T_round := (15 * n_cyc + 15 * K)%N in
  let X_end := X2 - 3 + Z.of_nat W + 15 * Z.of_N K in
  (forall t, (t < T_round)%N -> (run_N ag1 ag2 t c).(pos1) <> (run_N ag1 ag2 t c).(pos2)) /\
  let c' := run_N ag1 ag2 T_round c in
  c'.(pos1) = X_end /\ c'.(state1) = StB /\
  c'.(pos2) = X_end + G_next /\ c'.(state2) = StC /\
  c'.(tape) (-2) = false /\
  (forall z, -1 <= z <= X_end + G_next - 3 -> c'.(tape) z = true) /\
  c'.(tape) (X_end + G_next - 2) = false /\
  c'.(tape) (X_end + G_next - 1) = false /\
  c'.(tape) (X_end + G_next) = false /\
  c'.(tape) (X_end + G_next + 1) = true /\
  (forall z, X_end + G_next + 2 <= z -> c'.(tape) z = false).
Proof.
  intros c X1 X2 W n_cyc K G_next HX1 HX2 HW Hncyc HG Htot_eq Hgap_eq
         Hp1 Hs1 Hp2 Hs2 Hm2 Ht1 Hf_mid Hm3 Hm2' Hm1' H0' H1' Hge'.
  set (nw := Z.to_nat (X1 + 2)).
  set (m := Z.to_nat (X2 - 2)).
  assert (Hnw : Z.of_nat nw = X1 + 2) by (unfold nw; lia).
  assert (Hm : Z.of_nat m = X2 - 2) by (unfold m; lia).
  assert (Hnw_ge : (150 <= nw)%nat) by lia.
  (* Sub-phase A: 150 steps = ag1 wipes 150 left, ag2 runs 10 glider cycles *)
  set (sc1 := {| spos := X1; sstate := StC; stape := c.(tape) |}).
  set (sc2 := {| spos := X2; sstate := StC; stape := c.(tape) |}).
  assert (Hwl_base : forall z, -1 <= z <= -2 + Z.of_nat nw -> sc1.(stape) z = true)
    by (intros z Hz; apply Ht1; lia).
  (* First decompose ag1_wipe_left nw as 150 steps + (nw - 150) steps! *)
  set (sc1_A_pre := sc1).
  (* Run ag1 for (nw - 150) steps AFTER? Wait: wiping from X1 goes X1 -> X1 - 150, so run 150 steps on shifted? No: ag1_wipe_left works directly on (nw - 150)? No, ag1_wipe_left wipes ALL the way to -2!
     Instead, run ag1_wipe_left on shift_sc (-(X1 + 2 - 150)) sc1 for 150 steps, OR just use srun_agree_ge at -2?
     Better: prove wipe_left_step_bd inside ag1_wipe_left by applying ag1_wipe_left with m=150 on shifted tape! *)
  assert (Hwl150 : (forall k, (k < 150)%N -> X1 - 149 <= (srun ag1 k sc1).(spos) <= X1) /\
                   let sc1a := srun ag1 150 sc1 in
                   sc1a.(spos) = X1 - 150 /\
                   sc1a.(sstate) = StC /\
                   (forall z, X1 - 149 <= z <= X1 -> sc1a.(stape) z = false) /\
                   (forall z, z < X1 - 149 \/ z > X1 -> sc1a.(stape) z = sc1.(stape) z)).
  { set (d := -(X1 + 2 - 150)).
    set (sc_sh := shift_sc d sc1).
    assert (Hshp : sc_sh.(spos) = -2 + Z.of_nat 150) by (unfold sc_sh, d, sc1; simpl; lia).
    assert (Hsht : forall z, -1 <= z <= -2 + Z.of_nat 150 -> sc_sh.(stape) z = true).
    { intros z Hz. unfold sc_sh, shift_tape, sc1, d; simpl. apply Ht1. lia. }
    destruct (ag1_wipe_left 150%nat sc_sh Hshp eq_refl Hsht) as [Wbd [Wp [Ws [Wf Wo]]]].
    change (N.of_nat 150) with 150%N in *.
    cbv zeta. splits.
    - intros k Hk. pose proof (srun_shift ag1 d k sc1) as [Sp _ _].
      simpl in Sp. pose proof (Wbd k Hk). unfold sc_sh, d in *. lia.
    - pose proof (srun_shift ag1 d 150 sc1) as [Sp _ _].
      simpl in Sp. unfold sc_sh, d in *. lia.
    - pose proof (srun_shift ag1 d 150 sc1) as [_ Ss _].
      simpl in Ss. unfold sc_sh in *. congruence.
    - intros z Hz. pose proof (srun_shift ag1 d 150 sc1) as [_ _ St].
      specialize (St (z + d)). unfold shift_sc, shift_tape in St. simpl in St.
      replace (z + d - d) with z in St by lia. rewrite <- St. apply Wf. unfold d in *. lia.
    - intros z Hz. pose proof (srun_shift ag1 d 150 sc1) as [_ _ St].
      specialize (St (z + d)). unfold shift_sc, shift_tape in St. simpl in St.
      replace (z + d - d) with z in St by lia. rewrite <- St.
      rewrite Wo by (unfold d in *; lia). unfold sc_sh, shift_tape. simpl.
      replace (z + d - d) with z by lia. reflexivity. }
  destruct Hwl150 as [A1bd [A1p [A1s [A1f A1o]]]].
  assert (Hgl10_lt : forall z, X2 - 2 <= z < X2 - 2 -> sc2.(stape) z = true) by (intros; lia).
  destruct (ag2_glider 10 X2 X2 sc2 ltac:(lia) eq_refl eq_refl Hgl10_lt Hm2' Hm1' H0' H1' Hge')
    as [A2bd [A2p [A2s [A2old [A2lt [A2m2 [A2m1 [A2_0 [A2_1 A2ge]]]]]]]]].
  change (15 * 10)%N with 150%N in *.
  assert (HA_bd1 : forall k, (k < 150)%N -> (srun ag1 k sc1).(spos) <= X1)
    by (intros k Hk; pose proof (A1bd k Hk); lia).
  destruct (run_decouple ag1 ag2 X1 (X2 - 2) 150 c sc1 sc2 ltac:(lia)
              Hp1 Hs1 Hp2 Hs2 ltac:(intros; reflexivity) ltac:(intros; reflexivity)
              HA_bd1 A2bd)
    as [DAp1 [DAs1 [DAp2 [DAs2 [DAt1 [DAt2 [DAmid DAnc]]]]]]].
  set (cA := run_N ag1 ag2 150 c) in *.
  (* Now prove cA invariants for Sub-phase B: (15 * n_cyc - 150) steps! *)
  set (nB := (15 * n_cyc - 150)%N).
  assert (HnB_eq : (15 * n_cyc = nB + 150)%N) by (unfold nB; lia).
  assert (HnB_ag1 : nB = (N.of_nat (nw - 150) + S_rec m + N.of_nat W)%N).
  { unfold nB. change 150%N with (N.of_nat 150%nat) in *.
    rewrite <- Htot_eq. lia. }
  set (sc1B := {| spos := cA.(pos1); sstate := cA.(state1); stape := cA.(tape) |}).
  set (sc2B := {| spos := cA.(pos2); sstate := cA.(state2); stape := cA.(tape) |}).
  assert (HB_ag1_wipe_t : forall z, -1 <= z <= -2 + Z.of_nat (nw - 150) -> sc1B.(stape) z = true).
  { intros z Hz. unfold sc1B. simpl. rewrite DAt1 by lia. rewrite A1o by lia. apply Ht1. lia. }
  destruct (ag1_wipe_left (nw - 150) sc1B ltac:(unfold sc1B; simpl; rewrite DAp1, A1p; lia)
              ltac:(unfold sc1B; simpl; rewrite DAs1, A1s; reflexivity) HB_ag1_wipe_t)
    as [B1w_bd [B1w_p [B1w_s [B1w_f B1w_o]]]].
  set (sc1B_mid1 := srun ag1 (N.of_nat (nw - 150)) sc1B) in *.
  assert (HB_ag1_cnt_t : forall z, -2 <= z <= -2 + Z.of_nat m -> sc1B_mid1.(stape) z = false).
  { intros z Hz.
    destruct (Z.lt_ge_cases z (-1)).
    - replace z with (-2) by lia. rewrite B1w_o by lia.
      unfold sc1B; simpl. rewrite DAt1 by lia. rewrite A1o by lia. exact Hm2.
    - destruct (Z.le_gt_cases z (X1 - 150)).
      + apply B1w_f. lia.
      + rewrite B1w_o by lia. unfold sc1B; simpl.
        destruct (Z.le_gt_cases z X1).
        * rewrite DAt1 by lia. apply A1f. lia.
        * rewrite DAmid by lia. apply Hf_mid. lia. }
  destruct (ag1_counter m sc1B_mid1 B1w_p B1w_s HB_ag1_cnt_t)
    as [B1c_bd [B1c_p [B1c_s [B1c_m2 [B1c_t B1c_o]]]]].
  set (sc1B_mid2 := srun ag1 (S_rec m) sc1B_mid1) in *.
  assert (HB_ag1_wlk_t : forall z, (X2 - 3) <= z < (X2 - 3) + Z.of_nat W -> sc1B_mid2.(stape) z = true).
  { intros z Hz. rewrite B1c_o by lia.
    unfold sc1B; simpl.
    destruct (Z.eq_dec z (X2 - 3)).
    - subst z. rewrite DAmid by lia. exact Hm3.
    - rewrite DAt2 by lia. apply A2lt. lia. }
  destruct (ag1_walk_ones W (X2 - 3) sc1B_mid2 ltac:(rewrite B1c_p; lia) B1c_s HB_ag1_wlk_t)
    as [B1k_bd [B1k_p [B1k_s B1k_t]]].
  assert (HB_ag1_all_bd : forall k, (k < nB)%N -> (srun ag1 k sc1B).(spos) <= X2 + 6).
  { intros k Hk. rewrite HnB_ag1 in Hk.
    destruct (N.lt_ge_cases k (N.of_nat (nw - 150))) as [Hk1 | Hk1ge].
    - pose proof (B1w_bd k Hk1). lia.
    - destruct (N.lt_ge_cases k (S_rec m + N.of_nat (nw - 150))) as [Hk2 | Hk2ge].
      + replace k with ((k - N.of_nat (nw - 150)) + N.of_nat (nw - 150))%N by lia.
        rewrite srun_add. change (srun ag1 (N.of_nat (nw - 150)) sc1B) with sc1B_mid1.
        pose proof (B1c_bd (k - N.of_nat (nw - 150))%N ltac:(lia)). lia.
      + replace k with ((k - (S_rec m + N.of_nat (nw - 150))) + (S_rec m + N.of_nat (nw - 150)))%N by lia.
        replace (S_rec m + N.of_nat (nw - 150))%N with (S_rec m + N.of_nat (nw - 150))%N by reflexivity.
        rewrite srun_add. rewrite (srun_add ag1 (S_rec m)).
        change (srun ag1 (N.of_nat (nw - 150)) sc1B) with sc1B_mid1.
        change (srun ag1 (S_rec m) sc1B_mid1) with sc1B_mid2.
        pose proof (B1k_bd (k - (S_rec m + N.of_nat (nw - 150)))%N ltac:(lia)). lia. }
  (* Agent 2 in Sub-phase B: (n_cyc - 10) cycles starting at X2 + 10 *)
  assert (HnB_ag2 : nB = (15 * (n_cyc - 10))%N) by (unfold nB; lia).
  assert (HB_ag2_t0 : sc2B.(stape) ((X2 + 10) - 2) = false)
    by (unfold sc2B; simpl; rewrite DAt2 by lia; replace (X2 + 10 - 2) with (X2 + 10 - 2) by lia;
        replace (X2 + Z.of_N 10 - 2) with (X2 + 10 - 2) in A2m2 by lia; exact A2m2).
  assert (HB_ag2_t1 : sc2B.(stape) ((X2 + 10) - 1) = false)
    by (unfold sc2B; simpl; rewrite DAt2 by lia; replace (X2 + 10 - 1) with (X2 + Z.of_N 10 - 1) by lia; exact A2m1).
  assert (HB_ag2_t2 : sc2B.(stape) (X2 + 10) = false)
    by (unfold sc2B; simpl; rewrite DAt2 by lia; replace (X2 + 10) with (X2 + Z.of_N 10) by lia; exact A2_0).
  assert (HB_ag2_t3 : sc2B.(stape) ((X2 + 10) + 1) = true)
    by (unfold sc2B; simpl; rewrite DAt2 by lia; replace (X2 + 10 + 1) with (X2 + Z.of_N 10 + 1) by lia; exact A2_1).
  assert (HB_ag2_ge : forall z, (X2 + 10) + 2 <= z -> sc2B.(stape) z = false)
    by (intros z Hz; unfold sc2B; simpl; rewrite DAt2 by lia; apply A2ge; lia).
  destruct (ag2_glider (n_cyc - 10) (X2 + 8) (X2 + 10) sc2B ltac:(lia)
              ltac:(unfold sc2B; simpl; rewrite DAp2, A2p; lia)
              ltac:(unfold sc2B; simpl; rewrite DAs2, A2s; reflexivity)
              ltac:(intros; lia) HB_ag2_t0 HB_ag2_t1 HB_ag2_t2 HB_ag2_t3 HB_ag2_ge)
    as [B2bd [B2p [B2s [B2old [B2lt [B2m2 [B2m1 [B2_0 [B2_1 B2ge]]]]]]]]].
  rewrite <- HnB_ag2 in *.
  destruct (run_decouple ag1 ag2 (X2 + 6) (X2 + 8) nB cA sc1B sc2B ltac:(lia)
              eq_refl eq_refl eq_refl eq_refl ltac:(intros; reflexivity) ltac:(intros; reflexivity)
              HB_ag1_all_bd B2bd)
    as [DBp1 [DBs1 [DBp2 [DBs2 [DBt1 [DBt2 [DBmid DBnc]]]]]]].
  set (cB := run_N ag1 ag2 nB cA) in *.
  (* Summarize state at cB = run_N ag1 ag2 (15 * n_cyc) c *)
  assert (HcB_eq : cB = run_N ag1 ag2 (15 * n_cyc) c)
    by (unfold cB, cA; rewrite HnB_eq, run_N_add; reflexivity).
  assert (HcB_p1 : cB.(pos1) = (X2 - 3) + Z.of_nat W).
  { rewrite DBp1, HnB_ag1.
    replace (N.of_nat (nw - 150) + S_rec m + N.of_nat W)%N
      with (N.of_nat W + (S_rec m + N.of_nat (nw - 150)))%N by lia.
    rewrite !srun_add.
    change (srun ag1 (N.of_nat (nw - 150)) sc1B) with sc1B_mid1.
    change (srun ag1 (S_rec m) sc1B_mid1) with sc1B_mid2. exact B1k_p. }
  assert (HcB_s1 : cB.(state1) = StB).
  { rewrite DBs1, HnB_ag1.
    replace (N.of_nat (nw - 150) + S_rec m + N.of_nat W)%N
      with (N.of_nat W + (S_rec m + N.of_nat (nw - 150)))%N by lia.
    rewrite !srun_add.
    change (srun ag1 (N.of_nat (nw - 150)) sc1B) with sc1B_mid1.
    change (srun ag1 (S_rec m) sc1B_mid1) with sc1B_mid2. exact B1k_s. }
  assert (HcB_p2 : cB.(pos2) = X2 + Z.of_N n_cyc)
    by (rewrite DBp2, B2p; lia).
  assert (HcB_s2 : cB.(state2) = StC)
    by (rewrite DBs2; exact B2s).
  assert (HcB_m2 : cB.(tape) (-2) = false).
  { rewrite DBt1 by lia. rewrite HnB_ag1.
    replace (N.of_nat (nw - 150) + S_rec m + N.of_nat W)%N
      with (N.of_nat W + (S_rec m + N.of_nat (nw - 150)))%N by lia.
    rewrite !srun_add.
    change (srun ag1 (N.of_nat (nw - 150)) sc1B) with sc1B_mid1.
    change (srun ag1 (S_rec m) sc1B_mid1) with sc1B_mid2.
    rewrite B1k_t. exact B1c_m2. }
  assert (HcB_tr : forall z, -1 <= z <= X2 + Z.of_N n_cyc - 3 -> cB.(tape) z = true).
  { intros z Hz.
    destruct (Z.le_gt_cases z (X2 + 6)).
    - rewrite DBt1 by lia. rewrite HnB_ag1.
      replace (N.of_nat (nw - 150) + S_rec m + N.of_nat W)%N
        with (N.of_nat W + (S_rec m + N.of_nat (nw - 150)))%N by lia.
      rewrite !srun_add.
      change (srun ag1 (N.of_nat (nw - 150)) sc1B) with sc1B_mid1.
      change (srun ag1 (S_rec m) sc1B_mid1) with sc1B_mid2.
      rewrite B1k_t.
      destruct (Z.le_gt_cases z (X2 - 4)).
      + apply B1c_t. lia.
      + rewrite B1c_o by lia.
        destruct (Z.eq_dec z (X2 - 3)).
        * subst z. unfold sc1B; simpl; rewrite DAmid by lia; exact Hm3.
        * unfold sc1B; simpl; rewrite DAt2 by lia; apply A2lt; lia.
    - destruct (Z.lt_ge_cases z (X2 + 8)).
      + rewrite DBmid by lia. unfold cA. rewrite DAt2 by lia. apply A2lt. lia.
      + rewrite DBt2 by lia. apply B2lt. lia. }
  assert (HcB_m2' : cB.(tape) (X2 + Z.of_N n_cyc - 2) = false)
    by (rewrite DBt2 by lia; replace (X2 + Z.of_N n_cyc - 2) with (X2 + 10 + Z.of_N (n_cyc - 10) - 2) by lia; exact B2m2).
  assert (HcB_m1' : cB.(tape) (X2 + Z.of_N n_cyc - 1) = false)
    by (rewrite DBt2 by lia; replace (X2 + Z.of_N n_cyc - 1) with (X2 + 10 + Z.of_N (n_cyc - 10) - 1) by lia; exact B2m1).
  assert (HcB_0' : cB.(tape) (X2 + Z.of_N n_cyc) = false)
    by (rewrite DBt2 by lia; replace (X2 + Z.of_N n_cyc) with (X2 + 10 + Z.of_N (n_cyc - 10)) by lia; exact B2_0).
  assert (HcB_1' : cB.(tape) (X2 + Z.of_N n_cyc + 1) = true)
    by (rewrite DBt2 by lia; replace (X2 + Z.of_N n_cyc + 1) with (X2 + 10 + Z.of_N (n_cyc - 10) + 1) by lia; exact B2_1).
  assert (HcB_ge' : forall z, X2 + Z.of_N n_cyc + 2 <= z -> cB.(tape) z = false)
    by (intros z Hz; rewrite DBt2 by lia; apply B2ge; lia).
  (* Now prove inner chase loop by induction on K starting from cB! *)
  assert (Hchase : forall j (P1 P2 : Z) cj,
    -1 <= P1 ->
    cj.(pos1) = P1 -> cj.(state1) = StB ->
    cj.(pos2) = P2 -> cj.(state2) = StC ->
    P2 - P1 = G_next + 14 * Z.of_N j ->
    cj.(tape) (-2) = false ->
    (forall z, -1 <= z <= P2 - 3 -> cj.(tape) z = true) ->
    cj.(tape) (P2 - 2) = false ->
    cj.(tape) (P2 - 1) = false ->
    cj.(tape) P2 = false ->
    cj.(tape) (P2 + 1) = true ->
    (forall z, P2 + 2 <= z -> cj.(tape) z = false) ->
    (forall t, (t < 15 * j)%N -> (run_N ag1 ag2 t cj).(pos1) <> (run_N ag1 ag2 t cj).(pos2)) /\
    let cj' := run_N ag1 ag2 (15 * j) cj in
    cj'.(pos1) = P1 + 15 * Z.of_N j /\ cj'.(state1) = StB /\
    cj'.(pos2) = P1 + 15 * Z.of_N j + G_next /\ cj'.(state2) = StC /\
    cj'.(tape) (-2) = false /\
    (forall z, -1 <= z <= P1 + 15 * Z.of_N j + G_next - 3 -> cj'.(tape) z = true) /\
    cj'.(tape) (P1 + 15 * Z.of_N j + G_next - 2) = false /\
    cj'.(tape) (P1 + 15 * Z.of_N j + G_next - 1) = false /\
    cj'.(tape) (P1 + 15 * Z.of_N j + G_next) = false /\
    cj'.(tape) (P1 + 15 * Z.of_N j + G_next + 1) = true /\
    (forall z, P1 + 15 * Z.of_N j + G_next + 2 <= z -> cj'.(tape) z = false)).
  { clear -HG. intro j. induction j using N.peano_ind;
      intros P1 P2 cj HP1 Jp1 Js1 Jp2 Js2 Jgap Jm2 Jtr Jm2' Jm1' J0' J1' Jge'.
    - rewrite N.mul_0_r, run_N_0. cbv zeta. splits; [intros; lia | lia | exact Js1 | lia | exact Js2 | exact Jm2 | | | | | |];
        try (intros z Hz; apply Jtr; lia);
        try (replace (P1 + 15 * Z.of_N 0 + G_next - 2) with (P2 - 2) by lia; exact Jm2');
        try (replace (P1 + 15 * Z.of_N 0 + G_next - 1) with (P2 - 1) by lia; exact Jm1');
        try (replace (P1 + 15 * Z.of_N 0 + G_next) with P2 by lia; exact J0');
        try (replace (P1 + 15 * Z.of_N 0 + G_next + 1) with (P2 + 1) by lia; exact J1');
        try (intros z Hz; apply Jge'; lia).
    - rewrite N2Z.inj_succ in *.
      assert (Hsep : P1 + 17 <= P2) by (pose proof (N2Z.is_nonneg j); lia).
      set (q1 := {| spos := P1; sstate := StB; stape := cj.(tape) |}).
      set (q2 := {| spos := P2; sstate := StC; stape := cj.(tape) |}).
      assert (Hw : forall z, P1 <= z < P1 + Z.of_nat 15 -> q1.(stape) z = true)
        by (intros z Hz; apply Jtr; change (Z.of_nat 15) with 15 in Hz; lia).
      destruct (ag1_walk_ones 15 P1 q1 eq_refl eq_refl Hw) as [Wbd [Wp [Ws Wt]]].
      destruct (ag2_cycle15 P2 q2 eq_refl eq_refl Jm2' Jm1' J0' J1' Jge')
        as [Cbd [Cp [Cs [Cold [Cm2 [Cm1 [C0 [C1 [C2 Cge]]]]]]]]].
      assert (Hbd1 : forall k, (k < 15)%N -> (srun ag1 k q1).(spos) <= P1 + 14)
        by (intros k Hk; change 15%N with (N.of_nat 15) in Hk; pose proof (Wbd k Hk); change (Z.of_nat 15) with 15 in *; lia).
      destruct (run_decouple ag1 ag2 (P1 + 14) (P2 - 2) 15 cj q1 q2 ltac:(lia)
                  Jp1 Js1 Jp2 Js2 ltac:(intros; reflexivity) ltac:(intros; reflexivity) Hbd1 Cbd)
        as [Ep1 [Es1 [Ep2 [Es2 [Et1 [Et2 [Emid Enc]]]]]]].
      set (c15 := run_N ag1 ag2 15 cj) in *.
      assert (C15_p1 : c15.(pos1) = P1 + 15)
        by (rewrite Ep1; change 15%N with (N.of_nat 15); rewrite Wp; change (Z.of_nat 15) with 15; reflexivity).
      assert (C15_s1 : c15.(state1) = StB)
        by (rewrite Es1; change 15%N with (N.of_nat 15); exact Ws).
      assert (C15_p2 : c15.(pos2) = P2 + 1) by (rewrite Ep2; exact Cp).
      assert (C15_s2 : c15.(state2) = StC) by (rewrite Es2; exact Cs).
      assert (C15_m2 : c15.(tape) (-2) = false)
        by (rewrite Et1 by lia; change 15%N with (N.of_nat 15); rewrite Wt; exact Jm2).
      assert (C15_tr : forall z, -1 <= z <= (P2 + 1) - 3 -> c15.(tape) z = true).
      { intros z Hz. destruct (Z.le_gt_cases z (P1 + 14)).
        - rewrite Et1 by lia; change 15%N with (N.of_nat 15); rewrite Wt; apply Jtr; lia.
        - destruct (Z.lt_ge_cases z (P2 - 2)).
          + rewrite Emid by lia; apply Jtr; lia.
          + rewrite Et2 by lia; replace z with (P2 - 2) by lia; exact Cm2. }
      destruct (IHj (P1 + 15) (P2 + 1) c15 ltac:(lia) C15_p1 C15_s1 C15_p2 C15_s2 ltac:(lia) C15_m2 C15_tr
                  ltac:(rewrite Et2 by lia; replace (P2 + 1 - 2) with (P2 - 1) by lia; exact Cm1)
                  ltac:(rewrite Et2 by lia; replace (P2 + 1 - 1) with P2 by lia; exact C0)
                  ltac:(rewrite Et2 by lia; exact C1)
                  ltac:(rewrite Et2 by lia; replace (P2 + 1 + 1) with (P2 + 2) by lia; exact C2)
                  ltac:(intros z Hz; rewrite Et2 by lia; apply Cge; lia))
        as [Lnc [Lp1 [Ls1 [Lp2 [Ls2 [Lm2 [Ltr [Lm2' [Lm1' [L0' [L1' Lge']]]]]]]]]]].
      replace (15 * N.succ j)%N with (15 * j + 15)%N by lia.
      cbv zeta. rewrite run_N_add. change (run_N ag1 ag2 15 cj) with c15.
      splits; [| rewrite Lp1; lia | exact Ls1 | rewrite Lp2; lia | exact Ls2 | exact Lm2 | | | | | |].
      + intros k Hk. eapply no_coll_add; [exact Enc | exact Lnc | exact Hk].
      + intros z Hz. apply Ltr. lia.
      + replace (P1 + 15 * Z.succ (Z.of_N j) + G_next - 2) with (P1 + 15 + 15 * Z.of_N j + G_next - 2) by lia. exact Lm2'.
      + replace (P1 + 15 * Z.succ (Z.of_N j) + G_next - 1) with (P1 + 15 + 15 * Z.of_N j + G_next - 1) by lia. exact Lm1'.
      + replace (P1 + 15 * Z.succ (Z.of_N j) + G_next) with (P1 + 15 + 15 * Z.of_N j + G_next) by lia. exact L0'.
      + replace (P1 + 15 * Z.succ (Z.of_N j) + G_next + 1) with (P1 + 15 + 15 * Z.of_N j + G_next + 1) by lia. exact L1'.
      + intros z Hz. apply Lge'. lia. }
  destruct (Hchase K ((X2 - 3) + Z.of_nat W) (X2 + Z.of_N n_cyc) cB ltac:(lia)
              HcB_p1 HcB_s1 HcB_p2 HcB_s2 Hgap_eq HcB_m2 HcB_tr HcB_m2' HcB_m1' HcB_0' HcB_1' HcB_ge')
    as [CH_nc [CH_p1 [CH_s1 [CH_p2 [CH_s2 [CH_m2 [CH_tr [CH_m2' [CH_m1' [CH_0' [CH_1' CH_ge']]]]]]]]]]].
  cbv zeta.
  assert (Hnc_round : forall t, (t < 15 * n_cyc)%N -> (run_N ag1 ag2 t c).(pos1) <> (run_N ag1 ag2 t c).(pos2)).
  { intros t Ht. rewrite HnB_eq in Ht.
    eapply no_coll_add; [exact DAnc | | exact Ht].
    intro k. change (run_N ag1 ag2 150 c) with cA. exact (DBnc k). }
  splits.
  - intros t Ht. unfold T_round in Ht. replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N in Ht by lia.
    eapply no_coll_add; [exact Hnc_round | | exact Ht].
    intro k. rewrite <- HcB_eq. exact (CH_nc k).
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq. exact CH_p1.
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq. exact CH_s1.
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq. rewrite CH_p2. lia.
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq. exact CH_s2.
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq. exact CH_m2.
  - intros z Hz. replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq. apply CH_tr. lia.
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq.
    replace (X_end + G_next - 2) with (X2 - 3 + Z.of_nat W + 15 * Z.of_N K + G_next - 2) by lia. exact CH_m2'.
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq.
    replace (X_end + G_next - 1) with (X2 - 3 + Z.of_nat W + 15 * Z.of_N K + G_next - 1) by lia. exact CH_m1'.
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq.
    replace (X_end + G_next) with (X2 - 3 + Z.of_nat W + 15 * Z.of_N K + G_next) by lia. exact CH_0'.
  - replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq.
    replace (X_end + G_next + 1) with (X2 - 3 + Z.of_nat W + 15 * Z.of_N K + G_next + 1) by lia. exact CH_1'.
  - intros z Hz. replace (15 * n_cyc + 15 * K)%N with (15 * K + 15 * n_cyc)%N by lia.
    rewrite run_N_add, <- HcB_eq. apply CH_ge'. unfold X_end in Hz. lia.
Qed.

(** * 10. 45-Step Local Bounce at G = 10 and 7-Step Collision Suffix at G = 8 *)

Fixpoint bt_set_ones (lo : Z) (cnt : nat) (t : BTree) : BTree :=
  match cnt with
  | O => t
  | S n => bt_set_ones (lo + 1) n (bt_set (z_to_pos lo) true t)
  end.

Definition fc_bounce10 : FastConfig := {|
  fpos1 := 0; fpos2 := 10; fstate1 := StB; fstate2 := StC;
  ftape := bt_set (z_to_pos 11) true (bt_set_ones (-27) 35 BEmpty)
|}.

Definition check_bounce10 : bool :=
  let st45 := N.iter 45 (fast_step_chk_ge (-27)) (fc_bounce10, true) in
  let fc := fst st45 in
  snd st45 &&
  (fc.(fpos1) =? -27) &&
  (fc.(fpos2) =? 13) &&
  (match fc.(fstate1), fc.(fstate2) with StC, StC => true | _, _ => false end) &&
  bt_get (z_to_pos (-27)) fc.(ftape) &&
  check_all_false_nat (-26) 36%nat fc.(ftape) &&
  bt_get (z_to_pos 10) fc.(ftape) &&
  negb (bt_get (z_to_pos 11) fc.(ftape)) &&
  negb (bt_get (z_to_pos 12) fc.(ftape)) &&
  negb (bt_get (z_to_pos 13) fc.(ftape)) &&
  bt_get (z_to_pos 14) fc.(ftape) &&
  bt_bounded_aux (-27) 14 (fun q => q) fc.(ftape) &&
  check_all_true_nat (-27) 35%nat fc_bounce10.(ftape) &&
  bt_bounded_aux (-27) 11 (fun q => q) fc_bounce10.(ftape) &&
  negb (bt_get (z_to_pos 8) fc_bounce10.(ftape)) &&
  negb (bt_get (z_to_pos 9) fc_bounce10.(ftape)) &&
  negb (bt_get (z_to_pos 10) fc_bounce10.(ftape)) &&
  bt_get (z_to_pos 11) fc_bounce10.(ftape).

Lemma bounce10_ok : check_bounce10 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bounce_G10 : forall x0 c,
  26 <= x0 ->
  c.(pos1) = x0 -> c.(state1) = StB ->
  c.(pos2) = x0 + 10 -> c.(state2) = StC ->
  c.(tape) (-2) = false ->
  (forall z, -1 <= z <= x0 + 7 -> c.(tape) z = true) ->
  c.(tape) (x0 + 8) = false ->
  c.(tape) (x0 + 9) = false ->
  c.(tape) (x0 + 10) = false ->
  c.(tape) (x0 + 11) = true ->
  (forall z, x0 + 12 <= z -> c.(tape) z = false) ->
  (forall t, (t < 45)%N -> (run_N ag1 ag2 t c).(pos1) <> (run_N ag1 ag2 t c).(pos2)) /\
  let c' := run_N ag1 ag2 45 c in
  c'.(pos1) = x0 - 27 /\ c'.(state1) = StC /\
  c'.(pos2) = x0 + 13 /\ c'.(state2) = StC /\
  c'.(tape) (-2) = false /\
  (forall z, -1 <= z <= x0 - 27 -> c'.(tape) z = true) /\
  (forall z, x0 - 26 <= z <= x0 + 9 -> c'.(tape) z = false) /\
  c'.(tape) (x0 + 10) = true /\
  c'.(tape) (x0 + 11) = false /\
  c'.(tape) (x0 + 12) = false /\
  c'.(tape) (x0 + 13) = false /\
  c'.(tape) (x0 + 14) = true /\
  (forall z, x0 + 15 <= z -> c'.(tape) z = false).
Proof.
  intros x0 c Hx0 Hp1 Hs1 Hp2 Hs2 Hm2 Htr Hf8 Hf9 Hf10 Ht11 Hge12.
  pose proof bounce10_ok as Hok. unfold check_bounce10 in Hok.
  remember (N.iter 45 (fast_step_chk_ge (-27)) (fc_bounce10, true)) as st eqn:E.
  destruct st as [fc45 ok45].
  rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[[[[[[[[[[[[[Hsnd Fp1] Fp2] Fs] Fm27] Ffl] Ft10] Ff11] Ff12] Ff13] Ft14] Fbd] Btr] Bbd] Bf8] Bf9] Bf10] Bt11].
  (* Wait: 18 andb's: count carefully! Let's rewrite negb and eqb *)
  rewrite Z.eqb_eq in Fp1, Fp2.
  rewrite negb_true_iff in Ff11, Ff12, Ff13, Bf8, Bf9, Bf10.
  apply check_states_CC in Fs. destruct Fs as [Fs1 Fs2].
  assert (Hfc : fc45 = N.iter 45 fast_step fc_bounce10).
  { pose proof (fast_step_chk_ge_fst 45 (-27) fc_bounce10 true) as Hfst.
    rewrite <- E in Hfst. exact Hfst. }
  assert (Hsnd45 : snd (N.iter 45 (fast_step_chk_ge (-27)) (fc_bounce10, true)) = true)
    by (rewrite <- E; exact Hsnd).
  clear E Hsnd.
  destruct (fast_step_chk_ge_sound 45 (-27) fc_bounce10 true Hsnd45) as [_ Hchk].
  assert (Hbd_cf : forall k, (k < 45)%N ->
            (-27 <= (run_N ag1 ag2 k (fc_to_cfg fc_bounce10)).(pos1) /\
             -27 <= (run_N ag1 ag2 k (fc_to_cfg fc_bounce10)).(pos2)) /\
            (run_N ag1 ag2 k (fc_to_cfg fc_bounce10)).(pos1) <>
            (run_N ag1 ag2 k (fc_to_cfg fc_bounce10)).(pos2)).
  { intros k Hk.
    pose proof (fast_run_sound k fc_bounce10) as [Rp1 Rp2 _ _ _].
    change (pos1 (fc_to_cfg (N.iter k fast_step fc_bounce10))) with (N.iter k fast_step fc_bounce10).(fpos1) in Rp1.
    change (pos2 (fc_to_cfg (N.iter k fast_step fc_bounce10))) with (N.iter k fast_step fc_bounce10).(fpos2) in Rp2.
    rewrite <- Rp1, <- Rp2.
    destruct (N.eq_0_gt_0_cases k) as [-> | Hkgt].
    - cbn [N.iter]. unfold fc_bounce10. cbn [fpos1 fpos2]. lia.
    - destruct (Hchk k ltac:(lia)) as [Hn [Hb1 Hb2]]. lia. }
  assert (Hbd_only : forall k, (k < 45)%N ->
            -27 <= (run_N ag1 ag2 k (fc_to_cfg fc_bounce10)).(pos1) /\
            -27 <= (run_N ag1 ag2 k (fc_to_cfg fc_bounce10)).(pos2))
    by (intros k Hk; apply (Hbd_cf k Hk)).
  assert (Hag : agree_ge (-27) (fc_to_cfg fc_bounce10).(tape) (shift_cfg (- x0) c).(tape)).
  { intros z Hz. unfold fc_to_cfg, shift_cfg, shift_tape. cbn [tape ftape].
    assert (Hzc : (-27 <= z < 8) \/ z = 8 \/ z = 9 \/ z = 10 \/ z = 11 \/ z >= 12) by lia.
    destruct Hzc as [Hz1 | [-> | [-> | [-> | [-> | Hz2]]]]].
    - rewrite (check_all_true_nat_sound 35 (-27) fc_bounce10.(ftape) z Btr) by (change (Z.of_nat 35) with 35; lia).
      symmetry. apply Htr. lia.
    - replace (8 - - x0) with (x0 + 8) by lia. unfold bt_interp in *. congruence.
    - replace (9 - - x0) with (x0 + 9) by lia. unfold bt_interp in *. congruence.
    - replace (10 - - x0) with (x0 + 10) by lia. unfold bt_interp in *. congruence.
    - replace (11 - - x0) with (x0 + 11) by lia. unfold bt_interp in *. congruence.
    - rewrite (bt_bounded_sound (-27) 11 fc_bounce10.(ftape) z Bbd) by lia.
      symmetry. apply Hge12. lia. }
  destruct (run_N_agree_ge ag1 ag2 (-27) 45 (fc_to_cfg fc_bounce10) (shift_cfg (- x0) c)
              ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; congruence) ltac:(simpl; congruence)
              Hag Hbd_only)
    as [Ap1 [Ap2 [As1 [As2 [Aag [Alt Aprev]]]]]].
  pose proof (run_N_shift ag1 ag2 (- x0) 45 c) as [Sp1 Sp2 Ss1 Ss2 Stp].
  simpl in Sp1, Sp2, Ss1, Ss2.
  pose proof (fast_run_sound 45 fc_bounce10) as [F45p1 F45p2 F45s1 F45s2 F45tp].
  rewrite <- Hfc in F45p1, F45p2, F45s1, F45s2, F45tp.
  cbn [pos1 pos2 state1 state2 tape fc_to_cfg] in F45p1, F45p2, F45s1, F45s2, F45tp.
  (* Helper to read shifted tape cells at z >= -27 *)
  assert (Hread : forall z, -27 <= z -> c'.(tape) (x0 + z) = bt_interp fc45.(ftape) z).
  { intros z Hz. specialize (Stp z). unfold shift_cfg, shift_tape in Stp. simpl in Stp.
    replace (z - - x0) with (x0 + z) in Stp by lia. rewrite <- Stp, <- Aag by auto. exact (F45tp z). }
  (* Helper to preserve cells z < x0 - 27 *)
  assert (Hbd_orig : forall k, (k < 45)%N -> x0 - 27 <= (run_N ag1 ag2 k c).(pos1) /\ x0 - 27 <= (run_N ag1 ag2 k c).(pos2)).
  { intros k Hk.
    pose proof (run_N_shift ag1 ag2 (- x0) k c) as [Kp1 Kp2 _ _ _]. simpl in Kp1, Kp2.
    destruct (Aprev k Hk) as [Bp1 Bp2].
    destruct (Hbd_only k Hk) as [Op1 Op2]. lia. }
  destruct (run_N_agree_ge ag1 ag2 (x0 - 27) 45 c c eq_refl eq_refl eq_refl eq_refl
              ltac:(intros ? _; reflexivity) Hbd_orig)
    as [_ [_ [_ [_ [_ Hlt]]]]].
  cbv zeta in *. splits.
  - intros t Ht.
    pose proof (run_N_shift ag1 ag2 (- x0) t c) as [Tp1 Tp2 _ _ _]. simpl in Tp1, Tp2.
    destruct (Aprev t Ht) as [Bp1 Bp2]. destruct (Hbd_cf t Ht) as [_ Hnc]. lia.
  - lia.
  - congruence.
  - lia.
  - congruence.
  - rewrite Hlt by lia. exact Hm2.
  - intros z Hz. destruct (Z.lt_ge_cases z (x0 - 27)).
    + rewrite Hlt by lia. apply Htr. lia.
    + replace z with (x0 + (-27)) by lia. rewrite Hread by lia. exact Fm27.
  - intros z Hz. replace z with (x0 + (z - x0)) by lia. rewrite Hread by lia.
    eapply check_all_false_nat_sound; [exact Ffl |]; change (Z.of_nat 36%nat) with 36; lia.
  - replace (x0 + 10) with (x0 + 10) by lia. rewrite Hread by lia. exact Ft10.
  - rewrite Hread by lia. exact Ff11.
  - rewrite Hread by lia. exact Ff12.
  - rewrite Hread by lia. exact Ff13.
  - rewrite Hread by lia. exact Ft14.
  - intros z Hz. replace z with (x0 + (z - x0)) by lia. rewrite Hread by lia.
    eapply bt_bounded_sound; [exact Fbd | lia].
Qed.

Definition fc_final8 : FastConfig := {|
  fpos1 := 0; fpos2 := 8; fstate1 := StB; fstate2 := StC;
  ftape := bt_set (z_to_pos 9) true (bt_set_ones 0 6 BEmpty)
|}.

Definition check_final7 : bool :=
  let st6 := N.iter 6 (fast_step_chk_ge 0) (fc_final8, true) in
  let fc7 := fast_step (fst st6) in
  snd st6 &&
  (fc7.(fpos1) =? fc7.(fpos2)) &&
  check_all_true_nat 0 6%nat fc_final8.(ftape) &&
  bt_bounded_aux 0 9 (fun q => q) fc_final8.(ftape) &&
  negb (bt_get (z_to_pos 6) fc_final8.(ftape)) &&
  negb (bt_get (z_to_pos 7) fc_final8.(ftape)) &&
  negb (bt_get (z_to_pos 8) fc_final8.(ftape)) &&
  bt_get (z_to_pos 9) fc_final8.(ftape).

Lemma final7_ok : check_final7 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma suffix_7 : forall x0 c,
  c.(pos1) = x0 -> c.(state1) = StB ->
  c.(pos2) = x0 + 8 -> c.(state2) = StC ->
  (forall z, x0 <= z <= x0 + 5 -> c.(tape) z = true) ->
  c.(tape) (x0 + 6) = false ->
  c.(tape) (x0 + 7) = false ->
  c.(tape) (x0 + 8) = false ->
  c.(tape) (x0 + 9) = true ->
  (forall z, x0 + 10 <= z -> c.(tape) z = false) ->
  (run_N ag1 ag2 7 c).(pos1) = (run_N ag1 ag2 7 c).(pos2) /\
  forall t, (t < 7)%N -> (run_N ag1 ag2 t c).(pos1) <> (run_N ag1 ag2 t c).(pos2).
Proof.
  intros x0 c Hp1 Hs1 Hp2 Hs2 Htr Hf6 Hf7 Hf8 Ht9 Hge10.
  pose proof final7_ok as Hok. unfold check_final7 in Hok.
  rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[[[Hsnd Hcol] Btr] Bbd] Bf6] Bf7] Bf8] Bt9].
  rewrite Z.eqb_eq in Hcol.
  rewrite negb_true_iff in Bf6, Bf7, Bf8.
  destruct (fast_step_chk_ge_sound 6 0 fc_final8 true Hsnd) as [_ Hchk].
  assert (Hfc7 : fast_step (fst (N.iter 6 (fast_step_chk_ge 0) (fc_final8, true))) =
                 N.iter 7 fast_step fc_final8).
  { rewrite fast_step_chk_ge_fst. change 7%N with (N.succ 6). rewrite N.iter_succ. reflexivity. }
  rewrite Hfc7 in Hcol.
  remember (N.iter 7 fast_step fc_final8) as fc7 eqn:Efc7.
  assert (Hbd_cf : forall k, (k < 7)%N ->
            (0 <= (run_N ag1 ag2 k (fc_to_cfg fc_final8)).(pos1) /\
             0 <= (run_N ag1 ag2 k (fc_to_cfg fc_final8)).(pos2)) /\
            (run_N ag1 ag2 k (fc_to_cfg fc_final8)).(pos1) <>
            (run_N ag1 ag2 k (fc_to_cfg fc_final8)).(pos2)).
  { intros k Hk.
    pose proof (fast_run_sound k fc_final8) as [Rp1 Rp2 _ _ _].
    change (pos1 (fc_to_cfg (N.iter k fast_step fc_final8))) with (N.iter k fast_step fc_final8).(fpos1) in Rp1.
    change (pos2 (fc_to_cfg (N.iter k fast_step fc_final8))) with (N.iter k fast_step fc_final8).(fpos2) in Rp2.
    rewrite <- Rp1, <- Rp2.
    destruct (N.eq_0_gt_0_cases k) as [-> | Hkgt].
    - cbn [N.iter]. unfold fc_final8. cbn [fpos1 fpos2]. lia.
    - destruct (Hchk k ltac:(lia)) as [Hn [Hb1 Hb2]]. lia. }
  assert (Hbd_only : forall k, (k < 7)%N ->
            0 <= (run_N ag1 ag2 k (fc_to_cfg fc_final8)).(pos1) /\
            0 <= (run_N ag1 ag2 k (fc_to_cfg fc_final8)).(pos2))
    by (intros k Hk; apply (Hbd_cf k Hk)).
  assert (Hag : agree_ge 0 (fc_to_cfg fc_final8).(tape) (shift_cfg (- x0) c).(tape)).
  { intros z Hz. unfold fc_to_cfg, shift_cfg, shift_tape. cbn [tape ftape].
    assert (Hzc : (0 <= z < 6) \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/ z >= 10) by lia.
    destruct Hzc as [Hz1 | [-> | [-> | [-> | [-> | Hz2]]]]].
    - rewrite (check_all_true_nat_sound 6 0 fc_final8.(ftape) z Btr) by (change (Z.of_nat 6) with 6; lia).
      symmetry. apply Htr. lia.
    - replace (6 - - x0) with (x0 + 6) by lia. unfold bt_interp in *. congruence.
    - replace (7 - - x0) with (x0 + 7) by lia. unfold bt_interp in *. congruence.
    - replace (8 - - x0) with (x0 + 8) by lia. unfold bt_interp in *. congruence.
    - replace (9 - - x0) with (x0 + 9) by lia. unfold bt_interp in *. congruence.
    - rewrite (bt_bounded_sound 0 9 fc_final8.(ftape) z Bbd) by lia.
      symmetry. apply Hge10. lia. }
  destruct (run_N_agree_ge ag1 ag2 0 7 (fc_to_cfg fc_final8) (shift_cfg (- x0) c)
              ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; congruence) ltac:(simpl; congruence)
              Hag Hbd_only)
    as [Ap1 [Ap2 [_ [_ [_ [_ Aprev]]]]]].
  pose proof (run_N_shift ag1 ag2 (- x0) 7 c) as [Sp1 Sp2 _ _ _]. simpl in Sp1, Sp2.
  pose proof (fast_run_sound 7 fc_final8) as [F7p1 F7p2 _ _ _].
  rewrite <- Efc7 in F7p1, F7p2.
  cbn [pos1 pos2 fc_to_cfg] in F7p1, F7p2.
  split; [lia |].
  intros t Ht.
  pose proof (run_N_shift ag1 ag2 (- x0) t c) as [Tp1 Tp2 _ _ _]. simpl in Tp1, Tp2.
  destruct (Aprev t Ht) as [Bp1 Bp2]. destruct (Hbd_cf t Ht) as [_ Hnc]. lia.
Qed.

(** * 11. Exact Modular Arithmetic for Rounds 2 and 3 *)

Lemma pow2_add12_mod840 : forall n,
  3 <= n -> 2 ^ (n + 12) mod 840 = 2 ^ n mod 840.
Proof.
  intros n Hn.
  replace n with ((n - 3) + 3) by lia.
  replace ((n - 3) + 3 + 12) with ((n - 3) + 15) by lia.
  rewrite !Z.pow_add_r by lia.
  rewrite <- Zmult_mod_idemp_r.
  change (2 ^ 15 mod 840) with (2 ^ 3 mod 840).
  rewrite Zmult_mod_idemp_r. reflexivity.
Qed.

Lemma pow2_12k_plus_5_mod840 : forall k : nat,
  2 ^ (12 * Z.of_nat k + 5) mod 840 = 32.
Proof.
  induction k.
  - reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (12 * Z.succ (Z.of_nat k) + 5) with ((12 * Z.of_nat k + 5) + 12) by lia.
    rewrite pow2_add12_mod840 by lia. exact IHk.
Qed.

Lemma pow2_12k_plus_7_mod840 : forall k : nat,
  2 ^ (12 * Z.of_nat k + 7) mod 840 = 128.
Proof.
  induction k.
  - reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (12 * Z.succ (Z.of_nat k) + 7) with ((12 * Z.of_nat k + 7) + 12) by lia.
    rewrite pow2_add12_mod840 by lia. exact IHk.
Qed.

Definition K2 : N := ((2 ^ 4697 - 242) / 210)%N.
Definition n_cyc2 : N := (14 * (K2 + 1))%N.
Definition x0_2_Z : Z := 4701 + 15 * Z.of_N K2.
Definition m3 : N := Z.to_N (x0_2_Z + 11).
Definition K3 : N := ((2 ^ (m3 + 2) - 128) / 210)%N.
Definition n_cyc3 : N := (14 * K3 + 6)%N.

Definition exact_halt_steps : N :=
  (70429 + (15 * n_cyc2 + 15 * K2) + 45 + (15 * n_cyc3 + 15 * K3) + 7)%N.

Lemma K2_rel : (4659 + (2 ^ 4697 - 240) + 7 = 15 * n_cyc2)%N.
Proof. vm_compute. reflexivity. Qed.

Lemma K2_gap_rel : 4697 + Z.of_N n_cyc2 - (4694 + 7) = 10 + 14 * Z.of_N K2.
Proof. vm_compute. reflexivity. Qed.

Lemma K2_mod3 : Z.of_N K2 mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma K2_pow_rel : (2 ^ 4697 = 840 * ((Z.of_N K2 + 1) / 4) + 32)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma K2_ge3 : 1 <= (Z.of_N K2 + 1) / 4.
Proof. vm_compute. discriminate. Qed.

Lemma K2_arithmetic :
  exists q2 : Z,
    1 <= q2 /\
    Z.of_N K2 = 4 * q2 - 1 /\
    2 ^ 4697 = 840 * q2 + 32 /\
    (N.of_nat (Z.to_nat (4657 + 2)) + S_rec (Z.to_nat (4697 - 2)) + N.of_nat 7 = 15 * n_cyc2)%N /\
    4697 + Z.of_N n_cyc2 - ((4697 - 3) + Z.of_nat 7) = 10 + 14 * Z.of_N K2.
Proof.
  set (q2 := ((Z.of_N K2 + 1) / 4)%Z).
  exists q2. splits.
  - exact K2_ge3.
  - pose proof (Z.div_mod (Z.of_N K2 + 1) 4 ltac:(lia)) as Hdm.
    assert (Hm : (Z.of_N K2 + 1) mod 4 = 0).
    { rewrite <- Zplus_mod_idemp_l, K2_mod3. reflexivity. }
    rewrite Hm in Hdm. unfold q2. lia.
  - exact K2_pow_rel.
  - apply N2Z.inj. rewrite !N2Z.inj_add, S_rec_closed.
    change (Z.of_nat (Z.to_nat (4657 + 2))) with 4659.
    change (Z.of_nat (Z.to_nat (4697 - 2))) with 4695.
    change (Z.of_nat 7) with 7.
    change (4695 + 2) with 4697.
    pose proof K2_rel as Hr.
    apply N2Z.inj_iff in Hr.
    rewrite !N2Z.inj_add, N2Z.inj_sub, N2Z.inj_pow in Hr.
    + exact Hr.
    + change 240%N with (2 ^ 8 - 16)%N.
      assert (2 ^ 8 <= 2 ^ 4697)%N by (apply N.pow_le_mono_r; lia). lia.
  - exact K2_gap_rel.
Qed.

Lemma K3_arithmetic :
  exists q3 : Z,
    1 <= q3 /\
    Z.of_N K3 = 4 * q3 /\
    2 ^ (Z.of_N m3 + 2) = 840 * q3 + 128 /\
    (N.of_nat (Z.to_nat ((x0_2_Z - 27) + 2)) + S_rec (Z.to_nat ((x0_2_Z + 13) - 2)) + N.of_nat 1 = 15 * n_cyc3)%N /\
    (x0_2_Z + 13) + Z.of_N n_cyc3 - (((x0_2_Z + 13) - 3) + Z.of_nat 1) = 8 + 14 * Z.of_N K3.
Proof.
  destruct K2_arithmetic as [q2 [Hq2 [HK2 _]]].
  assert (Hx0_ge : 4701 <= x0_2_Z) by (unfold x0_2_Z; lia).
  assert (Hm3_eq : Z.of_N m3 = x0_2_Z + 11) by (unfold m3; lia).
  assert (Hm3_mod : Z.of_N m3 + 2 = 12 * Z.of_nat (Z.to_nat (391 + 5 * q2)) + 7).
  { rewrite Hm3_eq. unfold x0_2_Z. rewrite HK2.
    replace (Z.of_nat (Z.to_nat (391 + 5 * q2))) with (391 + 5 * q2) by lia. lia. }
  pose proof (pow2_12k_plus_7_mod840 (Z.to_nat (391 + 5 * q2))) as Hmod.
  rewrite <- Hm3_mod in Hmod.
  assert (H2_10 : 1024 <= 2 ^ (Z.of_N m3 + 2)).
  { change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia. }
  assert (Hpow_gt : (128 <= 2 ^ (m3 + 2))%N).
  { change 128%N with (2 ^ 7)%N. apply N.pow_le_mono_r; lia. }
  pose proof (Z.div_mod (2 ^ (Z.of_N m3 + 2)) 840 ltac:(lia)) as Hdm.
  rewrite Hmod in Hdm.
  remember (2 ^ (Z.of_N m3 + 2) / 840)%Z as q3 eqn:Eq3.
  remember (2 ^ (Z.of_N m3 + 2)) as P3 eqn:EP3.
  assert (Hpow : P3 = 840 * q3 + 128) by lia.
  assert (Hq3_ge : 1 <= q3) by lia.
  assert (HK3_eq : Z.of_N K3 = 4 * q3).
  { unfold K3.
    rewrite N2Z.inj_div, N2Z.inj_sub, N2Z.inj_pow, N2Z.inj_add; auto.
    change (Z.of_N 2) with 2. change (Z.of_N 128) with 128. change (Z.of_N 210) with 210.
    rewrite <- EP3.
    replace (P3 - 128) with (4 * q3 * 210) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  exists q3. splits; auto.
  - apply N2Z.inj. rewrite !N2Z.inj_add, !N2Z.inj_mul, !nat_N_Z, S_rec_closed.
    rewrite !Z2Nat.id by lia.
    change (Z.of_nat 1) with 1. change (Z.of_N 15) with 15.
    replace (x0_2_Z + 13 - 2) with (Z.of_N m3) by lia.
    rewrite <- EP3.
    unfold n_cyc3. rewrite N2Z.inj_add, N2Z.inj_mul, HK3_eq.
    change (Z.of_N 14) with 14. change (Z.of_N 6) with 6. lia.
  - unfold n_cyc3. rewrite N2Z.inj_add, N2Z.inj_mul.
    change (Z.of_N 14) with 14. change (Z.of_N 6) with 6. change (Z.of_nat 1) with 1. lia.
Qed.

Lemma T_halt_closed_form :
  Z.of_N exact_halt_steps =
  70411 + 2 ^ 4697 + 15 * Z.of_N K2 + 2 ^ (Z.of_N m3 + 2) + 15 * Z.of_N K3.
Proof.
  destruct K2_arithmetic as [q2 [Hq2 [HK2 [Hpow2 _]]]].
  destruct K3_arithmetic as [q3 [Hq3 [HK3 [Hpow3 _]]]].
  unfold exact_halt_steps, n_cyc2, n_cyc3.
  rewrite !N2Z.inj_add, !N2Z.inj_mul.
  change (Z.of_N 70429) with 70429. change (Z.of_N 15) with 15.
  change (Z.of_N 14) with 14. change (Z.of_N 1) with 1.
  change (Z.of_N 45) with 45. change (Z.of_N 6) with 6. change (Z.of_N 7) with 7.
  remember (2 ^ 4697) as P2. remember (2 ^ (Z.of_N m3 + 2)) as P3.
  lia.
Qed.

(** * 12. Master Halting Theorem *)

Theorem cet3_3round_champ_halts_exact : forall undef : Transition,
  halts_at_exact (ag1_with undef) ag2 c0 exact_halt_steps.
Proof.
  intro undef.
  pose proof state_70429 as H70429. cbv zeta in H70429.
  remember (run_N ag1 ag2 70429 c0) as c1 eqn:Ec1.
  destruct H70429 as [P1p1 [P1p2 [P1s1 [P1s2 [P1m2 [P1tr [P1fl [P1_94 [P1_95 [P1_96 [P1_97 [P1_98 [P1ge Hnc1]]]]]]]]]]]]].
  destruct K2_arithmetic as [q2 [Hq2 [HK2 [Hpow2 [Hn2eq Hgap2]]]]].
  destruct K3_arithmetic as [q3 [Hq3 [HK3 [Hpow3 [Hn3eq Hgap3]]]]].
  (* Round 2: counter + chase *)
  assert (Hn2_ge12 : (12 <= n_cyc2)%N) by (unfold n_cyc2; lia).
  destruct (round_decouple_and_chase c1 4657 4697 7%nat n_cyc2 K2 10
              ltac:(lia) ltac:(lia) ltac:(lia) Hn2_ge12 ltac:(lia) Hn2eq Hgap2
              P1p1 P1s1 P1p2 P1s2 P1m2 P1tr P1fl P1_94 P1_95 P1_96 P1_97 P1_98 P1ge)
    as [R2nc [R2p1 [R2s1 [R2p2 [R2s2 [R2m2 [R2tr [R2_8 [R2_9 [R2_10 [R2_11 R2ge]]]]]]]]]]].
  change (4697 - 3 + Z.of_nat 7 + 15 * Z.of_N K2) with x0_2_Z in *.
  set (c2 := run_N ag1 ag2 (15 * n_cyc2 + 15 * K2) c1) in *.
  (* Round 2: 45-step bounce at G = 10 *)
  assert (Hx0_2_ge : 26 <= x0_2_Z) by (unfold x0_2_Z; lia).
  assert (HR2tr' : forall z, -1 <= z <= x0_2_Z + 7 -> c2.(tape) z = true)
    by (intros z Hz; apply R2tr; lia).
  destruct (bounce_G10 x0_2_Z c2 Hx0_2_ge R2p1 R2s1 R2p2 R2s2 R2m2 HR2tr' R2_8 R2_9 R2_10 R2_11 R2ge)
    as [B2nc [B2p1 [B2s1 [B2p2 [B2s2 [B2m2 [B2tr [B2fl [B2_10 [B2_11 [B2_12 [B2_13 [B2_14 B2ge]]]]]]]]]]]]].
  set (c2b := run_N ag1 ag2 45 c2) in *.
  (* Round 3: counter + chase *)
  assert (Hn3_ge12 : (12 <= n_cyc3)%N) by (unfold n_cyc3; lia).
  destruct (round_decouple_and_chase c2b (x0_2_Z - 27) (x0_2_Z + 13) 1%nat n_cyc3 K3 8
              ltac:(lia) ltac:(lia) ltac:(lia) Hn3_ge12 ltac:(lia) Hn3eq Hgap3
              B2p1 B2s1 B2p2 B2s2 B2m2 B2tr
              ltac:(intros z Hz; apply B2fl; lia)
              ltac:(replace (x0_2_Z + 13 - 3) with (x0_2_Z + 10) by lia; exact B2_10)
              ltac:(replace (x0_2_Z + 13 - 2) with (x0_2_Z + 11) by lia; exact B2_11)
              ltac:(replace (x0_2_Z + 13 - 1) with (x0_2_Z + 12) by lia; exact B2_12)
              ltac:(exact B2_13)
              ltac:(replace (x0_2_Z + 13 + 1) with (x0_2_Z + 14) by lia; exact B2_14)
              ltac:(intros z Hz; apply B2ge; lia))
    as [R3nc [R3p1 [R3s1 [R3p2 [R3s2 [R3m2 [R3tr [R3_6 [R3_7 [R3_8 [R3_9 R3ge]]]]]]]]]]].
  set (x0_3 := (x0_2_Z + 13) - 3 + Z.of_nat 1 + 15 * Z.of_N K3) in *.
  set (c3 := run_N ag1 ag2 (15 * n_cyc3 + 15 * K3) c2b) in *.
  (* Final 7-step collision at G = 8 *)
  assert (Hx0_3_ge : 0 <= x0_3) by (unfold x0_3; lia).
  assert (HR3tr' : forall z, x0_3 <= z <= x0_3 + 5 -> c3.(tape) z = true)
    by (intros z Hz; apply R3tr; lia).
  destruct (suffix_7 x0_3 c3 R3p1 R3s1 R3p2 R3s2 HR3tr' R3_6 R3_7 R3_8 R3_9 R3ge)
    as [F7col F7nc].
  (* Assemble exact step count and non-collision *)
  assert (Hcol : collides_at ag1 ag2 c0 exact_halt_steps).
  { unfold collides_at, exact_halt_steps.
    rewrite !run_N_add, <- Ec1.
    change (run_N ag1 ag2 (15 * n_cyc2 + 15 * K2) c1) with c2.
    change (run_N ag1 ag2 45 c2) with c2b.
    change (run_N ag1 ag2 (15 * n_cyc3 + 15 * K3) c2b) with c3.
    exact F7col. }
  assert (Hnc : forall t, (t < exact_halt_steps)%N -> ~ collides_at ag1 ag2 c0 t).
  { intros t Ht. unfold collides_at, exact_halt_steps in *.
    assert (Hnc_2 : forall k, (k < 70429 + (15 * n_cyc2 + 15 * K2))%N ->
              (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2)).
    { intros k Hk.
      replace (70429 + (15 * n_cyc2 + 15 * K2))%N with ((15 * n_cyc2 + 15 * K2) + 70429)%N in Hk by lia.
      eapply no_coll_add; [exact Hnc1 | | exact Hk].
      intro j. rewrite <- Ec1. exact (R2nc j). }
    assert (Hnc_2b : forall k, (k < 70429 + (15 * n_cyc2 + 15 * K2) + 45)%N ->
              (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2)).
    { intros k Hk.
      replace (70429 + (15 * n_cyc2 + 15 * K2) + 45)%N
        with (45 + (70429 + (15 * n_cyc2 + 15 * K2)))%N in Hk by lia.
      eapply no_coll_add; [exact Hnc_2 | | exact Hk].
      intro j. rewrite run_N_add, <- Ec1. change (run_N ag1 ag2 (15 * n_cyc2 + 15 * K2) c1) with c2.
      exact (B2nc j). }
    assert (Hnc_3 : forall k, (k < 70429 + (15 * n_cyc2 + 15 * K2) + 45 + (15 * n_cyc3 + 15 * K3))%N ->
              (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2)).
    { intros k Hk.
      replace (70429 + (15 * n_cyc2 + 15 * K2) + 45 + (15 * n_cyc3 + 15 * K3))%N
        with ((15 * n_cyc3 + 15 * K3) + (70429 + (15 * n_cyc2 + 15 * K2) + 45))%N in Hk by lia.
      eapply no_coll_add; [exact Hnc_2b | | exact Hk].
      intro j. rewrite !run_N_add, <- Ec1.
      change (run_N ag1 ag2 (15 * n_cyc2 + 15 * K2) c1) with c2.
      change (run_N ag1 ag2 45 c2) with c2b. exact (R3nc j). }
    replace (70429 + (15 * n_cyc2 + 15 * K2) + 45 + (15 * n_cyc3 + 15 * K3) + 7)%N
      with (7 + (70429 + (15 * n_cyc2 + 15 * K2) + 45 + (15 * n_cyc3 + 15 * K3)))%N in Ht by lia.
    eapply no_coll_add; [exact Hnc_3 | | exact Ht].
    intro j. rewrite !run_N_add, <- Ec1.
    change (run_N ag1 ag2 (15 * n_cyc2 + 15 * K2) c1) with c2.
    change (run_N ag1 ag2 45 c2) with c2b.
    change (run_N ag1 ag2 (15 * n_cyc3 + 15 * K3) c2b) with c3. exact (F7nc j). }
  split.
  - unfold collides_at. destruct (run_N_undef_irrelevant undef exact_halt_steps) as [Heq _].
    rewrite Heq. exact Hcol.
  - intros t Ht Hc. unfold collides_at in Hc.
    destruct (run_N_undef_irrelevant undef t) as [Heq _].
    rewrite Heq in Hc. exact (Hnc t Ht Hc).
Qed.

Print Assumptions cet3_3round_champ_halts_exact.
