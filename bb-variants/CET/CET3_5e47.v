(** Formal Verification of the CET(3) 10^(5.28 * 10^47)-Step Halting Champion
    Machine: 1LB1RA_0RB1LC_1RA0LB | 1RB0RC_1LB1LC_1RA0RB
    Exact halting steps:
      exact_T_halt = (33 * 2^(m2 + 2) + 385836432255358370405772795837098717189166191380738) / 10
      where m2 = 1753801964797083501844421799259539623587119051732
    Verified in Rocq 9.1 with zero extra axioms ("Closed under the global context").
*)

From Stdlib Require Import ZArith NArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core CET Semantics *)

Inductive State : Type := StA | StB | StC.
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

(** * 2. Target Machine Definition: 1LB1RA_0RB1LC_1RA0LB | 1RB0RC_1LB1LC_1RA0RB *)

Definition ag1 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StA, true  => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StB, false => {| write_sym := false; move_dir := MoveR; next_state := StB |}
  | StB, true  => {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  | StC, false => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StC, true  => {| write_sym := false; move_dir := MoveL; next_state := StB |}
  end.

Definition ag2 (s : State) (b : bool) : Transition :=
  match s, b with
  | StA, false => {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StA, true  => {| write_sym := false; move_dir := MoveR; next_state := StC |}
  | StB, false => {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StB, true  => {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  | StC, false => {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StC, true  => {| write_sym := false; move_dir := MoveR; next_state := StB |}
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

(** * 4. Fast Binary-Tree Tape Engine for Concrete Prefix / Bounce / Collision *)

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
Proof.
  induction p; intros v t; destruct t; simpl; auto.
Qed.

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

(** * 5. Concrete Prefix Verification (t = 0 .. 3842) *)

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

Fixpoint check_alt_pairs_nat (lo : Z) (cnt : nat) (t : BTree) : bool :=
  match cnt with
  | O => true
  | S n => bt_get (z_to_pos lo) t && negb (bt_get (z_to_pos (lo + 1)) t) &&
           check_alt_pairs_nat (lo + 2) n t
  end.

Lemma check_alt_pairs_nat_sound : forall cnt lo t i,
  check_alt_pairs_nat lo cnt t = true ->
  (i < N.of_nat cnt)%N ->
  bt_interp t (lo + 2 * Z.of_N i) = true /\
  bt_interp t (lo + 2 * Z.of_N i + 1) = false.
Proof.
  induction cnt; intros lo t i Hc Hi; simpl in Hc.
  - lia.
  - rewrite !andb_true_iff in Hc. destruct Hc as [[H0 H1] Hrest].
    rewrite negb_true_iff in H1.
    destruct (N.eq_0_gt_0_cases i) as [Hi0 | Higt].
    + subst i. replace (lo + 2 * Z.of_N 0) with lo by lia.
      replace (lo + 1) with (lo + 1) by lia. split; assumption.
    + assert (Hi' : (i - 1 < N.of_nat cnt)%N) by lia.
      destruct (IHcnt (lo + 2) t (i - 1)%N Hrest Hi') as [A B].
      replace (lo + 2 * Z.of_N i) with (lo + 2 + 2 * Z.of_N (i - 1)) by lia.
      replace (lo + 2 * Z.of_N i + 1) with (lo + 2 + 2 * Z.of_N (i - 1) + 1) by lia.
      split; assumption.
Qed.

Definition alt_pairs (lo : Z) (n : N) (tp : Tape) : Prop :=
  forall i : N, (i < n)%N -> tp (lo + 2 * Z.of_N i) = true /\ tp (lo + 2 * Z.of_N i + 1) = false.

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

Lemma fc0_eq_c0 : cfg_eq (fc_to_cfg fc0) c0.
Proof.
  constructor; simpl; auto.
  intro z. unfold bt_interp, empty_tape. simpl. apply bt_get_empty.
Qed.

Definition check_fc_3842 (st : FastConfig * bool) : bool :=
  let (fc, ok) := st in
  ok &&
  (fc.(fpos1) =? -4) &&
  (fc.(fpos2) =? 350) &&
  (match fc.(fstate1), fc.(fstate2) with StB, StC => true | _, _ => false end) &&
  bt_bounded_aux (-2) 354 (fun q => q) fc.(ftape) &&
  check_alt_pairs_nat (-2) 161 fc.(ftape) &&
  check_all_true_nat 320 30 fc.(ftape) &&
  negb (bt_get (z_to_pos 350) fc.(ftape)) &&
  check_all_true_nat 351 4 fc.(ftape).

Lemma fc_3842_ok : check_fc_3842 (N.iter 3842 (fast_step_chk_ge (-4)) (fc0, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma check_states_BC : forall s1 s2,
  (match s1, s2 with StB, StC => true | _, _ => false end = true) ->
  s1 = StB /\ s2 = StC.
Proof. destruct s1, s2; simpl; intros H; try discriminate; auto. Qed.

Lemma state_3842 :
  let c := run_N ag1 ag2 3842 c0 in
  c.(pos1) = -4 /\ c.(pos2) = 350 /\ c.(state1) = StB /\ c.(state2) = StC /\
  (forall z, z <= -3 -> c.(tape) z = false) /\
  alt_pairs (-2) 161 c.(tape) /\
  (forall z, 320 <= z <= 349 -> c.(tape) z = true) /\
  c.(tape) 350 = false /\
  (forall z, 351 <= z <= 354 -> c.(tape) z = true) /\
  (forall z, 355 <= z -> c.(tape) z = false) /\
  (forall t, (t < 3842)%N -> (run_N ag1 ag2 t c0).(pos1) <> (run_N ag1 ag2 t c0).(pos2)).
Proof.
  pose proof fc_3842_ok as Hok.
  remember (N.iter 3842 (fast_step_chk_ge (-4)) (fc0, true)) as st eqn:E.
  destruct st as [fc_end ok_end].
  unfold check_fc_3842 in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[[[[Hok_b Hp1] Hp2] Hst] Hbd] Halt] Htr320] H350] Htr351].
  rewrite Z.eqb_eq in Hp1, Hp2.
  rewrite negb_true_iff in H350.
  apply check_states_BC in Hst. destruct Hst as [Hs1 Hs2].
  assert (Hfc : fc_end = N.iter 3842 fast_step fc0).
  { pose proof (fast_step_chk_ge_fst 3842 (-4) fc0 true) as Hfst.
    rewrite <- E in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 3842 (fast_step_chk_ge (-4)) (fc0, true)) = true).
  { rewrite <- E. exact Hok_b. }
  clear E Hok_b.
  pose proof (fast_run_sound 3842 fc0) as Hrun.
  pose proof (run_N_proper ag1 ag2 3842 _ _ fc0_eq_c0) as Hprop.
  assert (Heq : cfg_eq (fc_to_cfg fc_end) (run_N ag1 ag2 3842 c0)).
  { rewrite Hfc. eapply cfg_eq_trans; [exact Hrun | exact Hprop]. }
  clear Hfc Hrun Hprop.
  destruct Heq as [Ep1 Ep2 Es1 Es2 Etp].
  rewrite fc_to_cfg_pos1 in Ep1. rewrite fc_to_cfg_pos2 in Ep2.
  change (state1 (fc_to_cfg fc_end)) with fc_end.(fstate1) in Es1.
  change (state2 (fc_to_cfg fc_end)) with fc_end.(fstate2) in Es2.
  change (tape (fc_to_cfg fc_end)) with (bt_interp fc_end.(ftape)) in Etp.
  intro c. subst c.
  split; [rewrite <- Ep1; exact Hp1 |].
  split; [rewrite <- Ep2; exact Hp2 |].
  split; [rewrite <- Es1; exact Hs1 |].
  split; [rewrite <- Es2; exact Hs2 |].
  split; [intros z Hz; rewrite <- Etp; eapply bt_bounded_sound; [exact Hbd | lia] |].
  split; [intros i Hi; rewrite <- !Etp; apply (check_alt_pairs_nat_sound 161 (-2) fc_end.(ftape) i Halt);
          change (N.of_nat 161) with 161%N; exact Hi |].
  split; [intros z Hz; rewrite <- Etp; eapply check_all_true_nat_sound; [exact Htr320 |];
          change (Z.of_nat 30) with 30; lia |].
  split; [rewrite <- Etp; exact H350 |].
  split; [intros z Hz; rewrite <- Etp; eapply check_all_true_nat_sound; [exact Htr351 |];
          change (Z.of_nat 4) with 4; lia |].
  split; [intros z Hz; rewrite <- Etp; eapply bt_bounded_sound; [exact Hbd | lia] |].
  intros t Ht.
  destruct (N.eq_0_gt_0_cases t) as [Ht0 | Htgt0].
  - subst t. rewrite run_N_0. unfold c0; simpl; lia.
  - destruct (fast_step_chk_ge_sound 3842 (-4) fc0 true Hsnd) as [_ Hchk].
    assert (Hk : (1 <= t <= 3842)%N) by lia.
    destruct (Hchk t Hk) as [Hneq _].
    pose proof (fast_run_sound t fc0) as Hrt.
    pose proof (run_N_proper ag1 ag2 t _ _ fc0_eq_c0) as Hpt.
    assert (Heqt : cfg_eq (fc_to_cfg (N.iter t fast_step fc0)) (run_N ag1 ag2 t c0))
      by (eapply cfg_eq_trans; eauto).
    destruct Heqt as [Tp1 Tp2 _ _ _].
    rewrite fc_to_cfg_pos1 in Tp1. rewrite fc_to_cfg_pos2 in Tp2.
    lia.
Qed.

(** * 6. Single-Agent Execution, Locality, Shift Invariance, and Decoupling *)

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

Lemma srun_1 : forall ag sc, srun ag 1%N sc = sstep ag sc.
Proof. reflexivity. Qed.

Lemma srun_succ : forall ag n sc, srun ag (N.succ n) sc = sstep ag (srun ag n sc).
Proof. intros. unfold srun. apply N.iter_succ. Qed.

Lemma srun_add : forall ag p q sc, srun ag (p + q) sc = srun ag p (srun ag q sc).
Proof. intros. unfold srun. apply N.iter_add. Qed.

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

Definition agree_ge (lo : Z) (t1 t2 : Tape) : Prop :=
  forall z, lo <= z -> t1 z = t2 z.

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
  - rewrite !run_N_0. cbv zeta. repeat match goal with |- _ /\ _ => split end; simpl; auto; try (intros k Hk; lia).
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
    cbv zeta. repeat match goal with |- _ /\ _ => split end; simpl; auto.
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
Definition shift_cfg (d : Z) (c : Config) : Config :=
  {| pos1 := c.(pos1) + d; pos2 := c.(pos2) + d;
     state1 := c.(state1); state2 := c.(state2); tape := shift_tape d c.(tape) |}.

Lemma step_shift : forall a1 a2 d c,
  cfg_eq (shift_cfg d (step a1 a2 c)) (step a1 a2 (shift_cfg d c)).
Proof.
  intros a1 a2 d c. unfold shift_cfg, step, shift_tape, move_pos. simpl.
  replace (pos1 c + d - d) with (pos1 c) by lia.
  replace (pos2 c + d - d) with (pos2 c) by lia.
  constructor; simpl;
    try destruct (move_dir (a1 _ _)); try destruct (move_dir (a2 _ _)); try lia; auto.
  intro z. unfold write_tape.
  destruct (Z.eqb_spec (z - d) (pos1 c)), (Z.eqb_spec z (pos1 c + d)),
           (Z.eqb_spec (z - d) (pos2 c)), (Z.eqb_spec z (pos2 c + d)); auto; lia.
Qed.

Lemma run_N_shift : forall a1 a2 d n c,
  cfg_eq (shift_cfg d (run_N a1 a2 n c)) (run_N a1 a2 n (shift_cfg d c)).
Proof.
  intros a1 a2 d n c. induction n using N.peano_ind.
  - rewrite !run_N_0. constructor; simpl; auto. intro; auto.
  - rewrite !run_N_succ.
    eapply cfg_eq_trans; [apply step_shift | apply step_proper; exact IHn].
Qed.

Lemma shift_cfg_pos1 : forall d c, (shift_cfg d c).(pos1) = c.(pos1) + d.
Proof. intros; reflexivity. Qed.

Lemma shift_cfg_pos2 : forall d c, (shift_cfg d c).(pos2) = c.(pos2) + d.
Proof. intros; reflexivity. Qed.

Ltac splits := repeat match goal with |- _ /\ _ => split | |- let _ := _ in _ /\ _ => cbv zeta; split end.
Ltac proj_eval := cbn [spos sstate stape write_sym move_dir next_state].

(** * 7. Agent 1 (Binary Counter on N) and Agent 2 (Period-11 Glider) *)

Lemma ag1_wipe_pairs : forall K lo sc,
  sc.(spos) = lo + 2 * Z.of_N K - 2 ->
  sc.(sstate) = StB ->
  (forall z, lo - 1 <= z <= lo + 2 * Z.of_N K - 2 -> sc.(stape) z = true) ->
  (forall t, (t < 2 * K)%N -> lo - 1 <= (srun ag1 t sc).(spos) <= lo + 2 * Z.of_N K - 2) /\
  let sc' := srun ag1 (2 * K) sc in
  sc'.(spos) = lo - 2 /\
  sc'.(sstate) = StB /\
  (forall i : N, (i < K)%N ->
    sc'.(stape) (lo + 2 * Z.of_N i) = true /\ sc'.(stape) (lo + 2 * Z.of_N i - 1) = false) /\
  (forall z, z < lo - 1 \/ z > lo + 2 * Z.of_N K - 2 -> sc'.(stape) z = sc.(stape) z).
Proof.
  intro K. induction K using N.peano_ind; intros lo sc Hp Hs Ht.
  - rewrite N.mul_0_r, srun_0. cbv zeta. splits; [intros; lia | lia | exact Hs | intros; lia | auto].
  - rewrite N2Z.inj_succ in *.
    set (top := lo + 2 * Z.of_N K).
    assert (Hp_eq : sc.(spos) = top) by (unfold top; lia).
    (* 2 steps at top, top - 1 *)
    remember (srun ag1 1 sc) as sc1 eqn:E1.
    assert (H1 : sc1.(spos) = top - 1 /\ sc1.(sstate) = StC /\ forall z, sc1.(stape) z = sc.(stape) z).
    { rewrite E1, srun_1. unfold sstep, ag1, move_pos. rewrite Hp_eq, Hs, (Ht top ltac:(unfold top; lia)). proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z top); [subst z; rewrite write_tape_same; symmetry; apply Ht; unfold top; lia | apply write_tape_other; auto]. }
    destruct H1 as [P1 [S1 T1]].
    remember (srun ag1 2 sc) as sc2 eqn:E2.
    assert (H2 : sc2.(spos) = top - 2 /\ sc2.(sstate) = StB /\ sc2.(stape) (top - 1) = false /\
                 forall z, z <> top - 1 -> sc2.(stape) z = sc.(stape) z).
    { assert (Hs2 : sc2 = sstep ag1 sc1) by (rewrite E2, E1; change 2%N with (N.succ 1); apply srun_succ).
      rewrite Hs2. unfold sstep, ag1, move_pos. rewrite P1, S1, T1, (Ht (top - 1) ltac:(unfold top; lia)). proj_eval.
      splits; [lia | reflexivity | apply write_tape_same | intros z Hz; rewrite write_tape_other by auto; apply T1]. }
    destruct H2 as [P2 [S2 [W2 O2]]].
    assert (Ht2 : forall z, lo - 1 <= z <= lo + 2 * Z.of_N K - 2 -> sc2.(stape) z = true).
    { intros z Hz. rewrite O2 by (unfold top; lia). apply Ht. unfold top in *; lia. }
    assert (Hp2 : sc2.(spos) = lo + 2 * Z.of_N K - 2) by (unfold top in P2; lia).
    destruct (IHK lo sc2 Hp2 S2 Ht2) as [IHbd [IHp [IHs [IHalt IHo]]]].
    replace (2 * N.succ K)%N with (2 * K + 2)%N by lia.
    cbv zeta. rewrite srun_add, <- E2.
    splits.
    + intros t Htk. destruct (N.lt_ge_cases t 2%N) as [Ht_lt | Ht_ge].
      * assert (Hc : (t = 0 \/ t = 1)%N) by lia.
        destruct Hc as [-> | ->]; [rewrite srun_0; unfold top in Hp_eq; lia | rewrite <- E1; unfold top in P1; lia].
      * replace t with ((t - 2) + 2)%N by lia. rewrite srun_add, <- E2.
        pose proof (IHbd (t - 2)%N ltac:(lia)). lia.
    + exact IHp.
    + exact IHs.
    + intros i Hi. destruct (N.lt_ge_cases i K) as [Hi1 | Hi2].
      * apply IHalt; exact Hi1.
      * replace i with K by lia.
        rewrite !IHo by (unfold top; lia).
        split; [rewrite O2 by (unfold top; lia); apply Ht; unfold top; lia | exact W2].
    + intros z Hz. rewrite IHo by (unfold top in *; lia). rewrite O2 by (unfold top in *; lia). reflexivity.
Qed.

Definition S_val (m : N) : N := (3 * 2 ^ (m + 2) - 2 * m - 8)%N.

Lemma pow2_ge_8 : forall n : N, (3 <= n)%N -> (8 <= 2 ^ n)%N.
Proof.
  intros n Hn.
  replace n with ((n - 3) + 3)%N by lia.
  rewrite N.pow_add_r. change (2 ^ 3)%N with 8%N.
  assert (Hpos : (2 ^ (n - 3) <> 0)%N) by (apply N.pow_nonzero; discriminate).
  nia.
Qed.

Lemma S_val_1 : S_val 1%N = 14%N.
Proof. vm_compute. reflexivity. Qed.

Lemma n_lt_pow2 : forall n : N, (n < 2 ^ n)%N.
Proof.
  intro n. induction n using N.peano_ind.
  - simpl; lia.
  - rewrite N.pow_succ_r'. lia.
Qed.

Lemma S_val_succ : forall m : N, (1 <= m)%N -> S_val (N.succ m) = (2 * S_val m + 2 * m + 6)%N.
Proof.
  intros m Hm. unfold S_val.
  replace (N.succ m + 2)%N with (N.succ (m + 2)) by lia.
  rewrite N.pow_succ_r'.
  pose proof (n_lt_pow2 (m + 2)).
  pose proof (pow2_ge_8 (m + 2) ltac:(lia)).
  lia.
Qed.

Lemma ag1_counter : forall k sc,
  let m := (k + 1)%N in
  sc.(spos) = -4 ->
  sc.(sstate) = StB ->
  sc.(stape) (-4) = false ->
  sc.(stape) (-3) = false ->
  alt_pairs (-2) m sc.(stape) ->
  (forall t, (t < S_val m)%N -> -4 <= (srun ag1 t sc).(spos) <= -3 + 2 * Z.of_N m) /\
  let sc' := srun ag1 (S_val m) sc in
  sc'.(spos) = -2 + 2 * Z.of_N m /\
  sc'.(sstate) = StA /\
  sc'.(stape) (-4) = false /\
  (forall z, -3 <= z <= -3 + 2 * Z.of_N m -> sc'.(stape) z = true) /\
  (forall z, z < -4 \/ z >= -2 + 2 * Z.of_N m -> sc'.(stape) z = sc.(stape) z).
Proof.
  intro k. induction k using N.peano_ind; intros sc m Hp Hs Hf4 Hf3 Halt.
  - (* k = 0, m = 1, S_val 1 = 14 *)
    change m with 1%N. rewrite S_val_1.
    destruct (Halt 0%N ltac:(lia)) as [Ht_m2 Hf_m1].
    replace (-2 + 2 * Z.of_N 0) with (-2) in Ht_m2 by lia.
    replace (-2 + 2 * Z.of_N 0 + 1) with (-1) in Hf_m1 by lia.
    remember (srun ag1 1 sc) as sc1 eqn:E1.
    assert (H1 : sc1.(spos) = -3 /\ sc1.(sstate) = StB /\ forall z, sc1.(stape) z = sc.(stape) z).
    { rewrite E1, srun_1. unfold sstep, ag1, move_pos. rewrite Hp, Hs, Hf4. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-4)); [subst z; rewrite write_tape_same; symmetry; exact Hf4 | apply write_tape_other; auto]. }
    destruct H1 as [P1 [S1 T1]].
    remember (srun ag1 2 sc) as sc2 eqn:E2.
    assert (H2 : sc2.(spos) = -2 /\ sc2.(sstate) = StB /\ forall z, sc2.(stape) z = sc.(stape) z).
    { assert (Hs2 : sc2 = sstep ag1 sc1) by (rewrite E2, E1; change 2%N with (N.succ 1); apply srun_succ).
      rewrite Hs2. unfold sstep, ag1, move_pos. rewrite P1, S1, T1, Hf3. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-3)); [subst z; rewrite write_tape_same; symmetry; exact Hf3 | rewrite write_tape_other by auto; apply T1]. }
    destruct H2 as [P2 [S2 T2]].
    remember (srun ag1 3 sc) as sc3 eqn:E3.
    assert (H3 : sc3.(spos) = -3 /\ sc3.(sstate) = StC /\ forall z, sc3.(stape) z = sc.(stape) z).
    { assert (Hs3 : sc3 = sstep ag1 sc2) by (rewrite E3, E2; change 3%N with (N.succ 2); apply srun_succ).
      rewrite Hs3. unfold sstep, ag1, move_pos. rewrite P2, S2, T2, Ht_m2. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-2)); [subst z; rewrite write_tape_same; symmetry; exact Ht_m2 | rewrite write_tape_other by auto; apply T2]. }
    destruct H3 as [P3 [S3 T3]].
    remember (srun ag1 4 sc) as sc4 eqn:E4.
    assert (H4 : sc4.(spos) = -2 /\ sc4.(sstate) = StA /\ sc4.(stape) (-3) = true /\
                 forall z, z <> -3 -> sc4.(stape) z = sc.(stape) z).
    { assert (Hs4 : sc4 = sstep ag1 sc3) by (rewrite E4, E3; change 4%N with (N.succ 3); apply srun_succ).
      rewrite Hs4. unfold sstep, ag1, move_pos. rewrite P3, S3, T3, Hf3. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same | intros z Hz; rewrite write_tape_other by auto; apply T3]. }
    destruct H4 as [P4 [S4 [W4 O4]]].
    remember (srun ag1 5 sc) as sc5 eqn:E5.
    assert (H5 : sc5.(spos) = -1 /\ sc5.(sstate) = StA /\ forall z, sc5.(stape) z = sc4.(stape) z).
    { assert (Hs5 : sc5 = sstep ag1 sc4) by (rewrite E5, E4; change 5%N with (N.succ 4); apply srun_succ).
      rewrite Hs5. unfold sstep, ag1, move_pos. rewrite P4, S4, O4 by lia. rewrite Ht_m2. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-2)); [subst z; rewrite write_tape_same, O4 by lia; symmetry; exact Ht_m2 | apply write_tape_other; auto]. }
    destruct H5 as [P5 [S5 T5]].
    remember (srun ag1 6 sc) as sc6 eqn:E6.
    assert (H6 : sc6.(spos) = -2 /\ sc6.(sstate) = StB /\ sc6.(stape) (-1) = true /\
                 forall z, z <> -1 -> sc6.(stape) z = sc4.(stape) z).
    { assert (Hs6 : sc6 = sstep ag1 sc5) by (rewrite E6, E5; change 6%N with (N.succ 5); apply srun_succ).
      rewrite Hs6. unfold sstep, ag1, move_pos. rewrite P5, S5, T5, O4 by lia. rewrite Hf_m1. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same | intros z Hz; rewrite write_tape_other by auto; apply T5]. }
    destruct H6 as [P6 [S6 [W6 O6]]].
    remember (srun ag1 7 sc) as sc7 eqn:E7.
    assert (H7 : sc7.(spos) = -3 /\ sc7.(sstate) = StC /\ forall z, sc7.(stape) z = sc6.(stape) z).
    { assert (Hs7 : sc7 = sstep ag1 sc6) by (rewrite E7, E6; change 7%N with (N.succ 6); apply srun_succ).
      rewrite Hs7. unfold sstep, ag1, move_pos.
      assert (Hr6 : sc6.(stape) (-2) = true) by (rewrite O6, O4 by lia; exact Ht_m2).
      rewrite P6, S6, Hr6. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-2)); [subst z; rewrite write_tape_same; symmetry; exact Hr6 | apply write_tape_other; auto]. }
    destruct H7 as [P7 [S7 T7]].
    remember (srun ag1 8 sc) as sc8 eqn:E8.
    assert (H8 : sc8.(spos) = -4 /\ sc8.(sstate) = StB /\ sc8.(stape) (-3) = false /\
                 forall z, z <> -3 -> sc8.(stape) z = sc6.(stape) z).
    { assert (Hs8 : sc8 = sstep ag1 sc7) by (rewrite E8, E7; change 8%N with (N.succ 7); apply srun_succ).
      rewrite Hs8. unfold sstep, ag1, move_pos.
      assert (Hr7 : sc7.(stape) (-3) = true) by (rewrite T7, O6 by lia; exact W4).
      rewrite P7, S7, Hr7. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same | intros z Hz; rewrite write_tape_other by auto; apply T7]. }
    destruct H8 as [P8 [S8 [W8 O8]]].
    remember (srun ag1 9 sc) as sc9 eqn:E9.
    assert (H9 : sc9.(spos) = -3 /\ sc9.(sstate) = StB /\ forall z, sc9.(stape) z = sc8.(stape) z).
    { assert (Hs9 : sc9 = sstep ag1 sc8) by (rewrite E9, E8; change 9%N with (N.succ 8); apply srun_succ).
      rewrite Hs9. unfold sstep, ag1, move_pos.
      assert (Hr8 : sc8.(stape) (-4) = false) by (rewrite O8, O6, O4 by lia; exact Hf4).
      rewrite P8, S8, Hr8. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-4)); [subst z; rewrite write_tape_same; symmetry; exact Hr8 | apply write_tape_other; auto]. }
    destruct H9 as [P9 [S9 T9]].
    remember (srun ag1 10 sc) as sc10 eqn:E10.
    assert (H10 : sc10.(spos) = -2 /\ sc10.(sstate) = StB /\ forall z, sc10.(stape) z = sc8.(stape) z).
    { assert (Hs10 : sc10 = sstep ag1 sc9) by (rewrite E10, E9; change 10%N with (N.succ 9); apply srun_succ).
      rewrite Hs10. unfold sstep, ag1, move_pos.
      rewrite P9, S9, T9, W8. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-3)); [subst z; rewrite write_tape_same; symmetry; exact W8 | rewrite write_tape_other by auto; apply T9]. }
    destruct H10 as [P10 [S10 T10]].
    remember (srun ag1 11 sc) as sc11 eqn:E11.
    assert (H11 : sc11.(spos) = -3 /\ sc11.(sstate) = StC /\ forall z, sc11.(stape) z = sc8.(stape) z).
    { assert (Hs11 : sc11 = sstep ag1 sc10) by (rewrite E11, E10; change 11%N with (N.succ 10); apply srun_succ).
      rewrite Hs11. unfold sstep, ag1, move_pos.
      assert (Hr10 : sc10.(stape) (-2) = true) by (rewrite T10, O8, O6, O4 by lia; exact Ht_m2).
      rewrite P10, S10, Hr10. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-2)); [subst z; rewrite write_tape_same, <- T10; symmetry; exact Hr10 | rewrite write_tape_other by auto; apply T10]. }
    destruct H11 as [P11 [S11 T11]].
    remember (srun ag1 12 sc) as sc12 eqn:E12.
    assert (H12 : sc12.(spos) = -2 /\ sc12.(sstate) = StA /\ sc12.(stape) (-3) = true /\
                  forall z, z <> -3 -> sc12.(stape) z = sc8.(stape) z).
    { assert (Hs12 : sc12 = sstep ag1 sc11) by (rewrite E12, E11; change 12%N with (N.succ 11); apply srun_succ).
      rewrite Hs12. unfold sstep, ag1, move_pos. rewrite P11, S11, T11, W8. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same | intros z Hz; rewrite write_tape_other by auto; apply T11]. }
    destruct H12 as [P12 [S12 [W12 O12]]].
    remember (srun ag1 13 sc) as sc13 eqn:E13.
    assert (H13 : sc13.(spos) = -1 /\ sc13.(sstate) = StA /\ forall z, sc13.(stape) z = sc12.(stape) z).
    { assert (Hs13 : sc13 = sstep ag1 sc12) by (rewrite E13, E12; change 13%N with (N.succ 12); apply srun_succ).
      rewrite Hs13. unfold sstep, ag1, move_pos.
      assert (Hr12 : sc12.(stape) (-2) = true) by (rewrite O12, O8, O6, O4 by lia; exact Ht_m2).
      rewrite P12, S12, Hr12. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-2)); [subst z; rewrite write_tape_same; symmetry; exact Hr12 | apply write_tape_other; auto]. }
    destruct H13 as [P13 [S13 T13]].
    remember (srun ag1 14 sc) as sc14 eqn:E14.
    assert (H14 : sc14.(spos) = 0 /\ sc14.(sstate) = StA /\ forall z, sc14.(stape) z = sc12.(stape) z).
    { assert (Hs14 : sc14 = sstep ag1 sc13) by (rewrite E14, E13; change 14%N with (N.succ 13); apply srun_succ).
      rewrite Hs14. unfold sstep, ag1, move_pos.
      assert (Hr13 : sc13.(stape) (-1) = true) by (rewrite T13, O12, O8 by lia; exact W6).
      rewrite P13, S13, Hr13. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-1)); [subst z; rewrite write_tape_same, <- T13; symmetry; exact Hr13 | rewrite write_tape_other by auto; apply T13]. }
    destruct H14 as [P14 [S14 T14]].
    change (Z.of_N 1) with 1. cbv zeta. splits.
    + intros t Ht.
      assert (Hcases : (t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/
                        t = 7 \/ t = 8 \/ t = 9 \/ t = 10 \/ t = 11 \/ t = 12 \/ t = 13)%N) by lia.
      destruct Hcases as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]];
        [rewrite srun_0; lia | rewrite <- E1; lia | rewrite <- E2; lia | rewrite <- E3; lia |
         rewrite <- E4; lia | rewrite <- E5; lia | rewrite <- E6; lia | rewrite <- E7; lia |
         rewrite <- E8; lia | rewrite <- E9; lia | rewrite <- E10; lia | rewrite <- E11; lia |
         rewrite <- E12; lia | rewrite <- E13; lia].
    + lia.
    + exact S14.
    + rewrite T14, O12, O8, O6, O4 by lia. exact Hf4.
    + intros z Hz. rewrite T14.
      assert (Hzc : z = -3 \/ z = -2 \/ z = -1) by lia.
      destruct Hzc as [-> | [-> | ->]].
      * exact W12.
      * rewrite O12, O8, O6, O4 by lia. exact Ht_m2.
      * rewrite O12, O8 by lia. exact W6.
    + intros z Hz. rewrite T14, O12, O8, O6, O4 by lia. reflexivity.
  - (* Inductive step: k -> N.succ k, i.e., m -> N.succ m *)
    set (m_prev := (k + 1)%N) in *.
    unfold m in *. clear m.
    replace (N.succ k + 1)%N with (N.succ m_prev) in * by (unfold m_prev; lia).
    assert (Halt_prev : alt_pairs (-2) m_prev sc.(stape)) by (intros i Hi; apply Halt; lia).
    destruct (IHk sc Hp Hs Hf4 Hf3 Halt_prev) as [Bd1 [P1 [S1 [F1 [T1 O1]]]]].
    set (t1 := S_val m_prev) in *.
    remember (srun ag1 t1 sc) as sc1 eqn:E1.
    destruct (Halt m_prev ltac:(lia)) as [Hm_t Hm_f].
    (* Step 2: 2 steps from (-2 + 2*m_prev, StA) across (true, false) to (-2 + 2*m_prev, StB) *)
    remember (srun ag1 1 sc1) as sc2a eqn:E2a.
    assert (H2a : sc2a.(spos) = -1 + 2 * Z.of_N m_prev /\ sc2a.(sstate) = StA /\
                  forall z, sc2a.(stape) z = sc1.(stape) z).
    { rewrite E2a, srun_1. unfold sstep, ag1, move_pos.
      rewrite P1, S1, O1 by lia. rewrite Hm_t. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-2 + 2 * Z.of_N m_prev));
        [subst z; rewrite write_tape_same, O1 by lia; symmetry; exact Hm_t | apply write_tape_other; auto]. }
    destruct H2a as [P2a [S2a T2a]].
    remember (srun ag1 2 sc1) as sc2 eqn:E2.
    assert (H2 : sc2.(spos) = -2 + 2 * Z.of_N m_prev /\ sc2.(sstate) = StB /\
                 sc2.(stape) (-1 + 2 * Z.of_N m_prev) = true /\
                 forall z, z <> -1 + 2 * Z.of_N m_prev -> sc2.(stape) z = sc1.(stape) z).
    { assert (Hs2 : sc2 = sstep ag1 sc2a) by (rewrite E2, E2a; change 2%N with (N.succ 1); apply srun_succ).
      assert (Hr2_in : sc.(stape) (-1 + 2 * Z.of_N m_prev) = false)
        by (replace (-1 + 2 * Z.of_N m_prev) with (-2 + 2 * Z.of_N m_prev + 1) by lia; exact Hm_f).
      rewrite Hs2. unfold sstep, ag1, move_pos. rewrite P2a, S2a, T2a, O1, Hr2_in by lia. proj_eval.
      splits; [lia | reflexivity | apply write_tape_same | intros z Hz; rewrite write_tape_other by auto; apply T2a]. }
    destruct H2 as [P2 [S2 [W2 O2]]].
    (* Step 3: ag1_wipe_pairs for (m_prev + 1) pairs *)
    assert (Hp2' : sc2.(spos) = -2 + 2 * Z.of_N (m_prev + 1) - 2) by (rewrite N2Z.inj_add; lia).
    assert (Ht2' : forall z, -2 - 1 <= z <= -2 + 2 * Z.of_N (m_prev + 1) - 2 -> sc2.(stape) z = true).
    { intros z Hz. rewrite N2Z.inj_add in Hz.
      destruct (Z.eq_dec z (-2 + 2 * Z.of_N m_prev)).
      - subst z. rewrite O2, O1 by lia. exact Hm_t.
      - rewrite O2 by lia. apply T1. lia. }
    destruct (ag1_wipe_pairs (m_prev + 1) (-2) sc2 Hp2' S2 Ht2') as [Bd3 [P3 [S3 [Alt3 O3]]]].
    remember (srun ag1 (2 * (m_prev + 1)) sc2) as sc3 eqn:E3.
    (* Step 4: second call to IHk on sc3 *)
    assert (Hp3' : sc3.(spos) = -4) by lia.
    assert (Hf3_4 : sc3.(stape) (-4) = false) by (rewrite O3, O2 by (rewrite ?N2Z.inj_add; lia); exact F1).
    assert (Hf3_3 : sc3.(stape) (-3) = false) by (destruct (Alt3 0%N ltac:(lia)) as [_ H0]; exact H0).
    assert (Halt3 : alt_pairs (-2) m_prev sc3.(stape)).
    { intros i Hi.
      destruct (Alt3 i ltac:(lia)) as [Ha _].
      destruct (Alt3 (N.succ i) ltac:(lia)) as [_ Hb].
      rewrite N2Z.inj_succ in Hb.
      replace (-2 + 2 * Z.of_N i + 1) with (-2 + 2 * Z.succ (Z.of_N i) - 1) by lia.
      split; assumption. }
    destruct (IHk sc3 Hp3' S3 Hf3_4 Hf3_3 Halt3) as [Bd4 [P4 [S4 [F4 [T4 O4]]]]].
    remember (srun ag1 t1 sc3) as sc4 eqn:E4.
    (* Step 5: 2 final steps across (-2 + 2*m_prev, -1 + 2*m_prev) -> 2*m_prev, StA *)
    remember (srun ag1 1 sc4) as sc5a eqn:E5a.
    assert (Hr4a : sc4.(stape) (-2 + 2 * Z.of_N m_prev) = true).
    { rewrite O4 by lia. destruct (Alt3 m_prev ltac:(lia)) as [Hm _]. exact Hm. }
    assert (H5a : sc5a.(spos) = -1 + 2 * Z.of_N m_prev /\ sc5a.(sstate) = StA /\
                  forall z, sc5a.(stape) z = sc4.(stape) z).
    { rewrite E5a, srun_1. unfold sstep, ag1, move_pos. rewrite P4, S4, Hr4a. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-2 + 2 * Z.of_N m_prev));
        [subst z; rewrite write_tape_same; symmetry; exact Hr4a | apply write_tape_other; auto]. }
    destruct H5a as [P5a [S5a T5a]].
    remember (srun ag1 2 sc4) as sc5 eqn:E5.
    assert (Hr4b : sc4.(stape) (-1 + 2 * Z.of_N m_prev) = true).
    { rewrite O4, O3 by (rewrite ?N2Z.inj_add; lia). exact W2. }
    assert (H5 : sc5.(spos) = -2 + 2 * Z.of_N (N.succ m_prev) /\ sc5.(sstate) = StA /\
                 forall z, sc5.(stape) z = sc4.(stape) z).
    { assert (Hs5 : sc5 = sstep ag1 sc5a) by (rewrite E5, E5a; change 2%N with (N.succ 1); apply srun_succ).
      rewrite Hs5. unfold sstep, ag1, move_pos. rewrite P5a, S5a, T5a, Hr4b, N2Z.inj_succ. proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z (-1 + 2 * Z.of_N m_prev));
        [subst z; rewrite write_tape_same; symmetry; exact Hr4b | rewrite write_tape_other by auto; apply T5a]. }
    destruct H5 as [P5 [S5 T5]].
    (* Total step count *)
    assert (Htot : S_val (N.succ m_prev) = (2 + (t1 + (2 * (m_prev + 1) + (2 + t1))))%N).
    { rewrite S_val_succ by lia. unfold t1. lia. }
    rewrite Htot.
    remember (srun ag1 (2 + (t1 + (2 * (m_prev + 1) + (2 + t1)))) sc) as sc_end eqn:Eend.
    assert (Hsc_end : sc_end = sc5)
      by (rewrite Eend, !srun_add, <- E1, <- E2, <- E3, <- E4, <- E5; reflexivity).
    rewrite N2Z.inj_succ. cbv zeta. splits.
    + intros t Ht.
      destruct (N.lt_ge_cases t t1) as [Ht1 | Hge1].
      * pose proof (Bd1 t Ht1). lia.
      * destruct (N.lt_ge_cases t (2 + t1)) as [Ht2 | Hge2].
        -- assert (Hc : t = t1 \/ t = N.succ t1) by lia.
           destruct Hc as [-> | ->].
           ++ rewrite <- E1, P1. lia.
           ++ replace (N.succ t1) with (1 + t1)%N by lia.
              rewrite srun_add, <- E1, <- E2a, P2a. lia.
        -- destruct (N.lt_ge_cases t (2 * (m_prev + 1) + (2 + t1))) as [Ht3 | Hge3].
           ++ replace t with ((t - (2 + t1)) + (2 + t1))%N by lia.
              rewrite !srun_add, <- E1, <- E2.
              pose proof (Bd3 (t - (2 + t1))%N ltac:(lia)).
              rewrite N2Z.inj_add in *. lia.
           ++ destruct (N.lt_ge_cases t (t1 + (2 * (m_prev + 1) + (2 + t1)))) as [Ht4 | Hge4].
              ** replace t with ((t - (2 * (m_prev + 1) + (2 + t1))) + (2 * (m_prev + 1) + (2 + t1)))%N by lia.
                 rewrite !srun_add, <- E1, <- E2, <- E3.
                 pose proof (Bd4 (t - (2 * (m_prev + 1) + (2 + t1)))%N ltac:(lia)). lia.
              ** assert (Hc : t = (t1 + (2 * (m_prev + 1) + (2 + t1)))%N \/
                             t = N.succ (t1 + (2 * (m_prev + 1) + (2 + t1)))) by lia.
                 destruct Hc as [-> | ->].
                 --- rewrite !srun_add, <- E1, <- E2, <- E3, <- E4, P4. lia.
                 --- replace (N.succ (t1 + (2 * (m_prev + 1) + (2 + t1))))
                       with (1 + (t1 + (2 * (m_prev + 1) + (2 + t1))))%N by lia.
                     rewrite !srun_add, <- E1, <- E2, <- E3, <- E4, <- E5a, P5a. lia.
    + rewrite Hsc_end, P5, N2Z.inj_succ. reflexivity.
    + rewrite Hsc_end. exact S5.
    + rewrite Hsc_end, T5. exact F4.
    + intros z Hz. rewrite Hsc_end, T5.
      destruct (Z.lt_ge_cases z (-2 + 2 * Z.of_N m_prev)).
      * apply T4. lia.
      * destruct (Z.eq_dec z (-2 + 2 * Z.of_N m_prev)); [subst z; exact Hr4a | replace z with (-1 + 2 * Z.of_N m_prev) by lia; exact Hr4b].
    + intros z Hz. rewrite Hsc_end, T5, O4, O3, O2, O1 by (rewrite ?N2Z.inj_add; lia). reflexivity.
Qed.

Lemma ag1_walk_ones : forall n X sc,
  sc.(spos) = X ->
  sc.(sstate) = StA ->
  (forall z, X <= z < X + Z.of_N n -> sc.(stape) z = true) ->
  (forall t, (t < n)%N -> X <= (srun ag1 t sc).(spos) <= X + Z.of_N n - 1) /\
  let sc' := srun ag1 n sc in
  sc'.(spos) = X + Z.of_N n /\
  sc'.(sstate) = StA /\
  (forall z, sc'.(stape) z = sc.(stape) z).
Proof.
  intro n. induction n using N.peano_ind; intros X sc Hp Hs Ht.
  - rewrite srun_0. cbv zeta. splits; [intros; lia | lia | exact Hs | auto].
  - rewrite N2Z.inj_succ.
    remember (srun ag1 1 sc) as sc1 eqn:E1.
    assert (H1 : sc1.(spos) = X + 1 /\ sc1.(sstate) = StA /\ forall z, sc1.(stape) z = sc.(stape) z).
    { rewrite E1, srun_1. unfold sstep, ag1, move_pos. rewrite Hp, Hs, (Ht X ltac:(lia)). proj_eval.
      splits; [lia | reflexivity |].
      intro z. destruct (Z.eq_dec z X); [subst z; rewrite write_tape_same; symmetry; apply Ht; lia | apply write_tape_other; auto]. }
    destruct H1 as [P1 [S1 T1]].
    assert (Ht1 : forall z, X + 1 <= z < (X + 1) + Z.of_N n -> sc1.(stape) z = true)
      by (intros z Hz; rewrite T1; apply Ht; lia).
    destruct (IHn (X + 1) sc1 P1 S1 Ht1) as [IHbd [IHp [IHs IHt]]].
    replace (N.succ n) with (n + 1)%N by lia.
    cbv zeta. rewrite srun_add, <- E1.
    splits.
    + intros t Htk. destruct (N.eq_0_gt_0_cases t) as [-> | Htgt].
      * rewrite srun_0, Hp. lia.
      * replace t with ((t - 1) + 1)%N by lia. rewrite srun_add, <- E1.
        pose proof (IHbd (t - 1)%N ltac:(lia)). lia.
    + rewrite IHp. lia.
    + exact IHs.
    + intro z. rewrite IHt, T1. reflexivity.
Qed.

(** Agent 2: 7 steps bridging t=3842 -> t=3849 onto the dt=0 glider at X=355 *)
Lemma ag2_init_7 : forall sc,
  sc.(spos) = 350 ->
  sc.(sstate) = StC ->
  sc.(stape) 350 = false ->
  (forall z, 351 <= z <= 354 -> sc.(stape) z = true) ->
  (forall z, 355 <= z -> sc.(stape) z = false) ->
  (forall k, (k < 7)%N -> 350 <= (srun ag2 k sc).(spos)) /\
  let sc' := srun ag2 7 sc in
  sc'.(spos) = 355 /\
  sc'.(sstate) = StB /\
  (forall z, z < 350 -> sc'.(stape) z = sc.(stape) z) /\
  sc'.(stape) 350 = true /\
  sc'.(stape) 351 = false /\
  sc'.(stape) 352 = true /\
  sc'.(stape) 353 = false /\
  sc'.(stape) 354 = false /\
  (forall z, 355 <= z -> sc'.(stape) z = false).
Proof.
  intros sc Hp Hs H350 H351 H355.
  remember (srun ag2 1 sc) as sc1 eqn:E1.
  assert (H1 : sc1.(spos) = 351 /\ sc1.(sstate) = StA /\ sc1.(stape) 350 = true /\
               forall z, z <> 350 -> sc1.(stape) z = sc.(stape) z).
  { rewrite E1, srun_1. unfold sstep, ag2, move_pos. rewrite Hp, Hs, H350. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H1 as [P1 [S1 [W1 O1]]].
  remember (srun ag2 2 sc) as sc2 eqn:E2.
  assert (H2 : sc2.(spos) = 352 /\ sc2.(sstate) = StC /\ sc2.(stape) 351 = false /\
               forall z, z <> 351 -> sc2.(stape) z = sc1.(stape) z).
  { assert (Hs2 : sc2 = sstep ag2 sc1) by (rewrite E2, E1; change 2%N with (N.succ 1); apply srun_succ).
    rewrite Hs2. unfold sstep, ag2, move_pos. rewrite P1, S1, O1, (H351 351) by lia. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H2 as [P2 [S2 [W2 O2]]].
  remember (srun ag2 3 sc) as sc3 eqn:E3.
  assert (H3 : sc3.(spos) = 353 /\ sc3.(sstate) = StB /\ sc3.(stape) 352 = false /\
               forall z, z <> 352 -> sc3.(stape) z = sc2.(stape) z).
  { assert (Hs3 : sc3 = sstep ag2 sc2) by (rewrite E3, E2; change 3%N with (N.succ 2); apply srun_succ).
    rewrite Hs3. unfold sstep, ag2, move_pos. rewrite P2, S2, O2, O1, (H351 352) by lia. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H3 as [P3 [S3 [W3 O3]]].
  remember (srun ag2 4 sc) as sc4 eqn:E4.
  assert (H4 : sc4.(spos) = 352 /\ sc4.(sstate) = StC /\ forall z, sc4.(stape) z = sc3.(stape) z).
  { assert (Hs4 : sc4 = sstep ag2 sc3) by (rewrite E4, E3; change 4%N with (N.succ 3); apply srun_succ).
    rewrite Hs4. unfold sstep, ag2, move_pos.
    assert (Hr3 : sc3.(stape) 353 = true) by (rewrite O3, O2, O1, (H351 353) by lia; reflexivity).
    rewrite P3, S3, Hr3. proj_eval.
    splits; [lia | reflexivity |].
    intro z. destruct (Z.eq_dec z 353); [subst z; rewrite write_tape_same; symmetry; exact Hr3 | apply write_tape_other; auto]. }
  destruct H4 as [P4 [S4 T4]].
  remember (srun ag2 5 sc) as sc5 eqn:E5.
  assert (H5 : sc5.(spos) = 353 /\ sc5.(sstate) = StA /\ sc5.(stape) 352 = true /\
               forall z, z <> 352 -> sc5.(stape) z = sc4.(stape) z).
  { assert (Hs5 : sc5 = sstep ag2 sc4) by (rewrite E5, E4; change 5%N with (N.succ 4); apply srun_succ).
    rewrite Hs5. unfold sstep, ag2, move_pos.
    assert (Hr4 : sc4.(stape) 352 = false) by (rewrite T4; exact W3).
    rewrite P4, S4, Hr4. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H5 as [P5 [S5 [W5 O5]]].
  remember (srun ag2 6 sc) as sc6 eqn:E6.
  assert (H6 : sc6.(spos) = 354 /\ sc6.(sstate) = StC /\ sc6.(stape) 353 = false /\
               forall z, z <> 353 -> sc6.(stape) z = sc5.(stape) z).
  { assert (Hs6 : sc6 = sstep ag2 sc5) by (rewrite E6, E5; change 6%N with (N.succ 5); apply srun_succ).
    rewrite Hs6. unfold sstep, ag2, move_pos.
    assert (Hr5 : sc5.(stape) 353 = true) by (rewrite O5, T4, O3, O2, O1, (H351 353) by lia; reflexivity).
    rewrite P5, S5, Hr5. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H6 as [P6 [S6 [W6 O6]]].
  remember (srun ag2 7 sc) as sc7 eqn:E7.
  assert (H7 : sc7.(spos) = 355 /\ sc7.(sstate) = StB /\ sc7.(stape) 354 = false /\
               forall z, z <> 354 -> sc7.(stape) z = sc6.(stape) z).
  { assert (Hs7 : sc7 = sstep ag2 sc6) by (rewrite E7, E6; change 7%N with (N.succ 6); apply srun_succ).
    rewrite Hs7. unfold sstep, ag2, move_pos.
    assert (Hr6 : sc6.(stape) 354 = true) by (rewrite O6, O5, T4, O3, O2, O1, (H351 354) by lia; reflexivity).
    rewrite P6, S6, Hr6. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H7 as [P7 [S7 [W7 O7]]].
  cbv zeta. splits.
  - intros k Hk.
    assert (Hc : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6)%N) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]];
      [rewrite srun_0; lia | rewrite <- E1; lia | rewrite <- E2; lia | rewrite <- E3; lia |
       rewrite <- E4; lia | rewrite <- E5; lia | rewrite <- E6; lia].
  - exact P7.
  - exact S7.
  - intros z Hz. rewrite O7, O6, O5, T4, O3, O2, O1 by lia. reflexivity.
  - rewrite O7, O6, O5, T4, O3, O2 by lia. exact W1.
  - rewrite O7, O6, O5, T4, O3 by lia. exact W2.
  - rewrite O7, O6 by lia. exact W5.
  - rewrite O7 by lia. exact W6.
  - exact W7.
  - intros z Hz. rewrite O7, O6, O5, T4, O3, O2, O1 by lia. apply H355; lia.
Qed.

(** Agent 2 period-11 glider cycle *)
Definition ag2_head (X : Z) (tp : Tape) : Prop :=
  tp (X - 4) = false /\ tp (X - 3) = true /\ tp (X - 2) = false /\
  tp (X - 1) = false /\ tp X = false /\
  (forall z, X + 1 <= z -> tp z = false).

Lemma ag2_cycle11 : forall X sc,
  sc.(spos) = X ->
  sc.(sstate) = StB ->
  ag2_head X sc.(stape) ->
  (forall k, (k < 11)%N -> X - 4 <= (srun ag2 k sc).(spos)) /\
  let sc' := srun ag2 11 sc in
  sc'.(spos) = X + 1 /\
  sc'.(sstate) = StB /\
  (forall z, z <= X - 5 -> sc'.(stape) z = sc.(stape) z) /\
  sc'.(stape) (X - 4) = true /\
  ag2_head (X + 1) sc'.(stape).
Proof.
  intros X sc Hp0 Hs0 [Hm4 [Hm3 [Hm2 [Hm1 [H0 Hgt]]]]].
  remember (srun ag2 1 sc) as sc1 eqn:E1.
  assert (H1 : sc1.(spos) = X - 1 /\ sc1.(sstate) = StB /\ sc1.(stape) X = true /\
               forall z, z <> X -> sc1.(stape) z = sc.(stape) z).
  { rewrite E1, srun_1. unfold sstep, ag2, move_pos. rewrite Hp0, Hs0, H0. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H1 as [P1 [S1 [W1 O1]]].
  remember (srun ag2 2 sc) as sc2 eqn:E2.
  assert (H2 : sc2.(spos) = X - 2 /\ sc2.(sstate) = StB /\ sc2.(stape) (X - 1) = true /\
               forall z, z <> X - 1 -> sc2.(stape) z = sc1.(stape) z).
  { assert (Hs : sc2 = sstep ag2 sc1) by (rewrite E2, E1; change 2%N with (N.succ 1); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos. rewrite P1, S1, O1, Hm1 by lia. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H2 as [P2 [S2 [W2 O2]]].
  remember (srun ag2 3 sc) as sc3 eqn:E3.
  assert (H3 : sc3.(spos) = X - 3 /\ sc3.(sstate) = StB /\ sc3.(stape) (X - 2) = true /\
               forall z, z <> X - 2 -> sc3.(stape) z = sc2.(stape) z).
  { assert (Hs : sc3 = sstep ag2 sc2) by (rewrite E3, E2; change 3%N with (N.succ 2); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos. rewrite P2, S2, O2, O1, Hm2 by lia. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H3 as [P3 [S3 [W3 O3]]].
  remember (srun ag2 4 sc) as sc4 eqn:E4.
  assert (H4 : sc4.(spos) = X - 4 /\ sc4.(sstate) = StC /\ forall z, sc4.(stape) z = sc3.(stape) z).
  { assert (Hs : sc4 = sstep ag2 sc3) by (rewrite E4, E3; change 4%N with (N.succ 3); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr3 : sc3.(stape) (X - 3) = true) by (rewrite O3, O2, O1 by lia; exact Hm3).
    rewrite P3, S3, Hr3. proj_eval.
    splits; [lia | reflexivity |].
    intro z. destruct (Z.eq_dec z (X - 3)); [subst z; rewrite write_tape_same; symmetry; exact Hr3 | apply write_tape_other; auto]. }
  destruct H4 as [P4 [S4 T4]].
  remember (srun ag2 5 sc) as sc5 eqn:E5.
  assert (H5 : sc5.(spos) = X - 3 /\ sc5.(sstate) = StA /\ sc5.(stape) (X - 4) = true /\
               forall z, z <> X - 4 -> sc5.(stape) z = sc4.(stape) z).
  { assert (Hs : sc5 = sstep ag2 sc4) by (rewrite E5, E4; change 5%N with (N.succ 4); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr4 : sc4.(stape) (X - 4) = false) by (rewrite T4, O3, O2, O1 by lia; exact Hm4).
    rewrite P4, S4, Hr4. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H5 as [P5 [S5 [W5 O5]]].
  remember (srun ag2 6 sc) as sc6 eqn:E6.
  assert (H6 : sc6.(spos) = X - 2 /\ sc6.(sstate) = StC /\ sc6.(stape) (X - 3) = false /\
               forall z, z <> X - 3 -> sc6.(stape) z = sc5.(stape) z).
  { assert (Hs : sc6 = sstep ag2 sc5) by (rewrite E6, E5; change 6%N with (N.succ 5); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr5 : sc5.(stape) (X - 3) = true) by (rewrite O5, T4, O3, O2, O1 by lia; exact Hm3).
    rewrite P5, S5, Hr5. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H6 as [P6 [S6 [W6 O6]]].
  remember (srun ag2 7 sc) as sc7 eqn:E7.
  assert (H7 : sc7.(spos) = X - 1 /\ sc7.(sstate) = StB /\ sc7.(stape) (X - 2) = false /\
               forall z, z <> X - 2 -> sc7.(stape) z = sc6.(stape) z).
  { assert (Hs : sc7 = sstep ag2 sc6) by (rewrite E7, E6; change 7%N with (N.succ 6); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr6 : sc6.(stape) (X - 2) = true) by (rewrite O6, O5, T4 by lia; exact W3).
    rewrite P6, S6, Hr6. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H7 as [P7 [S7 [W7 O7]]].
  remember (srun ag2 8 sc) as sc8 eqn:E8.
  assert (H8 : sc8.(spos) = X - 2 /\ sc8.(sstate) = StC /\ forall z, sc8.(stape) z = sc7.(stape) z).
  { assert (Hs : sc8 = sstep ag2 sc7) by (rewrite E8, E7; change 8%N with (N.succ 7); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr7 : sc7.(stape) (X - 1) = true) by (rewrite O7, O6, O5, T4, O3 by lia; exact W2).
    rewrite P7, S7, Hr7. proj_eval.
    splits; [lia | reflexivity |].
    intro z. destruct (Z.eq_dec z (X - 1)); [subst z; rewrite write_tape_same; symmetry; exact Hr7 | apply write_tape_other; auto]. }
  destruct H8 as [P8 [S8 T8]].
  remember (srun ag2 9 sc) as sc9 eqn:E9.
  assert (H9 : sc9.(spos) = X - 1 /\ sc9.(sstate) = StA /\ sc9.(stape) (X - 2) = true /\
               forall z, z <> X - 2 -> sc9.(stape) z = sc8.(stape) z).
  { assert (Hs : sc9 = sstep ag2 sc8) by (rewrite E9, E8; change 9%N with (N.succ 8); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr8 : sc8.(stape) (X - 2) = false) by (rewrite T8; exact W7).
    rewrite P8, S8, Hr8. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H9 as [P9 [S9 [W9 O9]]].
  remember (srun ag2 10 sc) as sc10 eqn:E10.
  assert (H10 : sc10.(spos) = X /\ sc10.(sstate) = StC /\ sc10.(stape) (X - 1) = false /\
                forall z, z <> X - 1 -> sc10.(stape) z = sc9.(stape) z).
  { assert (Hs : sc10 = sstep ag2 sc9) by (rewrite E10, E9; change 10%N with (N.succ 9); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr9 : sc9.(stape) (X - 1) = true) by (rewrite O9, T8, O7, O6, O5, T4, O3 by lia; exact W2).
    rewrite P9, S9, Hr9. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H10 as [P10 [S10 [W10 O10]]].
  remember (srun ag2 11 sc) as sc11 eqn:E11.
  assert (H11 : sc11.(spos) = X + 1 /\ sc11.(sstate) = StB /\ sc11.(stape) X = false /\
                forall z, z <> X -> sc11.(stape) z = sc10.(stape) z).
  { assert (Hs : sc11 = sstep ag2 sc10) by (rewrite E11, E10; change 11%N with (N.succ 10); apply srun_succ).
    rewrite Hs. unfold sstep, ag2, move_pos.
    assert (Hr10 : sc10.(stape) X = true) by (rewrite O10, O9, T8, O7, O6, O5, T4, O3, O2 by lia; exact W1).
    rewrite P10, S10, Hr10. proj_eval.
    splits; [lia | reflexivity | apply write_tape_same | intros; apply write_tape_other; auto]. }
  destruct H11 as [P11 [S11 [W11 O11]]].
  cbv zeta. splits.
  - intros k Hk.
    assert (Hc : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
                  k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10)%N) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
      [rewrite srun_0; lia | rewrite <- E1; lia | rewrite <- E2; lia | rewrite <- E3; lia |
       rewrite <- E4; lia | rewrite <- E5; lia | rewrite <- E6; lia | rewrite <- E7; lia |
       rewrite <- E8; lia | rewrite <- E9; lia | rewrite <- E10; lia].
  - exact P11.
  - exact S11.
  - intros z Hz. rewrite O11, O10, O9, T8, O7, O6, O5, T4, O3, O2, O1 by lia. reflexivity.
  - rewrite O11, O10, O9, T8, O7, O6 by lia. exact W5.
  - unfold ag2_head.
    replace (X + 1 - 4) with (X - 3) by lia.
    replace (X + 1 - 3) with (X - 2) by lia.
    replace (X + 1 - 2) with (X - 1) by lia.
    replace (X + 1 - 1) with X by lia.
    splits.
    + rewrite O11, O10, O9, T8, O7 by lia. exact W6.
    + rewrite O11, O10 by lia. exact W9.
    + rewrite O11 by lia. exact W10.
    + exact W11.
    + rewrite O11, O10, O9, T8, O7, O6, O5, T4, O3, O2, O1 by lia. apply Hgt; lia.
    + intros z Hz. rewrite O11, O10, O9, T8, O7, O6, O5, T4, O3, O2, O1 by lia. apply Hgt; lia.
Qed.

Lemma ag2_glider : forall K lo X sc,
  lo <= X - 4 ->
  sc.(spos) = X ->
  sc.(sstate) = StB ->
  (forall z, lo <= z <= X - 5 -> sc.(stape) z = true) ->
  ag2_head X sc.(stape) ->
  (forall k, (k < 11 * K)%N -> X - 4 <= (srun ag2 k sc).(spos)) /\
  let sc' := srun ag2 (11 * K) sc in
  sc'.(spos) = X + Z.of_N K /\
  sc'.(sstate) = StB /\
  (forall z, z < lo -> sc'.(stape) z = sc.(stape) z) /\
  (forall z, lo <= z <= X + Z.of_N K - 5 -> sc'.(stape) z = true) /\
  ag2_head (X + Z.of_N K) sc'.(stape).
Proof.
  intro K. induction K using N.peano_ind; intros lo X sc Hlo Hp Hs Htr Hhd.
  - rewrite N.mul_0_r, srun_0. cbv zeta. splits; [intros; lia | lia | exact Hs | auto | intros z Hz; apply Htr; lia | replace (X + Z.of_N 0) with X by lia; exact Hhd].
  - replace (11 * N.succ K)%N with (11 + 11 * K)%N by lia.
    rewrite N2Z.inj_succ.
    destruct (IHK lo X sc Hlo Hp Hs Htr Hhd) as [IHbd [IHp [IHs [IHbelow [IHtr IHhd]]]]].
    remember (srun ag2 (11 * K) sc) as scK eqn:EK.
    set (XK := X + Z.of_N K) in *.
    destruct (ag2_cycle11 XK scK IHp IHs IHhd) as [Cybd [Cyp [Cys [Cyold [Cyw Cyhd]]]]].
    cbv zeta. rewrite srun_add, <- EK.
    splits.
    + intros k Hk. destruct (N.lt_ge_cases k (11 * K)%N) as [Hk1 | Hk2].
      * apply IHbd; exact Hk1.
      * replace k with ((k - 11 * K) + 11 * K)%N by lia.
        rewrite srun_add, <- EK.
        pose proof (Cybd (k - 11 * K)%N ltac:(lia)). unfold XK in *. lia.
    + rewrite Cyp. unfold XK. lia.
    + exact Cys.
    + intros z Hz. rewrite Cyold by (unfold XK; lia). apply IHbelow; auto.
    + intros z Hz. destruct (Z.lt_ge_cases z (XK - 4)).
      * rewrite Cyold by lia. apply IHtr. unfold XK in *. lia.
      * replace z with (XK - 4) by (unfold XK in *; lia). exact Cyw.
    + replace (X + Z.succ (Z.of_N K)) with (XK + 1) by (unfold XK; lia). exact Cyhd.
Qed.

(** * 8. Round 1 (m = 161): Bridge, Chase, and Bounce at D = 22 *)

Definition K1 : N := ((S_val 161 + 5 - 7) / 11)%N.
Definition t_counter1_sync : N := (S_val 161 + 5)%N.
Definition t_sync1 : N := (3842 + t_counter1_sync)%N.
Definition p1_sync1 : N := (355 + K1)%N.
Definition r1 : N := ((p1_sync1 - 325 - 22) / 20)%N.

Lemma t_counter1_sync_rel : t_counter1_sync = (7 + 11 * K1)%N.
Proof. vm_compute. reflexivity. Qed.

Lemma D1_decomp : (Z.of_N p1_sync1 - 325 = 22 + 20 * Z.of_N r1).
Proof. vm_compute. reflexivity. Qed.

Lemma bridge_to_sync1 :
  let c := run_N ag1 ag2 t_sync1 c0 in
  c.(pos1) = 325 /\
  c.(pos2) = Z.of_N p1_sync1 /\
  c.(state1) = StA /\
  c.(state2) = StB /\
  c.(tape) (-4) = false /\
  (forall z, -3 <= z <= Z.of_N p1_sync1 - 5 -> c.(tape) z = true) /\
  ag2_head (Z.of_N p1_sync1) c.(tape) /\
  (forall t, (t < t_sync1)%N -> (run_N ag1 ag2 t c0).(pos1) <> (run_N ag1 ag2 t c0).(pos2)).
Proof.
  pose proof state_3842 as H3842.
  cbv zeta in H3842.
  remember (run_N ag1 ag2 3842 c0) as c3842 eqn:Ec3842.
  destruct H3842 as [Hp1 [Hp2 [Hs1 [Hs2 [Hzm3 [Halt [Htr320 [H350 [Htr351 [Hz355 Hnc3842]]]]]]]]]].
  set (sc1 := {| spos := -4; sstate := StB; stape := c3842.(tape) |}).
  set (sc2 := {| spos := 350; sstate := StC; stape := c3842.(tape) |}).
  (* Agent 1: counter 161 (k=160) + walk 5 *)
  assert (Hm4 : sc1.(stape) (-4) = false) by (unfold sc1; cbn [stape]; apply Hzm3; lia).
  assert (Hm3 : sc1.(stape) (-3) = false) by (unfold sc1; cbn [stape]; apply Hzm3; lia).
  assert (Halt1 : alt_pairs (-2) (160 + 1) sc1.(stape)) by (change (160 + 1)%N with 161%N; exact Halt).
  destruct (ag1_counter 160 sc1 eq_refl eq_refl Hm4 Hm3 Halt1) as [Cbd [Cp [Cs [Cf4 [Ctr Co]]]]].
  change (160 + 1)%N with 161%N in Cbd, Cp, Cs, Cf4, Ctr, Co.
  remember (srun ag1 (S_val 161) sc1) as sc1_mid eqn:Esc1_mid.
  assert (Hw_base : forall z, 320 <= z < 320 + Z.of_N 5 -> sc1_mid.(stape) z = true).
  { intros z Hz. rewrite Co by (change (Z.of_N 161) with 161; lia).
    apply Htr320. change (Z.of_N 5) with 5 in Hz. lia. }
  assert (Cp' : sc1_mid.(spos) = 320) by (rewrite Cp; change (Z.of_N 161) with 161; lia).
  destruct (ag1_walk_ones 5 320 sc1_mid Cp' Cs Hw_base) as [Wbd [Wp [Ws Wt]]].
  assert (Hag1_bd : forall k, (k < t_counter1_sync)%N -> (srun ag1 k sc1).(spos) <= 324).
  { intros k Hk. unfold t_counter1_sync in Hk.
    destruct (N.lt_ge_cases k (S_val 161)) as [Hk1 | Hk2].
    - pose proof (Cbd k Hk1). change (Z.of_N 161) with 161 in *. lia.
    - replace k with ((k - S_val 161) + S_val 161)%N by lia.
      rewrite srun_add, <- Esc1_mid.
      pose proof (Wbd (k - S_val 161)%N ltac:(lia)).
      change (Z.of_N 5) with 5 in *. lia. }
  (* Agent 2: init 7 + glider K1 *)
  destruct (ag2_init_7 sc2 eq_refl eq_refl H350 Htr351 Hz355)
    as [Ibd [Ip [Is [Iold [I350 [I351 [I352 [I353 [I354 I355]]]]]]]]].
  remember (srun ag2 7 sc2) as sc2_mid eqn:Esc2_mid.
  assert (Hhd_mid : ag2_head 355 sc2_mid.(stape))
    by (unfold ag2_head; splits; [exact I351 | exact I352 | exact I353 | exact I354 | apply I355; lia | intros z Hz; apply I355; lia]).
  assert (Htr_mid : forall z, 350 <= z <= 355 - 5 -> sc2_mid.(stape) z = true)
    by (intros z Hz; replace z with 350 by lia; exact I350).
  destruct (ag2_glider K1 350 355 sc2_mid ltac:(lia) Ip Is Htr_mid Hhd_mid)
    as [Gbd [Gp [Gs [Gbelow [Gtr Ghd]]]]].
  assert (Hag2_bd : forall k, (k < t_counter1_sync)%N -> 350 <= (srun ag2 k sc2).(spos)).
  { intros k Hk. rewrite t_counter1_sync_rel in Hk.
    destruct (N.lt_ge_cases k 7%N) as [Hk1 | Hk2].
    - apply Ibd; exact Hk1.
    - replace k with ((k - 7) + 7)%N by lia.
      rewrite srun_add, <- Esc2_mid.
      pose proof (Gbd (k - 7)%N ltac:(lia)). lia. }
  (* Decouple *)
  assert (Hsep : 324 < 350) by lia.
  assert (Hdp1 : c3842.(pos1) = sc1.(spos)) by (unfold sc1; cbn [spos]; exact Hp1).
  assert (Hds1 : c3842.(state1) = sc1.(sstate)) by (unfold sc1; cbn [sstate]; exact Hs1).
  assert (Hdp2 : c3842.(pos2) = sc2.(spos)) by (unfold sc2; cbn [spos]; exact Hp2).
  assert (Hds2' : c3842.(state2) = sc2.(sstate)) by (unfold sc2; cbn [sstate]; exact Hs2).
  assert (Hdt1 : forall z, z <= 324 -> c3842.(tape) z = sc1.(stape) z) by (intros; unfold sc1; cbn [stape]; reflexivity).
  assert (Hdt2 : forall z, 350 <= z -> c3842.(tape) z = sc2.(stape) z) by (intros; unfold sc2; cbn [stape]; reflexivity).
  destruct (run_decouple ag1 ag2 324 350 t_counter1_sync c3842 sc1 sc2
              Hsep Hdp1 Hds1 Hdp2 Hds2' Hdt1 Hdt2 Hag1_bd Hag2_bd)
    as [Dp1 [Ds1 [Dp2 [Ds2 [Dt1 [Dt2 [Dmid Dnc]]]]]]].
  assert (Hts_eq : t_sync1 = (t_counter1_sync + 3842)%N) by (unfold t_sync1; lia).
  cbv zeta. rewrite Hts_eq, run_N_add, <- Ec3842.
  assert (Hp1_f : (run_N ag1 ag2 t_counter1_sync c3842).(pos1) = 325).
  { rewrite Dp1. unfold t_counter1_sync. replace (S_val 161 + 5)%N with (5 + S_val 161)%N by lia.
    rewrite srun_add, <- Esc1_mid, Wp. change (Z.of_N 5) with 5. lia. }
  assert (Hp2_f : (run_N ag1 ag2 t_counter1_sync c3842).(pos2) = Z.of_N p1_sync1).
  { rewrite Dp2, t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid, Gp.
    unfold p1_sync1. rewrite N2Z.inj_add. change (Z.of_N 355) with 355. lia. }
  splits.
  - exact Hp1_f.
  - exact Hp2_f.
  - rewrite Ds1. unfold t_counter1_sync. replace (S_val 161 + 5)%N with (5 + S_val 161)%N by lia.
    rewrite srun_add, <- Esc1_mid. exact Ws.
  - rewrite Ds2, t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid. exact Gs.
  - rewrite Dt1 by lia. unfold t_counter1_sync. replace (S_val 161 + 5)%N with (5 + S_val 161)%N by lia.
    rewrite srun_add, <- Esc1_mid, Wt. exact Cf4.
  - intros z Hz. destruct (Z.lt_ge_cases z 320) as [Hz1 | Hz2].
    + rewrite Dt1 by lia. unfold t_counter1_sync. replace (S_val 161 + 5)%N with (5 + S_val 161)%N by lia.
      rewrite srun_add, <- Esc1_mid, Wt. apply Ctr. change (Z.of_N 161) with 161. lia.
    + destruct (Z.lt_ge_cases z 325) as [Hz3 | Hz4].
      * rewrite Dt1 by lia. unfold t_counter1_sync. replace (S_val 161 + 5)%N with (5 + S_val 161)%N by lia.
        rewrite srun_add, <- Esc1_mid, Wt, Co by (change (Z.of_N 161) with 161; lia). apply Htr320. lia.
      * destruct (Z.lt_ge_cases z 350) as [Hz5 | Hz6].
        -- rewrite Dmid by lia. apply Htr320. lia.
        -- rewrite Dt2 by lia. rewrite t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid.
           apply Gtr. unfold p1_sync1 in Hz. rewrite N2Z.inj_add in Hz. change (Z.of_N 355) with 355 in Hz. lia.
  - unfold ag2_head in *.
    assert (Hp1_ge : 350 <= Z.of_N p1_sync1 - 4).
    { unfold p1_sync1. rewrite N2Z.inj_add. change (Z.of_N 355) with 355. pose proof (N2Z.is_nonneg K1). lia. }
    destruct Ghd as [Gh1 [Gh2 [Gh3 [Gh4 [Gh5 Gh6]]]]].
    assert (Heq_x : 355 + Z.of_N K1 = Z.of_N p1_sync1) by (unfold p1_sync1; rewrite N2Z.inj_add; change (Z.of_N 355) with 355; lia).
    rewrite Heq_x in Gh1, Gh2, Gh3, Gh4, Gh5, Gh6.
    splits.
    + rewrite Dt2 by lia. rewrite t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid. exact Gh1.
    + rewrite Dt2 by lia. rewrite t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid. exact Gh2.
    + rewrite Dt2 by lia. rewrite t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid. exact Gh3.
    + rewrite Dt2 by lia. rewrite t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid. exact Gh4.
    + rewrite Dt2 by lia. rewrite t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid. exact Gh5.
    + intros z Hz. rewrite Dt2 by lia. rewrite t_counter1_sync_rel, N.add_comm, srun_add, <- Esc2_mid. apply Gh6. lia.
  - intros t Ht.
    assert (Hnc_orig : forall k, (k < t_counter1_sync)%N ->
              (run_N ag1 ag2 k (run_N ag1 ag2 3842 c0)).(pos1) <>
              (run_N ag1 ag2 k (run_N ag1 ag2 3842 c0)).(pos2))
      by (rewrite <- Ec3842; exact Dnc).
    eapply (no_coll_add ag1 ag2 t_counter1_sync 3842 c0 Hnc3842 Hnc_orig t Ht).
Qed.

Lemma chase_cycle22 : forall lo P1 P2 c,
  lo <= P1 ->
  c.(pos1) = P1 -> c.(state1) = StA ->
  c.(pos2) = P2 -> c.(state2) = StB ->
  P1 + 26 <= P2 ->
  (forall z, lo <= z <= P2 - 5 -> c.(tape) z = true) ->
  ag2_head P2 c.(tape) ->
  (forall k, (k < 22)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  let c' := run_N ag1 ag2 22 c in
  c'.(pos1) = P1 + 22 /\ c'.(state1) = StA /\
  c'.(pos2) = P2 + 2 /\ c'.(state2) = StB /\
  (forall z, z < lo -> c'.(tape) z = c.(tape) z) /\
  (forall z, lo <= z <= P2 + 2 - 5 -> c'.(tape) z = true) /\
  ag2_head (P2 + 2) c'.(tape).
Proof.
  intros lo P1 P2 c Hlo Hp1 Hs1 Hp2 Hs2 Hsep Htr Hhd.
  set (sc1 := {| spos := P1; sstate := StA; stape := c.(tape) |}).
  set (sc2 := {| spos := P2; sstate := StB; stape := c.(tape) |}).
  assert (Hw1 : forall z, P1 <= z < P1 + Z.of_N 22 -> sc1.(stape) z = true)
    by (intros z Hz; apply Htr; change (Z.of_N 22) with 22 in Hz; lia).
  destruct (ag1_walk_ones 22 P1 sc1 eq_refl eq_refl Hw1) as [Wbd [Wp [Ws Wt]]].
  assert (Htr2 : forall z, P2 - 4 <= z <= P2 - 5 -> sc2.(stape) z = true) by (intros; lia).
  destruct (ag2_glider 2 (P2 - 4) P2 sc2 ltac:(lia) eq_refl eq_refl Htr2 Hhd)
    as [Gbd [Gp [Gs [Gbelow [Gtr Ghd]]]]].
  change (11 * 2)%N with 22%N in Gbd, Gp, Gs, Gbelow, Gtr, Ghd.
  change (Z.of_N 2) with 2 in Gp, Gtr, Ghd.
  assert (Hbd1 : forall k, (k < 22)%N -> (srun ag1 k sc1).(spos) <= P1 + 21).
  { intros k Hk. pose proof (Wbd k Hk). change (Z.of_N 22) with 22 in *. lia. }
  assert (Hbd2 : forall k, (k < 22)%N -> P2 - 4 <= (srun ag2 k sc2).(spos)) by exact Gbd.
  assert (Hsep_c : P1 + 21 < P2 - 4) by lia.
  assert (Hdp1 : c.(pos1) = sc1.(spos)) by (unfold sc1; cbn [spos]; exact Hp1).
  assert (Hds1 : c.(state1) = sc1.(sstate)) by (unfold sc1; cbn [sstate]; exact Hs1).
  assert (Hdp2 : c.(pos2) = sc2.(spos)) by (unfold sc2; cbn [spos]; exact Hp2).
  assert (Hds2 : c.(state2) = sc2.(sstate)) by (unfold sc2; cbn [sstate]; exact Hs2).
  assert (Hdt1 : forall z, z <= P1 + 21 -> c.(tape) z = sc1.(stape) z) by (intros; unfold sc1; cbn [stape]; reflexivity).
  assert (Hdt2 : forall z, P2 - 4 <= z -> c.(tape) z = sc2.(stape) z) by (intros; unfold sc2; cbn [stape]; reflexivity).
  destruct (run_decouple ag1 ag2 (P1 + 21) (P2 - 4) 22 c sc1 sc2
              Hsep_c Hdp1 Hds1 Hdp2 Hds2 Hdt1 Hdt2 Hbd1 Hbd2)
    as [Dp1 [Ds1 [Dp2 [Ds2 [Dt1 [Dt2 [Dmid Dnc]]]]]]].
  cbv zeta. splits.
  - exact Dnc.
  - rewrite Dp1, Wp. change (Z.of_N 22) with 22. lia.
  - rewrite Ds1. exact Ws.
  - rewrite Dp2, Gp. lia.
  - rewrite Ds2. exact Gs.
  - intros z Hz. rewrite Dt1 by lia. rewrite Wt. reflexivity.
  - intros z Hz. destruct (Z.lt_ge_cases z (P1 + 22)) as [Hz1 | Hz2].
    + rewrite Dt1 by lia. rewrite Wt. apply Htr. lia.
    + destruct (Z.lt_ge_cases z (P2 - 4)) as [Hz3 | Hz4].
      * rewrite Dmid by lia. apply Htr. lia.
      * rewrite Dt2 by lia. apply Gtr. lia.
  - unfold ag2_head in *. destruct Ghd as [Gh1 [Gh2 [Gh3 [Gh4 [Gh5 Gh6]]]]].
    splits.
    + rewrite Dt2 by lia. exact Gh1.
    + rewrite Dt2 by lia. exact Gh2.
    + rewrite Dt2 by lia. exact Gh3.
    + rewrite Dt2 by lia. exact Gh4.
    + rewrite Dt2 by lia. exact Gh5.
    + intros z Hz. rewrite Dt2 by lia. apply Gh6. exact Hz.
Qed.

Lemma chase_loop22 : forall j rem lo P1 P2 c,
  lo <= P1 ->
  c.(pos1) = P1 -> c.(state1) = StA ->
  c.(pos2) = P2 -> c.(state2) = StB ->
  6 <= rem ->
  P2 - P1 = rem + 20 * Z.of_N j ->
  (forall z, lo <= z <= P2 - 5 -> c.(tape) z = true) ->
  ag2_head P2 c.(tape) ->
  (forall k, (k < 22 * j)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  let c' := run_N ag1 ag2 (22 * j) c in
  c'.(pos1) = P1 + 22 * Z.of_N j /\ c'.(state1) = StA /\
  c'.(pos2) = P2 + 2 * Z.of_N j /\ c'.(state2) = StB /\
  c'.(pos2) - c'.(pos1) = rem /\
  (forall z, z < lo -> c'.(tape) z = c.(tape) z) /\
  (forall z, lo <= z <= c'.(pos2) - 5 -> c'.(tape) z = true) /\
  ag2_head c'.(pos2) c'.(tape).
Proof.
  intro j. induction j using N.peano_ind; intros rem lo P1 P2 c Hlo Hp1 Hs1 Hp2 Hs2 Hrem Hgap Htr Hhd.
  - rewrite N.mul_0_r, run_N_0. cbv zeta. splits; [intros; lia | lia | exact Hs1 | lia | exact Hs2 | lia | auto | intros z Hz; apply Htr; lia | rewrite Hp2; exact Hhd].
  - rewrite N2Z.inj_succ in Hgap.
    destruct (chase_cycle22 lo P1 P2 c Hlo Hp1 Hs1 Hp2 Hs2 ltac:(pose proof (N2Z.is_nonneg j); lia) Htr Hhd)
      as [Cnc [Cp1 [Cs1 [Cp2 [Cs2 [Cbelow [Ctr Chd]]]]]]].
    remember (run_N ag1 ag2 22 c) as c22 eqn:Ec22.
    destruct (IHj rem lo (P1 + 22) (P2 + 2) c22 ltac:(lia) Cp1 Cs1 Cp2 Cs2 Hrem ltac:(lia) Ctr Chd)
      as [Lnc [Lp1 [Ls1 [Lp2 [Ls2 [Lgap [Lbelow [Ltr Lhd]]]]]]]].
    replace (22 * N.succ j)%N with (22 * j + 22)%N by lia.
    cbv zeta. rewrite run_N_add, <- Ec22.
    rewrite N2Z.inj_succ.
    splits.
    + intros k Hk. eapply no_coll_add; [exact Cnc | rewrite <- Ec22; exact Lnc | exact Hk].
    + rewrite Lp1. lia.
    + exact Ls1.
    + rewrite Lp2. lia.
    + exact Ls2.
    + exact Lgap.
    + intros z Hz. rewrite Lbelow by exact Hz. apply Cbelow. exact Hz.
    + exact Ltr.
    + exact Lhd.
Qed.

Fixpoint bt_set_ones (lo : Z) (cnt : nat) (t : BTree) : BTree :=
  match cnt with
  | O => t
  | S n => bt_set_ones (lo + 1) n (bt_set (z_to_pos lo) true t)
  end.

Definition fc_bounce35 : FastConfig := {|
  fpos1 := -22; fpos2 := 0; fstate1 := StA; fstate2 := StB;
  ftape := bt_set (z_to_pos (-3)) true (bt_set_ones (-22) 18 BEmpty)
|}.

Lemma fc_to_cfg_state1 : forall fc, (fc_to_cfg fc).(state1) = fc.(fstate1).
Proof. intros; reflexivity. Qed.

Lemma fc_to_cfg_state2 : forall fc, (fc_to_cfg fc).(state2) = fc.(fstate2).
Proof. intros; reflexivity. Qed.

Lemma fc_to_cfg_tape : forall fc z, (fc_to_cfg fc).(tape) z = bt_get (z_to_pos z) fc.(ftape).
Proof. intros; reflexivity. Qed.

Lemma shift_cfg_state1 : forall d c, (shift_cfg d c).(state1) = c.(state1).
Proof. intros; reflexivity. Qed.

Lemma shift_cfg_state2 : forall d c, (shift_cfg d c).(state2) = c.(state2).
Proof. intros; reflexivity. Qed.

Lemma shift_cfg_tape : forall d c z, (shift_cfg d c).(tape) z = c.(tape) (z - d).
Proof. intros; reflexivity. Qed.

Definition check_bounce35 (st : FastConfig * bool) : bool :=
  let (fc, ok) := st in
  ok &&
  (fc.(fpos1) =? -17) &&
  (fc.(fpos2) =? 3) &&
  (match fc.(fstate1), fc.(fstate2) with StB, StB => true | _, _ => false end) &&
  check_all_true_nat (-22) 6 fc.(ftape) &&
  negb (bt_get (z_to_pos (-16)) fc.(ftape)) &&
  check_alt_pairs_nat (-15) 6 fc.(ftape) &&
  bt_get (z_to_pos (-3)) fc.(ftape) &&
  bt_get (z_to_pos (-2)) fc.(ftape) &&
  negb (bt_get (z_to_pos (-1)) fc.(ftape)) &&
  bt_get (z_to_pos 0) fc.(ftape) &&
  negb (bt_get (z_to_pos 1) fc.(ftape)) &&
  negb (bt_get (z_to_pos 2) fc.(ftape)) &&
  negb (bt_get (z_to_pos 3) fc.(ftape)) &&
  bt_bounded_aux (-22) 3 (fun q => q) fc.(ftape).

Lemma bounce35_ok :
  check_bounce35 (N.iter 35 (fast_step_chk_ge (-22)) (fc_bounce35, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fc_bounce35_tape_ok :
  (forall z, -22 <= z <= -5 -> (fc_to_cfg fc_bounce35).(tape) z = true) /\
  ag2_head 0 (fc_to_cfg fc_bounce35).(tape).
Proof.
  assert (Hcheck :
    check_all_true_nat (-22) 18 fc_bounce35.(ftape) &&
    negb (bt_get (z_to_pos (-4)) fc_bounce35.(ftape)) &&
    bt_get (z_to_pos (-3)) fc_bounce35.(ftape) &&
    negb (bt_get (z_to_pos (-2)) fc_bounce35.(ftape)) &&
    negb (bt_get (z_to_pos (-1)) fc_bounce35.(ftape)) &&
    negb (bt_get (z_to_pos 0) fc_bounce35.(ftape)) &&
    bt_bounded_aux (-22) (-3) (fun q => q) fc_bounce35.(ftape) = true)
    by (vm_compute; reflexivity).
  rewrite !andb_true_iff in Hcheck.
  destruct Hcheck as [[[[[[H18 Hm4] Hm3] Hm2] Hm1] H0] Hbd].
  rewrite !negb_true_iff in Hm4, Hm2, Hm1, H0.
  unfold fc_to_cfg, ag2_head. cbn [tape ftape].
  splits.
  - intros z Hz. eapply check_all_true_nat_sound; [exact H18 |]. change (Z.of_nat 18) with 18. lia.
  - exact Hm4.
  - exact Hm3.
  - exact Hm2.
  - exact Hm1.
  - exact H0.
  - intros z Hz. eapply bt_bounded_sound; [exact Hbd | lia].
Qed.

Lemma check_states_BB : forall s1 s2,
  (match s1, s2 with StB, StB => true | _, _ => false end = true) ->
  s1 = StB /\ s2 = StB.
Proof. destruct s1, s2; simpl; intros H; try discriminate; auto. Qed.

Lemma bounce_35 : forall P2 c,
  c.(pos1) = P2 - 22 ->
  c.(state1) = StA ->
  c.(pos2) = P2 ->
  c.(state2) = StB ->
  (forall z, P2 - 22 <= z <= P2 - 5 -> c.(tape) z = true) ->
  ag2_head P2 c.(tape) ->
  (forall k, (k < 35)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  let c' := run_N ag1 ag2 35 c in
  c'.(pos1) = P2 - 17 /\
  c'.(state1) = StB /\
  c'.(pos2) = P2 + 3 /\
  c'.(state2) = StB /\
  (forall z, z < P2 - 22 -> c'.(tape) z = c.(tape) z) /\
  (forall z, P2 - 22 <= z <= P2 - 17 -> c'.(tape) z = true) /\
  c'.(tape) (P2 - 16) = false /\
  alt_pairs (P2 - 15) 6 c'.(tape) /\
  c'.(tape) (P2 - 3) = true /\
  c'.(tape) (P2 - 2) = true /\
  ag2_head (P2 + 3) c'.(tape).
Proof.
  intros P2 c Hp1 Hs1 Hp2 Hs2 Htr Hhd.
  pose proof bounce35_ok as Hok.
  remember (N.iter 35 (fast_step_chk_ge (-22)) (fc_bounce35, true)) as st eqn:Est.
  destruct st as [fc35 ok35].
  unfold check_bounce35 in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[[[[[[[[[[Hok_b Hp1f] Hp2f] Hst] H6] Hm16] Halt] Hm3] Hm2] Hm1] H0] H1] H2] H3] Hbd].
  rewrite Z.eqb_eq in Hp1f, Hp2f.
  rewrite !negb_true_iff in Hm16, Hm1, H1, H2, H3.
  apply check_states_BB in Hst. destruct Hst as [Hs1f Hs2f].
  assert (Hfc35 : fc35 = N.iter 35 fast_step fc_bounce35).
  { pose proof (fast_step_chk_ge_fst 35 (-22) fc_bounce35 true) as Hfst.
    rewrite <- Est in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 35 (fast_step_chk_ge (-22)) (fc_bounce35, true)) = true).
  { rewrite <- Est. exact Hok_b. }
  clear Est Hok_b ok35.
  destruct (fast_step_chk_ge_sound 35 (-22) fc_bounce35 true Hsnd) as [_ Hchk].
  pose proof (fast_run_sound 35 fc_bounce35) as Hrun35.
  rewrite <- Hfc35 in Hrun35.
  destruct Hrun35 as [Rp1 Rp2 Rs1 Rs2 Rtp].
  rewrite fc_to_cfg_pos1 in Rp1. rewrite fc_to_cfg_pos2 in Rp2.
  rewrite fc_to_cfg_state1 in Rs1. rewrite fc_to_cfg_state2 in Rs2.
  assert (Hbd_cf : forall k, (k < 35)%N ->
            (-22 <= (run_N ag1 ag2 k (fc_to_cfg fc_bounce35)).(pos1) /\
             -22 <= (run_N ag1 ag2 k (fc_to_cfg fc_bounce35)).(pos2)) /\
            (run_N ag1 ag2 k (fc_to_cfg fc_bounce35)).(pos1) <>
            (run_N ag1 ag2 k (fc_to_cfg fc_bounce35)).(pos2)).
  { intros k Hk.
    pose proof (fast_run_sound k fc_bounce35) as [Kp1 Kp2 _ _ _].
    rewrite fc_to_cfg_pos1 in Kp1. rewrite fc_to_cfg_pos2 in Kp2.
    destruct (N.eq_0_gt_0_cases k) as [-> | Hkgt].
    - rewrite run_N_0, fc_to_cfg_pos1, fc_to_cfg_pos2.
      unfold fc_bounce35; cbn [fpos1 fpos2]; lia.
    - destruct (Hchk k ltac:(lia)) as [Hn [Hb1 Hb2]]. lia. }
  assert (Hbd_only : forall k, (k < 35)%N ->
            -22 <= (run_N ag1 ag2 k (fc_to_cfg fc_bounce35)).(pos1) /\
            -22 <= (run_N ag1 ag2 k (fc_to_cfg fc_bounce35)).(pos2))
    by (intros k Hk; apply (Hbd_cf k Hk)).
  destruct fc_bounce35_tape_ok as [Hcf_tr Hcf_hd].
  assert (Hag : agree_ge (-22) (fc_to_cfg fc_bounce35).(tape) (shift_cfg (- P2) c).(tape)).
  { intros z Hz. rewrite shift_cfg_tape.
    destruct (Z.lt_ge_cases z (-4)) as [Hz4 | Hz4].
    - rewrite Hcf_tr by lia. symmetry. apply Htr. lia.
    - destruct Hcf_hd as [A1 [A2 [A3 [A4 [A5 A6]]]]].
      change (0 - 4) with (-4) in A1. change (0 - 3) with (-3) in A2.
      change (0 - 2) with (-2) in A3. change (0 - 1) with (-1) in A4.
      destruct Hhd as [B1 [B2 [B3 [B4 [B5 B6]]]]].
      destruct (Z.eqb_spec z (-4)) as [-> | Hm4];
        [rewrite A1; symmetry; replace (-4 - - P2) with (P2 - 4) by lia; exact B1 |].
      destruct (Z.eqb_spec z (-3)) as [-> | Hm3'];
        [rewrite A2; symmetry; replace (-3 - - P2) with (P2 - 3) by lia; exact B2 |].
      destruct (Z.eqb_spec z (-2)) as [-> | Hm2'];
        [rewrite A3; symmetry; replace (-2 - - P2) with (P2 - 2) by lia; exact B3 |].
      destruct (Z.eqb_spec z (-1)) as [-> | Hm1'];
        [rewrite A4; symmetry; replace (-1 - - P2) with (P2 - 1) by lia; exact B4 |].
      destruct (Z.eqb_spec z 0) as [-> | Hz0];
        [rewrite A5; symmetry; replace (0 - - P2) with P2 by lia; exact B5 |].
      rewrite A6 by lia. symmetry. apply B6. lia. }
  assert (Hcf_p1 : (fc_to_cfg fc_bounce35).(pos1) = (shift_cfg (- P2) c).(pos1))
    by (rewrite fc_to_cfg_pos1, shift_cfg_pos1; unfold fc_bounce35; cbn [fpos1]; lia).
  assert (Hcf_p2 : (fc_to_cfg fc_bounce35).(pos2) = (shift_cfg (- P2) c).(pos2))
    by (rewrite fc_to_cfg_pos2, shift_cfg_pos2; unfold fc_bounce35; cbn [fpos2]; lia).
  assert (Hcf_s1 : (fc_to_cfg fc_bounce35).(state1) = (shift_cfg (- P2) c).(state1))
    by (rewrite fc_to_cfg_state1, shift_cfg_state1; unfold fc_bounce35; cbn [fstate1]; congruence).
  assert (Hcf_s2 : (fc_to_cfg fc_bounce35).(state2) = (shift_cfg (- P2) c).(state2))
    by (rewrite fc_to_cfg_state2, shift_cfg_state2; unfold fc_bounce35; cbn [fstate2]; congruence).
  destruct (run_N_agree_ge ag1 ag2 (-22) 35 (fc_to_cfg fc_bounce35) (shift_cfg (- P2) c)
              Hcf_p1 Hcf_p2 Hcf_s1 Hcf_s2 Hag Hbd_only)
    as [Ap1 [Ap2 [As1 [As2 [Aag [Alt Aprev]]]]]].
  assert (Hbd_sh : forall k, (k < 35)%N ->
            -22 <= (run_N ag1 ag2 k (shift_cfg (- P2) c)).(pos1) /\
            -22 <= (run_N ag1 ag2 k (shift_cfg (- P2) c)).(pos2)).
  { intros k Hk. destruct (Aprev k Hk) as [E1 E2]. rewrite <- E1, <- E2. apply Hbd_only; exact Hk. }
  assert (Hag_rev : agree_ge (-22) (shift_cfg (- P2) c).(tape) (fc_to_cfg fc_bounce35).(tape))
    by (intros z Hz; symmetry; apply Hag; exact Hz).
  destruct (run_N_agree_ge ag1 ag2 (-22) 35 (shift_cfg (- P2) c) (fc_to_cfg fc_bounce35)
              (eq_sym Hcf_p1) (eq_sym Hcf_p2) (eq_sym Hcf_s1) (eq_sym Hcf_s2) Hag_rev Hbd_sh)
    as [_ [_ [_ [_ [_ [Alt_sh _]]]]]].
  pose proof (run_N_shift ag1 ag2 (- P2) 35 c) as [Shp1 Shp2 Shs1 Shs2 Shtp].
  rewrite shift_cfg_pos1 in Shp1. rewrite shift_cfg_pos2 in Shp2.
  rewrite shift_cfg_state1 in Shs1. rewrite shift_cfg_state2 in Shs2.
  assert (Htp_ge : forall z, P2 - 22 <= z ->
            (run_N ag1 ag2 35 c).(tape) z = bt_get (z_to_pos (z - P2)) fc35.(ftape)).
  { intros z Hz.
    pose proof (Shtp (z - P2)) as Hz1.
    rewrite shift_cfg_tape in Hz1.
    replace (z - P2 - - P2) with z in Hz1 by lia.
    rewrite Hz1. rewrite <- Aag by lia. rewrite <- Rtp.
    rewrite fc_to_cfg_tape. reflexivity. }
  splits.
  - intros k Hk.
    pose proof (run_N_shift ag1 ag2 (- P2) k c) as [Kp1 Kp2 _ _ _].
    rewrite shift_cfg_pos1 in Kp1. rewrite shift_cfg_pos2 in Kp2.
    destruct (Aprev k Hk) as [Eq1 Eq2].
    destruct (Hbd_cf k Hk) as [_ Hne].
    lia.
  - lia.
  - rewrite Shs1, <- As1, <- Rs1. exact Hs1f.
  - lia.
  - rewrite Shs2, <- As2, <- Rs2. exact Hs2f.
  - intros z Hz.
    pose proof (Shtp (z - P2)) as Hz1.
    rewrite shift_cfg_tape in Hz1.
    replace (z - P2 - - P2) with z in Hz1 by lia.
    rewrite Hz1, Alt_sh by lia.
    rewrite shift_cfg_tape. f_equal. lia.
  - intros z Hz. rewrite Htp_ge by lia.
    eapply check_all_true_nat_sound; [exact H6 |]. change (Z.of_nat 6) with 6. lia.
  - rewrite Htp_ge by lia. replace (P2 - 16 - P2) with (-16) by lia. exact Hm16.
  - intros i Hi. split; rewrite Htp_ge by lia.
    + replace (P2 - 15 + 2 * Z.of_N i - P2) with (-15 + 2 * Z.of_N i) by lia.
      eapply (check_alt_pairs_nat_sound 6 (-15) fc35.(ftape) i Halt).
      change (N.of_nat 6) with 6%N. exact Hi.
    + replace (P2 - 15 + 2 * Z.of_N i + 1 - P2) with (-15 + 2 * Z.of_N i + 1) by lia.
      eapply (check_alt_pairs_nat_sound 6 (-15) fc35.(ftape) i Halt).
      change (N.of_nat 6) with 6%N. exact Hi.
  - rewrite Htp_ge by lia. replace (P2 - 3 - P2) with (-3) by lia. exact Hm3.
  - rewrite Htp_ge by lia. replace (P2 - 2 - P2) with (-2) by lia. exact Hm2.
  - unfold ag2_head. splits.
    + rewrite Htp_ge by lia. replace (P2 + 3 - 4 - P2) with (-1) by lia. exact Hm1.
    + rewrite Htp_ge by lia. replace (P2 + 3 - 3 - P2) with 0 by lia. exact H0.
    + rewrite Htp_ge by lia. replace (P2 + 3 - 2 - P2) with 1 by lia. exact H1.
    + rewrite Htp_ge by lia. replace (P2 + 3 - 1 - P2) with 2 by lia. exact H2.
    + rewrite Htp_ge by lia. replace (P2 + 3 - P2) with 3 by lia. exact H3.
    + intros z Hz. rewrite Htp_ge by lia. eapply bt_bounded_sound; [exact Hbd | lia].
Qed.


(** * 9. Round 2 (m2 bits) and Exact Halting at 26 Steps after D = 28 *)

Lemma srun_preserve_lt : forall ag lo n sc,
  (forall k, (k < n)%N -> lo <= (srun ag k sc).(spos)) ->
  forall z, z < lo -> (srun ag n sc).(stape) z = sc.(stape) z.
Proof.
  intros ag lo n sc Hbd z Hz.
  induction n using N.peano_ind.
  - rewrite srun_0. reflexivity.
  - rewrite srun_succ. unfold sstep. cbn [stape].
    rewrite write_tape_other.
    + apply IHn. intros k Hk. apply Hbd. lia.
    + pose proof (Hbd n ltac:(lia)). lia.
Qed.

Lemma ag2_prefix_ge : forall X sc k,
  sc.(spos) = X -> sc.(sstate) = StB -> ag2_head X sc.(stape) -> (k <= 11)%N ->
  (forall t, (t < k)%N -> X - 4 <= (srun ag2 t sc).(spos)) /\
  (forall z, z <= X - 5 -> (srun ag2 k sc).(stape) z = sc.(stape) z).
Proof.
  intros X sc k Hp Hs Hhd Hk.
  destruct (ag2_cycle11 X sc Hp Hs Hhd) as [Cybd _].
  split.
  - intros t Ht. apply Cybd. lia.
  - intros z Hz. eapply (srun_preserve_lt ag2 (X - 4)); [intros t Ht; apply Cybd; lia | lia].
Qed.

Lemma pow2_20q_14_mod220 : forall q : N,
  exists k : N, (2 ^ (20 * q + 14) = 220 * k + 104)%N.
Proof.
  intro q. induction q using N.peano_ind.
  - exists 74%N. vm_compute. reflexivity.
  - destruct IHq as [k Hk].
    exists (2 ^ 20 * k + 495690)%N.
    replace (20 * N.succ q + 14)%N with (20 + (20 * q + 14))%N by lia.
    rewrite N.pow_add_r, Hk.
    change (2 ^ 20)%N with 1048576%N.
    lia.
Qed.

Definition p1_prime : N := (p1_sync1 + 2 * r1)%N.
Definition t_dt0_r2 : N := (t_sync1 + 22 * r1 + 35)%N.
Definition p1_dt0_r2 : N := (p1_prime + 3)%N.
Definition wipe_steps : N := (p1_prime - 13)%N.
Definition K_wipe : N := (wipe_steps / 2)%N.
Definition m2 : N := (K_wipe + 6)%N.
Definition q_m2 : N := ((m2 + 2 - 14) / 20)%N.

Lemma t_dt0_r2_val :
  t_dt0_r2 = 38583643225535837040577279583709871718916619138094%N.
Proof. vm_compute. reflexivity. Qed.

Lemma wipe_K_eq : wipe_steps = (2 * K_wipe)%N.
Proof. vm_compute. reflexivity. Qed.

Lemma wipe_p1_eq : (wipe_steps + 13)%N = p1_prime.
Proof. vm_compute. reflexivity. Qed.

Lemma m2_kw_eq : m2 = (K_wipe + 6)%N.
Proof. reflexivity. Qed.

Lemma m2_val :
  m2 = 1753801964797083501844421799259539623587119051732%N.
Proof. vm_compute. reflexivity. Qed.

Lemma m2_plus2_eq : (m2 + 2)%N = (20 * q_m2 + 14)%N.
Proof. vm_compute. reflexivity. Qed.

Lemma p1_prime_ge : (25 <= p1_prime)%N.
Proof. apply N.leb_le. vm_compute. reflexivity. Qed.

Lemma K_wipe_pos : (1 <= K_wipe)%N.
Proof. apply N.leb_le. vm_compute. reflexivity. Qed.

Lemma m2_ge_10 : (10 <= m2)%N.
Proof. apply N.leb_le. vm_compute. reflexivity. Qed.

Lemma bridge_to_r2 :
  let c := run_N ag1 ag2 t_dt0_r2 c0 in
  c.(pos1) = Z.of_N p1_prime - 17 /\
  c.(state1) = StB /\
  c.(pos2) = Z.of_N p1_prime + 3 /\
  c.(state2) = StB /\
  c.(tape) (-4) = false /\
  (forall z, -3 <= z <= Z.of_N p1_prime - 17 -> c.(tape) z = true) /\
  c.(tape) (Z.of_N p1_prime - 16) = false /\
  alt_pairs (Z.of_N p1_prime - 15) 6 c.(tape) /\
  c.(tape) (Z.of_N p1_prime - 3) = true /\
  c.(tape) (Z.of_N p1_prime - 2) = true /\
  ag2_head (Z.of_N p1_prime + 3) c.(tape) /\
  (forall t, (t < t_dt0_r2)%N -> (run_N ag1 ag2 t c0).(pos1) <> (run_N ag1 ag2 t c0).(pos2)).
Proof.
  destruct bridge_to_sync1 as [B1p1 [B1p2 [B1s1 [B1s2 [B1m4 [B1tr [B1hd B1nc]]]]]]].
  remember (run_N ag1 ag2 t_sync1 c0) as c_s1 eqn:Ecs1.
  destruct (chase_loop22 r1 22 (-3) 325 (Z.of_N p1_sync1) c_s1
              ltac:(lia) B1p1 B1s1 B1p2 B1s2 ltac:(lia) D1_decomp B1tr B1hd)
    as [Lnc [Lp1 [Ls1 [Lp2 [Ls2 [Lgap [Lbelow [Ltr Lhd]]]]]]]].
  remember (run_N ag1 ag2 (22 * r1) c_s1) as c_ch1 eqn:Ecch1.
  assert (Hp1p : c_ch1.(pos2) = Z.of_N p1_prime).
  { rewrite Lp2. unfold p1_prime. rewrite N2Z.inj_add, N2Z.inj_mul. change (Z.of_N 2) with 2. reflexivity. }
  assert (Hp1_ch : c_ch1.(pos1) = Z.of_N p1_prime - 22) by lia.
  assert (Htr_ch : forall z, Z.of_N p1_prime - 22 <= z <= Z.of_N p1_prime - 5 -> c_ch1.(tape) z = true).
  { intros z Hz. pose proof p1_prime_ge. apply Ltr. lia. }
  rewrite Hp1p in Lhd.
  destruct (bounce_35 (Z.of_N p1_prime) c_ch1 Hp1_ch Ls1 Hp1p Ls2 Htr_ch Lhd)
    as [B35nc [B35p1 [B35s1 [B35p2 [B35s2 [B35below [B35tr [B35m16 [B35alt [B35m3 [B35m2 B35hd]]]]]]]]]]].
  assert (Htr2_eq : t_dt0_r2 = (35 + (22 * r1 + t_sync1))%N) by (unfold t_dt0_r2; lia).
  cbv zeta. rewrite Htr2_eq, !run_N_add, <- Ecs1, <- Ecch1.
  pose proof p1_prime_ge as Hp1ge.
  splits.
  - exact B35p1.
  - exact B35s1.
  - exact B35p2.
  - exact B35s2.
  - rewrite B35below by lia. rewrite Lbelow by lia. exact B1m4.
  - intros z Hz. destruct (Z.lt_ge_cases z (Z.of_N p1_prime - 22)).
    + rewrite B35below by lia. apply Ltr. lia.
    + apply B35tr. lia.
  - exact B35m16.
  - exact B35alt.
  - exact B35m3.
  - exact B35m2.
  - exact B35hd.
  - intros t Ht.
    assert (Hnc_mid : forall k, (k < 22 * r1 + t_sync1)%N ->
              (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2)).
    { intros k Hk. eapply no_coll_add; [exact B1nc | rewrite <- Ecs1; exact Lnc | exact Hk]. }
    eapply no_coll_add; [exact Hnc_mid | | exact Ht].
    rewrite run_N_add, <- Ecs1, <- Ecch1. exact B35nc.
Qed.

Lemma round2_to_sync2 : forall K_pow : N,
  (2 ^ (m2 + 2) = 220 * K_pow + 104)%N ->
  let t2 := (5 + (wipe_steps + S_val m2) + t_dt0_r2)%N in
  let Q := (60 * K_pow + 26)%N in
  let c := run_N ag1 ag2 t2 c0 in
  c.(pos1) = Z.of_N p1_prime + 2 /\
  c.(state1) = StA /\
  c.(pos2) = Z.of_N p1_prime + 4 + Z.of_N Q /\
  c.(state2) = StB /\
  (forall z, Z.of_N p1_prime + 2 <= z <= c.(pos2) - 5 -> c.(tape) z = true) /\
  ag2_head c.(pos2) c.(tape) /\
  (forall t, (t < t2)%N -> (run_N ag1 ag2 t c0).(pos1) <> (run_N ag1 ag2 t c0).(pos2)).
Proof.
  intros K_pow Hpow.
  set (Q := (60 * K_pow + 26)%N).
  set (t_2a := (wipe_steps + S_val m2)%N).
  pose proof m2_ge_10 as Hm2_10.
  pose proof K_wipe_pos as Hkw_1.
  pose proof p1_prime_ge as Hp1_25.
  pose proof wipe_K_eq as Hwk.
  pose proof wipe_p1_eq as Hwp1.
  pose proof m2_kw_eq as Hm2kw.
  assert (HS_eq : S_val m2 = (660 * K_pow + 312 - 2 * m2 - 8)%N)
    by (unfold S_val; rewrite Hpow; lia).
  pose proof (n_lt_pow2 (m2 + 2)) as Hlt_pow.
  rewrite Hpow in Hlt_pow.
  assert (Ht2a_eq : t_2a = (6 + 11 * Q)%N) by (unfold t_2a, Q; lia).
  destruct bridge_to_r2 as [R2p1 [R2s1 [R2p2 [R2s2 [R2m4 [R2tr [R2m16 [R2alt [R2m3 [R2m2 [R2hd R2nc]]]]]]]]]]].
  remember (run_N ag1 ag2 t_dt0_r2 c0) as cr2 eqn:Ecr2.
  (* Phase 2a: Agent 1 wipe + counter (t_2a steps), Agent 2 glider Q + 6 steps *)
  set (sc1 := {| spos := Z.of_N p1_prime - 17; sstate := StB; stape := cr2.(tape) |}).
  assert (Hwp_p : sc1.(spos) = -2 + 2 * Z.of_N K_wipe - 2) by (unfold sc1; cbn [spos]; lia).
  assert (Hwp_s : sc1.(sstate) = StB) by reflexivity.
  assert (Hwp_tr : forall z, -2 - 1 <= z <= -2 + 2 * Z.of_N K_wipe - 2 -> sc1.(stape) z = true)
    by (intros z Hz; unfold sc1; cbn [stape]; apply R2tr; lia).
  destruct (ag1_wipe_pairs K_wipe (-2) sc1 Hwp_p Hwp_s Hwp_tr)
    as [Wbd [Wp [Ws [Walt Wo]]]].
  rewrite <- Hwk in Wbd.
  remember (srun ag1 wipe_steps sc1) as sc1_w eqn:Esc1w.
  assert (Hsc1w_eq : sc1_w = srun ag1 (2 * K_wipe) sc1) by (rewrite Esc1w, Hwk; reflexivity).
  rewrite <- Hsc1w_eq in Wp, Ws, Walt, Wo.
  assert (Hwf4 : sc1_w.(stape) (-4) = false) by (rewrite Wo by lia; exact R2m4).
  assert (Hwf3 : sc1_w.(stape) (-3) = false)
    by (destruct (Walt 0%N ltac:(lia)) as [_ H0]; exact H0).
  assert (Halt2 : alt_pairs (-2) ((m2 - 1) + 1) sc1_w.(stape)).
  { replace ((m2 - 1) + 1)%N with m2 by lia.
    intros i Hi.
    destruct (N.lt_ge_cases i (K_wipe - 1)) as [Hi1 | Hi2].
    - destruct (Walt i ltac:(lia)) as [Ht _].
      destruct (Walt (N.succ i) ltac:(lia)) as [_ Hf].
      rewrite N2Z.inj_succ in Hf.
      split; [exact Ht | replace (-2 + 2 * Z.of_N i + 1) with (-2 + 2 * Z.succ (Z.of_N i) - 1) by lia; exact Hf].
    - destruct (N.eq_dec i (K_wipe - 1)) as [Heq | Hne].
      + subst i. destruct (Walt (K_wipe - 1)%N ltac:(lia)) as [Ht _].
        split; [exact Ht |].
        rewrite Wo by lia.
        replace (-2 + 2 * Z.of_N (K_wipe - 1) + 1) with (Z.of_N p1_prime - 16) by lia.
        exact R2m16.
      + assert (Hik : (K_wipe <= i < K_wipe + 6)%N) by lia.
        rewrite !Wo by lia.
        destruct (R2alt (i - K_wipe)%N ltac:(lia)) as [Ht Hf].
        split;
          [replace (-2 + 2 * Z.of_N i) with (Z.of_N p1_prime - 15 + 2 * Z.of_N (i - K_wipe)) by lia; exact Ht
          | replace (-2 + 2 * Z.of_N i + 1) with (Z.of_N p1_prime - 15 + 2 * Z.of_N (i - K_wipe) + 1) by lia; exact Hf]. }
  destruct (ag1_counter (m2 - 1) sc1_w Wp Ws Hwf4 Hwf3 Halt2)
    as [Cbd [Cp [Cs [Cf4 [Ctr Co]]]]].
  replace ((m2 - 1) + 1)%N with m2 in Cbd, Cp, Cs, Cf4, Ctr, Co by lia.
  remember (srun ag1 (S_val m2) sc1_w) as sc1_cnt eqn:Esc1cnt.
  assert (Ht2a_comm : t_2a = (S_val m2 + wipe_steps)%N) by (unfold t_2a; lia).
  assert (Hag1_2a_bd : forall k, (k < t_2a)%N -> (srun ag1 k sc1).(spos) <= Z.of_N p1_prime - 4).
  { intros k Hk. destruct (N.lt_ge_cases k wipe_steps) as [Hk1 | Hk2].
    - pose proof (Wbd k Hk1). lia.
    - replace k with ((k - wipe_steps) + wipe_steps)%N by lia.
      rewrite srun_add, <- Esc1w.
      pose proof (Cbd (k - wipe_steps)%N ltac:(unfold t_2a in Hk; lia)). lia. }
  set (sc2 := {| spos := Z.of_N p1_prime + 3; sstate := StB; stape := cr2.(tape) |}).
  assert (Hg_lo : Z.of_N p1_prime - 1 <= Z.of_N p1_prime + 3 - 4) by lia.
  assert (Hg_tr : forall z, Z.of_N p1_prime - 1 <= z <= Z.of_N p1_prime + 3 - 5 -> sc2.(stape) z = true)
    by (intros; lia).
  destruct (ag2_glider Q (Z.of_N p1_prime - 1) (Z.of_N p1_prime + 3) sc2 Hg_lo eq_refl eq_refl Hg_tr R2hd)
    as [Gbd [Gp [Gs [Gbelow [Gtr Ghd]]]]].
  remember (srun ag2 (11 * Q) sc2) as sc2_q eqn:Esc2q.
  assert (Hag2_2a_bd : forall k, (k < t_2a)%N -> Z.of_N p1_prime - 1 <= (srun ag2 k sc2).(spos)).
  { intros k Hk. rewrite Ht2a_eq in Hk.
    destruct (N.lt_ge_cases k (11 * Q)) as [Hk1 | Hk2].
    - apply Gbd; exact Hk1.
    - replace k with ((k - 11 * Q) + 11 * Q)%N by lia.
      rewrite srun_add, <- Esc2q.
      destruct (ag2_prefix_ge (Z.of_N p1_prime + 3 + Z.of_N Q) sc2_q 6 Gp Gs Ghd ltac:(lia)) as [Pbd _].
      pose proof (Pbd (k - 11 * Q)%N ltac:(lia)). lia. }
  assert (Hsep2a : Z.of_N p1_prime - 4 < Z.of_N p1_prime - 1) by lia.
  assert (Hdt1_2a : forall z, z <= Z.of_N p1_prime - 4 -> cr2.(tape) z = sc1.(stape) z)
    by (intros; unfold sc1; cbn [stape]; reflexivity).
  assert (Hdt2_2a : forall z, Z.of_N p1_prime - 1 <= z -> cr2.(tape) z = sc2.(stape) z)
    by (intros; unfold sc2; cbn [stape]; reflexivity).
  destruct (run_decouple ag1 ag2 (Z.of_N p1_prime - 4) (Z.of_N p1_prime - 1) t_2a cr2 sc1 sc2
              Hsep2a R2p1 R2s1 R2p2 R2s2 Hdt1_2a Hdt2_2a Hag1_2a_bd Hag2_2a_bd)
    as [D1p1 [D1s1 [D1p2 [D1s2 [D1t1 [D1t2 [D1mid D1nc]]]]]]].
  remember (run_N ag1 ag2 t_2a cr2) as c2a eqn:Ec2a.
  assert (Hc2a_ag1 : srun ag1 t_2a sc1 = sc1_cnt)
    by (rewrite Ht2a_comm, srun_add, <- Esc1w, <- Esc1cnt; reflexivity).
  assert (Hc2a_ag2 : srun ag2 t_2a sc2 = srun ag2 6 sc2_q)
    by (rewrite Ht2a_eq, srun_add, <- Esc2q; reflexivity).
  rewrite Hc2a_ag1 in D1p1, D1s1, D1t1.
  rewrite Hc2a_ag2 in D1p2, D1s2, D1t2.
  (* Phase 2b: Agent 1 walk 5 across [p1_prime-3..p1_prime+1], Agent 2 remainder 5 of cycle 11 *)
  set (sc1b := {| spos := Z.of_N p1_prime - 3; sstate := StA; stape := c2a.(tape) |}).
  assert (Hc2a_p1 : c2a.(pos1) = Z.of_N p1_prime - 3) by (rewrite D1p1, Cp; lia).
  assert (Hc2a_s1 : c2a.(state1) = StA) by (rewrite D1s1; exact Cs).
  destruct (ag2_prefix_ge (Z.of_N p1_prime + 3 + Z.of_N Q) sc2_q 6 Gp Gs Ghd ltac:(lia)) as [_ Hpre6].
  assert (Hw5_tr : forall z, Z.of_N p1_prime - 3 <= z < Z.of_N p1_prime - 3 + Z.of_N 5 -> sc1b.(stape) z = true).
  { intros z Hz. change (Z.of_N 5) with 5 in Hz. unfold sc1b; cbn [stape].
    destruct (Z.eqb_spec z (Z.of_N p1_prime - 3)) as [-> | Hn3]; [rewrite D1mid by lia; exact R2m3 |].
    destruct (Z.eqb_spec z (Z.of_N p1_prime - 2)) as [-> | Hn2]; [rewrite D1mid by lia; exact R2m2 |].
    rewrite D1t2 by lia. rewrite Hpre6 by (unfold Q; lia). apply Gtr. unfold Q; lia. }
  destruct (ag1_walk_ones 5 (Z.of_N p1_prime - 3) sc1b eq_refl eq_refl Hw5_tr)
    as [W5bd [W5p [W5s W5t]]].
  assert (Hag1_2b_bd : forall k, (k < 5)%N -> (srun ag1 k sc1b).(spos) <= Z.of_N p1_prime + 1).
  { intros k Hk. pose proof (W5bd k Hk). change (Z.of_N 5) with 5 in *. lia. }
  set (B2b := Z.of_N p1_prime + 3 + Z.of_N Q - 4).
  set (sc2b := srun ag2 6 sc2_q).
  destruct (ag2_cycle11 (Z.of_N p1_prime + 3 + Z.of_N Q) sc2_q Gp Gs Ghd)
    as [Cybd [Cyp [Cys [Cybelow [Cyw Cyhd]]]]].
  assert (Hag2_2b_bd : forall k, (k < 5)%N -> B2b <= (srun ag2 k sc2b).(spos)).
  { intros k Hk. unfold sc2b. rewrite <- srun_add.
    pose proof (Cybd (k + 6)%N ltac:(lia)). unfold B2b. lia. }
  assert (Hsep2b : Z.of_N p1_prime + 1 < B2b) by (unfold B2b, Q; lia).
  assert (Hdt1_2b : forall z, z <= Z.of_N p1_prime + 1 -> c2a.(tape) z = sc1b.(stape) z)
    by (intros; unfold sc1b; cbn [stape]; reflexivity).
  assert (Hdt2_2b : forall z, B2b <= z -> c2a.(tape) z = sc2b.(stape) z)
    by (intros z Hz; apply D1t2; unfold B2b, Q in *; lia).
  destruct (run_decouple ag1 ag2 (Z.of_N p1_prime + 1) B2b 5 c2a sc1b sc2b
              Hsep2b Hc2a_p1 Hc2a_s1 D1p2 D1s2 Hdt1_2b Hdt2_2b Hag1_2b_bd Hag2_2b_bd)
    as [D2p1 [D2s1 [D2p2 [D2s2 [D2t1 [D2t2 [D2mid D2nc]]]]]]].
  assert (H2b_11 : srun ag2 5 sc2b = srun ag2 11 sc2_q)
    by (unfold sc2b; rewrite <- srun_add; reflexivity).
  rewrite H2b_11 in D2p2, D2s2, D2t2.
  cbv zeta.
  replace (5 + (wipe_steps + S_val m2) + t_dt0_r2)%N with (5 + (t_2a + t_dt0_r2))%N by (unfold t_2a; lia).
  rewrite !run_N_add, <- Ecr2, <- Ec2a.
  splits.
  - rewrite D2p1, W5p. change (Z.of_N 5) with 5. lia.
  - rewrite D2s1. exact W5s.
  - rewrite D2p2, Cyp. fold Q. lia.
  - rewrite D2s2. exact Cys.
  - intros z Hz. rewrite D2p2, Cyp in Hz.
    destruct (Z.lt_ge_cases z B2b).
    + rewrite D2mid by lia. rewrite D1t2 by lia.
      rewrite Hpre6 by (unfold B2b in *; lia).
      apply Gtr. unfold B2b in *; lia.
    + rewrite D2t2 by exact H.
      replace z with (Z.of_N p1_prime + 3 + Z.of_N Q - 4) by (unfold B2b in *; lia).
      exact Cyw.
  - rewrite D2p2, Cyp. unfold ag2_head in *. destruct Cyhd as [A1 [A2 [A3 [A4 [A5 A6]]]]].
    splits.
    + rewrite D2t2 by (unfold B2b; lia). exact A1.
    + rewrite D2t2 by (unfold B2b; lia). exact A2.
    + rewrite D2t2 by (unfold B2b; lia). exact A3.
    + rewrite D2t2 by (unfold B2b; lia). exact A4.
    + rewrite D2t2 by (unfold B2b; lia). exact A5.
    + intros z Hz. rewrite D2t2 by (unfold B2b; lia). apply A6. exact Hz.
  - intros t Ht.
    assert (Hnc_2a : forall k, (k < t_2a + t_dt0_r2)%N ->
              (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
      by (intros k Hk; eapply no_coll_add; [exact R2nc | rewrite <- Ecr2; exact D1nc | exact Hk]).
    eapply (no_coll_add ag1 ag2 5 (t_2a + t_dt0_r2) c0 Hnc_2a); [rewrite run_N_add, <- Ecr2, <- Ec2a; exact D2nc | lia].
Qed.

Definition fc_final26 : FastConfig := {|
  fpos1 := -28; fpos2 := 0; fstate1 := StA; fstate2 := StB;
  ftape := bt_set (z_to_pos (-3)) true (bt_set_ones (-28) 24 BEmpty)
|}.

Definition check_final26 (st : FastConfig * bool) : bool :=
  let (fc, ok) := st in
  ok && ((fast_step fc).(fpos1) =? (fast_step fc).(fpos2)).

Lemma final26_ok :
  check_final26 (N.iter 25 (fast_step_chk_ge (-28)) (fc_final26, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fc_final26_tape_ok :
  (forall z, -28 <= z <= -5 -> (fc_to_cfg fc_final26).(tape) z = true) /\
  ag2_head 0 (fc_to_cfg fc_final26).(tape).
Proof.
  assert (Hcheck :
    check_all_true_nat (-28) 24 fc_final26.(ftape) &&
    negb (bt_get (z_to_pos (-4)) fc_final26.(ftape)) &&
    bt_get (z_to_pos (-3)) fc_final26.(ftape) &&
    negb (bt_get (z_to_pos (-2)) fc_final26.(ftape)) &&
    negb (bt_get (z_to_pos (-1)) fc_final26.(ftape)) &&
    negb (bt_get (z_to_pos 0) fc_final26.(ftape)) &&
    bt_bounded_aux (-28) (-3) (fun q => q) fc_final26.(ftape) = true)
    by (vm_compute; reflexivity).
  rewrite !andb_true_iff in Hcheck.
  destruct Hcheck as [[[[[[H24 Hm4] Hm3] Hm2] Hm1] H0] Hbd].
  rewrite !negb_true_iff in Hm4, Hm2, Hm1, H0.
  unfold fc_to_cfg, ag2_head. cbn [tape ftape].
  splits.
  - intros z Hz. eapply check_all_true_nat_sound; [exact H24 |]. change (Z.of_nat 24) with 24. lia.
  - exact Hm4.
  - exact Hm3.
  - exact Hm2.
  - exact Hm1.
  - exact H0.
  - intros z Hz. eapply bt_bounded_sound; [exact Hbd | lia].
Qed.

Lemma final_26 : forall P2 c,
  c.(pos1) = P2 - 28 ->
  c.(state1) = StA ->
  c.(pos2) = P2 ->
  c.(state2) = StB ->
  (forall z, P2 - 28 <= z <= P2 - 5 -> c.(tape) z = true) ->
  ag2_head P2 c.(tape) ->
  (forall k, (k < 26)%N -> (run_N ag1 ag2 k c).(pos1) <> (run_N ag1 ag2 k c).(pos2)) /\
  (run_N ag1 ag2 26 c).(pos1) = (run_N ag1 ag2 26 c).(pos2).
Proof.
  intros P2 c Hp1 Hs1 Hp2 Hs2 Htr Hhd.
  pose proof final26_ok as Hok.
  remember (N.iter 25 (fast_step_chk_ge (-28)) (fc_final26, true)) as st eqn:Est.
  destruct st as [fc25 ok25].
  unfold check_final26 in Hok. rewrite andb_true_iff, Z.eqb_eq in Hok.
  destruct Hok as [Hok_b Hcoll].
  assert (Hfc25 : fc25 = N.iter 25 fast_step fc_final26).
  { pose proof (fast_step_chk_ge_fst 25 (-28) fc_final26 true) as Hfst.
    rewrite <- Est in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 25 (fast_step_chk_ge (-28)) (fc_final26, true)) = true)
    by (rewrite <- Est; exact Hok_b).
  clear Est Hok_b ok25.
  destruct (fast_step_chk_ge_sound 25 (-28) fc_final26 true Hsnd) as [_ Hchk].
  assert (Hbd_cf : forall k, (k < 26)%N ->
            (-28 <= (run_N ag1 ag2 k (fc_to_cfg fc_final26)).(pos1) /\
             -28 <= (run_N ag1 ag2 k (fc_to_cfg fc_final26)).(pos2)) /\
            (run_N ag1 ag2 k (fc_to_cfg fc_final26)).(pos1) <>
            (run_N ag1 ag2 k (fc_to_cfg fc_final26)).(pos2)).
  { intros k Hk.
    pose proof (fast_run_sound k fc_final26) as [Kp1 Kp2 _ _ _].
    rewrite fc_to_cfg_pos1 in Kp1. rewrite fc_to_cfg_pos2 in Kp2.
    destruct (N.eq_0_gt_0_cases k) as [-> | Hkgt].
    - rewrite run_N_0, fc_to_cfg_pos1, fc_to_cfg_pos2.
      unfold fc_final26; cbn [fpos1 fpos2]; lia.
    - destruct (Hchk k ltac:(lia)) as [Hn [Hb1 Hb2]]. lia. }
  assert (Hbd_only : forall k, (k < 26)%N ->
            -28 <= (run_N ag1 ag2 k (fc_to_cfg fc_final26)).(pos1) /\
            -28 <= (run_N ag1 ag2 k (fc_to_cfg fc_final26)).(pos2))
    by (intros k Hk; apply (Hbd_cf k Hk)).
  destruct fc_final26_tape_ok as [Hcf_tr Hcf_hd].
  assert (Hag : agree_ge (-28) (fc_to_cfg fc_final26).(tape) (shift_cfg (- P2) c).(tape)).
  { intros z Hz. rewrite shift_cfg_tape.
    destruct (Z.lt_ge_cases z (-4)) as [Hz4 | Hz4].
    - rewrite Hcf_tr by lia. symmetry. apply Htr. lia.
    - destruct Hcf_hd as [A1 [A2 [A3 [A4 [A5 A6]]]]].
      change (0 - 4) with (-4) in A1. change (0 - 3) with (-3) in A2.
      change (0 - 2) with (-2) in A3. change (0 - 1) with (-1) in A4.
      destruct Hhd as [B1 [B2 [B3 [B4 [B5 B6]]]]].
      destruct (Z.eqb_spec z (-4)) as [-> | Hm4];
        [rewrite A1; symmetry; replace (-4 - - P2) with (P2 - 4) by lia; exact B1 |].
      destruct (Z.eqb_spec z (-3)) as [-> | Hm3'];
        [rewrite A2; symmetry; replace (-3 - - P2) with (P2 - 3) by lia; exact B2 |].
      destruct (Z.eqb_spec z (-2)) as [-> | Hm2'];
        [rewrite A3; symmetry; replace (-2 - - P2) with (P2 - 2) by lia; exact B3 |].
      destruct (Z.eqb_spec z (-1)) as [-> | Hm1'];
        [rewrite A4; symmetry; replace (-1 - - P2) with (P2 - 1) by lia; exact B4 |].
      destruct (Z.eqb_spec z 0) as [-> | Hz0];
        [rewrite A5; symmetry; replace (0 - - P2) with P2 by lia; exact B5 |].
      rewrite A6 by lia. symmetry. apply B6. lia. }
  assert (Hcf_p1 : (fc_to_cfg fc_final26).(pos1) = (shift_cfg (- P2) c).(pos1))
    by (rewrite fc_to_cfg_pos1, shift_cfg_pos1; unfold fc_final26; cbn [fpos1]; lia).
  assert (Hcf_p2 : (fc_to_cfg fc_final26).(pos2) = (shift_cfg (- P2) c).(pos2))
    by (rewrite fc_to_cfg_pos2, shift_cfg_pos2; unfold fc_final26; cbn [fpos2]; lia).
  assert (Hcf_s1 : (fc_to_cfg fc_final26).(state1) = (shift_cfg (- P2) c).(state1))
    by (rewrite fc_to_cfg_state1, shift_cfg_state1; unfold fc_final26; cbn [fstate1]; congruence).
  assert (Hcf_s2 : (fc_to_cfg fc_final26).(state2) = (shift_cfg (- P2) c).(state2))
    by (rewrite fc_to_cfg_state2, shift_cfg_state2; unfold fc_final26; cbn [fstate2]; congruence).
  destruct (run_N_agree_ge ag1 ag2 (-28) 26 (fc_to_cfg fc_final26) (shift_cfg (- P2) c)
              Hcf_p1 Hcf_p2 Hcf_s1 Hcf_s2 Hag Hbd_only)
    as [Ap1 [Ap2 [_ [_ [_ [_ Aprev]]]]]].
  pose proof (fast_run_sound 26 fc_final26) as [R26p1 R26p2 _ _ _].
  rewrite fc_to_cfg_pos1 in R26p1. rewrite fc_to_cfg_pos2 in R26p2.
  replace (N.iter 26 fast_step fc_final26) with (fast_step fc25) in R26p1, R26p2
    by (rewrite Hfc25; change 26%N with (N.succ 25); symmetry; apply N.iter_succ).
  pose proof (run_N_shift ag1 ag2 (- P2) 26 c) as [Sh26p1 Sh26p2 _ _ _].
  rewrite shift_cfg_pos1 in Sh26p1. rewrite shift_cfg_pos2 in Sh26p2.
  split.
  - intros k Hk.
    pose proof (run_N_shift ag1 ag2 (- P2) k c) as [Kp1 Kp2 _ _ _].
    rewrite shift_cfg_pos1 in Kp1. rewrite shift_cfg_pos2 in Kp2.
    destruct (Aprev k Hk) as [Eq1 Eq2].
    destruct (Hbd_cf k Hk) as [_ Hne].
    lia.
  - lia.
Qed.

Definition exact_T_halt : N :=
  ((33 * 2 ^ (m2 + 2) + 385836432255358370405772795837098717189166191380738) / 10)%N.

Theorem exact_T_halt_closed_form :
  (10 * exact_T_halt =
   33 * 2 ^ (m2 + 2) + 385836432255358370405772795837098717189166191380738)%N.
Proof.
  pose proof (pow2_20q_14_mod220 q_m2) as [K_pow Hpow].
  rewrite <- m2_plus2_eq in Hpow.
  unfold exact_T_halt. rewrite Hpow.
  replace (33 * (220 * K_pow + 104) + 385836432255358370405772795837098717189166191380738)%N
    with ((726 * K_pow + 38583643225535837040577279583709871718916619138417) * 10)%N by lia.
  rewrite N.div_mul by discriminate.
  lia.
Qed.

Theorem new_cet3_halts : halts_at_exact ag1 ag2 c0 exact_T_halt.
Proof.
  pose proof (pow2_20q_14_mod220 q_m2) as [K_pow Hpow].
  rewrite <- m2_plus2_eq in Hpow.
  set (Q := (60 * K_pow + 26)%N).
  set (t2 := (5 + (wipe_steps + S_val m2) + t_dt0_r2)%N).
  assert (HT_eq : exact_T_halt = (26 + (22 * (3 * K_pow) + t2))%N).
  { unfold exact_T_halt, t2. rewrite Hpow, t_dt0_r2_val.
    pose proof wipe_K_eq as Hwk. pose proof m2_kw_eq as Hm2kw.
    pose proof m2_ge_10 as Hm2_10.
    assert (HS_eq : S_val m2 = (660 * K_pow + 312 - 2 * m2 - 8)%N)
      by (unfold S_val; rewrite Hpow; lia).
    pose proof (n_lt_pow2 (m2 + 2)) as Hlt_pow. rewrite Hpow in Hlt_pow.
    replace (33 * (220 * K_pow + 104) + 385836432255358370405772795837098717189166191380738)%N
      with ((726 * K_pow + 38583643225535837040577279583709871718916619138417) * 10)%N by lia.
    rewrite N.div_mul by discriminate.
    lia. }
  destruct (round2_to_sync2 K_pow Hpow) as [S2p1 [S2s1 [S2p2 [S2s2 [S2tr [S2hd S2nc]]]]]].
  fold t2 Q in S2p1, S2s1, S2p2, S2s2, S2tr, S2hd, S2nc.
  remember (run_N ag1 ag2 t2 c0) as cs2 eqn:Ecs2.
  rewrite S2p2 in S2tr, S2hd.
  assert (Hgap2 : (Z.of_N p1_prime + 4 + Z.of_N Q) - (Z.of_N p1_prime + 2) = 28 + 20 * Z.of_N (3 * K_pow))
    by (rewrite N2Z.inj_mul; change (Z.of_N 3) with 3; unfold Q; rewrite N2Z.inj_add, N2Z.inj_mul; change (Z.of_N 60) with 60; change (Z.of_N 26) with 26; lia).
  destruct (chase_loop22 (3 * K_pow) 28 (Z.of_N p1_prime + 2)
              (Z.of_N p1_prime + 2) (Z.of_N p1_prime + 4 + Z.of_N Q) cs2
              ltac:(lia) S2p1 S2s1 S2p2 S2s2 ltac:(lia) Hgap2 S2tr S2hd)
    as [Cnc [Cp1 [Cs1 [Cp2 [Cs2 [Cgap [Cbelow [Ctr Chd]]]]]]]].
  remember (run_N ag1 ag2 (22 * (3 * K_pow)) cs2) as cc eqn:Ecc.
  assert (Hcc_p1 : cc.(pos1) = cc.(pos2) - 28) by lia.
  assert (Hcc_tr : forall z, cc.(pos2) - 28 <= z <= cc.(pos2) - 5 -> cc.(tape) z = true).
  { intros z Hz. apply Ctr. rewrite Cp2. pose proof (N2Z.is_nonneg (3 * K_pow)).
    unfold Q. rewrite !N2Z.inj_add, !N2Z.inj_mul.
    pose proof (N2Z.is_nonneg K_pow). lia. }
  destruct (final_26 cc.(pos2) cc Hcc_p1 Cs1 eq_refl Cs2 Hcc_tr Chd) as [Fnc Fcoll].
  unfold halts_at_exact, collides_at.
  rewrite HT_eq. split.
  - rewrite !run_N_add, <- Ecs2, <- Ecc. exact Fcoll.
  - intros t Ht.
    assert (Hnc_ch : forall k, (k < 22 * (3 * K_pow) + t2)%N ->
              (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2))
      by (intros k Hk; eapply no_coll_add; [exact S2nc | rewrite <- Ecs2; exact Cnc | exact Hk]).
    eapply no_coll_add; [exact Hnc_ch | | exact Ht].
    rewrite run_N_add, <- Ecs2, <- Ecc. exact Fnc.
Qed.

Print Assumptions new_cet3_halts.
Print Assumptions exact_T_halt_closed_form.
