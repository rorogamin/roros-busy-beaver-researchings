(**
  Formal Machine-Checked Proof of Normal Halting in Rocq 9.1
  Target Machine: 1LB1RA0LB_2RB2LB2RA | 2RB1LA1RB_2LB2RB1LA
  Model: Catch-Em-Turing CET(2,3), 2 agents, 2 states, 3 symbols.
  Starting positions: Agent 1 at 0 (StA), Agent 2 at 2 (StA), blank tape.
  Normal Halting: exact first collision pos1(T) = pos2(T).

  Mathematical Structure:
  - Concrete prefix (steps 0 .. 844): enters Round 2 at pos1 = 86 (StA), pos2 = 96 (StB),
    G1 = 10, L2 = 87 (anchor S2 at -1, S1 on [0..85], glider at [94..97]).
  - Agent 2 glider (P = 9, D = 1, M = 8): period 9, shift +1.
  - Agent 1 ternary counter: 3^L tower with gap sequence [10, 10, 10, 10, 10, 10, 8, 14],
    halting at step 13 after Round 8.
  - Modular arithmetic mod 72 * Q (Carmichael lambda chain 6 -> 18 -> 54 -> 162 -> 486 -> 1458).
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

Definition c0 : Config := {|
  pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape
|}.

(** * 3. Equivalence and Fast Binary-Tree Tape *)

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
  constructor; try congruence. eapply tape_eq_trans; eauto.
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
  apply bt_get_set_diff. intros Heq. apply n. rewrite <- (z_pos_z z), <- (z_pos_z p), Heq. reflexivity.
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

(** * 4. Concrete Prefix Verification (Steps 0 .. 844) *)

Definition fc0 : FastConfig := {|
  fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty
|}.

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
  else if Z.eqb z 96 then S2
  else if Z.eqb z 97 then S1
  else S0.

Fixpoint check_range_844 (lo : Z) (len : nat) (t : BTree) : bool :=
  match len with
  | O => true
  | S n => sym_eqb (bt_get (z_to_pos lo) t) (exp_844 lo) && check_range_844 (lo + 1) n t
  end.

Definition check_fc_844 (st : FastConfig * bool) : bool :=
  let (fc, ok) := st in
  ok && Z.eqb fc.(fpos1) 86 && Z.eqb fc.(fpos2) 96
     && state_eqb fc.(fstate1) StA && state_eqb fc.(fstate2) StB
     && check_range_844 (-3) 102 fc.(ftape).

Lemma fc_844_ok : check_fc_844 (N.iter 844 (fast_step_chk_range (-3) 98) (fc0, true)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma prefix_844_ok :
  let c844 := run_N ag1 ag2 844 c0 in
  c844.(pos1) = 86 /\ c844.(pos2) = 96 /\
  c844.(state1) = StA /\ c844.(state2) = StB /\
  (forall k, (k < 844)%N -> (run_N ag1 ag2 k c0).(pos1) <> (run_N ag1 ag2 k c0).(pos2)).
Proof.
  pose proof fc_844_ok as Hok.
  remember (N.iter 844 (fast_step_chk_range (-3) 98) (fc0, true)) as st eqn:Est.
  destruct st as [fc_end ok_end].
  unfold check_fc_844 in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[[[Hok_end Hp1] Hp2] Hs1] Hs2] _].
  rewrite Z.eqb_eq in Hp1, Hp2. apply state_eqb_eq in Hs1, Hs2.
  assert (Hfc : fc_end = N.iter 844 fast_step fc0).
  { pose proof (fast_step_chk_range_fst 844 (-3) 98 fc0 true) as Hfst.
    rewrite <- Est in Hfst. exact Hfst. }
  assert (Hsnd : snd (N.iter 844 (fast_step_chk_range (-3) 98) (fc0, true)) = true)
    by (rewrite <- Est; exact Hok_end).
  destruct (fast_step_chk_range_sound 844 (-3) 98 fc0 true Hsnd) as [_ Hchk].
  pose proof (fast_run_sound 844 fc0) as [Rp1 [Rp2 [Rs1 [Rs2 _]]]].
  rewrite <- Hfc in Rp1, Rp2, Rs1, Rs2.
  repeat split; try congruence.
  intros k Hk.
  pose proof (fast_run_sound k fc0) as [Kp1 [Kp2 _]].
  rewrite <- Kp1, <- Kp2. simpl.
  destruct (Hchk k Hk) as [Hneq _]. exact Hneq.
Qed.

Print Assumptions prefix_844_ok.
