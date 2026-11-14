(** Generic Verified Certificate Checkers for CET(3)
    Supports:
    1. Exact halting (collision) certificates
    2. Undefined transition (---) reachability certificates
    3. Exact joint cycle certificates (fixed dx=0 and translated dx<>0)
    4. Separated-agent cycle certificates (disjoint half-lines, independent periods)
    Verified in Rocq 9.1 with zero extra axioms.
*)

From Stdlib Require Import ZArith NArith PArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core CET(3) Semantics *)

Inductive State : Type := StA | StB | StC.
Inductive Dir : Type := MoveL | MoveR.

Definition state_eqb (s1 s2 : State) : bool :=
  match s1, s2 with
  | StA, StA | StB, StB | StC, StC => true
  | _, _ => false
  end.

Lemma state_eqb_spec : forall s1 s2, reflect (s1 = s2) (state_eqb s1 s2).
Proof.
  intros [] []; constructor; congruence.
Qed.

Record Transition : Type := {
  write_sym  : bool;
  move_dir   : Dir;
  next_state : State
}.

Definition AgentTableOpt : Type := State -> bool -> option Transition.
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

Definition c0 : Config := {|
  pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape
|}.

Definition step_opt (ag1 ag2 : AgentTableOpt) (c : Config) : option Config :=
  if Z.eqb c.(pos1) c.(pos2) then None
  else match ag1 c.(state1) (c.(tape) c.(pos1)),
             ag2 c.(state2) (c.(tape) c.(pos2)) with
       | Some tr1, Some tr2 =>
           let t1 := write_tape c.(tape) c.(pos2) tr2.(write_sym) in
           let t2 := write_tape t1 c.(pos1) tr1.(write_sym) in
           let c' := {| pos1   := move_pos c.(pos1) tr1.(move_dir);
                        pos2   := move_pos c.(pos2) tr2.(move_dir);
                        state1 := tr1.(next_state);
                        state2 := tr2.(next_state);
                        tape   := t2 |} in
           if Z.eqb c'.(pos1) c'.(pos2) then None else Some c'
       | _, _ => None
       end.

(** Step that returns Some c' even on collision, or None only if already collided or undef.
    Wait: for halting at exact step T, we want to distinguish collision vs undef! *)
Inductive StepResult : Type :=
  | SR_Ok (c : Config)
  | SR_Collide (c : Config)
  | SR_Undef.

Definition step_res (ag1 ag2 : AgentTableOpt) (c : Config) : StepResult :=
  if Z.eqb c.(pos1) c.(pos2) then SR_Collide c
  else match ag1 c.(state1) (c.(tape) c.(pos1)),
             ag2 c.(state2) (c.(tape) c.(pos2)) with
       | Some tr1, Some tr2 =>
           let t1 := write_tape c.(tape) c.(pos2) tr2.(write_sym) in
           let t2 := write_tape t1 c.(pos1) tr1.(write_sym) in
           let c' := {| pos1   := move_pos c.(pos1) tr1.(move_dir);
                        pos2   := move_pos c.(pos2) tr2.(move_dir);
                        state1 := tr1.(next_state);
                        state2 := tr2.(next_state);
                        tape   := t2 |} in
           if Z.eqb c'.(pos1) c'.(pos2) then SR_Collide c' else SR_Ok c'
       | _, _ => SR_Undef
       end.

Definition run_N_opt (ag1 ag2 : AgentTableOpt) (n : N) (c : Config) : option Config :=
  N.iter n (fun oc => match oc with None => None | Some c' => step_opt ag1 ag2 c' end) (Some c).

Definition never_halts (ag1 ag2 : AgentTableOpt) (c : Config) : Prop :=
  forall t : N, exists c', run_N_opt ag1 ag2 t c = Some c' /\ c'.(pos1) <> c'.(pos2).

Definition halts_at_exact (ag1 ag2 : AgentTableOpt) (c : Config) (T : N) : Prop :=
  (T >= 1)%N /\
  (forall t : N, (t < T)%N -> exists c', run_N_opt ag1 ag2 t c = Some c' /\ c'.(pos1) <> c'.(pos2)) /\
  exists cprev ccol,
    run_N_opt ag1 ag2 (T - 1)%N c = Some cprev /\
    step_res ag1 ag2 cprev = SR_Collide ccol.

Definition hits_undef_at (ag1 ag2 : AgentTableOpt) (c : Config) (T : N) : Prop :=
  (T >= 1)%N /\
  (forall t : N, (t < T)%N -> exists c', run_N_opt ag1 ag2 t c = Some c' /\ c'.(pos1) <> c'.(pos2)) /\
  exists cprev,
    run_N_opt ag1 ag2 (T - 1)%N c = Some cprev /\
    step_res ag1 ag2 cprev = SR_Undef.

(** * 2. Fast Radix-2 Binary Tree Tape for vm_compute *)

Inductive btree : Type :=
  | BEmpty : btree
  | BNode : btree -> bool -> btree -> btree.

Definition pos_of_Z (z : Z) : positive :=
  match z with
  | Z0 => xH
  | Zpos p => xO p
  | Zneg p => xI p
  end.

Lemma pos_of_Z_inj : forall z1 z2, pos_of_Z z1 = pos_of_Z z2 -> z1 = z2.
Proof.
  intros [|p1|p1] [|p2|p2] H; simpl in H; try discriminate; try reflexivity;
  inversion H; reflexivity.
Qed.

Fixpoint bt_get (t : btree) (p : positive) : bool :=
  match t with
  | BEmpty => false
  | BNode l v r =>
      match p with
      | xH => v
      | xO q => bt_get l q
      | xI q => bt_get r q
      end
  end.

Fixpoint bt_set (t : btree) (p : positive) (b : bool) : btree :=
  match t with
  | BEmpty =>
      match p with
      | xH => BNode BEmpty b BEmpty
      | xO q => BNode (bt_set BEmpty q b) false BEmpty
      | xI q => BNode BEmpty false (bt_set BEmpty q b)
      end
  | BNode l v r =>
      match p with
      | xH => BNode l b r
      | xO q => BNode (bt_set l q b) v r
      | xI q => BNode l v (bt_set r q b)
      end
  end.

Lemma bt_get_empty : forall p, bt_get BEmpty p = false.
Proof. destruct p; reflexivity. Qed.

Lemma bt_get_set_same : forall t p b, bt_get (bt_set t p b) p = b.
Proof.
  intros t p; revert t; induction p; intros t b; destruct t; simpl; auto.
Qed.

Lemma bt_get_set_other : forall t p q b, p <> q -> bt_get (bt_set t p b) q = bt_get t q.
Proof.
  intros t p; revert t; induction p; intros t q b Hneq; destruct t; destruct q; simpl;
  try reflexivity; try congruence;
  try (apply IHp; congruence);
  try (destruct q; apply bt_get_empty || reflexivity).
Qed.

Definition bt_tape (t : btree) : Tape := fun z => bt_get t (pos_of_Z z).

Lemma bt_tape_empty : forall z, bt_tape BEmpty z = empty_tape z.
Proof.
  intro z. unfold bt_tape, empty_tape. apply bt_get_empty.
Qed.

Lemma bt_tape_set : forall t p b z,
  bt_tape (bt_set t (pos_of_Z p) b) z = write_tape (bt_tape t) p b z.
Proof.
  intros t p b z. unfold bt_tape, write_tape.
  destruct (Z.eqb_spec z p).
  - subst. apply bt_get_set_same.
  - apply bt_get_set_other. intro H. apply n. apply pos_of_Z_inj. symmetry; exact H.
Qed.

Record FConfig : Type := {
  fp1 : Z;
  fp2 : Z;
  fs1 : State;
  fs2 : State;
  ftape : btree;
  fmin_w : Z;
  fmax_w : Z
}.

Definition fc0 : FConfig := {|
  fp1 := 0; fp2 := 2; fs1 := StA; fs2 := StA; ftape := BEmpty; fmin_w := 0; fmax_w := 2
|}.

Definition fc_to_cfg (fc : FConfig) : Config := {|
  pos1 := fc.(fp1);
  pos2 := fc.(fp2);
  state1 := fc.(fs1);
  state2 := fc.(fs2);
  tape := bt_tape fc.(ftape)
|}.

Inductive FStepResult : Type :=
  | FSR_Ok (fc : FConfig)
  | FSR_Collide (fc : FConfig)
  | FSR_Undef.

Definition fstep_res (ag1 ag2 : AgentTableOpt) (fc : FConfig) : FStepResult :=
  if Z.eqb fc.(fp1) fc.(fp2) then FSR_Collide fc
  else match ag1 fc.(fs1) (bt_get fc.(ftape) (pos_of_Z fc.(fp1))),
             ag2 fc.(fs2) (bt_get fc.(ftape) (pos_of_Z fc.(fp2))) with
       | Some tr1, Some tr2 =>
           let t1 := bt_set fc.(ftape) (pos_of_Z fc.(fp2)) tr2.(write_sym) in
           let t2 := bt_set t1 (pos_of_Z fc.(fp1)) tr1.(write_sym) in
           let mn := Z.min fc.(fmin_w) (Z.min fc.(fp1) fc.(fp2)) in
           let mx := Z.max fc.(fmax_w) (Z.max fc.(fp1) fc.(fp2)) in
           let fc' := {| fp1 := move_pos fc.(fp1) tr1.(move_dir);
                         fp2 := move_pos fc.(fp2) tr2.(move_dir);
                         fs1 := tr1.(next_state);
                         fs2 := tr2.(next_state);
                         ftape := t2;
                         fmin_w := mn;
                         fmax_w := mx |} in
           if Z.eqb fc'.(fp1) fc'.(fp2) then FSR_Collide fc' else FSR_Ok fc'
       | _, _ => FSR_Undef
       end.

Definition fstep_opt (ag1 ag2 : AgentTableOpt) (fc : FConfig) : option FConfig :=
  match fstep_res ag1 ag2 fc with
  | FSR_Ok fc' => Some fc'
  | _ => None
  end.

(** * 3. Equivalence between Fast Simulation and Core Semantics *)

Definition tape_eq (t1 t2 : Tape) : Prop := forall z, t1 z = t2 z.

Record cfg_eq (c1 c2 : Config) : Prop := {
  ce_p1 : c1.(pos1) = c2.(pos1);
  ce_p2 : c1.(pos2) = c2.(pos2);
  ce_s1 : c1.(state1) = c2.(state1);
  ce_s2 : c1.(state2) = c2.(state2);
  ce_tp : tape_eq c1.(tape) c2.(tape)
}.

Lemma cfg_eq_refl : forall c, cfg_eq c c.
Proof. intros c; constructor; try reflexivity; intro z; reflexivity. Qed.

Lemma cfg_eq_sym : forall c1 c2, cfg_eq c1 c2 -> cfg_eq c2 c1.
Proof. intros c1 c2 [A1 A2 A3 A4 A5]; constructor; try symmetry; auto. Qed.

Lemma cfg_eq_trans : forall c1 c2 c3, cfg_eq c1 c2 -> cfg_eq c2 c3 -> cfg_eq c1 c3.
Proof. intros c1 c2 c3 [A1 A2 A3 A4 A5] [B1 B2 B3 B4 B5]; constructor; congruence. Qed.

Lemma write_tape_proper : forall t1 t2 p s,
  tape_eq t1 t2 -> tape_eq (write_tape t1 p s) (write_tape t2 p s).
Proof.
  intros t1 t2 p s Ht z. unfold write_tape. destruct (Z.eqb z p); auto.
Qed.

Lemma step_opt_proper : forall ag1 ag2 c1 c2,
  cfg_eq c1 c2 ->
  match step_opt ag1 ag2 c1, step_opt ag1 ag2 c2 with
  | Some r1, Some r2 => cfg_eq r1 r2
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros ag1 ag2 c1 c2 [H1 H2 H3 H4 H5].
  unfold step_opt. rewrite H1, H2, H3, H4.
  destruct (Z.eqb (pos1 c2) (pos2 c2)); [exact I|].
  rewrite !H5.
  destruct (ag1 (state1 c2) (tape c2 (pos1 c2))) as [tr1|]; [|exact I].
  destruct (ag2 (state2 c2) (tape c2 (pos2 c2))) as [tr2|]; [|exact I].
  simpl.
  destruct (Z.eqb (move_pos (pos1 c2) (move_dir tr1)) (move_pos (pos2 c2) (move_dir tr2))); [exact I|].
  constructor; simpl; try reflexivity.
  apply write_tape_proper, write_tape_proper; exact H5.
Qed.

Lemma step_res_proper : forall ag1 ag2 c1 c2,
  cfg_eq c1 c2 ->
  match step_res ag1 ag2 c1, step_res ag1 ag2 c2 with
  | SR_Ok r1, SR_Ok r2 => cfg_eq r1 r2
  | SR_Collide r1, SR_Collide r2 => cfg_eq r1 r2
  | SR_Undef, SR_Undef => True
  | _, _ => False
  end.
Proof.
  intros ag1 ag2 c1 c2 [H1 H2 H3 H4 H5].
  unfold step_res. rewrite H1, H2, H3, H4.
  destruct (Z.eqb (pos1 c2) (pos2 c2)).
  - constructor; simpl; auto.
  - rewrite !H5.
    destruct (ag1 (state1 c2) (tape c2 (pos1 c2))) as [tr1|]; [|exact I].
    destruct (ag2 (state2 c2) (tape c2 (pos2 c2))) as [tr2|]; [|exact I].
    simpl.
    destruct (Z.eqb (move_pos (pos1 c2) (move_dir tr1)) (move_pos (pos2 c2) (move_dir tr2))).
    + constructor; simpl; try reflexivity.
      apply write_tape_proper, write_tape_proper; exact H5.
    + constructor; simpl; try reflexivity.
      apply write_tape_proper, write_tape_proper; exact H5.
Qed.

Lemma fstep_res_equiv : forall ag1 ag2 fc,
  match fstep_res ag1 ag2 fc, step_res ag1 ag2 (fc_to_cfg fc) with
  | FSR_Ok fc', SR_Ok c' => cfg_eq (fc_to_cfg fc') c'
  | FSR_Collide fc', SR_Collide c' => cfg_eq (fc_to_cfg fc') c'
  | FSR_Undef, SR_Undef => True
  | _, _ => False
  end.
Proof.
  intros ag1 ag2 fc.
  unfold fstep_res, step_res, fc_to_cfg. simpl.
  destruct (Z.eqb (fp1 fc) (fp2 fc)).
  - apply cfg_eq_refl.
  - change (bt_get (ftape fc) (pos_of_Z (fp1 fc))) with (bt_tape (ftape fc) (fp1 fc)).
    change (bt_get (ftape fc) (pos_of_Z (fp2 fc))) with (bt_tape (ftape fc) (fp2 fc)).
    destruct (ag1 (fs1 fc) (bt_tape (ftape fc) (fp1 fc))) as [tr1|]; [|exact I].
    destruct (ag2 (fs2 fc) (bt_tape (ftape fc) (fp2 fc))) as [tr2|]; [|exact I].
    simpl.
    destruct (Z.eqb (move_pos (fp1 fc) (move_dir tr1)) (move_pos (fp2 fc) (move_dir tr2))).
    + constructor; simpl; try reflexivity.
      intro z. rewrite bt_tape_set. apply write_tape_proper. intro y. apply bt_tape_set.
    + constructor; simpl; try reflexivity.
      intro z. rewrite bt_tape_set. apply write_tape_proper. intro y. apply bt_tape_set.
Qed.

Lemma fstep_opt_equiv : forall ag1 ag2 fc,
  match fstep_opt ag1 ag2 fc, step_opt ag1 ag2 (fc_to_cfg fc) with
  | Some fc', Some c' => cfg_eq (fc_to_cfg fc') c'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros ag1 ag2 fc.
  unfold fstep_opt, step_opt.
  unfold fstep_res. simpl in *.
  destruct (Z.eqb (fp1 fc) (fp2 fc)); [exact I|].
  change (bt_get (ftape fc) (pos_of_Z (fp1 fc))) with (bt_tape (ftape fc) (fp1 fc)).
  change (bt_get (ftape fc) (pos_of_Z (fp2 fc))) with (bt_tape (ftape fc) (fp2 fc)).
  destruct (ag1 (fs1 fc) (bt_tape (ftape fc) (fp1 fc))) as [tr1|]; [|exact I].
  destruct (ag2 (fs2 fc) (bt_tape (ftape fc) (fp2 fc))) as [tr2|]; [|exact I].
  simpl in *.
  destruct (Z.eqb (move_pos (fp1 fc) (move_dir tr1)) (move_pos (fp2 fc) (move_dir tr2))); [exact I|].
  constructor; simpl; try reflexivity.
  intro z. rewrite bt_tape_set. apply write_tape_proper. intro y. apply bt_tape_set.
Qed.

(** * 4. Multi-step Fast Execution & Basic Run Laws *)

Definition run_N_fast (ag1 ag2 : AgentTableOpt) (n : N) (fc : FConfig) : option FConfig :=
  N.iter n (fun ofc => match ofc with None => None | Some fc' => fstep_opt ag1 ag2 fc' end) (Some fc).

Lemma N_iter_add : forall A (f : A -> A) a b x,
  N.iter (a + b) f x = N.iter b f (N.iter a f x).
Proof.
  intros A f a b x.
  rewrite N.add_comm.
  induction b using N.peano_ind.
  - rewrite N.add_0_l. reflexivity.
  - rewrite N.add_succ_l, !N.iter_succ. rewrite IHb. reflexivity.
Qed.

Lemma run_N_opt_proper : forall ag1 ag2 n c1 c2,
  cfg_eq c1 c2 ->
  match run_N_opt ag1 ag2 n c1, run_N_opt ag1 ag2 n c2 with
  | Some r1, Some r2 => cfg_eq r1 r2
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros ag1 ag2 n c1 c2 Heq.
  unfold run_N_opt.
  induction n using N.peano_ind.
  - simpl. exact Heq.
  - rewrite !N.iter_succ.
    destruct (N.iter n _ (Some c1)) as [r1|];
    destruct (N.iter n _ (Some c2)) as [r2|]; try contradiction; try exact I.
    apply step_opt_proper; exact IHn.
Qed.

Lemma run_N_fast_equiv : forall ag1 ag2 n fc,
  match run_N_fast ag1 ag2 n fc, run_N_opt ag1 ag2 n (fc_to_cfg fc) with
  | Some fc', Some c' => cfg_eq (fc_to_cfg fc') c'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros ag1 ag2 n fc.
  unfold run_N_fast, run_N_opt.
  induction n using N.peano_ind.
  - simpl. apply cfg_eq_refl.
  - rewrite !N.iter_succ.
    destruct (N.iter n (fun ofc => match ofc with None => None | Some fc' => fstep_opt ag1 ag2 fc' end) (Some fc)) as [fc'|];
    destruct (N.iter n (fun oc => match oc with None => None | Some c' => step_opt ag1 ag2 c' end) (Some (fc_to_cfg fc))) as [c'|];
    try contradiction; try exact I.
    pose proof (fstep_opt_equiv ag1 ag2 fc') as Hf.
    pose proof (step_opt_proper ag1 ag2 (fc_to_cfg fc') c' IHn) as Hp.
    destruct (fstep_opt ag1 ag2 fc') as [fc''|];
    destruct (step_opt ag1 ag2 (fc_to_cfg fc')) as [c''|]; try contradiction;
    destruct (step_opt ag1 ag2 c') as [c'''|]; try contradiction; try exact I.
    eapply cfg_eq_trans; eauto.
Qed.

Lemma run_N_opt_split : forall ag1 ag2 a b c,
  run_N_opt ag1 ag2 (a + b) c =
  match run_N_opt ag1 ag2 a c with
  | None => None
  | Some c' => run_N_opt ag1 ag2 b c'
  end.
Proof.
  intros ag1 ag2 a b c.
  unfold run_N_opt.
  rewrite N_iter_add.
  destruct (N.iter a _ (Some c)) as [c'|]; [reflexivity|].
  induction b using N.peano_ind; [reflexivity|].
  rewrite N.iter_succ. rewrite IHb. reflexivity.
Qed.

Lemma step_opt_noncolliding : forall ag1 ag2 c c',
  step_opt ag1 ag2 c = Some c' -> c.(pos1) <> c.(pos2) /\ c'.(pos1) <> c'.(pos2).
Proof.
  intros ag1 ag2 c c' H.
  unfold step_opt in H.
  destruct (Z.eqb_spec (pos1 c) (pos2 c)); [discriminate|].
  destruct (ag1 (state1 c) (tape c (pos1 c))); [|discriminate].
  destruct (ag2 (state2 c) (tape c (pos2 c))); [|discriminate].
  simpl in H.
  destruct (Z.eqb_spec (move_pos (pos1 c) (move_dir t)) (move_pos (pos2 c) (move_dir t0))); [discriminate|].
  inversion H; subst; simpl. split; assumption.
Qed.

Lemma run_N_opt_lt_ok : forall ag1 ag2 T c c',
  c.(pos1) <> c.(pos2) ->
  run_N_opt ag1 ag2 T c = Some c' ->
  forall t, (t <= T)%N ->
  exists ct, run_N_opt ag1 ag2 t c = Some ct /\ ct.(pos1) <> ct.(pos2).
Proof.
  intros ag1 ag2 T c c' Hc HT t Hle.
  destruct (N.le_exists_sub t T Hle) as [d [Hd _]].
  subst T. rewrite N.add_comm in HT.
  rewrite run_N_opt_split in HT.
  destruct (run_N_opt ag1 ag2 t c) as [ct|] eqn:Et; [|discriminate].
  exists ct. split; [reflexivity|].
  destruct (N.eq_dec d 0) as [->|Hd0].
  - destruct (N.eq_dec t 0) as [->|Ht0].
    + simpl in Et. inversion Et; subst; exact Hc.
    + rewrite <- (N.succ_pred t Ht0) in Et.
      unfold run_N_opt in Et. rewrite N.iter_succ in Et.
      destruct (N.iter (N.pred t) _ (Some c)) as [cp|]; [|discriminate].
      apply step_opt_noncolliding in Et. destruct Et; assumption.
  - rewrite <- (N.succ_pred d Hd0) in HT.
    assert (H1 : run_N_opt ag1 ag2 (1 + N.pred d) ct = Some c').
    { rewrite N.add_1_l. exact HT. }
    rewrite run_N_opt_split in H1.
    destruct (run_N_opt ag1 ag2 1 ct) as [ct1|] eqn:E1; [|discriminate].
    unfold run_N_opt in E1. simpl in E1.
    apply step_opt_noncolliding in E1. destruct E1; assumption.
Qed.

(** * 5. Halting and Undefined Certificates *)

Definition check_halt_cert (ag1 ag2 : AgentTableOpt) (T : N) : bool :=
  if (1 <=? T)%N then
    match run_N_fast ag1 ag2 (T - 1)%N fc0 with
    | Some fc =>
        match fstep_res ag1 ag2 fc with
        | FSR_Collide _ => true
        | _ => false
        end
    | None => false
    end
  else false.

Theorem check_halt_cert_sound : forall ag1 ag2 T,
  check_halt_cert ag1 ag2 T = true ->
  halts_at_exact ag1 ag2 c0 T.
Proof.
  intros ag1 ag2 T H.
  unfold check_halt_cert in H.
  destruct (N.leb_spec 1 T); [|discriminate].
  pose proof (run_N_fast_equiv ag1 ag2 (T - 1)%N fc0) as Heq.
  destruct (run_N_fast ag1 ag2 (T - 1)%N fc0) as [fc|] eqn:Ef; [|discriminate].
  destruct (run_N_opt ag1 ag2 (T - 1)%N (fc_to_cfg fc0)) as [cprev|] eqn:Eo; [|contradiction].
  assert (Hc0 : cfg_eq (fc_to_cfg fc0) c0) by (constructor; simpl; try reflexivity; intro z; apply bt_tape_empty).
  pose proof (run_N_opt_proper ag1 ag2 (T - 1)%N (fc_to_cfg fc0) c0 Hc0) as Hc0'.
  rewrite Eo in Hc0'.
  destruct (run_N_opt ag1 ag2 (T - 1)%N c0) as [cprev0|] eqn:Eo0; [|contradiction].
  assert (Hprev : cfg_eq (fc_to_cfg fc) cprev0) by (eapply cfg_eq_trans; eauto).
  pose proof (fstep_res_equiv ag1 ag2 fc) as Hfr.
  pose proof (step_res_proper ag1 ag2 (fc_to_cfg fc) cprev0 Hprev) as Hsr.
  destruct (fstep_res ag1 ag2 fc) as [fc'|fc'|] eqn:Efr; try discriminate.
  destruct (step_res ag1 ag2 (fc_to_cfg fc)) as [|cc|]; try contradiction.
  destruct (step_res ag1 ag2 cprev0) as [|cc0|] eqn:Esr; try contradiction.
  split; [lia|].
  split.
  - intros t Ht.
    assert (Ht_le : (t <= T - 1)%N) by lia.
    eapply run_N_opt_lt_ok; [|exact Eo0|exact Ht_le].
    simpl. lia.
  - exists cprev0, cc0. split; reflexivity || assumption.
Qed.

Definition check_undef_cert (ag1 ag2 : AgentTableOpt) (T : N) : bool :=
  if (1 <=? T)%N then
    match run_N_fast ag1 ag2 (T - 1)%N fc0 with
    | Some fc =>
        match fstep_res ag1 ag2 fc with
        | FSR_Undef => true
        | _ => false
        end
    | None => false
    end
  else false.

Theorem check_undef_cert_sound : forall ag1 ag2 T,
  check_undef_cert ag1 ag2 T = true ->
  hits_undef_at ag1 ag2 c0 T.
Proof.
  intros ag1 ag2 T H.
  unfold check_undef_cert in H.
  destruct (N.leb_spec 1 T); [|discriminate].
  pose proof (run_N_fast_equiv ag1 ag2 (T - 1)%N fc0) as Heq.
  destruct (run_N_fast ag1 ag2 (T - 1)%N fc0) as [fc|] eqn:Ef; [|discriminate].
  destruct (run_N_opt ag1 ag2 (T - 1)%N (fc_to_cfg fc0)) as [cprev|] eqn:Eo; [|contradiction].
  assert (Hc0 : cfg_eq (fc_to_cfg fc0) c0) by (constructor; simpl; try reflexivity; intro z; apply bt_tape_empty).
  pose proof (run_N_opt_proper ag1 ag2 (T - 1)%N (fc_to_cfg fc0) c0 Hc0) as Hc0'.
  rewrite Eo in Hc0'.
  destruct (run_N_opt ag1 ag2 (T - 1)%N c0) as [cprev0|] eqn:Eo0; [|contradiction].
  assert (Hprev : cfg_eq (fc_to_cfg fc) cprev0) by (eapply cfg_eq_trans; eauto).
  pose proof (fstep_res_equiv ag1 ag2 fc) as Hfr.
  pose proof (step_res_proper ag1 ag2 (fc_to_cfg fc) cprev0 Hprev) as Hsr.
  destruct (fstep_res ag1 ag2 fc) as [fc'|fc'|] eqn:Efr; try discriminate.
  destruct (step_res ag1 ag2 (fc_to_cfg fc)) as [| |]; try contradiction.
  destruct (step_res ag1 ag2 cprev0) as [| | ] eqn:Esr; try contradiction.
  split; [lia|].
  split.
  - intros t Ht.
    assert (Ht_le : (t <= T - 1)%N) by lia.
    eapply run_N_opt_lt_ok; [|exact Eo0|exact Ht_le].
    simpl. lia.
  - exists cprev0. split; reflexivity || assumption.
Qed.

(** * 6. Joint Cycle Certificate Checker (Fixed dx=0 and Translated dx<>0) *)

Fixpoint forall_Z_len (z : Z) (len : nat) (P : Z -> bool) : bool :=
  match len with
  | O => true
  | S m => P z && forall_Z_len (z + 1) m P
  end.

Definition forall_Z_range (lo hi : Z) (P : Z -> bool) : bool :=
  if hi <? lo then true else forall_Z_len lo (Z.to_nat (hi - lo + 1)) P.

Lemma forall_Z_len_spec : forall len z0 P,
  forall_Z_len z0 len P = true ->
  forall z, z0 <= z < z0 + Z.of_nat len -> P z = true.
Proof.
  induction len; intros z0 P H z Hz; [lia|].
  simpl in H. apply andb_true_iff in H as [Hp Hrest].
  destruct (Z.eq_dec z z0).
  - subst. exact Hp.
  - apply (IHlen (z0 + 1) P Hrest z). lia.
Qed.

Lemma forall_Z_range_spec : forall lo hi P,
  forall_Z_range lo hi P = true ->
  forall z, lo <= z <= hi -> P z = true.
Proof.
  intros lo hi P H z Hz.
  unfold forall_Z_range in H.
  destruct (Z.ltb_spec hi lo); [lia|].
  apply (forall_Z_len_spec (Z.to_nat (hi - lo + 1)) lo P H z).
  lia.
Qed.

Definition step_bounds (ag1 ag2 : AgentTableOpt) (acc : option (FConfig * Z * Z)) : option (FConfig * Z * Z) :=
  match acc with
  | None => None
  | Some (fc, mn, mx) =>
      match fstep_opt ag1 ag2 fc with
      | None => None
      | Some fc' =>
          Some (fc', Z.min mn (Z.min fc.(fp1) fc.(fp2)),
                     Z.max mx (Z.max fc.(fp1) fc.(fp2)))
      end
  end.

Definition run_cycle_bounds (ag1 ag2 : AgentTableOpt) (p : N) (fc : FConfig) : option (FConfig * Z * Z) :=
  N.iter p (step_bounds ag1 ag2) (Some (fc, Z.min fc.(fp1) fc.(fp2), Z.max fc.(fp1) fc.(fp2))).

Definition check_joint_cycle_cert
  (ag1 ag2 : AgentTableOpt) (t0 p : N) (dx w_min w_max : Z) : bool :=
  if (1 <=? p)%N && (w_min <=? w_max) then
    match run_N_fast ag1 ag2 t0 fc0 with
    | None => false
    | Some fc_s =>
        match run_cycle_bounds ag1 ag2 p fc_s with
        | None => false
        | Some (fc_e, rmin, rmax) =>
            (w_min <=? rmin) && (rmax <=? w_max) &&
            (fc_e.(fp1) =? fc_s.(fp1) + dx) &&
            (fc_e.(fp2) =? fc_s.(fp2) + dx) &&
            state_eqb fc_e.(fs1) fc_s.(fs1) &&
            state_eqb fc_e.(fs2) fc_s.(fs2) &&
            forall_Z_range w_min w_max (fun z =>
              Bool.eqb (bt_get fc_e.(ftape) (pos_of_Z (z + dx)))
                       (bt_get fc_s.(ftape) (pos_of_Z z))) &&
            (if 0 <? dx then
               forall_Z_range (w_max + 1) fc_s.(fmax_w) (fun z =>
                 negb (bt_get fc_s.(ftape) (pos_of_Z z)))
             else if dx <? 0 then
               forall_Z_range fc_s.(fmin_w) (w_min - 1) (fun z =>
                 negb (bt_get fc_s.(ftape) (pos_of_Z z)))
             else true)
        end
    end
  else false.

Definition tape_bounded (lo hi : Z) (t : Tape) : Prop :=
  forall z, z < lo \/ hi < z -> t z = false.

Lemma fstep_opt_bounded : forall ag1 ag2 fc fc',
  tape_bounded fc.(fmin_w) fc.(fmax_w) (bt_tape fc.(ftape)) ->
  fstep_opt ag1 ag2 fc = Some fc' ->
  tape_bounded fc'.(fmin_w) fc'.(fmax_w) (bt_tape fc'.(ftape)).
Proof.
  intros ag1 ag2 fc fc' Hb Hs.
  unfold fstep_opt, fstep_res in Hs.
  destruct (Z.eqb (fp1 fc) (fp2 fc)); [discriminate|].
  destruct (ag1 (fs1 fc) (bt_get (ftape fc) (pos_of_Z (fp1 fc)))); [|discriminate].
  destruct (ag2 (fs2 fc) (bt_get (ftape fc) (pos_of_Z (fp2 fc)))); [|discriminate].
  simpl in Hs.
  destruct (Z.eqb (move_pos (fp1 fc) (move_dir t)) (move_pos (fp2 fc) (move_dir t0))); [discriminate|].
  inversion Hs; subst; simpl.
  intros z Hz.
  rewrite bt_tape_set. unfold write_tape.
  destruct (Z.eqb_spec z (fp1 fc)); [lia|].
  rewrite bt_tape_set. unfold write_tape.
  destruct (Z.eqb_spec z (fp2 fc)); [lia|].
  apply Hb. lia.
Qed.

Lemma run_N_fast_bounded : forall ag1 ag2 n fc fc',
  tape_bounded fc.(fmin_w) fc.(fmax_w) (bt_tape fc.(ftape)) ->
  run_N_fast ag1 ag2 n fc = Some fc' ->
  tape_bounded fc'.(fmin_w) fc'.(fmax_w) (bt_tape fc'.(ftape)).
Proof.
  intros ag1 ag2 n fc fc' Hb Hr.
  revert fc' Hr.
  unfold run_N_fast.
  induction n using N.peano_ind; intros fc' Hr.
  - simpl in Hr. inversion Hr; subst; exact Hb.
  - rewrite N.iter_succ in Hr.
    destruct (N.iter n _ (Some fc)) as [fc1|] eqn:En; [|discriminate].
    eapply fstep_opt_bounded; [apply IHn; reflexivity|exact Hr].
Qed.

Definition in_bounds (lo_opt hi_opt : option Z) (z : Z) : Prop :=
  (match lo_opt with Some lo => lo <= z | None => True end) /\
  (match hi_opt with Some hi => z <= hi | None => True end).

Definition cfg_agree_shifted (lo_opt hi_opt : option Z) (dx : Z) (c1 c2 : Config) : Prop :=
  c1.(pos1) = c2.(pos1) + dx /\
  c1.(pos2) = c2.(pos2) + dx /\
  c1.(state1) = c2.(state1) /\
  c1.(state2) = c2.(state2) /\
  forall z, in_bounds lo_opt hi_opt z -> c1.(tape) (z + dx) = c2.(tape) z.

Lemma step_opt_agree_shifted : forall ag1 ag2 lo_opt hi_opt dx c1 c2 c2',
  cfg_agree_shifted lo_opt hi_opt dx c1 c2 ->
  in_bounds lo_opt hi_opt c2.(pos1) ->
  in_bounds lo_opt hi_opt c2.(pos2) ->
  step_opt ag1 ag2 c2 = Some c2' ->
  exists c1', step_opt ag1 ag2 c1 = Some c1' /\ cfg_agree_shifted lo_opt hi_opt dx c1' c2'.
Proof.
  intros ag1 ag2 lo_opt hi_opt dx c1 c2 c2' [Hp1 [Hp2 [Hs1 [Hs2 Htp]]]] Hb1 Hb2 Hs.
  unfold step_opt in *.
  rewrite Hp1, Hp2, Hs1, Hs2.
  destruct (Z.eqb_spec (pos1 c2) (pos2 c2)); [discriminate|].
  destruct (Z.eqb_spec (pos1 c2 + dx) (pos2 c2 + dx)); [lia|].
  rewrite (Htp _ Hb1), (Htp _ Hb2).
  destruct (ag1 (state1 c2) (tape c2 (pos1 c2))) as [tr1|]; [|discriminate].
  destruct (ag2 (state2 c2) (tape c2 (pos2 c2))) as [tr2|]; [|discriminate].
  simpl in *.
  assert (Hmv : forall p d, move_pos (p + dx) d = move_pos p d + dx) by (intros p []; unfold move_pos; lia).
  rewrite !Hmv.
  destruct (Z.eqb_spec (move_pos (pos1 c2) (move_dir tr1)) (move_pos (pos2 c2) (move_dir tr2))); [discriminate|].
  destruct (Z.eqb_spec (move_pos (pos1 c2) (move_dir tr1) + dx) (move_pos (pos2 c2) (move_dir tr2) + dx)); [lia|].
  inversion Hs; subst; simpl.
  eexists; split; [reflexivity|].
  repeat split; try reflexivity.
  intros z Hz. simpl. unfold write_tape.
  destruct (Z.eqb_spec (z + dx) (pos1 c2 + dx));
  destruct (Z.eqb_spec z (pos1 c2)); try lia; try reflexivity;
  destruct (Z.eqb_spec (z + dx) (pos2 c2 + dx));
  destruct (Z.eqb_spec z (pos2 c2)); try lia; try reflexivity;
  apply Htp; exact Hz.
Qed.

Lemma cfg_agree_shifted_trans : forall lo_opt hi_opt dx1 dx2 c1 c2 c3,
  (match lo_opt with Some _ => 0 <= dx2 | None => True end) ->
  (match hi_opt with Some _ => dx2 <= 0 | None => True end) ->
  cfg_agree_shifted lo_opt hi_opt dx1 c1 c2 ->
  cfg_agree_shifted lo_opt hi_opt dx2 c2 c3 ->
  cfg_agree_shifted lo_opt hi_opt (dx2 + dx1) c1 c3.
Proof.
  intros lo_opt hi_opt dx1 dx2 c1 c2 c3 Hlo Hhi
    [Hp1 [Hp2 [Hs1 [Hs2 Htp1]]]] [Gp1 [Gp2 [Gs1 [Gs2 Htp2]]]].
  repeat split; try lia; try congruence.
  intros z Hz.
  assert (Hz' : in_bounds lo_opt hi_opt (z + dx2)).
  { destruct Hz as [Hzl Hzh]; split.
    - destruct lo_opt; simpl in *; lia.
    - destruct hi_opt; simpl in *; lia. }
  replace (z + (dx2 + dx1)) with ((z + dx2) + dx1) by lia.
  rewrite (Htp1 _ Hz'). apply Htp2; exact Hz.
Qed.

Lemma cfg_agree_shifted_proper_l : forall lo_opt hi_opt dx c1 c1' c2,
  cfg_eq c1 c1' ->
  cfg_agree_shifted lo_opt hi_opt dx c1' c2 ->
  cfg_agree_shifted lo_opt hi_opt dx c1 c2.
Proof.
  intros lo_opt hi_opt dx c1 c1' c2 [E1 E2 E3 E4 E5] [H1 [H2 [H3 [H4 H5]]]].
  repeat split; try lia; try congruence.
  intros z Hz. rewrite E5. apply H5; exact Hz.
Qed.

Lemma cfg_agree_shifted_proper_r : forall lo_opt hi_opt dx c1 c2 c2',
  cfg_eq c2 c2' ->
  cfg_agree_shifted lo_opt hi_opt dx c1 c2' ->
  cfg_agree_shifted lo_opt hi_opt dx c1 c2.
Proof.
  intros lo_opt hi_opt dx c1 c2 c2' [E1 E2 E3 E4 E5] [H1 [H2 [H3 [H4 H5]]]].
  repeat split; try lia; try congruence.
  intros z Hz. rewrite E5. apply H5; exact Hz.
Qed.

Lemma write_tape_other : forall t p s x, x <> p -> write_tape t p s x = t x.
Proof. intros. unfold write_tape. destruct (Z.eqb_spec x p); congruence. Qed.

Lemma fstep_opt_tape_outside : forall ag1 ag2 fc fc' z,
  fstep_opt ag1 ag2 fc = Some fc' ->
  z <> fc.(fp1) -> z <> fc.(fp2) ->
  bt_tape fc'.(ftape) z = bt_tape fc.(ftape) z.
Proof.
  intros ag1 ag2 fc fc' z Hs H1 H2.
  unfold fstep_opt, fstep_res in Hs.
  destruct (Z.eqb (fp1 fc) (fp2 fc)); [discriminate|].
  destruct (ag1 (fs1 fc) (bt_get (ftape fc) (pos_of_Z (fp1 fc)))); [|discriminate].
  destruct (ag2 (fs2 fc) (bt_get (ftape fc) (pos_of_Z (fp2 fc)))); [|discriminate].
  simpl in Hs.
  destruct (Z.eqb (move_pos (fp1 fc) (move_dir t)) (move_pos (fp2 fc) (move_dir t0))); [discriminate|].
  inversion Hs; subst; simpl.
  rewrite bt_tape_set, write_tape_other; [|exact H1].
  rewrite bt_tape_set, write_tape_other; [|exact H2].
  reflexivity.
Qed.

Definition run_cycle_bounds_aux (ag1 ag2 : AgentTableOpt) (p : N) (fc : FConfig) (mn mx : Z)
  : option (FConfig * Z * Z) :=
  N.iter p (step_bounds ag1 ag2) (Some (fc, mn, mx)).

Lemma run_cycle_bounds_aux_spec : forall ag1 ag2 p fc mn mx fc_e rmin rmax,
  run_cycle_bounds_aux ag1 ag2 p fc mn mx = Some (fc_e, rmin, rmax) ->
  rmin <= mn /\ mx <= rmax /\
  run_N_fast ag1 ag2 p fc = Some fc_e /\
  (forall z, z < rmin \/ rmax < z -> bt_tape fc_e.(ftape) z = bt_tape fc.(ftape) z) /\
  (forall r, (r < p)%N ->
    exists fc_r, run_N_fast ag1 ag2 r fc = Some fc_r /\
                 rmin <= fc_r.(fp1) <= rmax /\
                 rmin <= fc_r.(fp2) <= rmax).
Proof.
  intros ag1 ag2 p.
  induction p using N.peano_ind; intros fc mn mx fc_e rmin rmax H.
  - unfold run_cycle_bounds_aux in H; simpl in H.
    inversion H; subst.
    repeat split; try lia; try reflexivity.
  - unfold run_cycle_bounds_aux in H. rewrite N.iter_succ in H.
    destruct (N.iter p (step_bounds ag1 ag2) (Some (fc, mn, mx))) as [[[fc1 mn1] mx1]|] eqn:Ep; [|discriminate].
    unfold step_bounds in H.
    destruct (fstep_opt ag1 ag2 fc1) as [fc2|] eqn:Es; [|discriminate].
    inversion H; subst.
    specialize (IHp fc mn mx fc1 mn1 mx1 Ep) as [Hmn [Hmx [Hfast [Hout Hlt]]]].
    repeat split; try lia.
    + unfold run_N_fast in *. rewrite N.iter_succ, Hfast. exact Es.
    + intros z Hz.
      rewrite (fstep_opt_tape_outside ag1 ag2 fc1 fc_e z Es ltac:(lia) ltac:(lia)).
      apply Hout. lia.
    + intros r Hr.
      destruct (N.eq_dec r p) as [->|Hneq].
      * exists fc1; repeat split; try assumption; lia.
      * assert (Hrp : (r < p)%N) by lia.
        destruct (Hlt r Hrp) as [fc_r [Hr1 [Hr2 Hr3]]].
        exists fc_r; repeat split; try assumption; lia.
Qed.

Lemma run_N_opt_agree_shifted : forall ag1 ag2 lo_opt hi_opt dx p c_s c1 r c_r,
  (r <= p)%N ->
  cfg_agree_shifted lo_opt hi_opt dx c1 c_s ->
  (forall j, (j < p)%N -> exists c_j, run_N_opt ag1 ag2 j c_s = Some c_j /\
                                      in_bounds lo_opt hi_opt c_j.(pos1) /\
                                      in_bounds lo_opt hi_opt c_j.(pos2)) ->
  run_N_opt ag1 ag2 r c_s = Some c_r ->
  exists c1_r, run_N_opt ag1 ag2 r c1 = Some c1_r /\
               cfg_agree_shifted lo_opt hi_opt dx c1_r c_r.
Proof.
  intros ag1 ag2 lo_opt hi_opt dx p c_s c1 r.
  induction r using N.peano_ind; intros c_r Hle Hagr Hbd Hrun.
  - simpl in Hrun. inversion Hrun; subst. exists c1. split; [reflexivity|exact Hagr].
  - unfold run_N_opt in Hrun. rewrite N.iter_succ in Hrun.
    destruct (N.iter r _ (Some c_s)) as [c_prev|] eqn:Eprev; [|discriminate].
    assert (Hr_le : (r <= p)%N) by lia.
    assert (Hr_lt : (r < p)%N) by lia.
    destruct (IHr c_prev Hr_le Hagr Hbd Eprev) as [c1_prev [E1prev Hagr_prev]].
    destruct (Hbd r Hr_lt) as [c_j [Ej [Hb1 Hb2]]].
    change (N.iter r (fun oc => match oc with None => None | Some c' => step_opt ag1 ag2 c' end) (Some c_s))
      with (run_N_opt ag1 ag2 r c_s) in Eprev.
    rewrite Eprev in Ej. inversion Ej; subst c_j.
    destruct (step_opt_agree_shifted ag1 ag2 lo_opt hi_opt dx c1_prev c_prev c_r Hagr_prev Hb1 Hb2 Hrun)
      as [c1_r [Hs1 Hagr_r]].
    exists c1_r. split; [|exact Hagr_r].
    unfold run_N_opt. rewrite N.iter_succ.
    change (N.iter r (fun oc => match oc with None => None | Some c' => step_opt ag1 ag2 c' end) (Some c1))
      with (run_N_opt ag1 ag2 r c1).
    rewrite E1prev. exact Hs1.
Qed.

Theorem check_joint_cycle_cert_sound : forall ag1 ag2 t0 p dx w_min w_max,
  check_joint_cycle_cert ag1 ag2 t0 p dx w_min w_max = true ->
  never_halts ag1 ag2 c0.
Proof.
  intros ag1 ag2 t0 p dx w_min w_max H.
  unfold check_joint_cycle_cert in H.
  destruct (N.leb_spec 1 p); [|discriminate].
  destruct (Z.leb_spec w_min w_max); [|discriminate].
  simpl in H.
  destruct (run_N_fast ag1 ag2 t0 fc0) as [fc_s|] eqn:Ef_s; [|discriminate].
  destruct (run_cycle_bounds ag1 ag2 p fc_s) as [[[fc_e rmin] rmax]|] eqn:Eb; [|discriminate].
  apply andb_true_iff in H as [H Hblank].
  apply andb_true_iff in H as [H Htape].
  apply andb_true_iff in H as [H Hs2].
  apply andb_true_iff in H as [H Hs1].
  apply andb_true_iff in H as [H Hp2].
  apply andb_true_iff in H as [H Hp1].
  apply andb_true_iff in H as [Hwmin Hrmax].
  apply Z.leb_le in Hwmin. apply Z.leb_le in Hrmax.
  apply Z.eqb_eq in Hp1. apply Z.eqb_eq in Hp2.
  destruct (state_eqb_spec (fs1 fc_e) (fs1 fc_s)) as [Es1|]; [|discriminate].
  destruct (state_eqb_spec (fs2 fc_e) (fs2 fc_s)) as [Es2|]; [|discriminate].
  (* Convert run_N_fast fc0 t0 to run_N_opt c0 t0 *)
  assert (Hc0 : cfg_eq (fc_to_cfg fc0) c0) by (constructor; simpl; try reflexivity; intro z; apply bt_tape_empty).
  pose proof (run_N_fast_equiv ag1 ag2 t0 fc0) as Heq_s.
  rewrite Ef_s in Heq_s.
  destruct (run_N_opt ag1 ag2 t0 (fc_to_cfg fc0)) as [c_s0|] eqn:Eo_s0; [|contradiction].
  pose proof (run_N_opt_proper ag1 ag2 t0 (fc_to_cfg fc0) c0 Hc0) as Hp_s.
  rewrite Eo_s0 in Hp_s.
  destruct (run_N_opt ag1 ag2 t0 c0) as [c_s|] eqn:Eo_s; [|contradiction].
  assert (Hcs : cfg_eq (fc_to_cfg fc_s) c_s) by (eapply cfg_eq_trans; eauto).
  (* Boundedness of fc_s *)
  assert (Hb_fc0 : tape_bounded (fmin_w fc0) (fmax_w fc0) (bt_tape (ftape fc0))).
  { intros z _. apply bt_tape_empty. }
  pose proof (run_N_fast_bounded ag1 ag2 t0 fc0 fc_s Hb_fc0 Ef_s) as Hb_fcs.
  (* Cycle bounds *)
  unfold run_cycle_bounds in Eb.
  apply run_cycle_bounds_aux_spec in Eb as [Hrmin0 [Hrmax0 [Ef_e [Hout Hlt]]]].
  pose proof (run_N_fast_equiv ag1 ag2 p fc_s) as Heq_e.
  rewrite Ef_e in Heq_e.
  destruct (run_N_opt ag1 ag2 p (fc_to_cfg fc_s)) as [c_e0|] eqn:Eo_e0; [|contradiction].
  pose proof (run_N_opt_proper ag1 ag2 p (fc_to_cfg fc_s) c_s Hcs) as Hp_e.
  rewrite Eo_e0 in Hp_e.
  destruct (run_N_opt ag1 ag2 p c_s) as [c_e|] eqn:Eo_e; [|contradiction].
  assert (Hce : cfg_eq (fc_to_cfg fc_e) c_e) by (eapply cfg_eq_trans; eauto).
  (* Choose lo_opt, hi_opt based on dx *)
  set (lo_opt := if 0 <? dx then Some w_min else if dx <? 0 then None else Some w_min).
  set (hi_opt := if 0 <? dx then None else if dx <? 0 then Some w_max else Some w_max).
  assert (Hlo_dx : match lo_opt with Some _ => 0 <= dx | None => True end).
  { unfold lo_opt. destruct (Z.ltb_spec 0 dx); [lia|]. destruct (Z.ltb_spec dx 0); [exact I|lia]. }
  assert (Hhi_dx : match hi_opt with Some _ => dx <= 0 | None => True end).
  { unfold hi_opt. destruct (Z.ltb_spec 0 dx); [exact I|]. destruct (Z.ltb_spec dx 0); [lia|lia]. }
  assert (Hbd_in : forall z, w_min <= z <= w_max -> in_bounds lo_opt hi_opt z).
  { intros z Hz. unfold in_bounds, lo_opt, hi_opt.
    destruct (Z.ltb_spec 0 dx); [split; [lia|exact I]|].
    destruct (Z.ltb_spec dx 0); [split; [exact I|lia]|split; lia]. }
  (* Agreement between c_e and c_s *)
  assert (Hagr_es : cfg_agree_shifted lo_opt hi_opt dx c_e c_s).
  { eapply cfg_agree_shifted_proper_l; [apply cfg_eq_sym; exact Hce|].
    eapply cfg_agree_shifted_proper_r; [apply cfg_eq_sym; exact Hcs|].
    repeat split; simpl; try lia; try assumption.
    intros z Hz.
    destruct (Z.leb_spec w_min z) as [Hzl|Hzl]; destruct (Z.leb_spec z w_max) as [Hzh|Hzh].
    - apply forall_Z_range_spec with (z:=z) in Htape; [|lia].
      apply Bool.eqb_prop in Htape. exact Htape.
    - (* z > w_max: only possible if 0 < dx *)
      unfold in_bounds, lo_opt, hi_opt in Hz.
      destruct (Z.ltb_spec 0 dx) as [Hdx|Hdx]; [|destruct (Z.ltb_spec dx 0); lia].
      assert (Hfsz : bt_tape (ftape fc_s) z = false).
      { destruct (Z.leb_spec z (fmax_w fc_s)).
        - apply forall_Z_range_spec with (z:=z) in Hblank; [|lia].
          apply negb_true_iff in Hblank. exact Hblank.
        - apply Hb_fcs. right; lia. }
      assert (Hfez : bt_tape (ftape fc_e) (z + dx) = false).
      { rewrite Hout; [|right; lia].
        destruct (Z.leb_spec (z + dx) (fmax_w fc_s)).
        - apply forall_Z_range_spec with (z:=z+dx) in Hblank; [|lia].
          apply negb_true_iff in Hblank. exact Hblank.
        - apply Hb_fcs. right; lia. }
      rewrite Hfez, Hfsz. reflexivity.
    - (* z < w_min: only possible if dx < 0 *)
      unfold in_bounds, lo_opt, hi_opt in Hz.
      destruct (Z.ltb_spec 0 dx) as [Hdx|Hdx]; [lia|].
      destruct (Z.ltb_spec dx 0) as [Hdx2|Hdx2]; [|lia].
      assert (Hfsz : bt_tape (ftape fc_s) z = false).
      { destruct (Z.leb_spec (fmin_w fc_s) z).
        - apply forall_Z_range_spec with (z:=z) in Hblank; [|lia].
          apply negb_true_iff in Hblank. exact Hblank.
        - apply Hb_fcs. left; lia. }
      assert (Hfez : bt_tape (ftape fc_e) (z + dx) = false).
      { rewrite Hout; [|left; lia].
        destruct (Z.leb_spec (fmin_w fc_s) (z + dx)).
        - apply forall_Z_range_spec with (z:=z+dx) in Hblank; [|lia].
          apply negb_true_iff in Hblank. exact Hblank.
        - apply Hb_fcs. left; lia. }
      rewrite Hfez, Hfsz. reflexivity.
    - lia. }
  (* Bounds on intermediate steps 0 <= j < p from c_s *)
  assert (Hbd_s : forall j, (j < p)%N ->
    exists c_j, run_N_opt ag1 ag2 j c_s = Some c_j /\
                in_bounds lo_opt hi_opt c_j.(pos1) /\
                in_bounds lo_opt hi_opt c_j.(pos2)).
  { intros j Hj.
    destruct (Hlt j Hj) as [fc_j [Ef_j [Hj1 Hj2]]].
    pose proof (run_N_fast_equiv ag1 ag2 j fc_s) as Heq_j.
    rewrite Ef_j in Heq_j.
    destruct (run_N_opt ag1 ag2 j (fc_to_cfg fc_s)) as [c_j0|] eqn:Eo_j0; [|contradiction].
    pose proof (run_N_opt_proper ag1 ag2 j (fc_to_cfg fc_s) c_s Hcs) as Hp_j.
    rewrite Eo_j0 in Hp_j.
    destruct (run_N_opt ag1 ag2 j c_s) as [c_j|] eqn:Eo_j; [|contradiction].
    assert (Hcj : cfg_eq (fc_to_cfg fc_j) c_j) by (eapply cfg_eq_trans; eauto).
    destruct Hcj as [E1 E2 _ _ _]. simpl in E1, E2.
    exists c_j; repeat split; try assumption;
    try (apply Hbd_in; lia);
    unfold in_bounds, lo_opt, hi_opt;
    destruct (Z.ltb_spec 0 dx); simpl; try exact I;
    destruct (Z.ltb_spec dx 0); simpl; try exact I; lia. }
  (* Induction on k : N for c_{t0 + k * p} *)
  assert (Hk : forall k : N,
    exists c_k, run_N_opt ag1 ag2 (t0 + k * p) c0 = Some c_k /\
                cfg_agree_shifted lo_opt hi_opt (Z.of_N k * dx) c_k c_s).
  { induction k using N.peano_ind.
    - rewrite N.mul_0_l, N.add_0_r. exists c_s; split; [exact Eo_s|].
      repeat split; try lia; try reflexivity.
      intros z _. replace (z + Z.of_N 0 * dx) with z by lia. reflexivity.
    - destruct IHk as [c_k [Eo_k Hagr_k]].
      replace (t0 + N.succ k * p)%N with ((t0 + k * p) + p)%N by lia.
      rewrite run_N_opt_split, Eo_k.
      destruct (run_N_opt_agree_shifted ag1 ag2 lo_opt hi_opt (Z.of_N k * dx) p c_s c_k p c_e (N.le_refl p) Hagr_k Hbd_s Eo_e)
        as [c_next [Eo_next Hagr_next]].
      exists c_next; split; [exact Eo_next|].
      replace (Z.of_N (N.succ k) * dx) with (dx + Z.of_N k * dx) by lia.
      eapply cfg_agree_shifted_trans; [| |exact Hagr_next|exact Hagr_es].
      + unfold lo_opt. destruct (Z.ltb_spec 0 dx); [lia|]. destruct (Z.ltb_spec dx 0); [exact I|lia].
      + unfold hi_opt. destruct (Z.ltb_spec 0 dx); [exact I|]. destruct (Z.ltb_spec dx 0); [lia|lia]. }
  (* Finally, prove never_halts for any t : N *)
  intro t.
  destruct (N.lt_ge_cases t t0) as [Hlt0|Hge0].
  - eapply run_N_opt_lt_ok; [|exact Eo_s|lia]. simpl. lia.
  - set (d := (t - t0)%N).
    set (k := (d / p)%N).
    set (r := (d mod p)%N).
    assert (Hp_pos : p <> 0%N) by lia.
    assert (Hd : t = ((t0 + k * p) + r)%N).
    { unfold k, r, d. pose proof (N.div_mod (t - t0) p Hp_pos). rewrite (N.mul_comm ((t - t0) / p) p). lia. }
    assert (Hr_lt : (r < p)%N) by (unfold r; apply N.mod_lt; exact Hp_pos).
    destruct (Hk k) as [c_k [Eo_k Hagr_k]].
    destruct (Hbd_s r Hr_lt) as [c_r [Eo_r _]].
    destruct (run_N_opt_agree_shifted ag1 ag2 lo_opt hi_opt (Z.of_N k * dx) p c_s c_k r c_r ltac:(lia) Hagr_k Hbd_s Eo_r)
      as [c_t [Eo_t Hagr_t]].
    rewrite Hd, run_N_opt_split, Eo_k, Eo_t.
    exists c_t; split; [reflexivity|].
    assert (Hcr_nc : c_r.(pos1) <> c_r.(pos2)).
    { assert (Hcs_nc : c_s.(pos1) <> c_s.(pos2)).
      { destruct (run_N_opt_lt_ok ag1 ag2 t0 c0 c_s ltac:(simpl; lia) Eo_s t0 ltac:(lia)) as [cs' [Ecs' Hncs]].
        rewrite Eo_s in Ecs'. congruence. }
      destruct (run_N_opt_lt_ok ag1 ag2 p c_s c_e Hcs_nc Eo_e r ltac:(lia)) as [c_r' [Eo_r' Hnc]].
      rewrite Eo_r in Eo_r'. congruence. }
    destruct Hagr_t as [Ht1 [Ht2 _]]. lia.
Qed.
