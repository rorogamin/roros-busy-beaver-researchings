(** Formal Proof of Non-Halting for the CET(3) Machine:
      Agent 1: 0LB---_1LC1RB_0RB0LC
      Agent 2: 1RB0RB_1LB1RC_1RA1LC

    Target theorem (`target_never_halts`):
      From initial blank tape with pos1 = 0 (StA), pos2 = 2 (StA),
      under partial CET semantics (`step_opt` returning `None` on undefined `---`
      transitions or head collisions `pos1 = pos2` before or after a step),
      `forall t : N, exists c, run_N_opt t c0 = Some c /\ c.(pos1) <> c.(pos2)`.
*)

From Stdlib Require Import ZArith NArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Core CET Semantics (Partial `---` + Collision) *)

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

(** Target Agent 1 (partial): 0LB---_1LC1RB_0RB0LC *)
Definition ag1_opt (s : State) (b : bool) : option Transition :=
  match s, b with
  | StA, false => Some {| write_sym := false; move_dir := MoveL; next_state := StB |}
  | StA, true  => None
  | StB, false => Some {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  | StB, true  => Some {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StC, false => Some {| write_sym := false; move_dir := MoveR; next_state := StB |}
  | StC, true  => Some {| write_sym := false; move_dir := MoveL; next_state := StC |}
  end.

(** Target Agent 2 (total, wrapped in option): 1RB0RB_1LB1RC_1RA1LC *)
Definition ag2_opt (s : State) (b : bool) : option Transition :=
  match s, b with
  | StA, false => Some {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StA, true  => Some {| write_sym := false; move_dir := MoveR; next_state := StB |}
  | StB, false => Some {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StB, true  => Some {| write_sym := true;  move_dir := MoveR; next_state := StC |}
  | StC, false => Some {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  | StC, true  => Some {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  end.

(** Totalized tables (identical to partial tables on all active inputs). *)
Definition ag1 (s : State) (b : bool) : Transition :=
  match ag1_opt s b with
  | Some tr => tr
  | None    => {| write_sym := false; move_dir := MoveL; next_state := StB |}
  end.

Definition ag2 (s : State) (b : bool) : Transition :=
  match ag2_opt s b with
  | Some tr => tr
  | None    => {| write_sym := false; move_dir := MoveR; next_state := StA |}
  end.

Definition c0 : Config := {|
  pos1 := 0; pos2 := 2; state1 := StA; state2 := StA; tape := empty_tape
|}.

(** Partial CET step: halts (`None`) on collision before or after step, or undefined `---`. *)
Definition step_opt (c : Config) : option Config :=
  if Z.eqb c.(pos1) c.(pos2) then None
  else match ag1_opt c.(state1) (c.(tape) c.(pos1)),
             ag2_opt c.(state2) (c.(tape) c.(pos2)) with
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

Definition run_N_opt (n : N) (c : Config) : option Config :=
  N.iter n (fun oc => match oc with None => None | Some c' => step_opt c' end) (Some c).

(** Total CET step for clean algebraic manipulation. *)
Definition step (c : Config) : Config :=
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

Definition run_N (n : N) (c : Config) : Config :=
  N.iter n step c.

(** * 2. Configuration Equivalence, Shifting, and Disjoint Composition *)

Definition tape_eq (t1 t2 : Tape) : Prop := forall z, t1 z = t2 z.

Record cfg_eq (c1 c2 : Config) : Prop := {
  ce_p1 : c1.(pos1) = c2.(pos1);
  ce_p2 : c1.(pos2) = c2.(pos2);
  ce_s1 : c1.(state1) = c2.(state1);
  ce_s2 : c1.(state2) = c2.(state2);
  ce_tp : tape_eq c1.(tape) c2.(tape)
}.

Lemma cfg_eq_refl : forall c, cfg_eq c c.
Proof. intro c. constructor; reflexivity. Qed.

Lemma cfg_eq_sym : forall c1 c2, cfg_eq c1 c2 -> cfg_eq c2 c1.
Proof.
  intros c1 c2 [H1 H2 H3 H4 H5]. constructor; try congruence.
Qed.

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

Lemma step_proper : forall c1 c2, cfg_eq c1 c2 -> cfg_eq (step c1) (step c2).
Proof.
  intros c1 c2 [Hp1 Hp2 Hs1 Hs2 Htp].
  unfold step. rewrite Hp1, Hp2, Hs1, Hs2, (Htp c2.(pos1)), (Htp c2.(pos2)).
  constructor; simpl; auto.
  apply write_tape_proper, write_tape_proper. exact Htp.
Qed.

Lemma run_N_proper : forall n c1 c2, cfg_eq c1 c2 -> cfg_eq (run_N n c1) (run_N n c2).
Proof.
  intro n. induction n using N.peano_ind; intros c1 c2 H.
  - exact H.
  - unfold run_N in *. rewrite !N.iter_succ. apply step_proper, IHn; exact H.
Qed.

Lemma run_N_0 : forall c, run_N 0%N c = c.
Proof. reflexivity. Qed.

Lemma run_N_succ : forall n c, run_N (N.succ n) c = step (run_N n c).
Proof. intros. unfold run_N. apply N.iter_succ. Qed.

Lemma run_N_add : forall p q c, run_N (p + q) c = run_N p (run_N q c).
Proof. intros. unfold run_N. apply N.iter_add. Qed.

Lemma step_opt_proper : forall c1 c2,
  cfg_eq c1 c2 ->
  match step_opt c1, step_opt c2 with
  | None, None => True
  | Some d1, Some d2 => cfg_eq d1 d2
  | _, _ => False
  end.
Proof.
  intros c1 c2 [Hp1 Hp2 Hs1 Hs2 Htp].
  unfold step_opt. rewrite Hp1, Hp2, Hs1, Hs2, (Htp c2.(pos1)), (Htp c2.(pos2)).
  destruct (Z.eqb (pos1 c2) (pos2 c2)); auto.
  destruct (ag1_opt (state1 c2) (tape c2 (pos1 c2))) as [tr1|]; auto.
  destruct (ag2_opt (state2 c2) (tape c2 (pos2 c2))) as [tr2|]; auto.
  simpl. destruct (Z.eqb (move_pos (pos1 c2) (move_dir tr1)) (move_pos (pos2 c2) (move_dir tr2))); auto.
  constructor; simpl; auto. apply write_tape_proper, write_tape_proper. exact Htp.
Qed.

Lemma step_opt_matches_step : forall c,
  c.(pos1) <> c.(pos2) ->
  (step c).(pos1) <> (step c).(pos2) ->
  (c.(state1) = StB \/ c.(state1) = StC \/ (c.(state1) = StA /\ c.(tape) c.(pos1) = false)) ->
  exists c', step_opt c = Some c' /\ cfg_eq c' (step c).
Proof.
  intros c Hpre Hpost Hs1.
  unfold step_opt, step.
  destruct (Z.eqb_spec (pos1 c) (pos2 c)); [congruence|].
  assert (Hag1 : exists tr1, ag1_opt (state1 c) (tape c (pos1 c)) = Some tr1).
  { destruct Hs1 as [-> | [-> | [-> ->]]]; destruct (tape c (pos1 c)); eexists; reflexivity. }
  assert (Hag2 : exists tr2, ag2_opt (state2 c) (tape c (pos2 c)) = Some tr2).
  { destruct (state2 c), (tape c (pos2 c)); eexists; reflexivity. }
  destruct Hag1 as [tr1 H1], Hag2 as [tr2 H2].
  rewrite H1, H2.
  unfold step, ag1, ag2 in Hpost. rewrite H1, H2 in Hpost. simpl in *.
  destruct (Z.eqb_spec (move_pos (pos1 c) (move_dir tr1)) (move_pos (pos2 c) (move_dir tr2)));
    [congruence|].
  eexists. split; [reflexivity|]. unfold ag1, ag2. rewrite H1, H2. apply cfg_eq_refl.
Qed.

Theorem run_N_opt_from_total :
  (forall t : N, (run_N t c0).(pos1) <> (run_N t c0).(pos2)) ->
  (forall t : N, (1 <= t)%N -> (run_N t c0).(state1) = StB \/ (run_N t c0).(state1) = StC) ->
  forall t : N, exists c, run_N_opt t c0 = Some c /\ cfg_eq c (run_N t c0).
Proof.
  intros Hcol Hst t. induction t using N.peano_ind.
  - exists c0. split; [reflexivity | apply cfg_eq_refl].
  - destruct IHt as [c [Hopt Heq]].
    unfold run_N_opt in *. rewrite !N.iter_succ, Hopt.
    assert (Hs1 : (run_N t c0).(state1) = StB \/ (run_N t c0).(state1) = StC \/
                  ((run_N t c0).(state1) = StA /\ (run_N t c0).(tape) (run_N t c0).(pos1) = false)).
    { destruct (N.eq_0_gt_0_cases t) as [-> | Hgt].
      - right. right. split; reflexivity.
      - destruct (Hst t ltac:(lia)); auto. }
    assert (Hstep_ok : exists d, step_opt (run_N t c0) = Some d /\ cfg_eq d (step (run_N t c0))).
    { apply step_opt_matches_step; auto.
      rewrite <- run_N_succ. apply Hcol. }
    destruct Hstep_ok as [d [Hd Hdeq]].
    pose proof (step_opt_proper c (run_N t c0) Heq) as Hprop.
    rewrite Hd in Hprop.
    destruct (step_opt c) as [d'|]; [|contradiction].
    exists d'. rewrite run_N_succ. split; [reflexivity|].
    eapply cfg_eq_trans; eauto.
Qed.

(** Spatial translation *)
Definition shift_cfg (delta : Z) (c : Config) : Config := {|
  pos1   := c.(pos1) + delta;
  pos2   := c.(pos2) + delta;
  state1 := c.(state1);
  state2 := c.(state2);
  tape   := fun z => c.(tape) (z - delta)
|}.

Lemma shift_step : forall delta c,
  cfg_eq (step (shift_cfg delta c)) (shift_cfg delta (step c)).
Proof.
  intros delta c. unfold step, shift_cfg; simpl.
  replace (pos1 c + delta - delta) with (pos1 c) by lia.
  replace (pos2 c + delta - delta) with (pos2 c) by lia.
  constructor; simpl;
    [ unfold move_pos; destruct (move_dir (ag1 (state1 c) (tape c (pos1 c)))); lia
    | unfold move_pos; destruct (move_dir (ag2 (state2 c) (tape c (pos2 c)))); lia
    | reflexivity | reflexivity | ].
  intro z. unfold write_tape.
  destruct (Z.eqb_spec z (pos1 c + delta)) as [H1|H1];
  destruct (Z.eqb_spec (z - delta) (pos1 c)) as [H1'|H1']; try lia; auto.
  destruct (Z.eqb_spec z (pos2 c + delta)) as [H2|H2];
  destruct (Z.eqb_spec (z - delta) (pos2 c)) as [H2'|H2']; try lia; auto.
Qed.

Lemma shift_run : forall n delta c,
  cfg_eq (run_N n (shift_cfg delta c)) (shift_cfg delta (run_N n c)).
Proof.
  intro n. induction n using N.peano_ind; intros delta c.
  - apply cfg_eq_refl.
  - rewrite !run_N_succ.
    eapply cfg_eq_trans; [apply step_proper, IHn | apply shift_step].
Qed.

(** Solo agent execution *)
Record SoloConfig : Type := {
  spos   : Z;
  sstate : State;
  stape  : Tape
}.

Definition step_solo (tbl : AgentTable) (sc : SoloConfig) : SoloConfig :=
  let tr := tbl sc.(sstate) (sc.(stape) sc.(spos)) in
  {| spos   := move_pos sc.(spos) tr.(move_dir);
     sstate := tr.(next_state);
     stape  := write_tape sc.(stape) sc.(spos) tr.(write_sym) |}.

Definition run_solo (tbl : AgentTable) (n : N) (sc : SoloConfig) : SoloConfig :=
  N.iter n (step_solo tbl) sc.

Definition scfg_eq (a b : SoloConfig) : Prop :=
  a.(spos) = b.(spos) /\ a.(sstate) = b.(sstate) /\ tape_eq a.(stape) b.(stape).

Lemma step_solo_proper : forall tbl a b, scfg_eq a b -> scfg_eq (step_solo tbl a) (step_solo tbl b).
Proof.
  intros tbl a b [Hp [Hs Htp]]. unfold step_solo.
  rewrite Hp, Hs, (Htp (spos b)).
  repeat split; simpl; auto. apply write_tape_proper; auto.
Qed.

Lemma run_solo_proper : forall tbl n a b,
  scfg_eq a b -> scfg_eq (run_solo tbl n a) (run_solo tbl n b).
Proof.
  intros tbl n. induction n using N.peano_ind; intros a b H; auto.
  unfold run_solo in *. rewrite !N.iter_succ. apply step_solo_proper, IHn; auto.
Qed.

Lemma run_solo_0 : forall tbl sc, run_solo tbl 0%N sc = sc.
Proof. reflexivity. Qed.

Lemma run_solo_succ : forall tbl n sc,
  run_solo tbl (N.succ n) sc = step_solo tbl (run_solo tbl n sc).
Proof. intros. unfold run_solo. apply N.iter_succ. Qed.

Lemma run_solo_add : forall tbl p q sc,
  run_solo tbl (p + q) sc = run_solo tbl p (run_solo tbl q sc).
Proof. intros. unfold run_solo. apply N.iter_add. Qed.

Definition shift_scfg (delta : Z) (sc : SoloConfig) : SoloConfig := {|
  spos   := sc.(spos) + delta;
  sstate := sc.(sstate);
  stape  := fun z => sc.(stape) (z - delta)
|}.

Lemma shift_step_solo : forall tbl delta sc,
  scfg_eq (step_solo tbl (shift_scfg delta sc)) (shift_scfg delta (step_solo tbl sc)).
Proof.
  intros tbl delta sc. unfold step_solo, shift_scfg; simpl.
  replace (spos sc + delta - delta) with (spos sc) by lia.
  unfold scfg_eq. split; [|split]; simpl.
  - unfold move_pos. destruct (move_dir (tbl (sstate sc) (stape sc (spos sc)))); lia.
  - reflexivity.
  - intro z. unfold write_tape.
    destruct (Z.eqb_spec z (spos sc + delta));
    destruct (Z.eqb_spec (z - delta) (spos sc)); try lia; auto.
Qed.

Lemma shift_run_solo : forall tbl n delta sc,
  scfg_eq (run_solo tbl n (shift_scfg delta sc)) (shift_scfg delta (run_solo tbl n sc)).
Proof.
  intros tbl n. induction n using N.peano_ind; intros delta sc.
  - repeat split; auto; try reflexivity.
  - unfold run_solo in *. rewrite !N.iter_succ.
    pose proof (step_solo_proper tbl _ _ (IHn delta sc)) as [A [B C]].
    pose proof (shift_step_solo tbl delta (N.iter n (step_solo tbl) sc)) as [D [E F]].
    repeat split; try congruence.
Qed.

Lemma solo_preserves_outside : forall tbl n lo hi sc,
  (forall t, (t < n)%N -> lo <= (run_solo tbl t sc).(spos) < hi) ->
  forall z, z < lo \/ hi <= z -> (run_solo tbl n sc).(stape) z = sc.(stape) z.
Proof.
  intros tbl n. induction n using N.peano_ind; intros lo hi sc Hbnd z Hz; auto.
  rewrite run_solo_succ. unfold step_solo; simpl.
  rewrite write_tape_other.
  - apply (IHn lo hi); auto. intros t Ht. apply Hbnd. lia.
  - pose proof (Hbnd n ltac:(lia)). lia.
Qed.

Lemma solo_preserves_below : forall tbl n lo sc,
  (forall t, (t < n)%N -> lo <= (run_solo tbl t sc).(spos)) ->
  forall z, z < lo -> (run_solo tbl n sc).(stape) z = sc.(stape) z.
Proof.
  intros tbl n. induction n using N.peano_ind; intros lo sc Hbnd z Hz; auto.
  rewrite run_solo_succ. unfold step_solo; simpl.
  rewrite write_tape_other.
  - apply (IHn lo); auto. intros t Ht. apply Hbnd. lia.
  - pose proof (Hbnd n ltac:(lia)). lia.
Qed.

Lemma solo_depends_only_above : forall tbl n cut sc1 sc2,
  sc1.(spos) = sc2.(spos) ->
  sc1.(sstate) = sc2.(sstate) ->
  (forall z, cut <= z -> sc1.(stape) z = sc2.(stape) z) ->
  (forall t, (t < n)%N -> cut <= (run_solo tbl t sc1).(spos)) ->
  (run_solo tbl n sc1).(spos) = (run_solo tbl n sc2).(spos) /\
  (run_solo tbl n sc1).(sstate) = (run_solo tbl n sc2).(sstate) /\
  (forall z, cut <= z -> (run_solo tbl n sc1).(stape) z = (run_solo tbl n sc2).(stape) z).
Proof.
  intros tbl n. induction n using N.peano_ind; intros cut sc1 sc2 Hp Hs Htp Hbnd; auto.
  assert (IH : (run_solo tbl n sc1).(spos) = (run_solo tbl n sc2).(spos) /\
               (run_solo tbl n sc1).(sstate) = (run_solo tbl n sc2).(sstate) /\
               (forall z, cut <= z -> (run_solo tbl n sc1).(stape) z = (run_solo tbl n sc2).(stape) z)).
  { apply (IHn cut); auto. intros t Ht. apply Hbnd. lia. }
  destruct IH as [Ip [Is Itp]].
  pose proof (Hbnd n ltac:(lia)) as Hpos_n.
  rewrite !run_solo_succ. unfold step_solo; simpl.
  rewrite Ip, Is, (Itp (spos (run_solo tbl n sc2)) ltac:(lia)).
  repeat split; auto. intros z Hz. unfold write_tape.
  destruct (Z.eqb_spec z (spos (run_solo tbl n sc2))); auto.
Qed.

Theorem disjoint_split : forall n cut c s1 s2,
  c.(pos1) = s1.(spos) ->
  c.(state1) = s1.(sstate) ->
  c.(pos2) = s2.(spos) ->
  c.(state2) = s2.(sstate) ->
  (forall z, z < cut -> c.(tape) z = s1.(stape) z) ->
  (forall z, cut <= z -> c.(tape) z = s2.(stape) z) ->
  (forall t, (t < n)%N -> (run_solo ag1 t s1).(spos) < cut) ->
  (forall t, (t < n)%N -> cut <= (run_solo ag2 t s2).(spos)) ->
  (forall t, (t <= n)%N ->
    (run_N t c).(pos1) = (run_solo ag1 t s1).(spos) /\
    (run_N t c).(state1) = (run_solo ag1 t s1).(sstate) /\
    (run_N t c).(pos2) = (run_solo ag2 t s2).(spos) /\
    (run_N t c).(state2) = (run_solo ag2 t s2).(sstate) /\
    (forall z, z < cut -> (run_N t c).(tape) z = (run_solo ag1 t s1).(stape) z) /\
    (forall z, cut <= z -> (run_N t c).(tape) z = (run_solo ag2 t s2).(stape) z)) /\
  (forall t, (t < n)%N -> (run_N t c).(pos1) <> (run_N t c).(pos2)).
Proof.
  intros n cut c s1 s2 Hp1 Hs1 Hp2 Hs2 HtL HtR Hb1 Hb2.
  assert (Hmain : forall t, (t <= n)%N ->
    (run_N t c).(pos1) = (run_solo ag1 t s1).(spos) /\
    (run_N t c).(state1) = (run_solo ag1 t s1).(sstate) /\
    (run_N t c).(pos2) = (run_solo ag2 t s2).(spos) /\
    (run_N t c).(state2) = (run_solo ag2 t s2).(sstate) /\
    (forall z, z < cut -> (run_N t c).(tape) z = (run_solo ag1 t s1).(stape) z) /\
    (forall z, cut <= z -> (run_N t c).(tape) z = (run_solo ag2 t s2).(stape) z)).
  { intro t. induction t using N.peano_ind; intro Hle.
    - repeat split; auto.
    - assert (Hlt : (t < n)%N) by lia.
      destruct (IHt ltac:(lia)) as [P1 [S1 [P2 [S2 [TL TR]]]]].
      pose proof (Hb1 t Hlt) as B1. pose proof (Hb2 t Hlt) as B2.
      rewrite run_N_succ, !run_solo_succ. unfold step, step_solo; simpl.
      rewrite P1, S1, P2, S2, (TL _ B1), (TR _ B2).
      repeat split; auto; intros z Hz; unfold write_tape.
      + destruct (Z.eqb_spec z (spos (run_solo ag1 t s1))); auto.
        destruct (Z.eqb_spec z (spos (run_solo ag2 t s2))); [lia | apply TL; auto].
      + destruct (Z.eqb_spec z (spos (run_solo ag1 t s1))); [lia|].
        destruct (Z.eqb_spec z (spos (run_solo ag2 t s2))); auto. }
  split; [exact Hmain|].
  intros t Ht. destruct (Hmain t ltac:(lia)) as [P1 [_ [P2 _]]].
  pose proof (Hb1 t Ht). pose proof (Hb2 t Ht). lia.
Qed.

Lemma full_preserves_below : forall n lo c,
  (forall t, (t < n)%N -> lo <= (run_N t c).(pos1) /\ lo <= (run_N t c).(pos2)) ->
  forall z, z < lo -> (run_N n c).(tape) z = c.(tape) z.
Proof.
  intro n. induction n using N.peano_ind; intros lo c Hbnd z Hz; auto.
  rewrite run_N_succ. unfold step; simpl.
  pose proof (Hbnd n ltac:(lia)) as [H1 H2].
  rewrite !write_tape_other by lia.
  apply (IHn lo); auto. intros t Ht. apply Hbnd. lia.
Qed.

Lemma full_run_depends_only_above : forall n lo c1 c2,
  c1.(pos1) = c2.(pos1) ->
  c1.(pos2) = c2.(pos2) ->
  c1.(state1) = c2.(state1) ->
  c1.(state2) = c2.(state2) ->
  (forall z, lo <= z -> c1.(tape) z = c2.(tape) z) ->
  (forall t, (t < n)%N -> lo <= (run_N t c1).(pos1) /\ lo <= (run_N t c1).(pos2)) ->
  (forall t, (t <= n)%N ->
    (run_N t c1).(pos1) = (run_N t c2).(pos1) /\
    (run_N t c1).(pos2) = (run_N t c2).(pos2) /\
    (run_N t c1).(state1) = (run_N t c2).(state1) /\
    (run_N t c1).(state2) = (run_N t c2).(state2) /\
    (forall z, lo <= z -> (run_N t c1).(tape) z = (run_N t c2).(tape) z)).
Proof.
  intro n. induction n using N.peano_ind; intros lo c1 c2 P1 P2 S1 S2 Htp Hbnd t Ht.
  - assert (t = 0%N) by lia. subst. repeat split; auto.
  - destruct (N.le_gt_cases t n) as [Hle | Hgt].
    + apply (IHn lo); auto; try lia. intros k Hk. apply Hbnd. lia.
    + assert (Heq : t = N.succ n) by lia. subst t.
      assert (IH : (run_N n c1).(pos1) = (run_N n c2).(pos1) /\
                   (run_N n c1).(pos2) = (run_N n c2).(pos2) /\
                   (run_N n c1).(state1) = (run_N n c2).(state1) /\
                   (run_N n c1).(state2) = (run_N n c2).(state2) /\
                   (forall z, lo <= z -> (run_N n c1).(tape) z = (run_N n c2).(tape) z)).
      { apply (IHn lo); auto; try lia. intros k Hk. apply Hbnd. lia. }
      destruct IH as [I1 [I2 [Is1 [Is2 Itp]]]].
      pose proof (Hbnd n ltac:(lia)) as [B1 B2].
      rewrite !run_N_succ. unfold step; simpl.
      rewrite I1, I2, Is1, Is2.
      rewrite (Itp (pos1 (run_N n c2)) ltac:(lia)), (Itp (pos2 (run_N n c2)) ltac:(lia)).
      repeat split; auto; intros z Hz.
      unfold write_tape.
      destruct (Z.eqb_spec z (pos1 (run_N n c2))); auto.
      destruct (Z.eqb_spec z (pos2 (run_N n c2))); auto.
Qed.

(** * 3. Fast Binary-Tree Concrete Simulator *)

Inductive BTree : Type :=
| BEmpty : BTree
| BNode  : bool -> BTree -> BTree -> BTree.

Fixpoint bt_get (p : positive) (t : BTree) : bool :=
  match t with
  | BEmpty => false
  | BNode v l r =>
      match p with
      | xH    => v
      | xO p' => bt_get p' l
      | xI p' => bt_get p' r
      end
  end.

Fixpoint bt_set (p : positive) (v : bool) (t : BTree) : BTree :=
  match t with
  | BEmpty =>
      match p with
      | xH    => BNode v BEmpty BEmpty
      | xO p' => BNode false (bt_set p' v BEmpty) BEmpty
      | xI p' => BNode false BEmpty (bt_set p' v BEmpty)
      end
  | BNode v0 l r =>
      match p with
      | xH    => BNode v l r
      | xO p' => BNode v0 (bt_set p' v l) r
      | xI p' => BNode v0 l (bt_set p' v r)
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
  | Z0     => xH
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
  - apply bt_get_set_other. intro Heq. apply Hneq, z_to_pos_inj. symmetry; exact Heq.
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
  {| fpos1   := move_pos fc.(fpos1) tr1.(move_dir);
     fpos2   := move_pos fc.(fpos2) tr2.(move_dir);
     fstate1 := tr1.(next_state);
     fstate2 := tr2.(next_state);
     ftape   := t2 |}.

Lemma fast_step_sound : forall fc,
  cfg_eq (fc_to_cfg (fast_step fc)) (step (fc_to_cfg fc)).
Proof.
  intro fc. unfold fast_step, fc_to_cfg, step; simpl.
  constructor; simpl; try reflexivity.
  intro z.
  rewrite (bt_interp_set (bt_set (z_to_pos fc.(fpos2)) _ _) fc.(fpos1) _ z).
  apply write_tape_proper, bt_interp_set.
Qed.

Lemma fast_run_sound : forall n fc,
  cfg_eq (fc_to_cfg (N.iter n fast_step fc)) (run_N n (fc_to_cfg fc)).
Proof.
  intro n. induction n using N.peano_ind; intro fc.
  - apply cfg_eq_refl.
  - rewrite run_N_succ, N.iter_succ.
    eapply cfg_eq_trans; [apply fast_step_sound | apply step_proper, IHn].
Qed.

Definition bt_set_range (start : Z) (cnt : N) (v : bool) (t : BTree) : BTree :=
  snd (N.iter cnt (fun '(p, tr) => (p + 1, bt_set (z_to_pos p) v tr)) (start, t)).

Lemma bt_set_range_fst : forall cnt start v t,
  fst (N.iter cnt (fun '(p, tr) => (p + 1, bt_set (z_to_pos p) v tr)) (start, t)) =
  start + Z.of_N cnt.
Proof.
  intro cnt. induction cnt using N.peano_ind; intros start v t; simpl; [lia|].
  rewrite N.iter_succ.
  destruct (N.iter cnt _ (start, t)) as [p tr] eqn:E.
  pose proof (IHcnt start v t) as H. rewrite E in H. simpl in *. lia.
Qed.

Lemma bt_interp_set_range : forall cnt start v t z,
  bt_interp (bt_set_range start cnt v t) z =
  if (start <=? z) && (z <? start + Z.of_N cnt) then v else bt_interp t z.
Proof.
  intro cnt. induction cnt using N.peano_ind; intros start v t z.
  - unfold bt_set_range; simpl. destruct (start <=? z) eqn:E1; [|reflexivity].
    destruct (z <? start + 0) eqn:E2; [|reflexivity].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - unfold bt_set_range in *. rewrite N.iter_succ.
    destruct (N.iter cnt (fun '(p, tr) => (p + 1, bt_set (z_to_pos p) v tr)) (start, t)) as [p tr] eqn:E.
    pose proof (bt_set_range_fst cnt start v t) as Hfst. rewrite E in Hfst. simpl in Hfst.
    assert (IH : bt_interp tr z =
                 if (start <=? z) && (z <? start + Z.of_N cnt) then v else bt_interp t z).
    { replace tr with (snd (p, tr)) by reflexivity. rewrite <- E. apply IHcnt. }
    simpl. rewrite bt_interp_set. unfold write_tape. rewrite Hfst.
    destruct (Z.eqb_spec z (start + Z.of_N cnt)) as [->|Hne].
    + destruct (Z.leb_spec start (start + Z.of_N cnt)),
               (Z.ltb_spec (start + Z.of_N cnt) (start + Z.of_N (N.succ cnt))); try lia; auto.
    + rewrite IH.
      destruct (Z.leb_spec start z), (Z.ltb_spec z (start + Z.of_N cnt)),
               (Z.ltb_spec z (start + Z.of_N (N.succ cnt))); try lia; auto.
Qed.

Fixpoint bt_set_list (start : Z) (bs : list bool) (t : BTree) : BTree :=
  match bs with
  | [] => t
  | b :: bs' => bt_set_list (start + 1) bs' (bt_set (z_to_pos start) b t)
  end.

Lemma bt_interp_set_list : forall bs start t z,
  bt_interp (bt_set_list start bs t) z =
  if (start <=? z) && (z <? start + Z.of_nat (length bs))
  then nth (Z.to_nat (z - start)) bs false
  else bt_interp t z.
Proof.
  intro bs. induction bs as [|b bs' IH]; intros start t z; simpl.
  - destruct (Z.leb_spec start z), (Z.ltb_spec z (start + 0)); try lia; auto.
  - rewrite IH, bt_interp_set. unfold write_tape.
    destruct (Z.leb_spec start z) as [Hle|Hlt];
    destruct (Z.ltb_spec z (start + Z.pos (Pos.of_succ_nat (length bs')))) as [Hlt1|Hge1]; simpl.
    + destruct (Z.eqb_spec z start) as [->|Hne].
      * replace (start + 1 <=? start) with false by (symmetry; apply Z.leb_gt; lia).
        simpl. replace (start - start) with 0 by lia. reflexivity.
      * replace (start + 1 <=? z) with true by (symmetry; apply Z.leb_le; lia).
        replace (z <? start + 1 + Z.of_nat (length bs')) with true by (symmetry; apply Z.ltb_lt; lia).
        simpl.
        replace (Z.to_nat (z - start)) with (S (Z.to_nat (z - (start + 1)))) by lia.
        reflexivity.
    + replace (start + 1 <=? z) with true by (symmetry; apply Z.leb_le; lia).
      replace (z <? start + 1 + Z.of_nat (length bs')) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (Z.eqb_spec z start); [lia|reflexivity].
    + replace (start + 1 <=? z) with false by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.eqb_spec z start); [lia|reflexivity].
    + replace (start + 1 <=? z) with false by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.eqb_spec z start); [lia|reflexivity].
Qed.

Fixpoint check_range_nat (lo : Z) (len : nat) (f : Z -> bool) : bool :=
  match len with
  | O => true
  | S len' => f lo && check_range_nat (lo + 1) len' f
  end.

Lemma check_range_nat_sound : forall len lo f,
  check_range_nat lo len f = true ->
  forall z, lo <= z < lo + Z.of_nat len -> f z = true.
Proof.
  intro len. induction len as [|len' IH]; intros lo f H z Hz; [lia|].
  simpl in H. apply andb_true_iff in H as [H0 Hrest].
  destruct (Z.eq_dec z lo) as [->|Hne]; [exact H0|].
  apply (IH (lo + 1) f Hrest). lia.
Qed.

(** * 4. Agent 1 Binary Counter Proof (`0<C 0^n -> 0 B> 1^n`) *)

Fixpoint counter_steps (n : nat) : N :=
  match n with
  | O => 1%N
  | S O => 3%N
  | S k => 2 * counter_steps k + 2 * N.of_nat k + 1
  end.

Lemma counter_steps_formula : forall n : nat,
  (1 <= n)%nat ->
  Z.of_N (counter_steps n) = 2 ^ (Z.of_nat n + 2) - 2 * Z.of_nat n - 3.
Proof.
  intro n. induction n as [|k IH]; intro Hn; [lia|].
  destruct k as [|k'].
  - simpl. reflexivity.
  - assert (Hk : (1 <= S k')%nat) by lia.
    specialize (IH Hk).
    change (counter_steps (S (S k'))) with (2 * counter_steps (S k') + 2 * N.of_nat (S k') + 1)%N.
    rewrite !N2Z.inj_add, !N2Z.inj_mul, IH, nat_N_Z.
    change (Z.of_N 2) with 2. change (Z.of_N 1) with 1.
    replace (Z.of_nat (S (S k')) + 2) with (Z.succ (Z.of_nat (S k') + 2)) by lia.
    rewrite Z.pow_succ_r by lia. lia.
Qed.

Lemma B_walk_right : forall k : nat, forall start tp s,
  s = StB ->
  (forall z, start <= z < start + Z.of_nat k -> tp z = true) ->
  let sc := {| spos := start; sstate := s; stape := tp |} in
  (forall t, (t < N.of_nat k)%N ->
     (run_solo ag1 t sc).(spos) = start + Z.of_N t /\
     (run_solo ag1 t sc).(sstate) = StB) /\
  (run_solo ag1 (N.of_nat k) sc).(spos) = start + Z.of_nat k /\
  (run_solo ag1 (N.of_nat k) sc).(sstate) = StB /\
  tape_eq (run_solo ag1 (N.of_nat k) sc).(stape) tp.
Proof.
  intro k. induction k as [|k' IH]; intros start tp s -> Htp sc.
  - split; [intros t Ht; lia | repeat split; simpl; try lia; reflexivity].
  - replace (N.of_nat (S k')) with (N.of_nat k' + 1)%N by lia.
    destruct (IH (start + 1) tp StB eq_refl ltac:(intros z Hz; apply Htp; lia))
      as [IHb [IHp [IHs IHtp]]].
    assert (H1 : scfg_eq (run_solo ag1 1 sc)
                         {| spos := start + 1; sstate := StB; stape := tp |}).
    { change 1%N with (N.succ 0). rewrite run_solo_succ, run_solo_0.
      unfold step_solo, sc; simpl. rewrite Htp by lia.
      repeat split; simpl; auto. intro z. unfold write_tape.
      destruct (Z.eqb_spec z start); subst; auto. symmetry; apply Htp; lia. }
    assert (Hadd : forall t, scfg_eq (run_solo ag1 (t + 1) sc)
                                      (run_solo ag1 t {| spos := start + 1; sstate := StB; stape := tp |})).
    { intro t. rewrite run_solo_add. apply run_solo_proper. exact H1. }
    split.
    + intros t Ht. destruct (N.eq_0_gt_0_cases t) as [-> | Hpos].
      * simpl; split; [lia | reflexivity].
      * replace t with ((t - 1) + 1)%N by lia.
        destruct (Hadd (t - 1)%N) as [Ap [As _]].
        destruct (IHb (t - 1)%N ltac:(lia)) as [Bp Bs].
        split; [lia | congruence].
    + destruct (Hadd (N.of_nat k')) as [Ap [As Atp]].
      repeat split; try lia; try congruence.
Qed.

Lemma C_walk_left : forall k : nat, forall start tp s,
  s = StC ->
  (forall z, start - Z.of_nat k < z <= start -> tp z = true) ->
  let sc := {| spos := start; sstate := s; stape := tp |} in
  (forall t, (t < N.of_nat k)%N ->
     (run_solo ag1 t sc).(spos) = start - Z.of_N t /\
     (run_solo ag1 t sc).(sstate) = StC) /\
  (run_solo ag1 (N.of_nat k) sc).(spos) = start - Z.of_nat k /\
  (run_solo ag1 (N.of_nat k) sc).(sstate) = StC /\
  (forall z, (run_solo ag1 (N.of_nat k) sc).(stape) z =
             if (start - Z.of_nat k <? z) && (z <=? start) then false else tp z).
Proof.
  intro k. induction k as [|k' IH]; intros start tp s -> Htp sc.
  - split; [intros t Ht; lia | repeat split; simpl; try lia; try reflexivity].
    intro z. destruct (start - 0 <? z) eqn:E1; destruct (z <=? start) eqn:E2; auto.
    apply Z.ltb_lt in E1. apply Z.leb_le in E2. lia.
  - replace (N.of_nat (S k')) with (N.of_nat k' + 1)%N by lia.
    set (tp1 := write_tape tp start false).
    assert (H1 : scfg_eq (run_solo ag1 1 sc)
                         {| spos := start - 1; sstate := StC; stape := tp1 |}).
    { change 1%N with (N.succ 0). rewrite run_solo_succ, run_solo_0.
      unfold step_solo, sc; simpl. rewrite Htp by lia.
      repeat split; simpl; auto. }
    assert (Htp1 : forall z, (start - 1) - Z.of_nat k' < z <= start - 1 -> tp1 z = true).
    { intros z Hz. unfold tp1. rewrite write_tape_other by lia. apply Htp; lia. }
    destruct (IH (start - 1) tp1 StC eq_refl Htp1) as [IHb [IHp [IHs IHtp]]].
    assert (Hadd : forall t, scfg_eq (run_solo ag1 (t + 1) sc)
                                      (run_solo ag1 t {| spos := start - 1; sstate := StC; stape := tp1 |})).
    { intro t. rewrite run_solo_add. apply run_solo_proper. exact H1. }
    split.
    + intros t Ht. destruct (N.eq_0_gt_0_cases t) as [-> | Hpos].
      * simpl; split; [lia | reflexivity].
      * replace t with ((t - 1) + 1)%N by lia.
        destruct (Hadd (t - 1)%N) as [Ap [As _]].
        destruct (IHb (t - 1)%N ltac:(lia)) as [Bp Bs].
        split; [lia | congruence].
    + destruct (Hadd (N.of_nat k')) as [Ap [As Atp]].
      split; [lia | split; [congruence|]].
      intro z. rewrite (Atp z), IHtp. unfold tp1, write_tape.
      destruct (Z.eqb_spec z start) as [Heqz|Hne];
      destruct (Z.ltb_spec (start - Z.of_nat (S k')) z),
               (Z.ltb_spec (start - 1 - Z.of_nat k') z),
               (Z.leb_spec z start), (Z.leb_spec z (start - 1)); try lia; auto.
Qed.

Theorem agent1_counter : forall n : nat, (1 <= n)%nat -> forall tp,
  (forall z, z < -1 + Z.of_nat n -> tp z = false) ->
  let sc := {| spos := -2; sstate := StC; stape := tp |} in
  (forall t, (t < counter_steps n)%N ->
     -2 <= (run_solo ag1 t sc).(spos) < -1 + Z.of_nat n /\
     ((run_solo ag1 t sc).(sstate) = StB \/ (run_solo ag1 t sc).(sstate) = StC)) /\
  (run_solo ag1 (counter_steps n) sc).(spos) = -1 /\
  (run_solo ag1 (counter_steps n) sc).(sstate) = StB /\
  (forall z, (run_solo ag1 (counter_steps n) sc).(stape) z =
             if (-1 <=? z) && (z <? -1 + Z.of_nat n) then true else tp z).
Proof.
  intro n. induction n as [|k IH]; intros Hn tp Htp sc; [lia|].
  destruct k as [|k'].
  - assert (H1 : scfg_eq (run_solo ag1 1 sc)
                         {| spos := -1; sstate := StB; stape := write_tape tp (-2) false |}).
    { change 1%N with (N.succ 0). rewrite run_solo_succ, run_solo_0.
      unfold step_solo, sc; simpl. rewrite Htp by lia. repeat split; auto; try reflexivity. }
    assert (H2 : scfg_eq (run_solo ag1 2 sc)
                         {| spos := -2; sstate := StC; stape := write_tape (write_tape tp (-2) false) (-1) true |}).
    { change 2%N with (N.succ 1). rewrite run_solo_succ.
      pose proof (step_solo_proper ag1 _ _ H1) as Hp.
      unfold step_solo at 2 in Hp; simpl in Hp.
      rewrite write_tape_other, Htp in Hp by lia. simpl in Hp. exact Hp. }
    assert (H3 : scfg_eq (run_solo ag1 3 sc)
                         {| spos := -1; sstate := StB;
                            stape := write_tape (write_tape (write_tape tp (-2) false) (-1) true) (-2) false |}).
    { change 3%N with (N.succ 2). rewrite run_solo_succ.
      pose proof (step_solo_proper ag1 _ _ H2) as Hp.
      unfold step_solo at 2 in Hp; simpl in Hp. exact Hp. }
    destruct H1 as [P1 [S1 _]], H2 as [P2 [S2 _]], H3 as [P3 [S3 Tp3]].
    cbn [spos sstate stape] in P1, S1, P2, S2, P3, S3, Tp3.
    simpl (counter_steps 1). split.
    + intros t Ht. simpl in Ht.
      assert (t = 0 \/ t = 1 \/ t = 2)%N as [->|[->| ->]] by lia;
        [ simpl; split; [lia|right; reflexivity]
        | rewrite P1, S1; split; [lia|left; reflexivity]
        | rewrite P2, S2; split; [lia|right; reflexivity] ].
    + split; [exact P3 | split; [exact S3 | ]]. intro z. rewrite (Tp3 z).
      unfold write_tape. replace (-1 + Z.of_nat 1) with 0 by lia.
      destruct (Z.eqb_spec z (-2)) as [Hz2|Hnz2]; destruct (Z.eqb_spec z (-1)) as [Hz1|Hnz1]; simpl;
        destruct (Z.leb_spec (-1) z), (Z.ltb_spec z 0); try lia; try (rewrite Htp by lia); auto.
  - set (kk := S k').
    assert (Hkk : (1 <= kk)%nat) by (unfold kk; lia).
    set (T := counter_steps kk).
    change (counter_steps (S kk)) with (2 * T + 2 * N.of_nat kk + 1)%N.
    assert (Htp_k : forall z, z < -1 + Z.of_nat kk -> tp z = false).
    { intros z Hz. apply Htp. lia. }
    destruct (IH Hkk tp Htp_k) as [IHb [IHp [IHs IHtp]]].
    set (sc1 := run_solo ag1 T sc).
    assert (HB_in : forall z, -1 <= z < -1 + Z.of_nat kk -> (stape sc1) z = true).
    { intros z Hz. unfold sc1. rewrite IHtp.
      replace (-1 <=? z) with true by (symmetry; apply Z.leb_le; lia).
      replace (z <? -1 + Z.of_nat (S k')) with true by (symmetry; apply Z.ltb_lt; unfold kk in Hz; lia).
      reflexivity. }
    destruct (B_walk_right kk (-1) (stape sc1) StB eq_refl HB_in)
      as [BRb [BRp [BRs BRtp]]].
    assert (Hsc1_eq : scfg_eq sc1 {| spos := -1; sstate := StB; stape := stape sc1 |}).
    { split; [exact IHp | split; [exact IHs | intro; reflexivity]]. }
    set (sc2 := run_solo ag1 (N.of_nat kk) sc1).
    assert (Hsc2_at : sc2.(spos) = -1 + Z.of_nat kk /\ sc2.(sstate) = StB /\ tape_eq sc2.(stape) sc1.(stape)).
    { pose proof (run_solo_proper ag1 (N.of_nat kk) _ _ Hsc1_eq) as [A [B C]].
      split; [unfold sc2; rewrite A; exact BRp | split; [unfold sc2; rewrite B; exact BRs | intro z; unfold sc2; rewrite (C z); apply BRtp]]. }
    destruct Hsc2_at as [P2 [S2 Tp2]].
    assert (Hread2 : (stape sc2) (-1 + Z.of_nat kk) = false).
    { rewrite Tp2. unfold sc1. rewrite IHtp.
      replace (-1 + Z.of_nat kk <? -1 + Z.of_nat (S k')) with false by (symmetry; apply Z.ltb_ge; unfold kk; lia).
      rewrite andb_false_r. apply Htp. unfold kk; lia. }
    set (sc3 := run_solo ag1 1 sc2).
    assert (Hsc3_at : sc3.(spos) = -2 + Z.of_nat kk /\ sc3.(sstate) = StC /\
                      tape_eq sc3.(stape) (write_tape sc2.(stape) (-1 + Z.of_nat kk) true)).
    { unfold sc3. change 1%N with (N.succ 0). rewrite run_solo_succ, run_solo_0.
      unfold step_solo; rewrite P2, S2, Hread2.
      unfold ag1, ag1_opt, move_pos; cbn [spos sstate stape move_dir next_state write_sym].
      split; [lia | split; [reflexivity | intro z; reflexivity]]. }
    destruct Hsc3_at as [P3 [S3 Tp3]].
    assert (HC_in : forall z, (-2 + Z.of_nat kk) - Z.of_nat kk < z <= -2 + Z.of_nat kk ->
                              (stape sc3) z = true).
    { intros z Hz. rewrite Tp3, write_tape_other, Tp2 by lia. apply HB_in; lia. }
    destruct (C_walk_left kk (-2 + Z.of_nat kk) (stape sc3) StC eq_refl HC_in)
      as [CLb [CLp [CLs CLtp]]].
    assert (Hsc3_eq : scfg_eq sc3 {| spos := -2 + Z.of_nat kk; sstate := StC; stape := stape sc3 |}).
    { split; [exact P3 | split; [exact S3 | intro; reflexivity]]. }
    set (sc4 := run_solo ag1 (N.of_nat kk) sc3).
    assert (Hsc4_at : sc4.(spos) = -2 /\ sc4.(sstate) = StC /\
                      forall z, sc4.(stape) z =
                                if (-1 + Z.of_nat kk <=? z) && (z <? -1 + Z.of_nat (S kk))
                                then true
                                else if z <? -1 + Z.of_nat kk then false else tp z).
    { pose proof (run_solo_proper ag1 (N.of_nat kk) _ _ Hsc3_eq) as [A [B C]].
      split; [unfold sc4; rewrite A, CLp; lia | split; [unfold sc4; rewrite B; exact CLs |]].
      intro z. unfold sc4. rewrite (C z), CLtp, Tp3. unfold write_tape. rewrite Tp2. unfold sc1. rewrite IHtp.
      unfold kk in *.
      destruct (Z.eqb_spec z (-1 + Z.of_nat (S k'))) as [Hzk|Hne];
      destruct (Z.ltb_spec (-2 + Z.of_nat (S k') - Z.of_nat (S k')) z),
               (Z.leb_spec z (-2 + Z.of_nat (S k'))),
               (Z.leb_spec (-1 + Z.of_nat (S k')) z),
               (Z.ltb_spec z (-1 + Z.of_nat (S k'))),
               (Z.leb_spec (-1) z),
               (Z.ltb_spec z (-1 + Z.of_nat (S (S k'))));
        try lia; try (apply Htp; lia); try (symmetry; apply Htp; lia); auto. }
    destruct Hsc4_at as [P4 [S4 Tp4]].
    assert (Htp4_k : forall z, z < -1 + Z.of_nat kk -> (stape sc4) z = false).
    { intros z Hz. rewrite Tp4.
      destruct (Z.leb_spec (-1 + Z.of_nat kk) z), (Z.ltb_spec z (-1 + Z.of_nat kk)); try lia; auto. }
    destruct (IH Hkk (stape sc4) Htp4_k) as [IH2b [IH2p [IH2s IH2tp]]].
    assert (Hsc4_eq : scfg_eq sc4 {| spos := -2; sstate := StC; stape := stape sc4 |}).
    { split; [exact P4 | split; [exact S4 | intro; reflexivity]]. }
    assert (Hseg2 : forall t, (t <= N.of_nat kk)%N ->
      scfg_eq (run_solo ag1 (T + t) sc) (run_solo ag1 t {| spos := -1; sstate := StB; stape := stape sc1 |})).
    { intros t _. replace (T + t)%N with (t + T)%N by lia. rewrite run_solo_add. apply run_solo_proper, Hsc1_eq. }
    assert (Hseg4 : forall t, (t <= N.of_nat kk)%N ->
      scfg_eq (run_solo ag1 (T + N.of_nat kk + 1 + t) sc)
              (run_solo ag1 t {| spos := -2 + Z.of_nat kk; sstate := StC; stape := stape sc3 |})).
    { intros t _. replace (T + N.of_nat kk + 1 + t)%N with (t + (1 + (N.of_nat kk + T)))%N by lia.
      rewrite !run_solo_add. apply run_solo_proper.
      change (run_solo ag1 1 (run_solo ag1 (N.of_nat kk) (run_solo ag1 T sc))) with sc3.
      exact Hsc3_eq. }
    assert (Hseg5 : forall t,
      scfg_eq (run_solo ag1 (T + 2 * N.of_nat kk + 1 + t) sc)
              (run_solo ag1 t {| spos := -2; sstate := StC; stape := stape sc4 |})).
    { intro t. replace (T + 2 * N.of_nat kk + 1 + t)%N with (t + (N.of_nat kk + (1 + (N.of_nat kk + T))))%N by lia.
      rewrite !run_solo_add. apply run_solo_proper. exact Hsc4_eq. }
    split.
    + intros t Ht.
      destruct (N.lt_ge_cases t T) as [Ht1 | Hge1].
      * destruct (IHb t Ht1) as [[A B] C]. unfold sc in *. split; [lia | exact C].
      * destruct (N.lt_ge_cases t (T + N.of_nat kk)) as [Ht2 | Hge2].
        { replace t with (T + (t - T))%N by lia.
          destruct (Hseg2 (t - T)%N ltac:(lia)) as [Ap [As _]].
          destruct (BRb (t - T)%N ltac:(lia)) as [Bp Bs].
          unfold kk in *. split; [lia | left; congruence]. }
        destruct (N.eq_dec t (T + N.of_nat kk)) as [-> | Hne2].
        { replace (T + N.of_nat kk)%N with (N.of_nat kk + T)%N by lia.
          rewrite run_solo_add.
          change (run_solo ag1 (N.of_nat kk) (run_solo ag1 T sc)) with sc2.
          rewrite P2, S2. unfold kk in *. split; [lia | left; reflexivity]. }
        destruct (N.lt_ge_cases t (T + 2 * N.of_nat kk + 1)) as [Ht4 | Hge4].
        { replace t with (T + N.of_nat kk + 1 + (t - (T + N.of_nat kk + 1)))%N by lia.
          destruct (Hseg4 (t - (T + N.of_nat kk + 1))%N ltac:(lia)) as [Ap [As _]].
          destruct (CLb (t - (T + N.of_nat kk + 1))%N ltac:(lia)) as [Bp Bs].
          unfold kk in *. split; [lia | right; congruence]. }
        { unfold T, kk in *. replace t with (counter_steps (S k') + 2 * N.of_nat (S k') + 1 + (t - (counter_steps (S k') + 2 * N.of_nat (S k') + 1)))%N by lia.
          destruct (Hseg5 (t - (counter_steps (S k') + 2 * N.of_nat (S k') + 1))%N) as [Ap [As _]].
          destruct (IH2b (t - (counter_steps (S k') + 2 * N.of_nat (S k') + 1))%N ltac:(lia)) as [[Bp1 Bp2] Bs].
          split; [lia | rewrite As; exact Bs]. }
    + replace (2 * T + 2 * N.of_nat kk + 1)%N with (T + 2 * N.of_nat kk + 1 + T)%N by lia.
      destruct (Hseg5 T) as [Fp [Fs Ftp]].
      unfold T, kk in *. split; [congruence | split; [congruence|]].
      intro z. rewrite (Ftp z), IH2tp, Tp4.
      destruct (Z.leb_spec (-1) z), (Z.ltb_spec z (-1 + Z.of_nat (S k'))),
               (Z.leb_spec (-1 + Z.of_nat (S k')) z), (Z.ltb_spec z (-1 + Z.of_nat (S (S k'))));
        try lia; try (apply Htp; lia); try (symmetry; apply Htp; lia); auto.
Qed.

(** * 5. Agent 2 Period-21 Translated Glider *)

Definition gl0_tape : Tape :=
  fun z => if (z =? 1) || (z =? 2) || (z =? 3) then true else false.

Definition gl0 : SoloConfig := {|
  spos := 1; sstate := StB; stape := gl0_tape
|}.

Definition gl0_fast_bt : BTree :=
  bt_set_list 0 [false; true; true; true] BEmpty.

Lemma gl0_fast_bt_sound : tape_eq (bt_interp gl0_fast_bt) gl0_tape.
Proof.
  intro z. unfold gl0_fast_bt, gl0_tape. rewrite bt_interp_set_list.
  unfold bt_interp; rewrite bt_get_empty. simpl.
  destruct (Z.leb_spec 0 z), (Z.ltb_spec z 4); simpl.
  - assert (z = 0 \/ z = 1 \/ z = 2 \/ z = 3) as [->|[->|[->| ->]]] by lia; reflexivity.
  - destruct (Z.eqb_spec z 1), (Z.eqb_spec z 2), (Z.eqb_spec z 3); try lia; reflexivity.
  - destruct (Z.eqb_spec z 1), (Z.eqb_spec z 2), (Z.eqb_spec z 3); try lia; reflexivity.
  - destruct (Z.eqb_spec z 1), (Z.eqb_spec z 2), (Z.eqb_spec z 3); try lia; reflexivity.
Qed.

Definition fast_step2 (fc : Z * State * BTree) : Z * State * BTree :=
  let '(p, s, bt) := fc in
  let tr := ag2 s (bt_get (z_to_pos p) bt) in
  (move_pos p tr.(move_dir), tr.(next_state), bt_set (z_to_pos p) tr.(write_sym) bt).

Definition gl0_fast : Z * State * BTree := (1, StB, gl0_fast_bt).

Definition f2_to_scfg (fc : Z * State * BTree) : SoloConfig :=
  let '(p, s, bt) := fc in {| spos := p; sstate := s; stape := bt_interp bt |}.

Lemma fast_step2_sound : forall fc,
  scfg_eq (f2_to_scfg (fast_step2 fc)) (step_solo ag2 (f2_to_scfg fc)).
Proof.
  intros [[p s] bt]. unfold fast_step2, f2_to_scfg, step_solo; simpl.
  repeat split; simpl; auto. intro z. apply bt_interp_set.
Qed.

Lemma fast_run2_sound : forall n fc,
  scfg_eq (f2_to_scfg (N.iter n fast_step2 fc)) (run_solo ag2 n (f2_to_scfg fc)).
Proof.
  intro n. induction n using N.peano_ind; intro fc.
  - repeat split; auto; try reflexivity.
  - rewrite run_solo_succ, N.iter_succ.
    pose proof (fast_step2_sound (N.iter n fast_step2 fc)) as [A [B C]].
    pose proof (step_solo_proper ag2 _ _ (IHn fc)) as [D [E F]].
    repeat split; try congruence.
Qed.

Lemma iter_chk_sound : forall {A : Type} (stepf : A -> A) (pred : A -> bool) (n : N) (a0 : A),
  fst (N.iter n (fun '(ok, x) => (ok && pred x, stepf x)) (true, a0)) = true ->
  forall k, (k < n)%N -> pred (N.iter k stepf a0) = true.
Proof.
  intros A stepf pred n a0 Hn k Hk.
  set (f := fun '(ok, x) => (ok && pred x, stepf x)).
  assert (Hsnd : forall m a b, snd (N.iter m f (a, b)) = N.iter m stepf b).
  { intro m. induction m using N.peano_ind; intros a b; [reflexivity|].
    rewrite !N.iter_succ. destruct (N.iter m f (a, b)) as [a' b'] eqn:Em.
    pose proof (IHm a b) as Hm. rewrite Em in Hm. simpl in *. unfold f. simpl. congruence. }
  assert (Hmono : forall m d, (m <= d)%N -> forall a b,
    fst (N.iter d f (a, b)) = true -> fst (N.iter m f (a, b)) = true).
  { intros m d. induction d using N.peano_ind; intros Hmd a b Hd.
    - assert (m = 0)%N by lia. subst. exact Hd.
    - destruct (N.eq_dec m (N.succ d)) as [-> | Hne]; [exact Hd|].
      apply IHd; [lia|]. rewrite N.iter_succ in Hd.
      destruct (N.iter d f (a, b)) as [a' b']. unfold f in Hd. simpl in Hd.
      apply andb_true_iff in Hd as [Ha _]. exact Ha. }
  assert (Hk1 : fst (N.iter (N.succ k) f (true, a0)) = true) by (eapply Hmono; eauto; lia).
  rewrite N.iter_succ in Hk1.
  destruct (N.iter k f (true, a0)) as [a b] eqn:Ek.
  pose proof (Hsnd k true a0) as Hb. rewrite Ek in Hb. simpl in Hb. subst b.
  unfold f in Hk1. simpl in Hk1. apply andb_true_iff in Hk1 as [_ Hp]. exact Hp.
Qed.

Definition check_gl_cycle (n : N) : bool :=
  let '(p_end, s_end, bt_end) := N.iter n fast_step2 gl0_fast in
  (p_end =? 4) && state_eqb s_end StB &&
  check_range_nat 0 12 (fun z =>
    Bool.eqb (bt_get (z_to_pos z) bt_end)
             (if (z <? 3) then true else bt_get (z_to_pos (z - 3)) gl0_fast_bt)) &&
  fst (N.iter n (fun '(ok, fc) =>
    (ok && ((0 <=? fst (fst fc)) && (fst (fst fc) <? 10)), fast_step2 fc)) (true, gl0_fast)).

Lemma gl_cycle_verify_sound : forall n : N,
  check_gl_cycle n = true ->
  (forall t, (t < n)%N -> 0 <= (run_solo ag2 t gl0).(spos) < 10) /\
  (run_solo ag2 n gl0).(spos) = 4 /\
  (run_solo ag2 n gl0).(sstate) = StB /\
  forall z, (run_solo ag2 n gl0).(stape) z =
            if z <? 0 then false
            else if z <? 3 then true
            else gl0_tape (z - 3).
Proof.
  intros n Hchk. unfold check_gl_cycle in Hchk.
  destruct (N.iter n fast_step2 gl0_fast) as [[p_end s_end] bt_end] eqn:En.
  repeat rewrite andb_true_iff in Hchk.
  destruct Hchk as [[[Hp_end Hs_end] Hwin] Hloop].
  apply Z.eqb_eq in Hp_end.
  destruct (state_eqb_spec s_end StB); [|discriminate].
  assert (Hgl0_eq : scfg_eq (f2_to_scfg gl0_fast) gl0).
  { repeat split; auto. intro z. apply gl0_fast_bt_sound. }
  assert (Hbnd : forall t, (t < n)%N -> 0 <= (run_solo ag2 t gl0).(spos) < 10).
  { intros t Ht.
    pose proof (iter_chk_sound fast_step2
      (fun fc => (0 <=? fst (fst fc)) && (fst (fst fc) <? 10)) n gl0_fast Hloop t Ht) as Hpt.
    apply andb_true_iff in Hpt as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    pose proof (fast_run2_sound t gl0_fast) as [Ap _].
    pose proof (run_solo_proper ag2 t _ _ Hgl0_eq) as [Bp _].
    destruct (N.iter t fast_step2 gl0_fast) as [[pt st] btt]. simpl in *. lia. }
  split; [exact Hbnd|].
  pose proof (fast_run2_sound n gl0_fast) as [Ap [As Atp]].
  pose proof (run_solo_proper ag2 n _ _ Hgl0_eq) as [Bp [Bs Btp]].
  rewrite En in Ap, As, Atp. cbn [f2_to_scfg spos sstate stape] in Ap, As, Atp, Bp, Bs, Btp.
  split; [lia | split; [congruence |]].
  intro z.
  destruct (Z.lt_ge_cases z 0) as [Hz0 | Hgez0].
  - rewrite (solo_preserves_outside ag2 n 0 10 gl0 Hbnd z ltac:(lia)).
    simpl. destruct (Z.ltb_spec z 0); try lia.
    unfold gl0_tape. destruct (Z.eqb_spec z 1), (Z.eqb_spec z 2), (Z.eqb_spec z 3); try lia; auto.
  - destruct (Z.lt_ge_cases z 12) as [Hz12 | Hge12].
    + rewrite <- (Btp z), <- (Atp z).
      pose proof (check_range_nat_sound 12 0 _ Hwin z ltac:(lia)) as Hw.
      apply Bool.eqb_prop in Hw. unfold bt_interp. rewrite Hw.
      destruct (Z.ltb_spec z 0), (Z.ltb_spec z 3); try lia; auto.
      apply gl0_fast_bt_sound.
    + rewrite (solo_preserves_outside ag2 n 0 10 gl0 Hbnd z ltac:(lia)).
      simpl. replace (z <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (z <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
      unfold gl0_tape.
      destruct (Z.eqb_spec z 1), (Z.eqb_spec z 2), (Z.eqb_spec z 3);
      destruct (Z.eqb_spec (z - 3) 1), (Z.eqb_spec (z - 3) 2), (Z.eqb_spec (z - 3) 3); try lia; auto.
Qed.

Lemma gl21_cycle_step :
  (forall t, (t < 21)%N -> 0 <= (run_solo ag2 t gl0).(spos) < 10) /\
  (run_solo ag2 21 gl0).(spos) = 4 /\
  (run_solo ag2 21 gl0).(sstate) = StB /\
  forall z, (run_solo ag2 21 gl0).(stape) z =
            if z <? 0 then false
            else if z <? 3 then true
            else gl0_tape (z - 3).
Proof. apply gl_cycle_verify_sound. vm_compute. reflexivity. Qed.

Lemma gl_mult21 : forall q : N, forall pad : Z,
  (forall t, (t < 21 * q)%N -> pad <= (run_solo ag2 t (shift_scfg pad gl0)).(spos)) /\
  (run_solo ag2 (21 * q) (shift_scfg pad gl0)).(spos) = pad + 3 * Z.of_N q + 1 /\
  (run_solo ag2 (21 * q) (shift_scfg pad gl0)).(sstate) = StB /\
  forall z, (run_solo ag2 (21 * q) (shift_scfg pad gl0)).(stape) z =
            if z <? pad then false
            else if z <? pad + 3 * Z.of_N q then true
            else gl0_tape (z - (pad + 3 * Z.of_N q)).
Proof.
  intro q. induction q using N.peano_ind; intro pad.
  - replace (21 * 0)%N with 0%N by lia.
    split; [intros t Ht; lia|].
    split. { rewrite run_solo_0. unfold shift_scfg, gl0; cbn [spos]. lia. }
    split; [rewrite run_solo_0; reflexivity|].
    intro z; rewrite run_solo_0; unfold shift_scfg, gl0; cbn [stape].
    destruct (Z.ltb_spec z pad), (Z.ltb_spec z (pad + 3 * Z.of_N 0)); try lia;
      [ unfold gl0_tape; destruct (Z.eqb_spec (z - pad) 1), (Z.eqb_spec (z - pad) 2), (Z.eqb_spec (z - pad) 3); try lia; auto
      | replace (pad + 3 * Z.of_N 0) with pad by lia; reflexivity ].
  - replace (21 * N.succ q)%N with (21 + 21 * q)%N by lia.
    destruct (IHq pad) as [IHb [IHp [IHs IHtp]]].
    destruct gl21_cycle_step as [C21b [C21p [C21s C21tp]]].
    set (pad' := pad + 3 * Z.of_N q).
    assert (Hsc_eq : forall z, pad' <= z ->
      (run_solo ag2 (21 * q) (shift_scfg pad gl0)).(stape) z = (shift_scfg pad' gl0).(stape) z).
    { intros z Hz. unfold pad' in Hz. rewrite IHtp.
      replace (z <? pad) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (z <? pad + 3 * Z.of_N q) with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity. }
    assert (Hb_sh : forall t, (t < 21)%N ->
      pad' <= (run_solo ag2 t (shift_scfg pad' gl0)).(spos)).
    { intros t Ht. pose proof (shift_run_solo ag2 t pad' gl0) as [Ap _].
      cbn [spos gl0 shift_scfg] in Ap. pose proof (C21b t Ht) as Hb. lia. }
    assert (Hsym_run : forall t, (t <= 21)%N ->
      (run_solo ag2 t (shift_scfg pad' gl0)).(spos) = (run_solo ag2 t (run_solo ag2 (21 * q) (shift_scfg pad gl0))).(spos)).
    { intros t Ht. destruct (solo_depends_only_above ag2 t pad'
        (shift_scfg pad' gl0) (run_solo ag2 (21 * q) (shift_scfg pad gl0))
        ltac:(cbn [spos gl0 shift_scfg]; unfold pad'; lia) ltac:(cbn [sstate gl0 shift_scfg]; congruence)
        ltac:(intros z Hz; symmetry; apply Hsc_eq; exact Hz)
        ltac:(intros k Hk; apply Hb_sh; lia)) as [Sp _]; exact Sp. }
    destruct (solo_depends_only_above ag2 21 pad'
                (run_solo ag2 (21 * q) (shift_scfg pad gl0))
                (shift_scfg pad' gl0)
                ltac:(cbn [spos gl0 shift_scfg]; unfold pad'; lia) ltac:(cbn [sstate gl0 shift_scfg]; congruence) Hsc_eq
                ltac:(intros t Ht; rewrite <- (Hsym_run t ltac:(lia)); apply Hb_sh; exact Ht))
      as [Sp [Ss Stp]].
    assert (Hsh21 : scfg_eq (run_solo ag2 21 (shift_scfg pad' gl0))
                            (shift_scfg pad' (run_solo ag2 21 gl0))) by apply shift_run_solo.
    destruct Hsh21 as [Shp [Shs Shtp]].
    cbn [spos sstate shift_scfg] in Shp, Shs.
    split.
    + intros t Ht. destruct (N.lt_ge_cases t (21 * q)) as [Ht1 | Hge1].
      * apply IHb, Ht1.
      * replace t with ((t - 21 * q) + 21 * q)%N by lia.
        rewrite run_solo_add, <- (Hsym_run (t - 21 * q)%N ltac:(lia)).
        pose proof (Hb_sh (t - 21 * q)%N ltac:(lia)). unfold pad' in *. lia.
    + rewrite run_solo_add.
      split; [unfold pad' in *; lia | split; [congruence |]].
      assert (Hb_full : forall t, (t < 21)%N -> pad' <= (run_solo ag2 t (run_solo ag2 (21 * q) (shift_scfg pad gl0))).(spos)).
      { intros t Ht. rewrite <- (Hsym_run t ltac:(lia)). apply Hb_sh; exact Ht. }
      intro z. destruct (Z.lt_ge_cases z pad') as [HzL | HzR].
      * rewrite (solo_preserves_below ag2 21 pad' _ Hb_full z HzL), IHtp.
        unfold pad' in HzL.
        destruct (Z.ltb_spec z pad), (Z.ltb_spec z (pad + 3 * Z.of_N (N.succ q))),
                 (Z.ltb_spec z (pad + 3 * Z.of_N q)); try lia; auto.
      * rewrite (Stp z HzR), (Shtp z). unfold shift_scfg at 1; cbn [stape]. rewrite C21tp.
        unfold pad' in *.
        destruct (Z.ltb_spec (z - (pad + 3 * Z.of_N q)) 0),
                 (Z.ltb_spec (z - (pad + 3 * Z.of_N q)) 3),
                 (Z.ltb_spec z pad),
                 (Z.ltb_spec z (pad + 3 * Z.of_N (N.succ q))); try lia; auto.
        replace (z - (pad + 3 * Z.of_N q) - 3) with (z - (pad + 3 * Z.of_N (N.succ q))) by lia; auto.
Qed.

Lemma gl_never_left_of_pad : forall t pad,
  pad <= (run_solo ag2 t (shift_scfg pad gl0)).(spos).
Proof.
  intros t pad.
  set (q := (t / 21)%N). set (r := (t mod 21)%N).
  assert (Ht : t = (r + 21 * q)%N) by (unfold r, q; pose proof (N.div_mod t 21 ltac:(lia)); lia).
  assert (Hr : (r < 21)%N) by (unfold r; apply N.mod_lt; lia).
  destruct (gl_mult21 q pad) as [_ [Hp [Hs Htp]]].
  destruct gl21_cycle_step as [C21b _].
  set (pad' := pad + 3 * Z.of_N q).
  assert (Hsc_eq : forall z, pad' <= z ->
    (run_solo ag2 (21 * q) (shift_scfg pad gl0)).(stape) z = (shift_scfg pad' gl0).(stape) z).
  { intros z Hz. unfold pad' in Hz. rewrite Htp.
    replace (z <? pad) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (z <? pad + 3 * Z.of_N q) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity. }
  assert (Hb_sh : forall k, (k < 21)%N -> pad' <= (run_solo ag2 k (shift_scfg pad' gl0)).(spos)).
  { intros k Hk. pose proof (shift_run_solo ag2 k pad' gl0) as [Ap _].
    cbn [spos gl0 shift_scfg] in Ap. pose proof (C21b k Hk). lia. }
  rewrite Ht, run_solo_add.
  destruct (solo_depends_only_above ag2 r pad'
              (shift_scfg pad' gl0) (run_solo ag2 (21 * q) (shift_scfg pad gl0))
              ltac:(cbn [spos gl0 shift_scfg]; unfold pad'; lia) ltac:(cbn [sstate gl0 shift_scfg]; congruence)
              ltac:(intros z Hz; symmetry; apply Hsc_eq; exact Hz)
              ltac:(intros k Hk; apply Hb_sh; lia)) as [Ap _].
  pose proof (Hb_sh r Hr). unfold pad' in *. lia.
Qed.

Theorem agent2_glider_macro : forall dt0 T pad tp p2 s2,
  let sc_base := run_solo ag2 dt0 (shift_scfg pad gl0) in
  p2 = sc_base.(spos) ->
  s2 = sc_base.(sstate) ->
  (forall z, pad <= z -> tp z = sc_base.(stape) z) ->
  let sc := {| spos := p2; sstate := s2; stape := tp |} in
  let q := ((dt0 + T) / 21)%N in
  let dt1 := ((dt0 + T) mod 21)%N in
  let sc_end := run_solo ag2 dt1 (shift_scfg (pad + 3 * Z.of_N q) gl0) in
  (forall t, (t < T)%N -> pad <= (run_solo ag2 t sc).(spos)) /\
  (run_solo ag2 T sc).(spos) = sc_end.(spos) /\
  (run_solo ag2 T sc).(sstate) = sc_end.(sstate) /\
  (forall z, pad <= z < pad + 3 * Z.of_N q -> (run_solo ag2 T sc).(stape) z = true) /\
  (forall z, pad + 3 * Z.of_N q <= z -> (run_solo ag2 T sc).(stape) z = sc_end.(stape) z).
Proof.
  intros dt0 T pad tp p2 s2 sc_base Hp2 Hs2 Htp sc q dt1 sc_end.
  assert (Hdep : forall t,
    (run_solo ag2 t sc).(spos) = (run_solo ag2 t sc_base).(spos) /\
    (run_solo ag2 t sc).(sstate) = (run_solo ag2 t sc_base).(sstate) /\
    (forall z, pad <= z -> (run_solo ag2 t sc).(stape) z = (run_solo ag2 t sc_base).(stape) z)).
  { intro t.
    destruct (solo_depends_only_above ag2 t pad sc_base sc
                (eq_sym Hp2) (eq_sym Hs2) ltac:(intros z Hz; symmetry; apply Htp; exact Hz)
                ltac:(intros k _; unfold sc_base; rewrite <- run_solo_add; apply gl_never_left_of_pad))
      as [A [B C]].
    repeat split; auto; intros; symmetry; auto. }
  split.
  - intros t Ht. destruct (Hdep t) as [Ap _]. rewrite Ap.
    unfold sc_base. rewrite <- run_solo_add. apply gl_never_left_of_pad.
  - destruct (Hdep T) as [Ap [As Atp]].
    assert (Htot : (T + dt0 = dt1 + 21 * q)%N) by (unfold dt1, q; pose proof (N.div_mod (dt0 + T) 21 ltac:(lia)); lia).
    unfold sc_base in Ap, As, Atp. rewrite <- run_solo_add, Htot, run_solo_add in Ap, As, Atp.
    destruct (gl_mult21 q pad) as [_ [Mp [Ms Mtp]]].
    set (pad1 := pad + 3 * Z.of_N q).
    assert (Heq_pad1 : forall z, pad1 <= z ->
      (run_solo ag2 (21 * q) (shift_scfg pad gl0)).(stape) z = (shift_scfg pad1 gl0).(stape) z).
    { intros z Hz. unfold pad1 in Hz. rewrite Mtp.
      replace (z <? pad) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (z <? pad + 3 * Z.of_N q) with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity. }
    assert (Hb_dt1 : forall k,
      pad + 3 * Z.of_N q <= (run_solo ag2 k (run_solo ag2 (21 * q) (shift_scfg pad gl0))).(spos)).
    { intro k. destruct (solo_depends_only_above ag2 k (pad + 3 * Z.of_N q)
                         (shift_scfg (pad + 3 * Z.of_N q) gl0) (run_solo ag2 (21 * q) (shift_scfg pad gl0))
                         ltac:(cbn [spos gl0 shift_scfg]; lia) ltac:(cbn [sstate gl0 shift_scfg]; congruence)
                         ltac:(intros x Hx; symmetry; apply Heq_pad1; exact Hx)
                         ltac:(intros j _; apply gl_never_left_of_pad)) as [Jp _].
      rewrite <- Jp. apply gl_never_left_of_pad. }
    destruct (solo_depends_only_above ag2 dt1 pad1
                (run_solo ag2 (21 * q) (shift_scfg pad gl0))
                (shift_scfg pad1 gl0)
                ltac:(cbn [spos gl0 shift_scfg]; unfold pad1; lia) ltac:(cbn [sstate gl0 shift_scfg]; congruence) Heq_pad1
                ltac:(intros k _; apply Hb_dt1)) as [Ep [Es Etp]].
    unfold sc_end, pad1 in *.
    split; [congruence | split; [congruence | split]].
    + intros z Hz. rewrite Atp by lia.
      rewrite (solo_preserves_below ag2 dt1 (pad + 3 * Z.of_N q) _ (fun k _ => Hb_dt1 k) z ltac:(lia)).
      rewrite Mtp.
      replace (z <? pad) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (z <? pad + 3 * Z.of_N q) with true by (symmetry; apply Z.ltb_lt; lia).
      reflexivity.
    + intros z Hz. rewrite Atp by lia. apply Etp, Hz.
Qed.

(** * 6. Canonical Configurations, Phase A, and `+18*K` Phase B Shift *)

Definition round_tape (Z_cnt gap : Z) (dt : N) : Tape :=
  let pad := -1 + Z_cnt + gap in
  let gl  := run_solo ag2 dt (shift_scfg pad gl0) in
  fun z => if z <? -1 + Z_cnt then false
           else if z <? pad then true
           else gl.(stape) z.

Definition round_cfg (Z_cnt gap : Z) (dt : N) : Config :=
  let pad := -1 + Z_cnt + gap in
  let gl  := run_solo ag2 dt (shift_scfg pad gl0) in
  {| pos1 := -2; pos2 := gl.(spos); state1 := StC; state2 := gl.(sstate);
     tape := round_tape Z_cnt gap dt |}.

Definition bounce_tape (M : Z) (dt : N) : Tape :=
  let pad := -1 + M in
  let gl  := run_solo ag2 dt (shift_scfg pad gl0) in
  fun z => if z <? -1 then false
           else if z <? pad then true
           else gl.(stape) z.

Definition bounce_cfg (M : Z) (dt : N) : Config :=
  let pad := -1 + M in
  let gl  := run_solo ag2 dt (shift_scfg pad gl0) in
  {| pos1 := -1; pos2 := gl.(spos); state1 := StB; state2 := gl.(sstate);
     tape := bounce_tape M dt |}.

Lemma phase_A_sound : forall n : nat, (1 <= n)%nat -> forall gap : Z, 0 <= gap -> forall dt : N,
  let Z_cnt := Z.of_nat n in
  let T1 := counter_steps n in
  let q := ((dt + T1) / 21)%N in
  let dt_mid := ((dt + T1) mod 21)%N in
  let M := Z_cnt + gap + 3 * Z.of_N q in
  (forall t, (t < T1)%N ->
     (run_N t (round_cfg Z_cnt gap dt)).(pos1) <> (run_N t (round_cfg Z_cnt gap dt)).(pos2) /\
     ((run_N t (round_cfg Z_cnt gap dt)).(state1) = StB \/
      (run_N t (round_cfg Z_cnt gap dt)).(state1) = StC)) /\
  cfg_eq (run_N T1 (round_cfg Z_cnt gap dt)) (bounce_cfg M dt_mid).
Proof.
  intros n Hn gap Hgap dt Z_cnt T1 q dt_mid M.
  set (cut := -1 + Z_cnt).
  set (pad0 := -1 + Z_cnt + gap).
  set (s1 := {| spos := -2; sstate := StC; stape := empty_tape |}).
  set (gl_in := run_solo ag2 dt (shift_scfg pad0 gl0)).
  set (s2 := {| spos := gl_in.(spos); sstate := gl_in.(sstate);
                stape := fun z => if z <? pad0 then true else gl_in.(stape) z |}).
  destruct (agent1_counter n Hn empty_tape ltac:(intros; reflexivity))
    as [A1b [A1p [A1s A1tp]]].
  assert (Hpad_above : forall z, pad0 <= z -> s2.(stape) z = gl_in.(stape) z).
  { intros z Hz. cbn [stape s2]. replace (z <? pad0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  destruct (agent2_glider_macro dt T1 pad0 s2.(stape) s2.(spos) s2.(sstate)
              eq_refl eq_refl Hpad_above) as [A2b [A2p [A2s [A2fill A2tail]]]].
  assert (Hs2_eta : s2 = {| spos := s2.(spos); sstate := s2.(sstate); stape := s2.(stape) |}) by reflexivity.
  rewrite <- Hs2_eta in A2b, A2p, A2s, A2fill, A2tail.
  fold q in A2p, A2s, A2fill, A2tail.
  fold dt_mid in A2p, A2s, A2fill, A2tail.
  assert (Hb1 : forall t, (t < T1)%N -> (run_solo ag1 t s1).(spos) < cut).
  { intros t Ht. destruct (A1b t Ht) as [[_ Hlt] _]. exact Hlt. }
  assert (Hb2 : forall t, (t < T1)%N -> cut <= (run_solo ag2 t s2).(spos)).
  { intros t Ht. transitivity pad0; [unfold cut, pad0; lia | apply A2b, Ht]. }
  destruct (disjoint_split T1 cut (round_cfg Z_cnt gap dt) s1 s2
              eq_refl eq_refl eq_refl eq_refl
              ltac:(intros z Hz; unfold round_cfg, round_tape; cbn [tape stape s1];
                    unfold cut in Hz;
                    replace (z <? -1 + Z_cnt) with true by (symmetry; apply Z.ltb_lt; lia);
                    reflexivity)
              ltac:(intros z Hz; unfold round_cfg, round_tape; cbn [tape stape s2];
                    unfold cut, pad0 in *;
                    replace (z <? -1 + Z_cnt) with false by (symmetry; apply Z.ltb_ge; lia);
                    destruct (Z.ltb_spec z (-1 + Z_cnt + gap)); reflexivity)
              Hb1 Hb2) as [Hsplit Hnocoll].
  split.
  - intros t Ht. split; [apply Hnocoll, Ht|].
    destruct (Hsplit t ltac:(lia)) as [_ [Hs1 _]]. rewrite Hs1.
    destruct (A1b t Ht) as [_ Hs]. exact Hs.
  - destruct (Hsplit T1 ltac:(lia)) as [P1 [S1 [P2 [S2 [TL TR]]]]].
    assert (Hpad1 : pad0 + 3 * Z.of_N q = -1 + M) by (unfold pad0, M, Z_cnt; lia).
    constructor; cbn [pos1 pos2 state1 state2 tape bounce_cfg];
      try rewrite P1; try rewrite P2; try rewrite S1; try rewrite S2.
    + exact A1p.
    + rewrite A2p, Hpad1. reflexivity.
    + exact A1s.
    + rewrite A2s, Hpad1. reflexivity.
    + intro z. unfold bounce_tape.
      destruct (Z.lt_ge_cases z cut) as [HzL | HzR].
      * rewrite (TL z HzL), A1tp. unfold empty_tape. fold Z_cnt.
        destruct (Z.leb_spec (-1) z), (Z.ltb_spec z (-1 + Z_cnt)),
                 (Z.ltb_spec z (-1)), (Z.ltb_spec z (-1 + M));
          unfold cut, M, Z_cnt in *; try lia; reflexivity.
      * rewrite (TR z HzR).
        destruct (Z.ltb_spec z (-1)), (Z.ltb_spec z (-1 + M)); try lia.
        -- destruct (Z.lt_ge_cases z pad0) as [Hzp | Hzp].
           ++ rewrite (solo_preserves_below ag2 T1 pad0 s2 A2b z Hzp).
              cbn [stape s2]. replace (z <? pad0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
           ++ apply A2fill. unfold pad0, M, Z_cnt in *; lia.
        -- rewrite A2tail by (unfold pad0, M, Z_cnt in *; lia). rewrite Hpad1. reflexivity.
Qed.

Lemma bounce_shift_21 : forall M : Z, 21 <= M -> forall dt : N, (dt < 21)%N ->
  (forall t, (t < 21)%N ->
     (run_N t (bounce_cfg M dt)).(pos1) <> (run_N t (bounce_cfg M dt)).(pos2) /\
     (run_N t (bounce_cfg M dt)).(state1) = StB /\
     -1 <= (run_N t (bounce_cfg M dt)).(pos1) /\
     -1 <= (run_N t (bounce_cfg M dt)).(pos2)) /\
  (forall z, z < -1 -> (run_N 21 (bounce_cfg M dt)).(tape) z = false) /\
  (forall z, -1 <= z < 20 -> (run_N 21 (bounce_cfg M dt)).(tape) z = true) /\
  (forall z, 20 <= z -> (run_N 21 (bounce_cfg M dt)).(tape) z =
                        (shift_cfg 21 (bounce_cfg (M - 18) dt)).(tape) z) /\
  (run_N 21 (bounce_cfg M dt)).(pos1) = (shift_cfg 21 (bounce_cfg (M - 18) dt)).(pos1) /\
  (run_N 21 (bounce_cfg M dt)).(pos2) = (shift_cfg 21 (bounce_cfg (M - 18) dt)).(pos2) /\
  (run_N 21 (bounce_cfg M dt)).(state1) = StB /\
  (run_N 21 (bounce_cfg M dt)).(state2) = (shift_cfg 21 (bounce_cfg (M - 18) dt)).(state2).
Proof.
  intros M HM dt Hdt.
  set (cut := 20).
  set (pad0 := -1 + M).
  set (s1 := {| spos := -1; sstate := StB;
                stape := fun z => if (-1 <=? z) && (z <? 20) then true else false |}).
  set (gl_in := run_solo ag2 dt (shift_scfg pad0 gl0)).
  set (s2 := {| spos := gl_in.(spos); sstate := gl_in.(sstate);
                stape := fun z => if z <? pad0 then true else gl_in.(stape) z |}).
  destruct (B_walk_right 21 (-1) s1.(stape) StB eq_refl
              ltac:(intros z Hz; cbn [stape s1];
                    replace (-1 <=? z) with true by (symmetry; apply Z.leb_le; lia);
                    replace (z <? 20) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity))
    as [BRb [BRp [BRs BRtp]]].
  assert (Hs1_eta : s1 = {| spos := -1; sstate := StB; stape := s1.(stape) |}) by reflexivity.
  rewrite <- Hs1_eta in BRb, BRp, BRs, BRtp.
  change (N.of_nat 21) with 21%N in BRb, BRp, BRs, BRtp.
  assert (Hpad_above : forall z, pad0 <= z -> s2.(stape) z = gl_in.(stape) z).
  { intros z Hz. cbn [stape s2]. replace (z <? pad0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  destruct (agent2_glider_macro dt 21 pad0 s2.(stape) s2.(spos) s2.(sstate)
              eq_refl eq_refl Hpad_above) as [A2b [A2p [A2s [A2fill A2tail]]]].
  assert (Hs2_eta : s2 = {| spos := s2.(spos); sstate := s2.(sstate); stape := s2.(stape) |}) by reflexivity.
  rewrite <- Hs2_eta in A2b, A2p, A2s, A2fill, A2tail.
  assert (Hb1 : forall t, (t < 21)%N -> (run_solo ag1 t s1).(spos) < cut).
  { intros t Ht. destruct (BRb t ltac:(exact Ht)) as [Hp _]. unfold cut; lia. }
  assert (Hb2 : forall t, (t < 21)%N -> cut <= (run_solo ag2 t s2).(spos)).
  { intros t Ht. transitivity pad0; [unfold cut, pad0; lia | apply A2b, Ht]. }
  destruct (disjoint_split 21 cut (bounce_cfg M dt) s1 s2
              eq_refl eq_refl eq_refl eq_refl
              ltac:(intros z Hz; unfold bounce_cfg, bounce_tape; cbn [tape stape s1];
                    unfold cut, pad0 in *;
                    destruct (Z.ltb_spec z (-1)), (Z.leb_spec (-1) z),
                             (Z.ltb_spec z 20), (Z.ltb_spec z (-1 + M));
                      try lia; reflexivity)
              ltac:(intros z Hz; unfold bounce_cfg, bounce_tape; cbn [tape stape s2];
                    unfold cut, pad0 in *;
                    destruct (Z.ltb_spec z (-1)), (Z.ltb_spec z (-1 + M));
                      try lia; reflexivity)
              Hb1 Hb2) as [Hsplit Hnocoll].
  assert (Hq1 : ((dt + 21) / 21 = 1 /\ (dt + 21) mod 21 = dt)%N).
  { generalize (N.div_mod (dt + 21) 21 ltac:(lia)) (N.mod_lt (dt + 21) 21 ltac:(lia)).
    change (dt + 21 = 21 * ((dt + 21) / 21) + (dt + 21) mod 21 -> ((dt + 21) mod 21 < 21) -> ((dt + 21) / 21 = 1 /\ (dt + 21) mod 21 = dt))%N;
    generalize ((dt + 21) / 21)%N ((dt + 21) mod 21)%N; intros q r H1 H2; lia. }
  destruct Hq1 as [Hq_eq Hr_eq].
  rewrite Hq_eq in A2p, A2s, A2fill, A2tail.
  rewrite Hr_eq in A2p, A2s, A2tail.
  assert (Hsh_gl : scfg_eq (run_solo ag2 dt (shift_scfg (pad0 + 3 * Z.of_N 1) gl0))
                           (shift_scfg 21 (run_solo ag2 dt (shift_scfg (-1 + (M - 18)) gl0)))).
  { pose proof (shift_run_solo ag2 dt 21 (shift_scfg (-1 + (M - 18)) gl0)) as Hsh.
    assert (Hbase : scfg_eq (shift_scfg (pad0 + 3 * Z.of_N 1) gl0)
                            (shift_scfg 21 (shift_scfg (-1 + (M - 18)) gl0))).
    { unfold scfg_eq, shift_scfg, gl0; cbn [spos sstate stape].
      split; [unfold pad0; lia | split; [reflexivity|]].
      intro z. unfold pad0. f_equal. lia. }
    pose proof (run_solo_proper ag2 dt _ _ Hbase) as [Rp [Rs Rtp]].
    destruct Hsh as [Sp [Ss Stp]].
    split; [lia | split; [congruence | intro z; rewrite (Rtp z), (Stp z); reflexivity]]. }
  destruct Hsh_gl as [G2p [G2s G2tp]].
  split.
  - intros t Ht. destruct (Hsplit t ltac:(lia)) as [P1 [S1 [P2 _]]].
    destruct (BRb t ltac:(exact Ht)) as [Bp Bs].
    assert (B2 : pad0 <= (run_solo ag2 t s2).(spos)) by (apply A2b, Ht).
    repeat split; [apply Hnocoll, Ht | congruence | lia | unfold pad0 in *; lia].
  - destruct (Hsplit 21%N ltac:(lia)) as [P1 [S1 [P2 [S2 [TL TR]]]]].
    split; [intros z Hz; rewrite (TL z ltac:(lia)), (BRtp z); cbn [stape s1];
            destruct (Z.leb_spec (-1) z); try lia; reflexivity|].
    split; [intros z Hz; rewrite (TL z ltac:(lia)), (BRtp z); cbn [stape s1];
            replace (-1 <=? z) with true by (symmetry; apply Z.leb_le; lia);
            replace (z <? 20) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
    split.
    + intros z Hz. rewrite (TR z Hz).
      unfold shift_cfg, bounce_cfg, bounce_tape; cbn [tape].
      replace (z - 21 <? -1) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (Z.lt_ge_cases z pad0) as [Hzp | Hzp].
      * rewrite (solo_preserves_below ag2 21 pad0 s2 A2b z Hzp).
        cbn [stape s2]. replace (z <? pad0) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (z - 21 <? -1 + (M - 18)) with true by (symmetry; apply Z.ltb_lt; unfold pad0 in *; lia).
        reflexivity.
      * destruct (Z.lt_ge_cases z (pad0 + 3 * Z.of_N 1)) as [Hz3 | Hz3].
        -- rewrite (A2fill z ltac:(lia)).
           replace (z - 21 <? -1 + (M - 18)) with true by (symmetry; apply Z.ltb_lt; unfold pad0 in *; lia).
           reflexivity.
        -- rewrite (A2tail z ltac:(lia)), G2tp.
           replace (z - 21 <? -1 + (M - 18)) with false by (symmetry; apply Z.ltb_ge; unfold pad0 in *; lia).
           reflexivity.
    + rewrite P1, P2, S1, S2. unfold shift_cfg, bounce_cfg; cbn [pos1 pos2 state1 state2].
      split; [rewrite BRp; lia | split; [rewrite A2p, G2p; reflexivity | split; [exact BRs | rewrite A2s, G2s; reflexivity]]].
Qed.

Lemma bounce_forward_K : forall M_rep : Z, 21 <= M_rep -> forall dt : N, (dt < 21)%N -> forall K : N,
  let M := M_rep + 18 * Z.of_N K in
  let sh := 21 * Z.of_N K in
  (forall t, (t < 21 * K)%N ->
     (run_N t (bounce_cfg M dt)).(pos1) <> (run_N t (bounce_cfg M dt)).(pos2) /\
     (run_N t (bounce_cfg M dt)).(state1) = StB /\
     -1 <= (run_N t (bounce_cfg M dt)).(pos1) /\
     -1 <= (run_N t (bounce_cfg M dt)).(pos2)) /\
  (forall z, z < -1 -> (run_N (21 * K) (bounce_cfg M dt)).(tape) z = false) /\
  (forall z, -1 <= z < -1 + sh -> (run_N (21 * K) (bounce_cfg M dt)).(tape) z = true) /\
  (forall z, -1 + sh <= z ->
     (run_N (21 * K) (bounce_cfg M dt)).(tape) z =
     (shift_cfg sh (bounce_cfg M_rep dt)).(tape) z) /\
  (run_N (21 * K) (bounce_cfg M dt)).(pos1) = (shift_cfg sh (bounce_cfg M_rep dt)).(pos1) /\
  (run_N (21 * K) (bounce_cfg M dt)).(pos2) = (shift_cfg sh (bounce_cfg M_rep dt)).(pos2) /\
  (run_N (21 * K) (bounce_cfg M dt)).(state1) = (shift_cfg sh (bounce_cfg M_rep dt)).(state1) /\
  (run_N (21 * K) (bounce_cfg M dt)).(state2) = (shift_cfg sh (bounce_cfg M_rep dt)).(state2).
Proof.
  intros M_rep HM dt Hdt K. induction K using N.peano_ind; intros M sh.
  - assert (H0 : (21 * 0 = 0)%N /\ sh = 0 /\ M = M_rep) by (unfold sh, M; lia).
    destruct H0 as [Ht0 [Hsh HMeq]]. rewrite Ht0, Hsh, HMeq, run_N_0.
    split; [intros t Ht; lia|].
    split; [intros z Hz; unfold bounce_cfg, bounce_tape; cbn [tape];
            replace (z <? -1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
    split; [intros z Hz; lia|].
    split; [intros z _; unfold shift_cfg; cbn [tape]; replace (z - 0) with z by lia; reflexivity|].
    unfold shift_cfg; cbn [pos1 pos2 state1 state2]; repeat split; lia.
  - destruct IHK as [IHb [IHlt [IHmid [IHge [IHp1 [IHp2 [IHs1 IHs2]]]]]]].
    set (M_prev := M_rep + 18 * Z.of_N K).
    set (sh_prev := 21 * Z.of_N K).
    fold M_prev in IHb, IHlt, IHmid, IHge, IHp1, IHp2, IHs1, IHs2.
    fold sh_prev in IHb, IHlt, IHmid, IHge, IHp1, IHp2, IHs1, IHs2.
    assert (HM_ge : 21 <= M) by (unfold M; lia).
    destruct (bounce_shift_21 M HM_ge dt Hdt) as [B1b [B1lt [B1mid [B1ge [B1p1 [B1p2 [B1s1 B1s2]]]]]]].
    replace (M - 18) with M_prev in B1ge, B1p1, B1p2, B1s2 by (unfold M, M_prev; lia).
    set (c21 := run_N 21 (bounce_cfg M dt)).
    set (c_sh := shift_cfg 21 (bounce_cfg M_prev dt)).
    assert (Hsh_bnd : forall t, (t < 21 * K)%N ->
      20 <= (run_N t c_sh).(pos1) /\ 20 <= (run_N t c_sh).(pos2)).
    { intros t Ht. destruct (shift_run t 21 (bounce_cfg M_prev dt)) as [Sp1 Sp2 _ _ _].
      unfold c_sh. rewrite Sp1, Sp2. unfold shift_cfg; cbn [pos1 pos2].
      destruct (IHb t Ht) as [_ [_ [Hlo1 Hlo2]]]. split; lia. }
    assert (Hdep : forall t, (t <= 21 * K)%N ->
      (run_N t c21).(pos1) = (run_N t c_sh).(pos1) /\
      (run_N t c21).(pos2) = (run_N t c_sh).(pos2) /\
      (run_N t c21).(state1) = (run_N t c_sh).(state1) /\
      (run_N t c21).(state2) = (run_N t c_sh).(state2) /\
      (forall z, 20 <= z -> (run_N t c21).(tape) z = (run_N t c_sh).(tape) z)).
    { pose proof (full_run_depends_only_above (21 * K) 20 c_sh c21 ltac:(unfold c21, c_sh; symmetry; exact B1p1)
                    ltac:(unfold c21, c_sh; symmetry; exact B1p2)
                    ltac:(unfold c21, c_sh, shift_cfg, bounce_cfg; cbn [state1]; symmetry; exact B1s1)
                    ltac:(unfold c21, c_sh; symmetry; exact B1s2)
                    ltac:(intros z Hz; unfold c21, c_sh; symmetry; exact (B1ge z Hz)) Hsh_bnd) as Hdep'.
      intros t Ht. destruct (Hdep' t Ht) as [A [B [C [D E]]]].
      repeat split; symmetry; auto. }
    assert (Hpres : forall z, z < 20 -> (run_N (21 * K) c21).(tape) z = c21.(tape) z).
    { apply full_preserves_below. intros t Ht.
      destruct (Hdep t ltac:(lia)) as [Dp1 [Dp2 _]]. rewrite Dp1, Dp2. apply Hsh_bnd, Ht. }
    replace (21 * N.succ K)%N with (21 * K + 21)%N by lia.
    split.
    + intros t Ht.
      destruct (N.lt_ge_cases t 21) as [Ht1 | Hge1].
      * apply B1b, Ht1.
      * replace t with ((t - 21) + 21)%N by lia. rewrite run_N_add.
        change (run_N 21 (bounce_cfg M dt)) with c21.
        destruct (Hdep (t - 21)%N ltac:(lia)) as [Dp1 [Dp2 [Ds1 _]]].
        destruct (shift_run (t - 21)%N 21 (bounce_cfg M_prev dt)) as [Sp1 Sp2 Ss1 _ _].
        destruct (IHb (t - 21)%N ltac:(lia)) as [Ic [Is1 [Ilo1 Ilo2]]].
        rewrite Dp1, Dp2, Ds1. unfold c_sh. rewrite Sp1, Sp2, Ss1.
        unfold shift_cfg; cbn [pos1 pos2 state1].
        repeat split; try lia; exact Is1.
    + rewrite run_N_add. change (run_N 21 (bounce_cfg M dt)) with c21.
      destruct (Hdep (21 * K)%N ltac:(lia)) as [Fp1 [Fp2 [Fs1 [Fs2 Ftp]]]].
      destruct (shift_run (21 * K)%N 21 (bounce_cfg M_prev dt)) as [Sp1 Sp2 Ss1 Ss2 Stp].
      split; [intros z Hz; rewrite (Hpres z ltac:(lia)); apply B1lt, Hz|].
      split.
      * intros z Hz. destruct (Z.lt_ge_cases z 20) as [Hz20 | Hzge20].
        -- rewrite (Hpres z Hz20). apply B1mid. lia.
        -- rewrite (Ftp z Hzge20). unfold c_sh. rewrite (Stp z). unfold shift_cfg at 1; cbn [tape].
           apply IHmid. unfold sh_prev, sh in *; lia.
      * split.
        { intros z Hz. rewrite (Ftp z ltac:(unfold sh in *; lia)). unfold c_sh. rewrite (Stp z).
          unfold shift_cfg at 1; cbn [tape].
          rewrite (IHge (z - 21) ltac:(unfold sh_prev, sh in *; lia)).
          unfold shift_cfg; cbn [tape].
          replace (z - 21 - sh_prev) with (z - sh) by (unfold sh_prev, sh; lia). reflexivity. }
        rewrite Fp1, Fp2, Fs1, Fs2. unfold c_sh. rewrite Sp1, Sp2, Ss1, Ss2.
        unfold shift_cfg; cbn [pos1 pos2 state1 state2].
        rewrite IHp1, IHp2, IHs1, IHs2.
        unfold shift_cfg; cbn [pos1 pos2 state1 state2].
        repeat split; try (unfold sh_prev, sh; lia); reflexivity.
Qed.

(** Return phase: `21 * K` steps of `<C 1 -> 0 L C` + `K` glider cycles *)
Lemma bounce_return_K : forall Z_rep gap_rep : Z, 1 <= Z_rep -> 0 <= gap_rep ->
  forall dt_out : N, (dt_out < 21)%N -> forall K : N,
  let sh := 21 * Z.of_N K in
  forall c,
    c.(pos1) = -2 + sh ->
    c.(pos2) = (shift_cfg sh (round_cfg Z_rep gap_rep dt_out)).(pos2) ->
    c.(state1) = StC ->
    c.(state2) = (shift_cfg sh (round_cfg Z_rep gap_rep dt_out)).(state2) ->
    (forall z, z < -1 -> c.(tape) z = false) ->
    (forall z, -1 <= z < -1 + sh -> c.(tape) z = true) ->
    (forall z, -1 + sh <= z -> c.(tape) z = (shift_cfg sh (round_cfg Z_rep gap_rep dt_out)).(tape) z) ->
    (forall t, (t < 21 * K)%N ->
       (run_N t c).(pos1) <> (run_N t c).(pos2) /\
       (run_N t c).(state1) = StC) /\
    cfg_eq (run_N (21 * K) c) (round_cfg (Z_rep + sh) (gap_rep + 3 * Z.of_N K) dt_out).
Proof.
  intros Z_rep gap_rep HZ Hgap dt_out Hdt K sh c Hp1 Hp2 Hs1 Hs2 Hlt Hmid Hge.
  set (cut := -1 + sh).
  set (pad0 := -1 + sh + Z_rep + gap_rep).
  set (s1 := {| spos := -2 + sh; sstate := StC;
                stape := fun z => if (-1 <=? z) && (z <? cut) then true else false |}).
  set (gl_in := run_solo ag2 dt_out (shift_scfg pad0 gl0)).
  set (s2 := {| spos := gl_in.(spos); sstate := gl_in.(sstate);
                stape := fun z => if z <? -1 + sh + Z_rep then false
                                  else if z <? pad0 then true
                                  else gl_in.(stape) z |}).
  assert (Hsh_nat : Z.of_nat (N.to_nat (21 * K)) = sh) by (unfold sh; lia).
  assert (HC_in : forall z, (-2 + sh) - Z.of_nat (N.to_nat (21 * K)) < z <= -2 + sh -> s1.(stape) z = true).
  { intros z Hz. rewrite Hsh_nat in Hz. cbn [stape s1].
    replace (-1 <=? z) with true by (symmetry; apply Z.leb_le; lia).
    replace (z <? cut) with true by (symmetry; apply Z.ltb_lt; unfold cut; lia). reflexivity. }
  destruct (C_walk_left (N.to_nat (21 * K)) (-2 + sh) s1.(stape) StC eq_refl HC_in)
    as [CLb [CLp [CLs CLtp]]].
  assert (Hs1_eta : s1 = {| spos := -2 + sh; sstate := StC; stape := s1.(stape) |}) by reflexivity.
  rewrite <- Hs1_eta in CLb, CLp, CLs, CLtp.
  rewrite N2Nat.id in CLb, CLp, CLs, CLtp.
  rewrite Hsh_nat in CLp, CLtp.
  assert (Hpad_above : forall z, pad0 <= z -> s2.(stape) z = gl_in.(stape) z).
  { intros z Hz. cbn [stape s2].
    replace (z <? -1 + sh + Z_rep) with false by (symmetry; apply Z.ltb_ge; unfold pad0 in *; lia).
    replace (z <? pad0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  destruct (agent2_glider_macro dt_out (21 * K) pad0 s2.(stape) s2.(spos) s2.(sstate)
              eq_refl eq_refl Hpad_above) as [A2b [A2p [A2s [A2fill A2tail]]]].
  assert (Hs2_eta : s2 = {| spos := s2.(spos); sstate := s2.(sstate); stape := s2.(stape) |}) by reflexivity.
  rewrite <- Hs2_eta in A2b, A2p, A2s, A2fill, A2tail.
  assert (HqK : ((dt_out + 21 * K) / 21 = K /\ (dt_out + 21 * K) mod 21 = dt_out)%N).
  { generalize (N.div_mod (dt_out + 21 * K) 21 ltac:(lia)) (N.mod_lt (dt_out + 21 * K) 21 ltac:(lia)).
    generalize ((dt_out + 21 * K) / 21)%N ((dt_out + 21 * K) mod 21)%N; intros q r H1 H2; lia. }
  destruct HqK as [Hq_eq Hr_eq].
  rewrite Hq_eq in A2p, A2s, A2fill, A2tail.
  rewrite Hr_eq in A2p, A2s, A2tail.
  assert (Hsh_gl_in : scfg_eq (shift_scfg sh (run_solo ag2 dt_out (shift_scfg (-1 + Z_rep + gap_rep) gl0))) gl_in).
  { pose proof (shift_run_solo ag2 dt_out sh (shift_scfg (-1 + Z_rep + gap_rep) gl0)) as [Sp [Ss Stp]].
    assert (Hbase : scfg_eq (shift_scfg sh (shift_scfg (-1 + Z_rep + gap_rep) gl0)) (shift_scfg pad0 gl0)).
    { unfold scfg_eq, shift_scfg, gl0; cbn [spos sstate stape].
      split; [unfold pad0; lia | split; [reflexivity|]].
      intro z. unfold pad0. replace (z - sh - (-1 + Z_rep + gap_rep)) with (z - (-1 + sh + Z_rep + gap_rep)) by lia. reflexivity. }
    pose proof (run_solo_proper ag2 dt_out _ _ Hbase) as [Rp [Rs Rtp]].
    split; [unfold gl_in; lia | split; [unfold gl_in; congruence | intro z; unfold gl_in; rewrite <- (Rtp z), (Stp z); reflexivity]]. }
  destruct Hsh_gl_in as [Gin_p [Gin_s Gin_tp]].
  assert (Hp2_eq : c.(pos2) = s2.(spos)).
  { rewrite Hp2. unfold shift_cfg, round_cfg; cbn [pos2]. exact Gin_p. }
  assert (Hs2_eq : c.(state2) = s2.(sstate)).
  { rewrite Hs2. unfold shift_cfg, round_cfg; cbn [state2]. exact Gin_s. }
  assert (Hleft_eq : forall z, z < cut -> c.(tape) z = s1.(stape) z).
  { intros z Hz. cbn [stape s1]. destruct (Z.lt_ge_cases z (-1)) as [Hz1 | Hzge1].
    - rewrite (Hlt z Hz1). replace (-1 <=? z) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - rewrite (Hmid z ltac:(unfold cut in *; lia)).
      replace (-1 <=? z) with true by (symmetry; apply Z.leb_le; lia).
      replace (z <? cut) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  assert (Hright_eq : forall z, cut <= z -> c.(tape) z = s2.(stape) z).
  { intros z Hz. rewrite (Hge z ltac:(unfold cut in *; lia)).
    unfold shift_cfg, round_cfg, round_tape; cbn [tape].
    cbn [stape s2]. unfold pad0.
    destruct (Z.ltb_spec (z - sh) (-1 + Z_rep));
      destruct (Z.ltb_spec z (-1 + sh + Z_rep)); try lia; auto.
    destruct (Z.ltb_spec (z - sh) (-1 + Z_rep + gap_rep));
      destruct (Z.ltb_spec z (-1 + sh + Z_rep + gap_rep)); try lia; auto.
    exact (Gin_tp z). }
  assert (Hb1 : forall t, (t < 21 * K)%N -> (run_solo ag1 t s1).(spos) < cut).
  { intros t Ht. destruct (CLb t ltac:(lia)) as [Hp _]. unfold cut; lia. }
  assert (Hb2 : forall t, (t < 21 * K)%N -> cut <= (run_solo ag2 t s2).(spos)).
  { intros t Ht. transitivity pad0; [unfold cut, pad0; lia | apply A2b, Ht]. }
  destruct (disjoint_split (21 * K) cut c s1 s2 Hp1 Hs1 Hp2_eq Hs2_eq Hleft_eq Hright_eq Hb1 Hb2)
    as [Hsplit Hnocoll].
  split.
  - intros t Ht. split; [apply Hnocoll, Ht|].
    destruct (Hsplit t ltac:(lia)) as [_ [Hs1t _]]. rewrite Hs1t.
    destruct (CLb t ltac:(lia)) as [_ Hs]. exact Hs.
  - destruct (Hsplit (21 * K)%N ltac:(lia)) as [P1 [S1 [P2 [S2 [TL TR]]]]].
    assert (Hpad_end : -1 + (Z_rep + sh) + (gap_rep + 3 * Z.of_N K) = pad0 + 3 * Z.of_N K) by (unfold pad0; lia).
    constructor; unfold round_cfg; cbn [pos1 pos2 state1 state2 tape];
      rewrite ?Hpad_end, ?P1, ?P2, ?S1, ?S2.
    + rewrite CLp; lia.
    + exact A2p.
    + exact CLs.
    + exact A2s.
    + intro z. unfold round_tape. rewrite Hpad_end.
      destruct (Z.lt_ge_cases z cut) as [HzL | HzR].
      * rewrite (TL z HzL), CLtp. cbn [stape s1].
        destruct (Z.ltb_spec (-2 + sh - sh) z), (Z.leb_spec z (-2 + sh)),
                 (Z.leb_spec (-1) z), (Z.ltb_spec z cut),
                 (Z.ltb_spec z (-1 + (Z_rep + sh))); unfold cut in *; try lia; reflexivity.
      * rewrite (TR z HzR). destruct (Z.lt_ge_cases z pad0) as [Hzp | Hzp].
        -- rewrite (solo_preserves_below ag2 (21 * K) pad0 s2 A2b z Hzp). cbn [stape s2].
           unfold pad0 in *.
           destruct (Z.ltb_spec z (-1 + sh + Z_rep)), (Z.ltb_spec z (-1 + sh + Z_rep + gap_rep)),
                    (Z.ltb_spec z (-1 + (Z_rep + sh))), (Z.ltb_spec z (-1 + sh + Z_rep + gap_rep + 3 * Z.of_N K));
             try lia; reflexivity.
        -- destruct (Z.lt_ge_cases z (pad0 + 3 * Z.of_N K)) as [Hz3 | Hz3].
           ++ rewrite (A2fill z ltac:(lia)).
              destruct (Z.ltb_spec z (-1 + (Z_rep + sh))), (Z.ltb_spec z (pad0 + 3 * Z.of_N K));
                unfold pad0 in *; try lia; reflexivity.
           ++ rewrite (A2tail z ltac:(lia)).
              destruct (Z.ltb_spec z (-1 + (Z_rep + sh))), (Z.ltb_spec z (pad0 + 3 * Z.of_N K));
                unfold pad0 in *; try lia; reflexivity.
Qed.

(** ** 6b. Concrete Base-Bounce Lifting and Round Transition *)

Lemma full_preserves_outside : forall n lo hi c,
  (forall t, (t < n)%N -> lo <= (run_N t c).(pos1) < hi /\ lo <= (run_N t c).(pos2) < hi) ->
  forall z, z < lo \/ hi <= z -> (run_N n c).(tape) z = c.(tape) z.
Proof.
  intro n. induction n using N.peano_ind; intros lo hi c Hbnd z Hz; auto.
  rewrite run_N_succ. unfold step; simpl.
  pose proof (Hbnd n ltac:(lia)) as [[H1a H1b] [H2a H2b]].
  rewrite !write_tape_other by lia.
  apply (IHn lo hi); auto. intros t Ht. apply Hbnd. lia.
Qed.

Lemma iter_chk_snd : forall {A : Type} (stepf : A -> A) (pred : A -> bool) (n : N) (a : bool) (b : A),
  snd (N.iter n (fun '(ok, x) => (ok && pred x, stepf x)) (a, b)) = N.iter n stepf b.
Proof.
  intros A stepf pred n. induction n using N.peano_ind; intros a b; [reflexivity|].
  rewrite !N.iter_succ.
  destruct (N.iter n (fun '(ok, x) => (ok && pred x, stepf x)) (a, b)) as [a' b'] eqn:En.
  pose proof (IHn a b) as Hn. rewrite En in Hn. simpl in *. congruence.
Qed.

Lemma gl_outside_10 : forall dt pad z, (dt < 21)%N ->
  z < pad \/ pad + 10 <= z ->
  (run_solo ag2 dt (shift_scfg pad gl0)).(stape) z = false.
Proof.
  intros dt pad z Hdt Hz.
  destruct (shift_run_solo ag2 dt pad gl0) as [_ [_ Stp]].
  rewrite (Stp z). unfold shift_scfg; cbn [stape].
  destruct gl21_cycle_step as [Hgl _].
  rewrite (solo_preserves_outside ag2 dt 0 10 gl0
             (fun t Ht => Hgl t ltac:(lia)) (z - pad) ltac:(lia)).
  cbn [gl0 stape]. unfold gl0_tape.
  destruct (Z.eqb_spec (z - pad) 1), (Z.eqb_spec (z - pad) 2), (Z.eqb_spec (z - pad) 3); try lia; reflexivity.
Qed.

Lemma run_gl_from_bt : forall (pad : Z) (dt : N) (bt0 : BTree),
  (dt < 21)%N ->
  (forall z, pad <= z -> bt_interp bt0 z = gl0_tape (z - pad)) ->
  let '(p2, s2, bt2) := N.iter dt fast_step2 (pad + 1, StB, bt0) in
  let gl := run_solo ag2 dt (shift_scfg pad gl0) in
  p2 = gl.(spos) /\ s2 = gl.(sstate) /\
  (forall z, pad <= z -> bt_interp bt2 z = gl.(stape) z) /\
  (forall z, z < pad -> bt_interp bt2 z = bt_interp bt0 z).
Proof.
  intros pad dt bt0 Hdt Habove.
  destruct (N.iter dt fast_step2 (pad + 1, StB, bt0)) as [[p2 s2] bt2] eqn:En.
  pose proof (fast_run2_sound dt (pad + 1, StB, bt0)) as [Ap [As Atp]].
  rewrite En in Ap, As, Atp. cbn [f2_to_scfg spos sstate stape] in Ap, As, Atp.
  set (sc_bt := {| spos := pad + 1; sstate := StB; stape := bt_interp bt0 |}).
  assert (Hbnd_gl : forall k, pad <= (run_solo ag2 k (shift_scfg pad gl0)).(spos)).
  { intro k. apply gl_never_left_of_pad. }
  assert (Hdep : forall t,
    (run_solo ag2 t (shift_scfg pad gl0)).(spos) = (run_solo ag2 t sc_bt).(spos) /\
    (run_solo ag2 t (shift_scfg pad gl0)).(sstate) = (run_solo ag2 t sc_bt).(sstate) /\
    (forall z, pad <= z -> (run_solo ag2 t (shift_scfg pad gl0)).(stape) z = (run_solo ag2 t sc_bt).(stape) z)).
  { intro t.
    apply (solo_depends_only_above ag2 t pad (shift_scfg pad gl0) sc_bt).
    - cbn [shift_scfg gl0 sc_bt spos]; lia.
    - cbn [shift_scfg gl0 sc_bt sstate]; reflexivity.
    - intros z Hz. cbn [shift_scfg gl0 sc_bt stape]. symmetry; apply Habove, Hz.
    - intros k _. apply Hbnd_gl. }
  destruct (Hdep dt) as [Dp [Ds Dtp]].
  unfold sc_bt in Dp, Ds, Dtp.
  assert (Hpres : forall z, z < pad -> (run_solo ag2 dt sc_bt).(stape) z = bt_interp bt0 z).
  { apply solo_preserves_below. intros k _. destruct (Hdep k) as [Kp _]. rewrite <- Kp. apply Hbnd_gl. }
  repeat split.
  - lia.
  - congruence.
  - intros z Hz. rewrite (Atp z). symmetry; apply Dtp, Hz.
  - intros z Hz. rewrite (Atp z). apply Hpres, Hz.
Qed.

Definition mk_bounce_bt (M : Z) : BTree :=
  bt_set_list (-1 + M) [false; true; true; true] (bt_set_range (-1) (Z.to_N M) true BEmpty).

Definition fast_bounce_cfg (M : Z) (dt : N) : FastConfig :=
  let '(p2, s2, bt) := N.iter dt fast_step2 (-1 + M + 1, StB, mk_bounce_bt M) in
  {| fpos1 := -1; fpos2 := p2; fstate1 := StB; fstate2 := s2; ftape := bt |}.

Lemma fast_bounce_cfg_sound : forall M : Z, 0 <= M -> forall dt : N, (dt < 21)%N ->
  cfg_eq (fc_to_cfg (fast_bounce_cfg M dt)) (bounce_cfg M dt).
Proof.
  intros M HM dt Hdt. unfold fast_bounce_cfg.
  assert (Hbt0 : forall z, bt_interp (mk_bounce_bt M) z = bounce_tape M 0 z).
  { intro z. unfold mk_bounce_bt, bounce_tape.
    rewrite bt_interp_set_list, bt_interp_set_range.
    unfold bt_interp; rewrite bt_get_empty.
    rewrite run_solo_0. cbn [gl0 shift_scfg stape length]. change (Z.of_nat 4) with 4.
    replace (Z.of_N (Z.to_N M)) with M by lia.
    destruct (Z.leb_spec (-1 + M) z), (Z.ltb_spec z (-1 + M + 4)),
             (Z.leb_spec (-1) z), (Z.ltb_spec z (-1 + M)), (Z.ltb_spec z (-1)); try lia; auto.
    - unfold gl0_tape.
      assert (z - (-1 + M) = 0 \/ z - (-1 + M) = 1 \/ z - (-1 + M) = 2 \/ z - (-1 + M) = 3)
        as [Hidx | [Hidx | [Hidx | Hidx]]] by lia; rewrite Hidx; reflexivity.
    - unfold gl0_tape.
      destruct (Z.eqb_spec (z - (-1 + M)) 1), (Z.eqb_spec (z - (-1 + M)) 2),
               (Z.eqb_spec (z - (-1 + M)) 3); try lia; reflexivity. }
  assert (Habove : forall z, -1 + M <= z -> bt_interp (mk_bounce_bt M) z = gl0_tape (z - (-1 + M))).
  { intros z Hz. rewrite Hbt0. unfold bounce_tape.
    destruct (Z.ltb_spec z (-1)), (Z.ltb_spec z (-1 + M)); try lia.
    reflexivity. }
  pose proof (run_gl_from_bt (-1 + M) dt (mk_bounce_bt M) Hdt Habove) as Hgl.
  destruct (N.iter dt fast_step2 (-1 + M + 1, StB, mk_bounce_bt M)) as [[p2 s2] bt2].
  destruct Hgl as [Hp2 [Hs2 [Hge Hlt]]].
  constructor; unfold bounce_cfg, fc_to_cfg; cbn [pos1 pos2 state1 state2 tape fpos1 fpos2 fstate1 fstate2 ftape];
    repeat split; try congruence.
  intro z. unfold bounce_tape.
  destruct (Z.lt_ge_cases z (-1 + M)) as [Hzl | Hzr].
  - rewrite (Hlt z Hzl), Hbt0. unfold bounce_tape.
    destruct (Z.ltb_spec z (-1)), (Z.ltb_spec z (-1 + M)); try lia; reflexivity.
  - rewrite (Hge z Hzr).
    destruct (Z.ltb_spec z (-1)), (Z.ltb_spec z (-1 + M)); try lia; reflexivity.
Qed.

Definition mk_round_bt (Z_cnt gap : Z) : BTree :=
  bt_set_list (-1 + Z_cnt + gap) [false; true; true; true] (bt_set_range (-1 + Z_cnt) (Z.to_N gap) true BEmpty).

Definition fast_round_cfg (Z_cnt gap : Z) (dt : N) : FastConfig :=
  let '(p2, s2, bt) := N.iter dt fast_step2 (-1 + Z_cnt + gap + 1, StB, mk_round_bt Z_cnt gap) in
  {| fpos1 := -2; fpos2 := p2; fstate1 := StC; fstate2 := s2; ftape := bt |}.

Lemma fast_round_cfg_sound : forall Z_cnt gap : Z, 1 <= Z_cnt -> 0 <= gap ->
  forall dt : N, (dt < 21)%N ->
  cfg_eq (fc_to_cfg (fast_round_cfg Z_cnt gap dt)) (round_cfg Z_cnt gap dt).
Proof.
  intros Z_cnt gap HZ Hgap dt Hdt. unfold fast_round_cfg.
  set (pad := -1 + Z_cnt + gap).
  assert (Hbt0 : forall z, bt_interp (mk_round_bt Z_cnt gap) z = round_tape Z_cnt gap 0 z).
  { intro z. unfold mk_round_bt, round_tape.
    rewrite bt_interp_set_list, bt_interp_set_range.
    unfold bt_interp; rewrite bt_get_empty.
    rewrite run_solo_0. cbn [gl0 shift_scfg stape length]. change (Z.of_nat 4) with 4.
    replace (-1 + Z_cnt + Z.of_N (Z.to_N gap)) with (-1 + Z_cnt + gap) by lia.
    destruct (Z.leb_spec (-1 + Z_cnt + gap) z), (Z.ltb_spec z (-1 + Z_cnt + gap + 4)),
             (Z.leb_spec (-1 + Z_cnt) z), (Z.ltb_spec z (-1 + Z_cnt + gap)),
             (Z.ltb_spec z (-1 + Z_cnt)); try lia; auto.
    - unfold gl0_tape.
      assert (z - (-1 + Z_cnt + gap) = 0 \/ z - (-1 + Z_cnt + gap) = 1 \/
              z - (-1 + Z_cnt + gap) = 2 \/ z - (-1 + Z_cnt + gap) = 3)
        as [Hidx | [Hidx | [Hidx | Hidx]]] by lia; rewrite Hidx; reflexivity.
    - unfold gl0_tape.
      destruct (Z.eqb_spec (z - (-1 + Z_cnt + gap)) 1),
               (Z.eqb_spec (z - (-1 + Z_cnt + gap)) 2),
               (Z.eqb_spec (z - (-1 + Z_cnt + gap)) 3); try lia; reflexivity. }
  assert (Habove : forall z, pad <= z -> bt_interp (mk_round_bt Z_cnt gap) z = gl0_tape (z - pad)).
  { intros z Hz. rewrite Hbt0. unfold round_tape, pad in *.
    destruct (Z.ltb_spec z (-1 + Z_cnt)), (Z.ltb_spec z (-1 + Z_cnt + gap)); try lia; reflexivity. }
  pose proof (run_gl_from_bt pad dt (mk_round_bt Z_cnt gap) Hdt Habove) as Hgl.
  replace (-1 + Z_cnt + gap + 1) with (pad + 1) by (unfold pad; lia).
  destruct (N.iter dt fast_step2 (pad + 1, StB, mk_round_bt Z_cnt gap)) as [[p2 s2] bt2].
  destruct Hgl as [Hp2 [Hs2 [Hge Hlt]]].
  constructor; unfold round_cfg, fc_to_cfg; cbn [pos1 pos2 state1 state2 tape fpos1 fpos2 fstate1 fstate2 ftape];
    fold pad; repeat split; try congruence.
  intro z. unfold round_tape. fold pad.
  destruct (Z.lt_ge_cases z pad) as [Hzl | Hzr].
  - rewrite (Hlt z Hzl), Hbt0. unfold round_tape. fold pad.
    destruct (Z.ltb_spec z (-1 + Z_cnt)), (Z.ltb_spec z pad); try lia; reflexivity.
  - rewrite (Hge z Hzr).
    destruct (Z.ltb_spec z (-1 + Z_cnt)), (Z.ltb_spec z pad); try lia; reflexivity.
Qed.

Definition bounce_safe_step (M_rep : Z) (fc : FastConfig) : bool :=
  (-1 <=? fc.(fpos1)) && (fc.(fpos1) <? M_rep + 200) &&
  (-1 <=? fc.(fpos2)) && (fc.(fpos2) <? M_rep + 200) &&
  negb (fc.(fpos1) =? fc.(fpos2)) &&
  (state_eqb fc.(fstate1) StB || state_eqb fc.(fstate1) StC).

Definition check_base_bounce (M_rep : Z) (dt_mid dt_b : N) (Z_rep gap_rep : Z) (dt_out : N) : bool :=
  (21 <=? M_rep) && (dt_mid <? 21)%N && (1 <=? Z_rep) && (0 <=? gap_rep) && (dt_out <? 21)%N &&
  (Z_rep + gap_rep <=? M_rep + 190) &&
  let fc0 := fast_bounce_cfg M_rep dt_mid in
  let res := N.iter dt_b (fun '(ok, fc) => (ok && bounce_safe_step M_rep fc, fast_step fc)) (true, fc0) in
  let fc_end := snd res in
  let fc_target := fast_round_cfg Z_rep gap_rep dt_out in
  fst res &&
  (fc_end.(fpos1) =? fc_target.(fpos1)) &&
  (fc_end.(fpos2) =? fc_target.(fpos2)) &&
  state_eqb fc_end.(fstate1) fc_target.(fstate1) &&
  state_eqb fc_end.(fstate2) fc_target.(fstate2) &&
  check_range_nat (-2) (Z.to_nat (M_rep + 202)) (fun z =>
    Bool.eqb (bt_get (z_to_pos z) fc_end.(ftape)) (bt_get (z_to_pos z) fc_target.(ftape))).

Lemma base_bounce_verify_sound : forall M_rep dt_mid dt_b Z_rep gap_rep dt_out,
  check_base_bounce M_rep dt_mid dt_b Z_rep gap_rep dt_out = true ->
  (forall t, (t < dt_b)%N ->
     (run_N t (bounce_cfg M_rep dt_mid)).(pos1) <> (run_N t (bounce_cfg M_rep dt_mid)).(pos2) /\
     ((run_N t (bounce_cfg M_rep dt_mid)).(state1) = StB \/
      (run_N t (bounce_cfg M_rep dt_mid)).(state1) = StC) /\
     -1 <= (run_N t (bounce_cfg M_rep dt_mid)).(pos1) /\
     -1 <= (run_N t (bounce_cfg M_rep dt_mid)).(pos2)) /\
  cfg_eq (run_N dt_b (bounce_cfg M_rep dt_mid)) (round_cfg Z_rep gap_rep dt_out).
Proof.
  intros M_rep dt_mid dt_b Z_rep gap_rep dt_out Hchk.
  unfold check_base_bounce in Hchk.
  destruct (andb_prop _ _ Hchk) as [Hpre Hpost].
  repeat rewrite andb_true_iff in Hpre.
  destruct Hpre as [[[[[HM Hdt_m] HZ] Hgap] Hdt_o] Hbnd_z].
  cbv zeta in Hpost.
  set (fc0 := fast_bounce_cfg M_rep dt_mid) in *.
  set (res := N.iter dt_b (fun '(ok, fc) => (ok && bounce_safe_step M_rep fc, fast_step fc)) (true, fc0)) in *.
  repeat rewrite andb_true_iff in Hpost.
  destruct Hpost as [[[[[Hloop Hp1] Hp2] Hs1] Hs2] Hwin].
  apply Z.leb_le in HM. apply N.ltb_lt in Hdt_m.
  apply Z.leb_le in HZ. apply Z.leb_le in Hgap. apply N.ltb_lt in Hdt_o.
  apply Z.leb_le in Hbnd_z.
  apply Z.eqb_eq in Hp1. apply Z.eqb_eq in Hp2.
  destruct (state_eqb_spec (snd res).(fstate1) (fast_round_cfg Z_rep gap_rep dt_out).(fstate1)); [|discriminate].
  destruct (state_eqb_spec (snd res).(fstate2) (fast_round_cfg Z_rep gap_rep dt_out).(fstate2)); [|discriminate].
  assert (Hfc0_eq : cfg_eq (fc_to_cfg fc0) (bounce_cfg M_rep dt_mid)) by (apply fast_bounce_cfg_sound; lia).
  assert (Htrg_eq : cfg_eq (fc_to_cfg (fast_round_cfg Z_rep gap_rep dt_out)) (round_cfg Z_rep gap_rep dt_out))
    by (apply fast_round_cfg_sound; lia).
  assert (Hbnd_box : forall t, (t < dt_b)%N ->
    -1 <= (run_N t (bounce_cfg M_rep dt_mid)).(pos1) < M_rep + 200 /\
    -1 <= (run_N t (bounce_cfg M_rep dt_mid)).(pos2) < M_rep + 200 /\
    (run_N t (bounce_cfg M_rep dt_mid)).(pos1) <> (run_N t (bounce_cfg M_rep dt_mid)).(pos2) /\
    ((run_N t (bounce_cfg M_rep dt_mid)).(state1) = StB \/
     (run_N t (bounce_cfg M_rep dt_mid)).(state1) = StC)).
  { intros t Ht.
    pose proof (iter_chk_sound fast_step (bounce_safe_step M_rep) dt_b fc0 Hloop t Ht) as Hs.
    unfold bounce_safe_step in Hs. repeat rewrite andb_true_iff in Hs.
    destruct Hs as [[[[[B1a B1b] B2a] B2b] Bne] Bst].
    apply Z.leb_le in B1a. apply Z.ltb_lt in B1b.
    apply Z.leb_le in B2a. apply Z.ltb_lt in B2b.
    apply Bool.negb_true_iff in Bne. apply Z.eqb_neq in Bne.
    apply orb_true_iff in Bst.
    pose proof (fast_run_sound t fc0) as [Rp1 Rp2 Rs1 _ _].
    pose proof (run_N_proper t _ _ Hfc0_eq) as [Qp1 Qp2 Qs1 _ _].
    cbn [fc_to_cfg pos1 pos2 state1] in Rp1, Rp2, Rs1.
    repeat split; try lia.
    destruct Bst as [Bst | Bst];
      [destruct (state_eqb_spec (N.iter t fast_step fc0).(fstate1) StB); [|discriminate]; left; congruence
      |destruct (state_eqb_spec (N.iter t fast_step fc0).(fstate1) StC); [|discriminate]; right; congruence]. }
  split.
  - intros t Ht. destruct (Hbnd_box t Ht) as [[H1a _] [[H2a _] [Hne Hst]]]. repeat split; assumption.
  - pose proof (fast_run_sound dt_b fc0) as [Ep1 Ep2 Es1 Es2 Etp].
    pose proof (run_N_proper dt_b _ _ Hfc0_eq) as [Qp1 Qp2 Qs1 Qs2 Qtp].
    assert (Hsnd_eq : snd res = N.iter dt_b fast_step fc0) by (unfold res; apply iter_chk_snd).
    rewrite <- Hsnd_eq in Ep1, Ep2, Es1, Es2, Etp.
    cbn [fc_to_cfg pos1 pos2 state1 state2 tape] in Ep1, Ep2, Es1, Es2, Etp.
    destruct Htrg_eq as [Tp1 Tp2 Ts1 Ts2 Ttp].
    cbn [fc_to_cfg pos1 pos2 state1 state2 tape] in Tp1, Tp2, Ts1, Ts2, Ttp.
    constructor; [congruence | congruence | congruence | congruence | ].
    intro z.
    destruct (Z.lt_ge_cases z (-1)) as [Hzl | Hzge].
    + rewrite (full_preserves_outside dt_b (-1) (M_rep + 200) (bounce_cfg M_rep dt_mid)
                 (fun t Ht => match Hbnd_box t Ht with conj A (conj B _) => conj A B end) z ltac:(lia)).
      unfold bounce_cfg, round_cfg, bounce_tape, round_tape; cbn [tape].
      destruct (Z.ltb_spec z (-1)), (Z.ltb_spec z (-1 + Z_rep)); try lia; reflexivity.
    + destruct (Z.lt_ge_cases z (M_rep + 200)) as [Hzm | Hzhi].
      * rewrite <- (Qtp z), <- (Etp z), <- (Ttp z).
        pose proof (check_range_nat_sound (Z.to_nat (M_rep + 202)) (-2) _ Hwin z ltac:(lia)) as Hcell.
        apply Bool.eqb_prop in Hcell. unfold bt_interp. congruence.
      * rewrite (full_preserves_outside dt_b (-1) (M_rep + 200) (bounce_cfg M_rep dt_mid)
                   (fun t Ht => match Hbnd_box t Ht with conj A (conj B _) => conj A B end) z ltac:(lia)).
        unfold bounce_cfg, round_cfg, bounce_tape, round_tape; cbn [tape].
        destruct (Z.ltb_spec z (-1)), (Z.ltb_spec z (-1 + M_rep));
        destruct (Z.ltb_spec z (-1 + Z_rep)), (Z.ltb_spec z (-1 + Z_rep + gap_rep)); try lia.
        rewrite (gl_outside_10 dt_mid (-1 + M_rep) z Hdt_m ltac:(lia)).
        rewrite (gl_outside_10 dt_out (-1 + Z_rep + gap_rep) z Hdt_o ltac:(lia)).
        reflexivity.
Qed.

Theorem round_transition_sound :
  forall (n : nat) (gap : Z) (dt_in dt_mid : N)
         (M_rep : Z) (K dt_b : N)
         (Z_rep gap_rep : Z) (dt_out : N),
  (1 <= n)%nat ->
  0 <= gap ->
  (dt_in < 21)%N ->
  21 <= M_rep ->
  1 <= Z_rep ->
  0 <= gap_rep ->
  (dt_mid < 21)%N ->
  (dt_out < 21)%N ->
  let Z_cnt := Z.of_nat n in
  let T1 := counter_steps n in
  ((dt_in + T1) mod 21)%N = dt_mid ->
  Z_cnt + gap + 3 * Z.of_N ((dt_in + T1) / 21) = M_rep + 18 * Z.of_N K ->
  ((forall t, (t < dt_b)%N ->
      (run_N t (bounce_cfg M_rep dt_mid)).(pos1) <> (run_N t (bounce_cfg M_rep dt_mid)).(pos2) /\
      ((run_N t (bounce_cfg M_rep dt_mid)).(state1) = StB \/
       (run_N t (bounce_cfg M_rep dt_mid)).(state1) = StC) /\
      -1 <= (run_N t (bounce_cfg M_rep dt_mid)).(pos1) /\
      -1 <= (run_N t (bounce_cfg M_rep dt_mid)).(pos2)) /\
   cfg_eq (run_N dt_b (bounce_cfg M_rep dt_mid)) (round_cfg Z_rep gap_rep dt_out)) ->
  let T_tot := (T1 + 21 * K + dt_b + 21 * K)%N in
  let Z_next := Z_rep + 21 * Z.of_N K in
  let gap_next := gap_rep + 3 * Z.of_N K in
  (forall t, (t < T_tot)%N ->
     (run_N t (round_cfg Z_cnt gap dt_in)).(pos1) <> (run_N t (round_cfg Z_cnt gap dt_in)).(pos2) /\
     ((run_N t (round_cfg Z_cnt gap dt_in)).(state1) = StB \/
      (run_N t (round_cfg Z_cnt gap dt_in)).(state1) = StC)) /\
  cfg_eq (run_N T_tot (round_cfg Z_cnt gap dt_in)) (round_cfg Z_next gap_next dt_out).
Proof.
  intros n gap dt_in dt_mid M_rep K dt_b Z_rep gap_rep dt_out
         Hn Hgap Hdt_in HM_rep HZ_rep Hgap_rep Hdt_mid Hdt_out
         Z_cnt T1 Hdt_eq HM_eq [Hb_safe Hb_end] T_tot Z_next gap_next.
  set (M := Z_cnt + gap + 3 * Z.of_N ((dt_in + T1) / 21)).
  set (sh := 21 * Z.of_N K).
  destruct (phase_A_sound n Hn gap Hgap dt_in) as [PA_safe PA_end].
  fold Z_cnt T1 in PA_safe, PA_end. rewrite Hdt_eq in PA_end.
  rewrite HM_eq in PA_end.
  destruct (bounce_forward_K M_rep HM_rep dt_mid Hdt_mid K)
    as [BF_safe [BF_lt [BF_mid [BF_ge [BF_p1 [BF_p2 [BF_s1 BF_s2]]]]]]].
  fold sh in BF_safe, BF_lt, BF_mid, BF_ge, BF_p1, BF_p2, BF_s1, BF_s2.
  set (c_a := run_N T1 (round_cfg Z_cnt gap dt_in)).
  set (c_b0 := bounce_cfg (M_rep + 18 * Z.of_N K) dt_mid).
  set (c_b1 := run_N (21 * K) c_a).
  set (c_b1_canon := run_N (21 * K) c_b0).
  assert (Hc_b1_eq : cfg_eq c_b1 c_b1_canon) by (apply run_N_proper, PA_end).
  destruct Hc_b1_eq as [B1p1 B1p2 B1s1 B1s2 B1tp].
  unfold c_b1_canon, c_b0 in B1p1, B1p2, B1s1, B1s2, B1tp.
  set (c_sh := shift_cfg sh (bounce_cfg M_rep dt_mid)).
  assert (Hsh_bnd : forall t, (t < dt_b)%N ->
    -1 + sh <= (run_N t c_sh).(pos1) /\ -1 + sh <= (run_N t c_sh).(pos2)).
  { intros t Ht. destruct (shift_run t sh (bounce_cfg M_rep dt_mid)) as [Sp1 Sp2 _ _ _].
    unfold c_sh; rewrite Sp1, Sp2; unfold shift_cfg; cbn [pos1 pos2].
    destruct (Hb_safe t Ht) as [_ [_ [H1 H2]]]. split; lia. }
  assert (Hdep_b : forall t, (t <= dt_b)%N ->
    (run_N t c_b1).(pos1) = (run_N t c_sh).(pos1) /\
    (run_N t c_b1).(pos2) = (run_N t c_sh).(pos2) /\
    (run_N t c_b1).(state1) = (run_N t c_sh).(state1) /\
    (run_N t c_b1).(state2) = (run_N t c_sh).(state2) /\
    (forall z, -1 + sh <= z -> (run_N t c_b1).(tape) z = (run_N t c_sh).(tape) z)).
  { pose proof (full_run_depends_only_above dt_b (-1 + sh) c_sh c_b1
                  ltac:(rewrite B1p1, BF_p1; reflexivity)
                  ltac:(rewrite B1p2, BF_p2; reflexivity)
                  ltac:(rewrite B1s1, BF_s1; unfold c_sh, shift_cfg, bounce_cfg; cbn [state1]; reflexivity)
                  ltac:(rewrite B1s2, BF_s2; reflexivity)
                  ltac:(intros z Hz; rewrite (B1tp z), (BF_ge z Hz); reflexivity)
                  Hsh_bnd) as Hdep'.
    intros t Ht. destruct (Hdep' t Ht) as [A [B [C [D E]]]]. repeat split; symmetry; auto. }
  assert (Hpres_b : forall z, z < -1 + sh -> (run_N dt_b c_b1).(tape) z = c_b1.(tape) z).
  { apply full_preserves_below. intros t Ht.
    destruct (Hdep_b t ltac:(lia)) as [Dp1 [Dp2 _]]. rewrite Dp1, Dp2. apply Hsh_bnd, Ht. }
  set (c_r0 := run_N dt_b c_b1).
  destruct (Hdep_b dt_b ltac:(lia)) as [Rp1 [Rp2 [Rs1 [Rs2 Rtp]]]].
  destruct (shift_run dt_b sh (bounce_cfg M_rep dt_mid)) as [Sp1 Sp2 Ss1 Ss2 Stp].
  destruct Hb_end as [Ep1 Ep2 Es1 Es2 Etp].
  assert (Hr0_p1 : c_r0.(pos1) = -2 + sh).
  { unfold c_r0; rewrite Rp1; unfold c_sh; rewrite Sp1; unfold shift_cfg; cbn [pos1]; rewrite Ep1; reflexivity. }
  assert (Hr0_p2 : c_r0.(pos2) = (shift_cfg sh (round_cfg Z_rep gap_rep dt_out)).(pos2)).
  { unfold c_r0; rewrite Rp2; unfold c_sh; rewrite Sp2; unfold shift_cfg; cbn [pos2]; rewrite Ep2; reflexivity. }
  assert (Hr0_s1 : c_r0.(state1) = StC).
  { unfold c_r0; rewrite Rs1; unfold c_sh; rewrite Ss1; unfold shift_cfg; cbn [state1]; rewrite Es1; reflexivity. }
  assert (Hr0_s2 : c_r0.(state2) = (shift_cfg sh (round_cfg Z_rep gap_rep dt_out)).(state2)).
  { unfold c_r0; rewrite Rs2; unfold c_sh; rewrite Ss2; unfold shift_cfg; cbn [state2]; rewrite Es2; reflexivity. }
  assert (Hr0_lt : forall z, z < -1 -> c_r0.(tape) z = false).
  { intros z Hz. unfold c_r0. rewrite (Hpres_b z ltac:(unfold sh; lia)), (B1tp z). apply BF_lt, Hz. }
  assert (Hr0_mid : forall z, -1 <= z < -1 + sh -> c_r0.(tape) z = true).
  { intros z Hz. unfold c_r0. rewrite (Hpres_b z ltac:(lia)), (B1tp z). apply BF_mid, Hz. }
  assert (Hr0_ge : forall z, -1 + sh <= z -> c_r0.(tape) z = (shift_cfg sh (round_cfg Z_rep gap_rep dt_out)).(tape) z).
  { intros z Hz. unfold c_r0. rewrite (Rtp z Hz); unfold c_sh; rewrite (Stp z).
    unfold shift_cfg; cbn [tape]. apply Etp. }
  destruct (bounce_return_K Z_rep gap_rep HZ_rep Hgap_rep dt_out Hdt_out K c_r0
              Hr0_p1 Hr0_p2 Hr0_s1 Hr0_s2 Hr0_lt Hr0_mid Hr0_ge) as [BR_safe BR_end].
  fold sh Z_next gap_next in BR_safe, BR_end.
  split.
  - intros t Ht.
    destruct (N.lt_ge_cases t T1) as [Ht1 | Hge1].
    + apply PA_safe, Ht1.
    + destruct (N.lt_ge_cases t (T1 + 21 * K)) as [Ht2 | Hge2].
      * replace t with ((t - T1) + T1)%N by lia. rewrite run_N_add.
        pose proof (run_N_proper (t - T1)%N _ _ PA_end) as [Qp1 Qp2 Qs1 _ _].
        rewrite Qp1, Qp2, Qs1.
        destruct (BF_safe (t - T1)%N ltac:(lia)) as [Hne [Hst _]].
        split; [exact Hne | left; exact Hst].
      * destruct (N.lt_ge_cases t (T1 + 21 * K + dt_b)) as [Ht3 | Hge3].
        -- replace t with ((t - (T1 + 21 * K)) + (21 * K + T1))%N by lia.
           rewrite !run_N_add. fold c_a c_b1.
           set (t' := (t - (T1 + 21 * K))%N).
           destruct (Hdep_b t' ltac:(lia)) as [Dp1 [Dp2 [Ds1 _]]].
           destruct (shift_run t' sh (bounce_cfg M_rep dt_mid)) as [Tp1 Tp2 Ts1 _ _].
           destruct (Hb_safe t' ltac:(unfold t'; lia)) as [Hne [Hst _]].
           rewrite Dp1, Dp2, Ds1; unfold c_sh; rewrite Tp1, Tp2, Ts1; unfold shift_cfg; cbn [pos1 pos2 state1].
           split; [lia | exact Hst].
        -- replace t with ((t - (T1 + 21 * K + dt_b)) + (dt_b + (21 * K + T1)))%N by lia.
           rewrite !run_N_add. fold c_a c_b1 c_r0.
           destruct (BR_safe (t - (T1 + 21 * K + dt_b))%N ltac:(unfold T_tot in *; lia)) as [Hne Hst].
           split; [exact Hne | right; exact Hst].
  - replace T_tot with (21 * K + (dt_b + (21 * K + T1)))%N by (unfold T_tot; lia).
    rewrite !run_N_add. fold c_a c_b1 c_r0. exact BR_end.
Qed.

(** * 7. 14-Entry Modular Cycle Verification *)

Lemma r6_div4_63 : forall m6 : Z, 0 <= m6 < 6 ->
  let r6 := (2 ^ (m6 + 2)) mod 252 in
  0 <= r6 < 252 /\ 64 * r6 = 252 * (r6 / 4) + r6 /\ 0 <= r6 / 4.
Proof.
  intros m6 Hm.
  assert (m6 = 0 \/ m6 = 1 \/ m6 = 2 \/ m6 = 3 \/ m6 = 4 \/ m6 = 5)
    as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia;
    cbv zeta; repeat split;
    try apply Z.leb_le; try apply Z.ltb_lt; try apply Z.eqb_eq; vm_compute; reflexivity.
Qed.

Lemma pow2_Z2_mod252 : forall Z_cnt : Z, 0 <= Z_cnt ->
  let m6 := Z_cnt mod 6 in
  exists D : Z, 0 <= D /\ 2 ^ (Z_cnt + 2) = 252 * D + ((2 ^ (m6 + 2)) mod 252).
Proof.
  intros Z_cnt HZ m6.
  pose proof (Z.div_mod Z_cnt 6 ltac:(lia)) as HZdm.
  pose proof (Z.div_pos Z_cnt 6 HZ ltac:(lia)) as HQ.
  pose proof (Z.mod_pos_bound Z_cnt 6 ltac:(lia)) as Hm6.
  fold m6 in HZdm, Hm6.
  set (q := Z_cnt / 6) in *.
  set (k := Z.to_nat q).
  assert (Hk : Z_cnt = 6 * Z.of_nat k + m6) by (unfold k; lia).
  rewrite Hk. clearbody q k m6. clear HZdm HQ Hk HZ Z_cnt.
  induction k as [|k' IH].
  - replace (6 * Z.of_nat 0 + m6 + 2) with (m6 + 2) by lia.
    pose proof (Z.div_mod (2 ^ (m6 + 2)) 252 ltac:(lia)) as Hdm.
    pose proof (Z.div_pos (2 ^ (m6 + 2)) 252 (Z.pow_nonneg 2 (m6 + 2) ltac:(lia)) ltac:(lia)) as Hd.
    exists (2 ^ (m6 + 2) / 252). split; [exact Hd | exact Hdm].
  - destruct IH as [D' [HD' Heq]].
    replace (6 * Z.of_nat (S k') + m6 + 2) with (6 + (6 * Z.of_nat k' + m6 + 2)) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64. rewrite Heq.
    destruct (r6_div4_63 m6 Hm6) as [_ [Hr6 Hr4]].
    set (r6 := (2 ^ (m6 + 2)) mod 252) in *.
    exists (64 * D' + r6 / 4). split; lia.
Qed.

Lemma pow2_bound_14 : forall Z_cnt : Z, 14 <= Z_cnt ->
  65536 <= 2 ^ (Z_cnt + 2).
Proof.
  intros Z_cnt HZ. change 65536 with (2 ^ (14 + 2)). apply Z.pow_le_mono_r; lia.
Qed.

Record CycleEntry : Type := {
  ce_idx     : N;
  ce_z42     : Z;
  ce_dt_in   : N;
  ce_C_gap   : Z;
  ce_dt_mid  : N;
  ce_M_rep   : Z;
  ce_dt_b    : N;
  ce_Z_rep   : Z;
  ce_gap_rep : Z;
  ce_dt_out  : N;
  ce_C_out   : Z;
  ce_z42_out : Z
}.

Definition mkE (idx : N) (z42 : Z) (dt_in : N) (C_gap : Z) (dt_mid : N)
               (M_rep : Z) (dt_b : N) (Z_rep gap_rep : Z) (dt_out : N)
               (C_out z42_out : Z) : CycleEntry :=
  {| ce_idx := idx; ce_z42 := z42; ce_dt_in := dt_in; ce_C_gap := C_gap;
     ce_dt_mid := dt_mid; ce_M_rep := M_rep; ce_dt_b := dt_b;
     ce_Z_rep := Z_rep; ce_gap_rep := gap_rep; ce_dt_out := dt_out;
     ce_C_out := C_out; ce_z42_out := z42_out |}.

Definition cycle_table : list CycleEntry := [
  mkE  0 14  0  0  6 67 159 78 10 12  8 15;
  mkE  1 15 12  8 11 70 169 83 11  6  6 20;
  mkE  2 20  6  6  0 55 129 63  7 18 14 21;
  mkE  3 21 18 14  5 58 139 68  8 12 12 26;
  mkE  4 26 12 12 15 58 141 69 10  3 (-1) 27;
  mkE  5 27  3 (-1) 20 61 151 74  8 18 18 32;
  mkE  6 32 18 18  9 64 153 75 10  9  5 33;
  mkE  7 33  9  5 14 67 163 80 11  3  3 38;
  mkE  8 38  3  3  3 70 165 81 10 15 11 39;
  mkE  9 39 15 11  8 55 133 65  8  9  9  2;
  mkE 10  2  9  9 18 55 135 66 10  0 (-4)  3;
  mkE 11  3  0 (-4)  2 61 145 71  8 15 15  8;
  mkE 12  8 15 15 12 61 147 72 10  6  2  9;
  mkE 13  9  6  2 17 64 157 77 11  0  0 14
].

Definition default_entry : CycleEntry := mkE 0 14 0 0 6 67 159 78 10 12 8 15.

Definition nth_entry (idx : N) : CycleEntry :=
  nth (N.to_nat idx) cycle_table default_entry.

Definition check_cycle_entry (e : CycleEntry) : bool :=
  let z42 := e.(ce_z42) in
  let r6 := (2 ^ ((z42 mod 6) + 2)) mod 252 in
  let dt_num := Z.of_N e.(ce_dt_in) + r6 - 2 * z42 - 3 in
  let q0 := dt_num / 21 in
  let g0 := (z42 - e.(ce_C_gap)) / 7 in
  let m_num := z42 + g0 + 3 * q0 - e.(ce_M_rep) in
  let k0 := m_num / 18 in
  (0 <=? z42) && (z42 <? 42) &&
  (e.(ce_dt_in) <? 21)%N && (e.(ce_dt_mid) <? 21)%N && (e.(ce_dt_out) <? 21)%N &&
  (21 <=? e.(ce_M_rep)) && (1 <=? e.(ce_Z_rep)) && (0 <=? e.(ce_gap_rep)) &&
  (dt_num mod 21 =? Z.of_N e.(ce_dt_mid)) &&
  ((z42 - e.(ce_C_gap)) mod 7 =? 0) &&
  (m_num mod 18 =? 0) &&
  (0 <=? e.(ce_z42_out)) && (e.(ce_z42_out) <? 42) &&
  ((e.(ce_Z_rep) + 21 * k0) mod 42 =? e.(ce_z42_out)) &&
  (e.(ce_Z_rep) - 7 * e.(ce_gap_rep) =? e.(ce_C_out)) &&
  (0 <=? e.(ce_Z_rep) + 21 * k0 - z42) &&
  (-10 <=? k0) &&
  check_base_bounce e.(ce_M_rep) e.(ce_dt_mid) e.(ce_dt_b) e.(ce_Z_rep) e.(ce_gap_rep) e.(ce_dt_out).

Definition check_table_entry (i : Z) : bool :=
  let idx := Z.to_N i in
  let e := nth_entry idx in
  let nxt := nth_entry ((idx + 1) mod 14) in
  check_cycle_entry e &&
  (e.(ce_z42_out) =? nxt.(ce_z42)) &&
  (e.(ce_dt_out) =? nxt.(ce_dt_in))%N &&
  (e.(ce_C_out) =? nxt.(ce_C_gap)).

Lemma all_14_entries_ok : check_range_nat 0 14 check_table_entry = true.
Proof. vm_compute. reflexivity. Qed.

Lemma check_cycle_entry_sound : forall e : CycleEntry,
  check_cycle_entry e = true ->
  let z42 := e.(ce_z42) in
  let r6 := (2 ^ ((z42 mod 6) + 2)) mod 252 in
  exists q0 g0 k0 Q_out : Z,
    0 <= z42 < 42 /\
    (e.(ce_dt_in) < 21)%N /\
    (e.(ce_dt_mid) < 21)%N /\
    (e.(ce_dt_out) < 21)%N /\
    21 <= e.(ce_M_rep) /\
    1 <= e.(ce_Z_rep) /\
    0 <= e.(ce_gap_rep) /\
    Z.of_N e.(ce_dt_in) + r6 - 2 * z42 - 3 = 21 * q0 + Z.of_N e.(ce_dt_mid) /\
    z42 - e.(ce_C_gap) = 7 * g0 /\
    z42 + g0 + 3 * q0 - e.(ce_M_rep) = 18 * k0 /\
    0 <= e.(ce_z42_out) < 42 /\
    e.(ce_Z_rep) + 21 * k0 = 42 * Q_out + e.(ce_z42_out) /\
    e.(ce_Z_rep) - 7 * e.(ce_gap_rep) = e.(ce_C_out) /\
    0 <= e.(ce_Z_rep) + 21 * k0 - z42 /\
    -10 <= k0 /\
    check_base_bounce e.(ce_M_rep) e.(ce_dt_mid) e.(ce_dt_b) e.(ce_Z_rep) e.(ce_gap_rep) e.(ce_dt_out) = true.
Proof.
  intros e Hchk z42 r6. unfold check_cycle_entry in Hchk. cbv zeta in Hchk.
  repeat rewrite andb_true_iff in Hchk.
  destruct Hchk as [[[[[[[[[[[[[[[[[Hz0 Hz42] Hdi] Hdm] Hdo] HM] HZ] Hgp] Hdmod] Hgmod] Hmmod] Hzo0] Hzo42] Hzomod] Hcout] Hdz] Hk0] Hbb].
  apply Z.leb_le in Hz0. apply Z.ltb_lt in Hz42.
  apply N.ltb_lt in Hdi. apply N.ltb_lt in Hdm. apply N.ltb_lt in Hdo.
  apply Z.leb_le in HM. apply Z.leb_le in HZ. apply Z.leb_le in Hgp.
  apply Z.eqb_eq in Hdmod. apply Z.eqb_eq in Hgmod. apply Z.eqb_eq in Hmmod.
  apply Z.leb_le in Hzo0. apply Z.ltb_lt in Hzo42.
  apply Z.eqb_eq in Hzomod. apply Z.eqb_eq in Hcout.
  apply Z.leb_le in Hdz. apply Z.leb_le in Hk0.
  set (dt_num := Z.of_N e.(ce_dt_in) + r6 - 2 * z42 - 3).
  set (q0 := dt_num / 21).
  set (g0 := (z42 - e.(ce_C_gap)) / 7).
  set (m_num := z42 + g0 + 3 * q0 - e.(ce_M_rep)).
  set (k0 := m_num / 18).
  fold z42 in Hdmod, Hgmod, Hmmod, Hzomod, Hdz, Hk0, Hbb.
  fold r6 in Hdmod, Hmmod, Hzomod, Hdz, Hk0.
  fold dt_num in Hdmod, Hmmod, Hzomod, Hdz, Hk0.
  fold q0 in Hmmod, Hzomod, Hdz, Hk0.
  fold g0 in Hmmod, Hzomod, Hdz, Hk0.
  fold m_num in Hmmod, Hzomod, Hdz, Hk0.
  fold k0 in Hzomod, Hdz, Hk0.
  pose proof (Z.div_mod dt_num 21 ltac:(lia)) as H1.
  pose proof (Z.div_mod (z42 - e.(ce_C_gap)) 7 ltac:(lia)) as H2.
  pose proof (Z.div_mod m_num 18 ltac:(lia)) as H3.
  pose proof (Z.div_mod (e.(ce_Z_rep) + 21 * k0) 42 ltac:(lia)) as H4.
  exists q0, g0, k0, ((e.(ce_Z_rep) + 21 * k0) / 42).
  rewrite Hdmod in H1. rewrite Hgmod in H2. rewrite Hmmod in H3. rewrite Hzomod in H4.
  repeat split; try lia; assumption.
Qed.

Definition CycleInv (idx : N) (Z_cnt gap : Z) (c : Config) : Prop :=
  (idx < 14)%N /\
  let e := nth_entry idx in
  14 <= Z_cnt /\
  0 <= gap /\
  Z_cnt mod 42 = e.(ce_z42) /\
  Z_cnt - 7 * gap = e.(ce_C_gap) /\
  cfg_eq c (round_cfg Z_cnt gap e.(ce_dt_in)).

Theorem cycle_step_sound : forall (idx : N) (Z_cnt gap : Z) (c : Config),
  CycleInv idx Z_cnt gap c ->
  exists (T_step : N) (Z_next gap_next : Z),
    (1 <= T_step)%N /\
    Z_cnt + 10 <= Z_next /\
    (forall t, (t < T_step)%N ->
       (run_N t c).(pos1) <> (run_N t c).(pos2) /\
       ((run_N t c).(state1) = StB \/ (run_N t c).(state1) = StC)) /\
    CycleInv ((idx + 1) mod 14) Z_next gap_next (run_N T_step c).
Proof.
  intros idx Z_cnt gap c [Hidx [HZ14 [Hgap0 [Hzmod [HCgap Hceq]]]]].
  set (e := nth_entry idx) in *.
  set (nxt := nth_entry ((idx + 1) mod 14)) in *.
  pose proof (check_range_nat_sound 14 0 check_table_entry all_14_entries_ok (Z.of_N idx) ltac:(lia)) as Hrow.
  unfold check_table_entry in Hrow. rewrite N2Z.id in Hrow.
  fold e nxt in Hrow.
  repeat rewrite andb_true_iff in Hrow.
  destruct Hrow as [[[Hchk Hz_nxt] Hdt_nxt] HC_nxt].
  apply Z.eqb_eq in Hz_nxt. apply N.eqb_eq in Hdt_nxt. apply Z.eqb_eq in HC_nxt.
  destruct (check_cycle_entry_sound e Hchk) as
    [q0 [g0 [k0 [Q_out [Hz042 [Hdi [Hdm [Hdo [HMrep [HZrep [Hgrep [Hdtnum [Hg0eq [Hmnum [Hzo042 [Hzout [Hcout [Hdzconst [Hk0bnd Hbb]]]]]]]]]]]]]]]]]]].
  pose proof (Z.div_mod Z_cnt 42 ltac:(lia)) as HZdm.
  pose proof (Z.div_pos Z_cnt 42 ltac:(lia) ltac:(lia)) as HQpos.
  set (Q := Z_cnt / 42) in *. rewrite Hzmod in HZdm.
  pose proof (Z.div_mod e.(ce_z42) 6 ltac:(lia)) as Hz42_6.
  pose proof (Z.mod_pos_bound e.(ce_z42) 6 ltac:(lia)) as Hm6_e.
  pose proof (Z.div_mod Z_cnt 6 ltac:(lia)) as HZ_6.
  pose proof (Z.mod_pos_bound Z_cnt 6 ltac:(lia)) as Hm6_Z.
  assert (Hm6_eq : Z_cnt mod 6 = e.(ce_z42) mod 6) by lia.
  destruct (pow2_Z2_mod252 Z_cnt ltac:(lia)) as [D [HD Hpow]].
  rewrite Hm6_eq in Hpow.
  set (r6 := (2 ^ ((e.(ce_z42) mod 6) + 2)) mod 252) in *.
  pose proof (pow2_bound_14 Z_cnt HZ14) as Hpow_lo.
  pose proof (Z.mod_pos_bound (2 ^ ((e.(ce_z42) mod 6) + 2)) 252 ltac:(lia)) as Hr6_bnd.
  fold r6 in Hr6_bnd.
  assert (HD_lo : 259 <= D) by lia.
  set (n := Z.to_nat Z_cnt).
  assert (Hn1 : (1 <= n)%nat) by (unfold n; lia).
  assert (HZn : Z.of_nat n = Z_cnt) by (unfold n; lia).
  set (T1 := counter_steps n).
  pose proof (counter_steps_formula n Hn1) as HT1.
  rewrite HZn, Hpow in HT1.
  set (q := ((e.(ce_dt_in) + T1) / 21)%N).
  set (dt_mid_act := ((e.(ce_dt_in) + T1) mod 21)%N).
  generalize (N.div_mod (e.(ce_dt_in) + T1) 21 ltac:(lia)) (N.mod_lt (e.(ce_dt_in) + T1) 21 ltac:(lia)).
  fold q dt_mid_act. intros HdmN HltN.
  assert (Hdt_mid_eq : dt_mid_act = e.(ce_dt_mid) /\ Z.of_N q = 12 * D - 4 * Q + q0).
  { assert (HZq : 21 * Z.of_N q + Z.of_N dt_mid_act = 21 * (12 * D - 4 * Q + q0) + Z.of_N e.(ce_dt_mid)) by lia.
    assert (H1 : Z.of_N dt_mid_act = Z.of_N e.(ce_dt_mid) /\ Z.of_N q = 12 * D - 4 * Q + q0) by lia.
    destruct H1 as [Hdtz Hqz]. split; [lia | exact Hqz]. }
  destruct Hdt_mid_eq as [Hdt_eq Hq_eq].
  assert (Hgap_eq : gap = 6 * Q + g0) by lia.
  set (K_z := 2 * Q + 2 * D + k0).
  assert (HKz_pos : 500 <= K_z) by (unfold K_z; lia).
  set (K := Z.to_N K_z).
  assert (HM_eq : Z_cnt + gap + 3 * Z.of_N q = e.(ce_M_rep) + 18 * Z.of_N K).
  { replace (Z.of_N K) with K_z by (unfold K; lia). unfold K_z. lia. }
  pose proof (base_bounce_verify_sound e.(ce_M_rep) e.(ce_dt_mid) e.(ce_dt_b)
                e.(ce_Z_rep) e.(ce_gap_rep) e.(ce_dt_out) Hbb) as Hbase.
  destruct (round_transition_sound n gap e.(ce_dt_in) e.(ce_dt_mid)
              e.(ce_M_rep) K e.(ce_dt_b) e.(ce_Z_rep) e.(ce_gap_rep) e.(ce_dt_out)
              Hn1 Hgap0 Hdi HMrep HZrep Hgrep Hdm Hdo Hdt_eq ltac:(rewrite HZn; exact HM_eq) Hbase)
    as [Hround_safe Hround_end].
  rewrite HZn in Hround_safe, Hround_end.
  fold T1 in Hround_safe, Hround_end.
  set (T_step := (T1 + 21 * K + e.(ce_dt_b) + 21 * K)%N) in *.
  set (Z_next := e.(ce_Z_rep) + 21 * Z.of_N K) in *.
  set (gap_next := e.(ce_gap_rep) + 3 * Z.of_N K) in *.
  exists T_step, Z_next, gap_next.
  split; [assert (HK1 : (1 <= K)%N) by (unfold K; lia); lia |].
  split; [unfold Z_next; replace (Z.of_N K) with K_z by (unfold K; lia); unfold K_z; lia |].
  split.
  - intros t Ht.
    destruct (Hround_safe t Ht) as [Hne Hst].
    destruct (run_N_proper t _ _ Hceq) as [Rp1 Rp2 Rs1 _ _].
    rewrite Rp1, Rp2, Rs1. split; assumption.
  - unfold CycleInv.
    split; [apply N.mod_lt; lia |].
    fold nxt.
    split; [unfold Z_next; replace (Z.of_N K) with K_z by (unfold K; lia); unfold K_z; lia |].
    split; [unfold gap_next; lia |].
    split.
    + rewrite <- Hz_nxt.
      pose proof (Z.div_mod Z_next 42 ltac:(lia)) as Hdm_next.
      pose proof (Z.mod_pos_bound Z_next 42 ltac:(lia)) as Hmod_next.
      assert (HZnext_split : Z_next = 42 * (Q + D + Q_out) + e.(ce_z42_out))
        by (unfold Z_next; replace (Z.of_N K) with K_z by (unfold K; lia); unfold K_z; lia).
      lia.
    + split; [rewrite <- HC_nxt; unfold Z_next, gap_next; lia |].
      rewrite <- Hdt_nxt.
      eapply cfg_eq_trans; [apply run_N_proper, Hceq | exact Hround_end].
Qed.

(** * 8. Step-120 Prefix Check and Global Non-Halting Theorem *)

Definition fc_init : FastConfig :=
  {| fpos1 := 0; fpos2 := 2; fstate1 := StA; fstate2 := StA; ftape := BEmpty |}.

Definition prefix_safe_step (fc : FastConfig) : bool :=
  (-2 <=? fc.(fpos1)) && (fc.(fpos1) <? 20) &&
  (-2 <=? fc.(fpos2)) && (fc.(fpos2) <? 20) &&
  negb (fc.(fpos1) =? fc.(fpos2)) &&
  (state_eqb fc.(fstate1) StB || state_eqb fc.(fstate1) StC).

Definition check_prefix_run (m : N) : bool :=
  let fc1 := fast_step fc_init in
  let res := N.iter m (fun '(ok, fc) => (ok && prefix_safe_step fc, fast_step fc)) (true, fc1) in
  let fc_end := snd res in
  let fc_trg := fast_round_cfg 14 2 0 in
  fst res &&
  (fc_end.(fpos1) =? fc_trg.(fpos1)) &&
  (fc_end.(fpos2) =? fc_trg.(fpos2)) &&
  state_eqb fc_end.(fstate1) fc_trg.(fstate1) &&
  state_eqb fc_end.(fstate2) fc_trg.(fstate2) &&
  check_range_nat (-3) 28 (fun z =>
    Bool.eqb (bt_get (z_to_pos z) fc_end.(ftape)) (bt_get (z_to_pos z) fc_trg.(ftape))).

Lemma prefix_verify_sound : forall m : N,
  check_prefix_run m = true ->
  (forall t, (t < m + 1)%N ->
     (run_N t c0).(pos1) <> (run_N t c0).(pos2) /\
     ((1 <= t)%N -> (run_N t c0).(state1) = StB \/ (run_N t c0).(state1) = StC)) /\
  cfg_eq (run_N (m + 1) c0) (round_cfg 14 2 0).
Proof.
  intros m Hchk.
  unfold check_prefix_run in Hchk. cbv zeta in Hchk.
  set (fc1 := fast_step fc_init) in *.
  set (res := N.iter m (fun '(ok, fc) => (ok && prefix_safe_step fc, fast_step fc)) (true, fc1)) in *.
  repeat rewrite andb_true_iff in Hchk.
  destruct Hchk as [[[[[Hloop Hp1] Hp2] Hs1] Hs2] Hwin].
  apply Z.eqb_eq in Hp1. apply Z.eqb_eq in Hp2.
  destruct (state_eqb_spec (snd res).(fstate1) (fast_round_cfg 14 2 0).(fstate1)) as [He1|]; [|discriminate].
  destruct (state_eqb_spec (snd res).(fstate2) (fast_round_cfg 14 2 0).(fstate2)) as [He2|]; [|discriminate].
  assert (Hfc0 : cfg_eq (fc_to_cfg fc_init) c0).
  { constructor; cbn [fc_to_cfg c0 pos1 pos2 state1 state2 tape fpos1 fpos2 fstate1 fstate2 ftape];
      try reflexivity.
    intro z. unfold bt_interp, empty_tape. apply bt_get_empty. }
  assert (Hbnd_all : forall t, (t < m + 1)%N ->
    -2 <= (run_N t c0).(pos1) < 20 /\
    -2 <= (run_N t c0).(pos2) < 20 /\
    (run_N t c0).(pos1) <> (run_N t c0).(pos2) /\
    ((1 <= t)%N -> (run_N t c0).(state1) = StB \/ (run_N t c0).(state1) = StC)).
  { intros t Ht.
    destruct (N.eq_0_gt_0_cases t) as [-> | Hpos].
    - cbn [run_N N.iter c0 pos1 pos2]. repeat split; try lia.
    - replace t with ((t - 1) + 1)%N by lia.
      pose proof (iter_chk_sound fast_step prefix_safe_step m fc1 Hloop (t - 1)%N ltac:(lia)) as Hs.
      unfold prefix_safe_step in Hs. repeat rewrite andb_true_iff in Hs.
      destruct Hs as [[[[[B1a B1b] B2a] B2b] Bne] Bst].
      apply Z.leb_le in B1a. apply Z.ltb_lt in B1b.
      apply Z.leb_le in B2a. apply Z.ltb_lt in B2b.
      apply Bool.negb_true_iff in Bne. apply Z.eqb_neq in Bne.
      apply orb_true_iff in Bst.
      pose proof (fast_run_sound (t - 1)%N fc1) as [Rp1 Rp2 Rs1 _ _].
      assert (Hfc_step : cfg_eq (fc_to_cfg fc1) (run_N 1 c0)).
      { unfold fc1. change (run_N 1 c0) with (step c0).
        eapply cfg_eq_trans; [apply fast_step_sound | apply step_proper, Hfc0]. }
      pose proof (run_N_proper (t - 1)%N _ _ Hfc_step) as [Qp1 Qp2 Qs1 _ _].
      rewrite run_N_add. cbn [fc_to_cfg pos1 pos2 state1] in Rp1, Rp2, Rs1.
      repeat split; try lia. intros _.
      destruct Bst as [Bst | Bst];
        [destruct (state_eqb_spec (N.iter (t - 1) fast_step fc1).(fstate1) StB) as [Heq|];
          [|discriminate]; left; rewrite <- Qs1, <- Rs1; exact Heq
        |destruct (state_eqb_spec (N.iter (t - 1) fast_step fc1).(fstate1) StC) as [Heq|];
          [|discriminate]; right; rewrite <- Qs1, <- Rs1; exact Heq]. }
  split.
  - intros t Ht. destruct (Hbnd_all t Ht) as [_ [_ [Hne Hst]]]. split; assumption.
  - assert (Hsnd_eq : snd res = N.iter m fast_step fc1) by (unfold res; apply iter_chk_snd).
    assert (Hiter_succ : N.iter m fast_step fc1 = N.iter (m + 1) fast_step fc_init).
    { rewrite N.iter_add. unfold fc1. reflexivity. }
    pose proof (fast_run_sound (m + 1)%N fc_init) as [Ep1 Ep2 Es1 Es2 Etp].
    pose proof (run_N_proper (m + 1)%N _ _ Hfc0) as [Qp1 Qp2 Qs1 Qs2 Qtp].
    rewrite <- Hiter_succ, <- Hsnd_eq in Ep1, Ep2, Es1, Es2, Etp.
    cbn [fc_to_cfg pos1 pos2 state1 state2 tape] in Ep1, Ep2, Es1, Es2, Etp.
    destruct (fast_round_cfg_sound 14 2 ltac:(lia) ltac:(lia) 0 ltac:(lia)) as [Tp1 Tp2 Ts1 Ts2 Ttp].
    cbn [fc_to_cfg pos1 pos2 state1 state2 tape] in Tp1, Tp2, Ts1, Ts2, Ttp.
    constructor;
      [ rewrite <- Qp1, <- Ep1, Hp1, Tp1; reflexivity
      | rewrite <- Qp2, <- Ep2, Hp2, Tp2; reflexivity
      | rewrite <- Qs1, <- Es1, He1, Ts1; reflexivity
      | rewrite <- Qs2, <- Es2, He2, Ts2; reflexivity
      | ].
    intro z.
    destruct (Z.lt_ge_cases z (-2)) as [Hzl | Hzge].
    + rewrite (full_preserves_outside (m + 1)%N (-2) 20 c0
                 (fun t Ht => match Hbnd_all t Ht with conj A (conj B _) => conj A B end) z ltac:(lia)).
      unfold c0, round_cfg, round_tape; cbn [tape]. unfold empty_tape.
      destruct (Z.ltb_spec z (-1 + 14)); try lia; reflexivity.
    + destruct (Z.lt_ge_cases z 20) as [Hzhi | Hzr].
      * rewrite <- (Qtp z), <- (Etp z), <- (Ttp z).
        pose proof (check_range_nat_sound 28 (-3) _ Hwin z ltac:(lia)) as Hcell.
        apply Bool.eqb_prop in Hcell. unfold bt_interp. exact Hcell.
      * rewrite (full_preserves_outside (m + 1)%N (-2) 20 c0
                   (fun t Ht => match Hbnd_all t Ht with conj A (conj B _) => conj A B end) z ltac:(lia)).
        unfold c0, round_cfg, round_tape; cbn [tape]. unfold empty_tape.
        destruct (Z.ltb_spec z (-1 + 14)), (Z.ltb_spec z (-1 + 14 + 2)); try lia.
        rewrite run_solo_0; cbn [shift_scfg gl0 stape]; unfold gl0_tape.
        destruct (Z.eqb_spec (z - (-1 + 14 + 2)) 1),
                 (Z.eqb_spec (z - (-1 + 14 + 2)) 2),
                 (Z.eqb_spec (z - (-1 + 14 + 2)) 3); try lia; reflexivity.
Qed.

Lemma prefix_120_sound :
  (forall t, (t < 120)%N ->
     (run_N t c0).(pos1) <> (run_N t c0).(pos2) /\
     ((1 <= t)%N -> (run_N t c0).(state1) = StB \/ (run_N t c0).(state1) = StC)) /\
  cfg_eq (run_N 120 c0) (round_cfg 14 2 0).
Proof.
  change 120%N with (119 + 1)%N.
  apply (prefix_verify_sound 119). vm_compute. reflexivity.
Qed.

Lemma reach_any_time_from_inv : forall (m : nat) (t idx : N) (Z_cnt gap : Z) (c : Config),
  (N.to_nat t <= m)%nat ->
  CycleInv idx Z_cnt gap c ->
  (run_N t c).(pos1) <> (run_N t c).(pos2) /\
  ((run_N t c).(state1) = StB \/ (run_N t c).(state1) = StC).
Proof.
  intro m. induction m as [|m' IH]; intros t idx Z_cnt gap c Htm Hinv.
  - assert (Ht0 : t = 0%N) by lia. subst t.
    destruct (cycle_step_sound idx Z_cnt gap c Hinv) as [T_step [_ [_ [HT [_ [Hsafe _]]]]]].
    apply Hsafe. lia.
  - destruct (cycle_step_sound idx Z_cnt gap c Hinv) as [T_step [Z_next [gap_next [HT [_ [Hsafe Hnext]]]]]].
    destruct (N.lt_ge_cases t T_step) as [Hlt | Hge].
    + apply Hsafe, Hlt.
    + replace t with ((t - T_step) + T_step)%N by lia.
      rewrite run_N_add.
      apply (IH (t - T_step)%N ((idx + 1) mod 14)%N Z_next gap_next (run_N T_step c)); [lia | exact Hnext].
Qed.

Theorem target_never_halts :
  forall t : N, exists c : Config, run_N_opt t c0 = Some c /\ c.(pos1) <> c.(pos2).
Proof.
  destruct prefix_120_sound as [Hpre H120].
  assert (Hinv120 : CycleInv 0 14 2 (run_N 120 c0)).
  { unfold CycleInv.
    split; [lia | split; [lia | split; [lia | split; [vm_compute; reflexivity | split; [apply Z.eqb_eq; vm_compute; reflexivity | change (ce_dt_in (nth_entry 0)) with 0%N; exact H120]]]]]. }
  assert (Htotal_safe : forall t : N, (run_N t c0).(pos1) <> (run_N t c0).(pos2)).
  { intro t. destruct (N.lt_ge_cases t 120) as [Hlt | Hge].
    - exact (proj1 (Hpre t Hlt)).
    - replace t with ((t - 120) + 120)%N by lia. rewrite run_N_add.
      exact (proj1 (reach_any_time_from_inv (N.to_nat (t - 120)) (t - 120)%N 0 14 2
                       (run_N 120 c0) ltac:(lia) Hinv120)). }
  assert (Htotal_st : forall t : N, (1 <= t)%N ->
    (run_N t c0).(state1) = StB \/ (run_N t c0).(state1) = StC).
  { intros t Ht1. destruct (N.lt_ge_cases t 120) as [Hlt | Hge].
    - exact (proj2 (Hpre t Hlt) Ht1).
    - replace t with ((t - 120) + 120)%N by lia. rewrite run_N_add.
      exact (proj2 (reach_any_time_from_inv (N.to_nat (t - 120)) (t - 120)%N 0 14 2
                       (run_N 120 c0) ltac:(lia) Hinv120)). }
  intro t.
  destruct (run_N_opt_from_total Htotal_safe Htotal_st t) as [c [Hopt [Hp1 Hp2 _ _ _]]].
  exists c. split; [exact Hopt|].
  pose proof (Htotal_safe t) as Hne. congruence.
Qed.

Print Assumptions target_never_halts.


