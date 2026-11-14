(** Separated-Agents Certificate Checker for CET(3)
    Proves non-halting when after t0 steps, Agent 1 stays <= w1_max
    and Agent 2 stays >= w2_min with w1_max < w2_min, and each agent
    independently loops (Agent 1 with dx1 <= 0, Agent 2 with dx2 >= 0).
*)

From Stdlib Require Import ZArith NArith PArith Bool List Lia.
Require Import CET3_Cert.
Open Scope Z_scope.

Definition fstep1_only (ag1 : AgentTableOpt) (p1 : Z) (s1 : State) (tp : btree)
  : option (Z * State * btree) :=
  match ag1 s1 (bt_get tp (pos_of_Z p1)) with
  | None => None
  | Some tr1 =>
      Some (move_pos p1 tr1.(move_dir), tr1.(next_state),
            bt_set tp (pos_of_Z p1) tr1.(write_sym))
  end.

Definition fstep2_only (ag2 : AgentTableOpt) (p2 : Z) (s2 : State) (tp : btree)
  : option (Z * State * btree) :=
  match ag2 s2 (bt_get tp (pos_of_Z p2)) with
  | None => None
  | Some tr2 =>
      Some (move_pos p2 tr2.(move_dir), tr2.(next_state),
            bt_set tp (pos_of_Z p2) tr2.(write_sym))
  end.

Definition step1_bounds (ag1 : AgentTableOpt)
  (acc : option (Z * State * btree * Z * Z)) : option (Z * State * btree * Z * Z) :=
  match acc with
  | None => None
  | Some (p, s, tp, mn, mx) =>
      match fstep1_only ag1 p s tp with
      | None => None
      | Some (p', s', tp') => Some (p', s', tp', Z.min mn p, Z.max mx p)
      end
  end.

Definition step2_bounds (ag2 : AgentTableOpt)
  (acc : option (Z * State * btree * Z * Z)) : option (Z * State * btree * Z * Z) :=
  match acc with
  | None => None
  | Some (p, s, tp, mn, mx) =>
      match fstep2_only ag2 p s tp with
      | None => None
      | Some (p', s', tp') => Some (p', s', tp', Z.min mn p, Z.max mx p)
      end
  end.

Definition check_separated_cert
  (ag1 ag2 : AgentTableOpt) (t0 : N)
  (p1 : N) (dx1 w1_min w1_max : Z)
  (p2 : N) (dx2 w2_min w2_max : Z) : bool :=
  if (1 <=? p1)%N && (1 <=? p2)%N &&
     (dx1 <=? 0) && (0 <=? dx2) &&
     (w1_min <=? w1_max) && (w1_max <? w2_min) && (w2_min <=? w2_max) then
    match run_N_fast ag1 ag2 t0 fc0 with
    | None => false
    | Some fc_s =>
        match N.iter p1 (step1_bounds ag1)
                     (Some (fc_s.(fp1), fc_s.(fs1), fc_s.(ftape), fc_s.(fp1), fc_s.(fp1))),
              N.iter p2 (step2_bounds ag2)
                     (Some (fc_s.(fp2), fc_s.(fs2), fc_s.(ftape), fc_s.(fp2), fc_s.(fp2))) with
        | Some (p1_e, s1_e, tp1_e, r1_min, r1_max),
          Some (p2_e, s2_e, tp2_e, r2_min, r2_max) =>
            (w1_min <=? r1_min) && (r1_max <=? w1_max) &&
            (p1_e =? fc_s.(fp1) + dx1) && state_eqb s1_e fc_s.(fs1) &&
            forall_Z_range w1_min w1_max (fun z =>
              Bool.eqb (bt_get tp1_e (pos_of_Z (z + dx1)))
                       (bt_get fc_s.(ftape) (pos_of_Z z))) &&
            (if dx1 <? 0 then
               forall_Z_range fc_s.(fmin_w) (w1_min - 1) (fun z =>
                 negb (bt_get fc_s.(ftape) (pos_of_Z z)))
             else true) &&
            (w2_min <=? r2_min) && (r2_max <=? w2_max) &&
            (p2_e =? fc_s.(fp2) + dx2) && state_eqb s2_e fc_s.(fs2) &&
            forall_Z_range w2_min w2_max (fun z =>
              Bool.eqb (bt_get tp2_e (pos_of_Z (z + dx2)))
                       (bt_get fc_s.(ftape) (pos_of_Z z))) &&
            (if 0 <? dx2 then
               forall_Z_range (w2_max + 1) fc_s.(fmax_w) (fun z =>
                 negb (bt_get fc_s.(ftape) (pos_of_Z z)))
             else true)
        | _, _ => false
        end
    end
  else false.

(** * Soundness of Separated-Agents Certificate Checker *)

Definition step1_tape (ag1 : AgentTableOpt) (p1 : Z) (s1 : State) (tp : Tape)
  : option (Z * State * Tape) :=
  match ag1 s1 (tp p1) with
  | None => None
  | Some tr1 => Some (move_pos p1 tr1.(move_dir), tr1.(next_state), write_tape tp p1 tr1.(write_sym))
  end.

Definition step2_tape (ag2 : AgentTableOpt) (p2 : Z) (s2 : State) (tp : Tape)
  : option (Z * State * Tape) :=
  match ag2 s2 (tp p2) with
  | None => None
  | Some tr2 => Some (move_pos p2 tr2.(move_dir), tr2.(next_state), write_tape tp p2 tr2.(write_sym))
  end.

Definition run1_N (ag1 : AgentTableOpt) (n : N) (p1 : Z) (s1 : State) (tp : Tape)
  : option (Z * State * Tape) :=
  N.iter n (fun o => match o with None => None | Some (p, s, t) => step1_tape ag1 p s t end)
           (Some (p1, s1, tp)).

Definition run2_N (ag2 : AgentTableOpt) (n : N) (p2 : Z) (s2 : State) (tp : Tape)
  : option (Z * State * Tape) :=
  N.iter n (fun o => match o with None => None | Some (p, s, t) => step2_tape ag2 p s t end)
           (Some (p2, s2, tp)).

Lemma run_N_opt_disjoint : forall ag1 ag2 c w1_max w2_min,
  w1_max < w2_min ->
  (forall t, exists p1 s1 tp1, run1_N ag1 t c.(pos1) c.(state1) c.(tape) = Some (p1, s1, tp1) /\ p1 <= w1_max) ->
  (forall t, exists p2 s2 tp2, run2_N ag2 t c.(pos2) c.(state2) c.(tape) = Some (p2, s2, tp2) /\ w2_min <= p2) ->
  forall t, exists ct p1 s1 tp1 p2 s2 tp2,
    run_N_opt ag1 ag2 t c = Some ct /\
    run1_N ag1 t c.(pos1) c.(state1) c.(tape) = Some (p1, s1, tp1) /\
    run2_N ag2 t c.(pos2) c.(state2) c.(tape) = Some (p2, s2, tp2) /\
    ct.(pos1) = p1 /\ ct.(state1) = s1 /\
    ct.(pos2) = p2 /\ ct.(state2) = s2 /\
    (forall z, z <= w1_max -> ct.(tape) z = tp1 z) /\
    (forall z, w2_min <= z -> ct.(tape) z = tp2 z) /\
    ct.(pos1) <> ct.(pos2).
Proof.
  intros ag1 ag2 c w1_max w2_min Hsep H1 H2 t.
  induction t using N.peano_ind.
  - destruct (H1 0%N) as [p1 [s1 [tp1 [E1 Hb1]]]].
    destruct (H2 0%N) as [p2 [s2 [tp2 [E2 Hb2]]]].
    simpl in E1, E2. inversion E1; inversion E2; subst.
    exists c, (pos1 c), (state1 c), (tape c), (pos2 c), (state2 c), (tape c).
    repeat split; try reflexivity; try lia.
  - destruct IHt as [ct [p1 [s1 [tp1 [p2 [s2 [tp2 [Et [E1 [E2 [Hp1 [Hs1 [Hp2 [Hs2 [Ht1 [Ht2 Hnc]]]]]]]]]]]]]]]].
    destruct (H1 (N.succ t)) as [p1' [s1' [tp1' [E1' Hb1']]]].
    destruct (H2 (N.succ t)) as [p2' [s2' [tp2' [E2' Hb2']]]].
    pose proof E1' as E1'_orig. pose proof E2' as E2'_orig.
    destruct (H1 t) as [p1_t [s1_t [tp1_t [E1_t Hb1_t]]]].
    destruct (H2 t) as [p2_t [s2_t [tp2_t [E2_t Hb2_t]]]].
    rewrite E1 in E1_t; inversion E1_t; subst p1_t s1_t tp1_t.
    rewrite E2 in E2_t; inversion E2_t; subst p2_t s2_t tp2_t.
    unfold run1_N in E1'; rewrite N.iter_succ in E1'.
    change (N.iter t _ (Some (pos1 c, state1 c, tape c))) with (run1_N ag1 t (pos1 c) (state1 c) (tape c)) in E1'.
    rewrite E1 in E1'.
    unfold run2_N in E2'; rewrite N.iter_succ in E2'.
    change (N.iter t _ (Some (pos2 c, state2 c, tape c))) with (run2_N ag2 t (pos2 c) (state2 c) (tape c)) in E2'.
    rewrite E2 in E2'.
    unfold step1_tape in E1'; unfold step2_tape in E2'.
    unfold run_N_opt; rewrite N.iter_succ.
    change (N.iter t _ (Some c)) with (run_N_opt ag1 ag2 t c).
    rewrite Et. unfold step_opt.
    destruct (Z.eqb_spec (pos1 ct) (pos2 ct)); [lia|].
    rewrite Hp1, Hs1, Hp2, Hs2, (Ht1 p1 Hb1_t), (Ht2 p2 Hb2_t).
    destruct (ag1 s1 (tp1 p1)) as [tr1|]; [|discriminate].
    destruct (ag2 s2 (tp2 p2)) as [tr2|]; [|discriminate].
    inversion E1' as [[Hp1' Hs1' Htp1']]; inversion E2' as [[Hp2' Hs2' Htp2']].
    simpl.
    destruct (Z.eqb_spec (move_pos p1 (move_dir tr1)) (move_pos p2 (move_dir tr2))); [lia|].
    exists {| pos1 := move_pos p1 (move_dir tr1);
              pos2 := move_pos p2 (move_dir tr2);
              state1 := next_state tr1;
              state2 := next_state tr2;
              tape := write_tape (write_tape (tape ct) p2 (write_sym tr2)) p1 (write_sym tr1) |},
           p1', s1', tp1', p2', s2', tp2'.
    repeat split; try reflexivity; try lia.
    + exact E1'_orig.
    + exact E2'_orig.
    + rewrite Hp1'. reflexivity.
    + rewrite Hs1'. reflexivity.
    + rewrite Hp2'. reflexivity.
    + rewrite Hs2'. reflexivity.
    + intros z Hz. rewrite <- Htp1'. simpl. unfold write_tape.
      destruct (Z.eqb_spec z p1); [reflexivity|].
      destruct (Z.eqb_spec z p2); [lia|].
      apply Ht1; exact Hz.
    + intros z Hz. rewrite <- Htp2'. simpl. unfold write_tape.
      destruct (Z.eqb_spec z p1); [lia|].
      destruct (Z.eqb_spec z p2); [reflexivity|].
      apply Ht2; exact Hz.
    + simpl; exact n0.
Qed.

(** * Cycle-bound lemmas for Agent 1 and Agent 2 *)

Definition agree1_shifted (lo_opt : option Z) (hi : Z) (dx : Z)
  (p1 : Z) (s1 : State) (tp1 : Tape) (p2 : Z) (s2 : State) (tp2 : Tape) : Prop :=
  p1 = p2 + dx /\ s1 = s2 /\
  forall z, (match lo_opt with Some lo => lo <= z | None => True end) -> z <= hi ->
            tp1 (z + dx) = tp2 z.

Lemma step1_tape_agree_shifted : forall ag1 lo_opt hi dx p1 s1 tp1 p2 s2 tp2 p2' s2' tp2',
  agree1_shifted lo_opt hi dx p1 s1 tp1 p2 s2 tp2 ->
  (match lo_opt with Some lo => lo <= p2 | None => True end) ->
  p2 <= hi ->
  step1_tape ag1 p2 s2 tp2 = Some (p2', s2', tp2') ->
  exists p1' s1' tp1',
    step1_tape ag1 p1 s1 tp1 = Some (p1', s1', tp1') /\
    agree1_shifted lo_opt hi dx p1' s1' tp1' p2' s2' tp2'.
Proof.
  intros ag1 lo_opt hi dx p1 s1 tp1 p2 s2 tp2 p2' s2' tp2' [Hp [Hs Htp]] Hlo Hhi Hst.
  unfold step1_tape in *.
  rewrite Hp, Hs, (Htp p2 Hlo Hhi).
  destruct (ag1 s2 (tp2 p2)) as [tr1|]; [|discriminate].
  inversion Hst; subst.
  assert (Hmv : move_pos (p2 + dx) (move_dir tr1) = move_pos p2 (move_dir tr1) + dx)
    by (destruct (move_dir tr1); unfold move_pos; lia).
  rewrite Hmv.
  eexists _, _, _; split; [reflexivity|].
  repeat split; try reflexivity.
  intros z Hzl Hzh. unfold write_tape.
  destruct (Z.eqb_spec (z + dx) (p2 + dx));
  destruct (Z.eqb_spec z p2); try lia; try reflexivity.
  apply Htp; assumption.
Qed.

Lemma run1_N_agree_shifted : forall ag1 lo_opt hi dx p p_s s_s tp_s p1 s1 tp1 r p_r s_r tp_r,
  (r <= p)%N ->
  agree1_shifted lo_opt hi dx p1 s1 tp1 p_s s_s tp_s ->
  (forall j, (j < p)%N -> exists pj sj tpj,
    run1_N ag1 j p_s s_s tp_s = Some (pj, sj, tpj) /\
    (match lo_opt with Some lo => lo <= pj | None => True end) /\ pj <= hi) ->
  run1_N ag1 r p_s s_s tp_s = Some (p_r, s_r, tp_r) ->
  exists p1_r s1_r tp1_r,
    run1_N ag1 r p1 s1 tp1 = Some (p1_r, s1_r, tp1_r) /\
    agree1_shifted lo_opt hi dx p1_r s1_r tp1_r p_r s_r tp_r.
Proof.
  intros ag1 lo_opt hi dx p p_s s_s tp_s p1 s1 tp1 r.
  induction r using N.peano_ind; intros p_r s_r tp_r Hle Hagr Hbd Hrun.
  - simpl in Hrun; inversion Hrun; subst; exists p1, s1, tp1; split; [reflexivity|exact Hagr].
  - unfold run1_N in Hrun; rewrite N.iter_succ in Hrun.
    destruct (N.iter r _ (Some (p_s, s_s, tp_s))) as [[[pp sp] tpp]|] eqn:Ep; [|discriminate].
    destruct (IHr pp sp tpp ltac:(lia) Hagr Hbd Ep) as [p1p [s1p [tp1p [E1p Hagr_p]]]].
    destruct (Hbd r ltac:(lia)) as [pj [sj [tpj [Ej [Hlo Hhi]]]]].
    change (N.iter r _ (Some (p_s, s_s, tp_s))) with (run1_N ag1 r p_s s_s tp_s) in Ep.
    rewrite Ep in Ej; inversion Ej; subst pj sj tpj.
    destruct (step1_tape_agree_shifted ag1 lo_opt hi dx p1p s1p tp1p pp sp tpp p_r s_r tp_r Hagr_p Hlo Hhi Hrun)
      as [p1_r [s1_r [tp1_r [Es1 Hagr_r]]]].
    exists p1_r, s1_r, tp1_r; split; [|exact Hagr_r].
    unfold run1_N; rewrite N.iter_succ.
    change (N.iter r _ (Some (p1, s1, tp1))) with (run1_N ag1 r p1 s1 tp1).
    rewrite E1p; exact Es1.
Qed.

Definition agree2_shifted (lo : Z) (hi_opt : option Z) (dx : Z)
  (p1 : Z) (s1 : State) (tp1 : Tape) (p2 : Z) (s2 : State) (tp2 : Tape) : Prop :=
  p1 = p2 + dx /\ s1 = s2 /\
  forall z, lo <= z -> (match hi_opt with Some hi => z <= hi | None => True end) ->
            tp1 (z + dx) = tp2 z.

Lemma step2_tape_agree_shifted : forall ag2 lo hi_opt dx p1 s1 tp1 p2 s2 tp2 p2' s2' tp2',
  agree2_shifted lo hi_opt dx p1 s1 tp1 p2 s2 tp2 ->
  lo <= p2 ->
  (match hi_opt with Some hi => p2 <= hi | None => True end) ->
  step2_tape ag2 p2 s2 tp2 = Some (p2', s2', tp2') ->
  exists p1' s1' tp1',
    step2_tape ag2 p1 s1 tp1 = Some (p1', s1', tp1') /\
    agree2_shifted lo hi_opt dx p1' s1' tp1' p2' s2' tp2'.
Proof.
  intros ag2 lo hi_opt dx p1 s1 tp1 p2 s2 tp2 p2' s2' tp2' [Hp [Hs Htp]] Hlo Hhi Hst.
  unfold step2_tape in *.
  rewrite Hp, Hs, (Htp p2 Hlo Hhi).
  destruct (ag2 s2 (tp2 p2)) as [tr2|]; [|discriminate].
  inversion Hst; subst.
  assert (Hmv : move_pos (p2 + dx) (move_dir tr2) = move_pos p2 (move_dir tr2) + dx)
    by (destruct (move_dir tr2); unfold move_pos; lia).
  rewrite Hmv.
  eexists _, _, _; split; [reflexivity|].
  repeat split; try reflexivity.
  intros z Hzl Hzh. unfold write_tape.
  destruct (Z.eqb_spec (z + dx) (p2 + dx));
  destruct (Z.eqb_spec z p2); try lia; try reflexivity.
  apply Htp; assumption.
Qed.

Lemma run2_N_agree_shifted : forall ag2 lo hi_opt dx p p_s s_s tp_s p1 s1 tp1 r p_r s_r tp_r,
  (r <= p)%N ->
  agree2_shifted lo hi_opt dx p1 s1 tp1 p_s s_s tp_s ->
  (forall j, (j < p)%N -> exists pj sj tpj,
    run2_N ag2 j p_s s_s tp_s = Some (pj, sj, tpj) /\
    lo <= pj /\ (match hi_opt with Some hi => pj <= hi | None => True end)) ->
  run2_N ag2 r p_s s_s tp_s = Some (p_r, s_r, tp_r) ->
  exists p1_r s1_r tp1_r,
    run2_N ag2 r p1 s1 tp1 = Some (p1_r, s1_r, tp1_r) /\
    agree2_shifted lo hi_opt dx p1_r s1_r tp1_r p_r s_r tp_r.
Proof.
  intros ag2 lo hi_opt dx p p_s s_s tp_s p1 s1 tp1 r.
  induction r using N.peano_ind; intros p_r s_r tp_r Hle Hagr Hbd Hrun.
  - simpl in Hrun; inversion Hrun; subst; exists p1, s1, tp1; split; [reflexivity|exact Hagr].
  - unfold run2_N in Hrun; rewrite N.iter_succ in Hrun.
    destruct (N.iter r _ (Some (p_s, s_s, tp_s))) as [[[pp sp] tpp]|] eqn:Ep; [|discriminate].
    destruct (IHr pp sp tpp ltac:(lia) Hagr Hbd Ep) as [p1p [s1p [tp1p [E1p Hagr_p]]]].
    destruct (Hbd r ltac:(lia)) as [pj [sj [tpj [Ej [Hlo Hhi]]]]].
    change (N.iter r _ (Some (p_s, s_s, tp_s))) with (run2_N ag2 r p_s s_s tp_s) in Ep.
    rewrite Ep in Ej; inversion Ej; subst pj sj tpj.
    destruct (step2_tape_agree_shifted ag2 lo hi_opt dx p1p s1p tp1p pp sp tpp p_r s_r tp_r Hagr_p Hlo Hhi Hrun)
      as [p1_r [s1_r [tp1_r [Es1 Hagr_r]]]].
    exists p1_r, s1_r, tp1_r; split; [|exact Hagr_r].
    unfold run2_N; rewrite N.iter_succ.
    change (N.iter r _ (Some (p1, s1, tp1))) with (run2_N ag2 r p1 s1 tp1).
    rewrite E1p; exact Es1.
Qed.
