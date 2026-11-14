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
