(** * BB(2,5) holdout 7: the deep-shield reduction

    Machine:
      1RB---3RA2LA2RB_2LB3LA4LB4RA0RA

    This file formalizes the *conditional* reduction that was previously
    proved in Lean.  It does NOT prove that the machine is nonhalting.  The
    candidate invariants [A3ShieldDeep] and [B1Safe] are hypotheses here;
    they are the finite-checked shape conditions, not global theorems.

    Why the distinction matters: the public analysis of this machine records
    a second halt route through a [1] written mid-tape by a dying cascade.
    The reduction below only excludes halts whose predecessor is an
    [A]-on-[3] or [B]-on-[1] with a [1] immediately to its left.  A global
    proof of the two candidate invariants would therefore be a nonhalting
    theorem, not a consequence of the finite checks. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import BB25.
Import ListNotations.

(** ** The literal two-state, five-symbol table *)

Definition tm25 : table5 := fun q s =>
  match q, s with
  | 0, b0 => Some (b1, true, 1)
  | 0, b1 => None
  | 0, b2 => Some (b3, true, 0)
  | 0, b3 => Some (b2, false, 0)
  | 0, b4 => Some (b2, true, 1)
  | 1, b0 => Some (b2, false, 1)
  | 1, b1 => Some (b3, false, 0)
  | 1, b2 => Some (b4, false, 1)
  | 1, b3 => Some (b4, true, 0)
  | 1, b4 => Some (b0, true, 0)
  | _, _ => None
  end.

Definition init25 : conf5 := init5.

Definition Halts25 : Prop := exists n, run5 tm25 n init25 = None.

Definition Reachable25 (c : conf5) : Prop :=
  exists n, run5 tm25 n init25 = Some c.

(** ** The candidate shield predicates *)

Definition NoOneRight (c : conf5) : Prop :=
  ~ In b1 (right5 c).

Definition ShieldBeforeOneDeep (l : list sym5) : Prop :=
  exists (u : list sym5) (zc : sym5) (zs : list sym5),
    l = u ++ b4 :: zc :: zs /\ forall s, In s u -> s <> b1.

Definition A3ShieldDeep : Prop :=
  forall c, Reachable25 c -> st5 c = 0 -> cur5 c = b3 ->
    ShieldBeforeOneDeep (left5 c).

Definition B1Safe : Prop :=
  forall c, Reachable25 c -> st5 c = 1 -> cur5 c = b1 ->
    forall l, left5 c <> b1 :: l.

(** The finite checks establish these predicates only on a prefix.  The
    following record is the exact missing global statement. *)
Record CandidateShield : Prop := {
  candidate_a3 :
    A3ShieldDeep;
  candidate_b1 :
    B1Safe
}.

(** ** [NoOneRight] is a genuine global invariant *)

Lemma no_one_right_tl :
  forall r, ~ In b1 r -> ~ In b1 (tl r).
Proof.
  intros [|a r] H; simpl.
  - exact H.
  - intro Hin. apply H. right. exact Hin.
Qed.

Lemma no_one_right_cons :
  forall w r, w <> b1 -> ~ In b1 r -> ~ In b1 (w :: r).
Proof.
  intros w r Hw Hr [Heq | Hin].
  - exact (Hw Heq).
  - exact (Hr Hin).
Qed.

Lemma no_one_right_step :
  forall c d, NoOneRight c -> step5 tm25 c = Some d -> NoOneRight d.
Proof.
  intros [q l x r] d Hno Hstep.
  destruct q as [|q].
  - destruct x.
    + (* A on 0 *) simpl in Hstep. inversion Hstep; subst d. simpl.
      apply no_one_right_tl. exact Hno.
    + (* A on 1 *) simpl in Hstep. change (None = Some d) in Hstep.
      discriminate Hstep.
    + (* A on 2 *) simpl in Hstep. inversion Hstep; subst d. simpl.
      apply no_one_right_tl. exact Hno.
    + (* A on 3 *) simpl in Hstep. inversion Hstep; subst d. simpl.
      apply no_one_right_cons; [discriminate|exact Hno].
    + (* A on 4 *) simpl in Hstep. inversion Hstep; subst d. simpl.
      apply no_one_right_tl. exact Hno.
  - destruct q as [|q].
    + destruct x.
      * (* B on 0 *) simpl in Hstep. inversion Hstep; subst d. simpl.
        apply no_one_right_cons; [discriminate|exact Hno].
      * (* B on 1 *) simpl in Hstep. inversion Hstep; subst d. simpl.
        apply no_one_right_cons; [discriminate|exact Hno].
      * (* B on 2 *) simpl in Hstep. inversion Hstep; subst d. simpl.
        apply no_one_right_cons; [discriminate|exact Hno].
      * (* B on 3 *) simpl in Hstep. inversion Hstep; subst d. simpl.
        apply no_one_right_tl. exact Hno.
      * (* B on 4 *) simpl in Hstep. inversion Hstep; subst d. simpl.
        apply no_one_right_tl. exact Hno.
    + (* only states 0 and 1 exist in this table *)
      simpl in Hstep. change (None = Some d) in Hstep. discriminate Hstep.
Qed.

Lemma no_one_right_run :
  forall n c d, NoOneRight c -> run5 tm25 n c = Some d -> NoOneRight d.
Proof.
  induction n as [|n IH]; intros c d Hno Hrun.
  - simpl in Hrun. injection Hrun as Hc. subst d. exact Hno.
  - rewrite run5_S in Hrun.
    destruct (step5 tm25 c) as [c'|] eqn:E; [|discriminate].
    apply (IH c' d).
    + eapply no_one_right_step; eauto.
    + exact Hrun.
Qed.

Lemma no_one_right_init : NoOneRight init25.
Proof.
  unfold NoOneRight, init25, init5. simpl. intros [].
Qed.

Lemma no_one_right_reachable :
  forall c, Reachable25 c -> NoOneRight c.
Proof.
  intros c [n Hn].
  eapply no_one_right_run; eauto using no_one_right_init.
Qed.

(** ** Elementary machine facts *)

Lemma tm25_step_none_valid :
  forall c,
    (st5 c = 0 \/ st5 c = 1) ->
    step5 tm25 c = None ->
    st5 c = 0 /\ cur5 c = b1.
Proof.
  intros [q l x r] Hq Hstep.
  destruct q as [|q].
  - destruct x; simpl in Hstep; try discriminate; try (inversion Hstep); auto.
  - destruct q as [|q].
    + destruct x; simpl in Hstep; try discriminate; try (inversion Hstep); auto.
    + destruct Hq as [Hq | Hq]; discriminate Hq.
Qed.

Lemma tm25_step_some_valid :
  forall c d,
    (st5 c = 0 \/ st5 c = 1) ->
    step5 tm25 c = Some d ->
    st5 d = 0 \/ st5 d = 1.
Proof.
  intros [q l x r] d Hq Hstep.
  destruct q as [|q].
  - destruct x; simpl in Hstep; try discriminate;
      inversion Hstep; subst d; simpl; auto.
  - destruct q as [|q].
    + destruct x; simpl in Hstep; try discriminate;
        inversion Hstep; subst d; simpl; auto.
    + destruct Hq as [Hq | Hq]; discriminate Hq.
Qed.

Lemma init25_valid : st5 init25 = 0 \/ st5 init25 = 1.
Proof. simpl. auto. Qed.

Lemma run5_state_valid :
  forall n c0 c,
    (st5 c0 = 0 \/ st5 c0 = 1) ->
    run5 tm25 n c0 = Some c ->
    st5 c = 0 \/ st5 c = 1.
Proof.
  induction n as [|n IH]; intros c0 c Hvalid Hrun.
  - simpl in Hrun. injection Hrun as Hc. subst c. exact Hvalid.
  - rewrite run5_S in Hrun.
    destruct (step5 tm25 c0) as [c'|] eqn:E; [|discriminate].
    apply (IH c' c).
    + eapply tm25_step_some_valid; eauto.
    + exact Hrun.
Qed.

Lemma reachable25_state_valid :
  forall c, Reachable25 c -> st5 c = 0 \/ st5 c = 1.
Proof.
  intros c [n Hn].
  eapply run5_state_valid; eauto using init25_valid.
Qed.

(** ** A halting run has an incoming A-on-1 step *)

(** One-step unfolding, with the predecessor configuration explicit. *)
Lemma run5_succ_run :
  forall n c,
    run5 tm25 (S n) c =
    match run5 tm25 n c with
    | Some c' => step5 tm25 c'
    | None => None
    end.
Proof.
  induction n as [|n IH]; intros c.
  - simpl. destruct (step5 tm25 c); reflexivity.
  - rewrite (run5_S tm25 (S n) c).
    destruct (step5 tm25 c) as [c'|] eqn:E.
    + rewrite (run5_S tm25 n c). rewrite E.
      rewrite (IH c'). reflexivity.
    + rewrite (run5_S tm25 n c). rewrite E. reflexivity.
Qed.

Lemma halt_has_predecessor :
  forall n c,
    run5 tm25 n c = None ->
    exists m, m < n /\ exists d,
      run5 tm25 m c = Some d /\ step5 tm25 d = None.
Proof.
  induction n as [|n IH]; intros c Hrun.
  - simpl in Hrun. discriminate.
  - rewrite run5_S in Hrun.
    destruct (step5 tm25 c) as [c'|] eqn:E.
    + destruct (IH c' Hrun) as [m [Hlt [d [Hd Hnone]]]].
      exists (S m). split; [lia|]. exists d. split; [|exact Hnone].
      rewrite run5_S. rewrite E. exact Hd.
    + exists 0. split; [lia|]. exists c. split; [reflexivity|exact E].
Qed.

Lemma halt_has_incoming_A1 :
  Halts25 ->
  exists p d,
    Reachable25 p /\ step5 tm25 p = Some d /\ st5 d = 0 /\ cur5 d = b1.
Proof.
  intros [n Hn].
  destruct (halt_has_predecessor n init25 Hn)
    as [m [_ [d [Hd Hnone]]]].
  assert (Hvalid : st5 d = 0 \/ st5 d = 1).
  { eapply run5_state_valid; eauto using init25_valid. }
  destruct (tm25_step_none_valid d Hvalid Hnone) as [Hst Hcur].
  destruct m as [|m'].
  - simpl in Hd. injection Hd as Hd. subst d.
    simpl in Hnone. discriminate.
  - rewrite run5_succ_run in Hd.
    destruct (run5 tm25 m' init25) as [p|] eqn:Ep; [|discriminate].
    exists p, d. split; [exists m'; exact Ep|].
    split; [|split]; auto.
Qed.

(** ** The five shapes of an incoming A-on-1 step *)

Lemma step_to_A1_shape :
  forall p d,
    step5 tm25 p = Some d ->
    st5 d = 0 -> cur5 d = b1 ->
    (st5 p = 0 /\ cur5 p = b3 /\ exists l, left5 p = b1 :: l) \/
    (st5 p = 1 /\ cur5 p = b1 /\ exists l, left5 p = b1 :: l) \/
    (st5 p = 0 /\ cur5 p = b2 /\ exists r, right5 p = b1 :: r) \/
    (st5 p = 1 /\ cur5 p = b3 /\ exists r, right5 p = b1 :: r) \/
    (st5 p = 1 /\ cur5 p = b4 /\ exists r, right5 p = b1 :: r).
Proof.
  intros [q l x r] d Hstep Hst Hcur.
  destruct q as [|q].
  - (* state A *)
    destruct x.
    + (* A on 0 *) simpl in Hstep. inversion Hstep; subst d; simpl in Hst; discriminate.
    + (* A on 1 *) simpl in Hstep. change (None = Some d) in Hstep. discriminate Hstep.
    + (* A on 2 -> 3RA, head lands on the first right cell *)
      simpl in Hstep. inversion Hstep; subst d. simpl in *.
      destruct r as [|a r']; [simpl in Hcur; discriminate|].
      simpl in Hcur. subst a.
      right; right; left. repeat split; auto. exists r'; reflexivity.
    + (* A on 3 -> 2LA, head lands on the first left cell *)
      simpl in Hstep. inversion Hstep; subst d. simpl in *.
      destruct l as [|a l']; [simpl in Hcur; discriminate|].
      simpl in Hcur. subst a.
      left. repeat split; auto. exists l'; reflexivity.
    + (* A on 4 -> 2RB, next state B *)
      simpl in Hstep. inversion Hstep; subst d; simpl in Hst; discriminate.
  - destruct q as [|q].
    + (* state B *)
      destruct x.
      * (* B on 0 *) simpl in Hstep. inversion Hstep; subst d; simpl in Hst; discriminate.
      * (* B on 1 -> 3LA, head lands on the first left cell *)
        simpl in Hstep. inversion Hstep; subst d. simpl in *.
        destruct l as [|a l']; [simpl in Hcur; discriminate|].
        simpl in Hcur. subst a.
        right; left. repeat split; auto. exists l'; reflexivity.
      * (* B on 2 *) simpl in Hstep. inversion Hstep; subst d; simpl in Hst; discriminate.
      * (* B on 3 -> 4RA, head lands on the first right cell *)
        simpl in Hstep. inversion Hstep; subst d. simpl in *.
        destruct r as [|a r']; [simpl in Hcur; discriminate|].
        simpl in Hcur. subst a.
        right; right; right; left. repeat split; auto.
        exists r'; reflexivity.
      * (* B on 4 -> 0RA, head lands on the first right cell *)
        simpl in Hstep. inversion Hstep; subst d. simpl in *.
        destruct r as [|a r']; [simpl in Hcur; discriminate|].
        simpl in Hcur. subst a.
        right; right; right; right. repeat split; auto.
        exists r'; reflexivity.
    + (* only states 0 and 1 exist in this table *)
      simpl in Hstep. change (None = Some d) in Hstep. discriminate Hstep.
Qed.

Lemma not_shield_deep_cons_one :
  forall l, ~ ShieldBeforeOneDeep (b1 :: l).
Proof.
  intros l [u [zc [zs [Heq Hu]]]].
  destruct u as [|a u'].
  - simpl in Heq. discriminate.
  - simpl in Heq. injection Heq as Ha _. subst a.
    exact (Hu b1 (or_introl eq_refl) eq_refl).
Qed.

(** ** Conditional nonhalting theorem

    This is the honest Rocq form of the finite-shield result: if the three
    candidate invariants were global, the machine would not halt.  The
    conclusion is not unconditional, and this file deliberately does not
    assert [~ Halts25]. *)

Theorem candidate_shield_no_halt :
  CandidateShield -> ~ Halts25.
Proof.
  intros [HA3 HB1] Hhalt.
  destruct (halt_has_incoming_A1 Hhalt)
    as [p [d [Hreach [Hstep [Hst Hcur]]]]].
  assert (Hno : NoOneRight p) by (apply no_one_right_reachable; exact Hreach).
  destruct (step_to_A1_shape p d Hstep Hst Hcur) as
    [HA3shape | [HB1shape | [HA2shape | [HB3shape | HB4shape]]]].
  - (* A on 3 with a 1 immediately to its left *)
    destruct HA3shape as [Hpst [Hpcur [l Hleft]]].
    pose proof (HA3 p Hreach Hpst Hpcur) as Hshield.
    rewrite Hleft in Hshield.
    exact (not_shield_deep_cons_one l Hshield).
  - (* B on 1 with a 1 immediately to its left *)
    destruct HB1shape as [Hpst [Hpcur [l Hleft]]].
    exact (HB1 p Hreach Hpst Hpcur l Hleft).
  - (* A on 2 moving right onto a 1: impossible by NoOneRight *)
    destruct HA2shape as [_ [_ [r Hright]]].
    exfalso. apply Hno. rewrite Hright. left. reflexivity.
  - (* B on 3 moving right onto a 1: impossible by NoOneRight *)
    destruct HB3shape as [_ [_ [r Hright]]].
    exfalso. apply Hno. rewrite Hright. left. reflexivity.
  - (* B on 4 moving right onto a 1: impossible by NoOneRight *)
    destruct HB4shape as [_ [_ [r Hright]]].
    exfalso. apply Hno. rewrite Hright. left. reflexivity.
Qed.

(** The contrapositive is useful for the public record: any halting run
    would refute at least one of the three finite-checked candidates. *)
Theorem halt_refutes_candidate_shield :
  Halts25 -> ~ CandidateShield.
Proof.
  intros Hhalt Hcandidate.
  exact (candidate_shield_no_halt Hcandidate Hhalt).
Qed.

Print Assumptions candidate_shield_no_halt.
Print Assumptions halt_refutes_candidate_shield.
