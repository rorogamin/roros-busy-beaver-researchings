From Stdlib Require Import Arith Lia.
From Top Require Import BB33_758_TBudget.

(* ------------------------------------------------------------------ *)
(** ** Pass 29: Odd-[c] invariance along [hrun], shallow odd-[a] kill band, and [g4cnt = 0] *)
(* ------------------------------------------------------------------ *)

Lemma odd_c_mod4 (c : nat) (hc : c mod 2 = 1) : c mod 4 = 1 \/ c mod 4 = 3.
Proof.
  pose proof (Nat.div_mod c 4 (ltac:(lia))) as Hd4.
  assert (hm : c mod 4 = 0 \/ c mod 4 = 1 \/ c mod 4 = 2 \/ c mod 4 = 3).
  { pose proof (Nat.mod_upper_bound c 4 (ltac:(lia))). lia. }
  set (q := c / 4) in *.
  destruct hm as [h0 | [h1 | [h2 | h3]]].
  - exfalso.
    assert (He : c mod 2 = 0).
    { replace c with (2 * (2 * q)) by lia. rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity. }
    lia.
  - left. exact h1.
  - exfalso.
    assert (He : c mod 2 = 0).
    { replace c with (2 * (2 * q + 1)) by lia. rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity. }
    lia.
  - right. exact h3.
Qed.

Lemma step_b_odd_c (c : nat) (h1 : c mod 4 = 1) : (3 * ((c - 1) / 2) + 5) mod 2 = 1.
Proof.
  pose proof (half_mod2_of_mod4_one c h1) as hq.
  set (q := (c - 1) / 2) in *.
  exact (three_mul_add5_odd q hq).
Qed.

Lemma step_c_odd_c (c : nat) (h3 : c mod 4 = 3) : (3 * ((c - 1) / 2) + 8) mod 2 = 1.
Proof.
  pose proof (half_mod2_of_mod4_three c h3) as hq.
  set (q := (c - 1) / 2) in *.
  exact (three_mul_add8_odd q hq).
Qed.

Lemma sub_odd_odd_add1 (a c : nat) (hle : a <= c) (ha : a mod 2 = 1) (hc : c mod 2 = 1) :
    (c - a + 1) mod 2 = 1.
Proof.
  pose proof (Nat.div_mod a 2 (ltac:(lia))) as Hda.
  pose proof (Nat.div_mod c 2 (ltac:(lia))) as Hdc.
  set (qa := a / 2) in *. set (qc := c / 2) in *.
  replace (c - a + 1) with (2 * (qc - qa) + 1) by lia.
  rewrite Nat.add_comm, Nat.mul_comm, Nat.Div0.mod_add. reflexivity.
Qed.

(** Every non-stopping step of [hrun] preserves [c mod 2 = 1]. *)
Lemma step_odd_c (a c a' c' : nat) (hc : c mod 2 = 1)
    (hs : step a c = Next a' c') (ha1 : a' <> 1) : c' mod 2 = 1.
Proof.
  destruct (Nat.leb a c) eqn:E1.
  - assert (hle : a <= c) by (apply Nat.leb_le; exact E1).
    destruct (Nat.eqb (a mod 2) 0) eqn:E2.
    + assert (E3 : Nat.eqb (c mod 2) 0 = false) by (apply Nat.eqb_neq; lia).
      rewrite (step_h a c E1 E2 E3) in hs. inversion hs; subst.
      exfalso. apply ha1. reflexivity.
    + assert (ha1m : a mod 2 = 1).
      { pose proof (Nat.mod_upper_bound a 2 (ltac:(lia))).
        apply Nat.eqb_neq in E2. lia. }
      assert (E3 : Nat.eqb (c mod 2) 0 = false) by (apply Nat.eqb_neq; lia).
      rewrite (step_j a c E1 E2 E3) in hs. inversion hs; subst.
      exact (sub_odd_odd_add1 a c hle ha1m hc).
  - assert (hm : c mod 4 = 1 \/ c mod 4 = 3) by (exact (odd_c_mod4 c hc)).
    destruct hm as [h1 | h3].
    + assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
        by (apply orb_mod4_false; lia).
      assert (E5 : Nat.eqb (c mod 4) 1 = true) by (apply Nat.eqb_eq; exact h1).
      destruct (Nat.eqb a (c + 1)) eqn:E6.
      * rewrite (step_f a c E1 E4 E5 E6) in hs. discriminate hs.
      * rewrite (step_b a c E1 E4 E5 E6) in hs. inversion hs; subst.
        exact (step_b_odd_c c h1).
    + assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
        by (apply orb_mod4_false; lia).
      assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
      destruct (Nat.eqb a (c + 1)) eqn:E6.
      * rewrite (step_halt1 a c E1 E4 E5 E6) in hs. discriminate hs.
      * destruct (Nat.eqb a (c + 2)) eqn:E7.
        -- rewrite (step_e a c E1 E4 E5 E6 E7) in hs. inversion hs; subst. reflexivity.
        -- destruct (Nat.eqb a (c + 3)) eqn:E8.
           ++ rewrite (step_halt3 a c E1 E4 E5 E6 E7 E8) in hs. discriminate hs.
           ++ rewrite (step_c a c E1 E4 E5 E6 E7 E8) in hs. inversion hs; subst.
              exact (step_c_odd_c c h3).
Qed.

(** **[c] stays odd throughout any halving run started at odd [c].** *)
Lemma hrun_odd_c (c0 : nat) : forall (n a c a' c' : nat),
    c mod 2 = 1 -> hrun c0 n a c = Some (a', c') -> c' mod 2 = 1.
Proof.
  induction n as [|n ih]; intros a c a' c' hc hr.
  - cbn [hrun] in hr. inversion hr; subst. exact hc.
  - cbn [hrun] in hr. destruct (step a c) as [|a1 c1] eqn:hs.
    + discriminate hr.
    + destruct (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) eqn:Estop.
      * discriminate hr.
      * assert (ha1 : a1 <> 1).
        { intro heq. subst a1. rewrite Nat.eqb_refl in Estop. discriminate Estop. }
        assert (hc1 : c1 mod 2 = 1) by (exact (step_odd_c a c a1 c1 hc hs ha1)).
        exact (ih a1 c1 a' c' hc1 hr).
Qed.

Lemma sub_odd_odd_even (a c k : nat) (hle : c + k <= a) (ha : a mod 2 = 1) (hc : c mod 2 = 1)
    (hk : k = 2 \/ k = 4) : (a - c - k) mod 2 = 0.
Proof.
  pose proof (Nat.div_mod a 2 (ltac:(lia))) as Hda.
  pose proof (Nat.div_mod c 2 (ltac:(lia))) as Hdc.
  set (qa := a / 2) in *. set (qc := c / 2) in *.
  destruct hk as [hk | hk]; subst k.
  - replace (a - c - 2) with (2 * (qa - qc - 1)) by lia.
    rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity.
  - replace (a - c - 4) with (2 * (qa - qc - 2)) by lia.
    rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity.
Qed.

(** **Shallow odd-[a] kill band**: on odd [c], every odd [a] with [c < a] and
    [2 * a <= 5 * c + 11] dies in at most two halving steps. *)
Lemma hrun_two_odd_a_shallow (c0 a c : nat) (hc0 : 2 <= c0)
    (hc : c mod 2 = 1) (ha : a mod 2 = 1) (hlt : c < a) (hub : 2 * a <= 5 * c + 11) :
    hrun c0 2 a c = None.
Proof.
  assert (E1c : Nat.leb a c = false) by (apply Nat.leb_gt; lia).
  assert (hm : c mod 4 = 1 \/ c mod 4 = 3) by (exact (odd_c_mod4 c hc)).
  pose proof (Nat.div_mod c 2 (ltac:(lia))) as Hdc.
  assert (Hc1 : 1 <= c).
  { pose proof (Nat.div_mod c 2 (ltac:(lia))). set (qc := c / 2) in *. lia. }
  assert (Hdiv : 2 * ((c - 1) / 2) = c - 1).
  { pose proof (Nat.div_mod (c - 1) 2 (ltac:(lia))) as Hd1.
    assert (Hm1 : (c - 1) mod 2 = 0).
    { set (qc := c / 2) in *. replace (c - 1) with (2 * qc) by lia.
      rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity. }
    set (q1 := (c - 1) / 2) in *. lia. }
  assert (Hge2 : c + 2 <= a).
  { set (qc := c / 2) in *. pose proof (Nat.div_mod a 2 (ltac:(lia))). set (qa := a / 2) in *. lia. }
  destruct hm as [h1 | h3].
  - assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
      by (apply orb_mod4_false; lia).
    assert (E5 : Nat.eqb (c mod 4) 1 = true) by (apply Nat.eqb_eq; exact h1).
    assert (E6 : Nat.eqb a (c + 1) = false) by (apply Nat.eqb_neq; lia).
    assert (hstep : step a c = Next (a - c - 2) (3 * ((c - 1) / 2) + 5))
      by (exact (step_b a c E1c E4 E5 E6)).
    apply (hrun_two_step c0 a c (a - c - 2) (3 * ((c - 1) / 2) + 5) hstep).
    apply (hrun_stops_of_even_le c0 (a - c - 2) (3 * ((c - 1) / 2) + 5)).
    + set (q := (c - 1) / 2) in *. lia.
    + exact (sub_odd_odd_even a c 2 Hge2 ha hc (or_introl eq_refl)).
  - assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
      by (apply orb_mod4_false; lia).
    assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
    assert (E6 : Nat.eqb a (c + 1) = false) by (apply Nat.eqb_neq; lia).
    destruct (Nat.eq_dec a (c + 2)) as [ha2 | hne2].
    + assert (E7 : Nat.eqb a (c + 2) = true) by (apply Nat.eqb_eq; exact ha2).
      assert (hstep : step a c = Next (3 * c + 8) 1)
        by (exact (step_e a c E1c E4 E5 E6 E7)).
      assert (hstop2 : 2 * 1 <= c0) by lia.
      exact (hrun_two_stop c0 a c (3 * c + 8) 1 hstep (or_intror hstop2)).
    + assert (Hge4 : c + 4 <= a).
      { set (qc := c / 2) in *. pose proof (Nat.div_mod a 2 (ltac:(lia))). set (qa := a / 2) in *. lia. }
      assert (E7 : Nat.eqb a (c + 2) = false) by (apply Nat.eqb_neq; exact hne2).
      assert (E8 : Nat.eqb a (c + 3) = false) by (apply Nat.eqb_neq; lia).
      assert (hstep : step a c = Next (a - c - 4) (3 * ((c - 1) / 2) + 8))
        by (exact (step_c a c E1c E4 E5 E6 E7 E8)).
      apply (hrun_two_step c0 a c (a - c - 4) (3 * ((c - 1) / 2) + 8) hstep).
      apply (hrun_stops_of_even_le c0 (a - c - 4) (3 * ((c - 1) / 2) + 8)).
      * set (q := (c - 1) / 2) in *. lia.
      * exact (sub_odd_odd_even a c 4 Hge4 ha hc (or_intror eq_refl)).
Qed.

(** **Zero gap-4 collapses on every surviving odd-[c] halving run.** *)
Lemma g4cnt_zero_of_odd_survives (c0 : nat) : forall (n a c : nat),
    c mod 2 = 1 -> HSurvives c0 (S n) a c -> g4cnt c0 n a c = 0.
Proof.
  induction n as [|n ih]; intros a c hc hs.
  - reflexivity.
  - destruct hs as [af [cf hr]].
    assert (hnotg4 : ~ g4 a c).
    { intro hg. destruct hg as [_ hgap]. subst a.
      assert (h2 : hrun c0 2 (c + 4) c = None)
        by (exact (hrun_two_gap_four_odd c0 c (odd_c_mod4 c hc))).
      cbn [hrun] in hr, h2.
      destruct (step (c + 4) c) as [|a1 c1]; [discriminate hr|].
      destruct (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)); [discriminate hr|].
      destruct (step a1 c1) as [|a2 c2]; [discriminate hr|].
      destruct (orb (Nat.eqb a2 1) (Nat.leb (2 * c2) c0)); [discriminate hr | discriminate h2]. }
    cbn [hrun] in hr.
    destruct (step a c) as [|a1 c1] eqn:hstep; [discriminate hr|].
    destruct (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) eqn:Estop; [discriminate hr|].
    assert (ha1 : a1 <> 1).
    { intro heq. subst a1. rewrite Nat.eqb_refl in Estop. discriminate Estop. }
    assert (hc1 : c1 mod 2 = 1) by (exact (step_odd_c a c a1 c1 hc hstep ha1)).
    assert (hrec : g4cnt c0 n a1 c1 = 0) by (exact (ih a1 c1 hc1 (ex_intro _ af (ex_intro _ cf hr)))).
    assert (Eg4 : g4b a c = false).
    { destruct (g4b a c) eqn:E; [exfalso; apply hnotg4; apply (proj1 (g4b_spec a c)); exact E | reflexivity]. }
    cbn [g4cnt]. rewrite hstep, Estop, Eg4, hrec. reflexivity.
Qed.

Print Assumptions odd_c_mod4.
Print Assumptions step_b_odd_c.
Print Assumptions step_c_odd_c.
Print Assumptions sub_odd_odd_add1.
Print Assumptions step_odd_c.
Print Assumptions hrun_odd_c.
Print Assumptions sub_odd_odd_even.
Print Assumptions hrun_two_odd_a_shallow.
Print Assumptions g4cnt_zero_of_odd_survives.

(* ------------------------------------------------------------------ *)
(** ** Pass 30: Surviving [L]-phase length [>= 2] and the [5/11] [J]-exit ratio *)
(* ------------------------------------------------------------------ *)

(** When [c mod 4 = 3] and [a] is odd, the two-step kill band extends to [2 * a <= 5 * c + 21]. *)
Lemma hrun_two_odd_a_mod3_wide (c0 a c : nat) (hc0 : 2 <= c0)
    (h3 : c mod 4 = 3) (ha : a mod 2 = 1) (hlt : c < a) (hub : 2 * a <= 5 * c + 21) :
    hrun c0 2 a c = None.
Proof.
  assert (hc : c mod 2 = 1).
  { pose proof (Nat.div_mod c 4 (ltac:(lia))). set (q4 := c / 4) in *.
    replace c with (2 * (2 * q4 + 1) + 1) by lia.
    rewrite Nat.add_comm, Nat.mul_comm, Nat.Div0.mod_add. reflexivity. }
  assert (E1c : Nat.leb a c = false) by (apply Nat.leb_gt; lia).
  assert (Hc1 : 1 <= c).
  { pose proof (Nat.div_mod c 2 (ltac:(lia))). set (qc := c / 2) in *. lia. }
  assert (Hdiv : 2 * ((c - 1) / 2) = c - 1).
  { pose proof (Nat.div_mod c 2 (ltac:(lia))) as Hdc.
    pose proof (Nat.div_mod (c - 1) 2 (ltac:(lia))) as Hd1.
    assert (Hm1 : (c - 1) mod 2 = 0).
    { set (qc := c / 2) in *. replace (c - 1) with (2 * qc) by lia.
      rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity. }
    set (q1 := (c - 1) / 2) in *. lia. }
  assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
    by (apply orb_mod4_false; lia).
  assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
  assert (E6 : Nat.eqb a (c + 1) = false).
  { apply Nat.eqb_neq. pose proof (Nat.div_mod a 2 (ltac:(lia))). pose proof (Nat.div_mod c 2 (ltac:(lia))).
    set (qa := a / 2) in *. set (qc := c / 2) in *. lia. }
  destruct (Nat.eq_dec a (c + 2)) as [ha2 | hne2].
  - assert (E7 : Nat.eqb a (c + 2) = true) by (apply Nat.eqb_eq; exact ha2).
    assert (hstep : step a c = Next (3 * c + 8) 1) by (exact (step_e a c E1c E4 E5 E6 E7)).
    assert (hstop2 : 2 * 1 <= c0) by lia.
    exact (hrun_two_stop c0 a c (3 * c + 8) 1 hstep (or_intror hstop2)).
  - assert (Hge4 : c + 4 <= a).
    { pose proof (Nat.div_mod a 2 (ltac:(lia))). pose proof (Nat.div_mod c 2 (ltac:(lia))).
      set (qa := a / 2) in *. set (qc := c / 2) in *. lia. }
    assert (E7 : Nat.eqb a (c + 2) = false) by (apply Nat.eqb_neq; exact hne2).
    assert (E8 : Nat.eqb a (c + 3) = false) by (apply Nat.eqb_neq; lia).
    assert (hstep : step a c = Next (a - c - 4) (3 * ((c - 1) / 2) + 8))
      by (exact (step_c a c E1c E4 E5 E6 E7 E8)).
    apply (hrun_two_step c0 a c (a - c - 4) (3 * ((c - 1) / 2) + 8) hstep).
    apply (hrun_stops_of_even_le c0 (a - c - 4) (3 * ((c - 1) / 2) + 8)).
    + set (q := (c - 1) / 2) in *. lia.
    + exact (sub_odd_odd_even a c 4 Hge4 ha hc (or_intror eq_refl)).
Qed.

(** **Every surviving odd-[a], odd-[c] [L]-start satisfies [5 * c + 13 <= 2 * a].** *)
Lemma surviving_L_start_ratio (c0 a c : nat) (hc0 : 2 <= c0)
    (hc : c mod 2 = 1) (ha : a mod 2 = 1) (hlt : c < a) (hs : HSurvives c0 2 a c) :
    5 * c + 13 <= 2 * a.
Proof.
  destruct hs as [af [cf hr]].
  destruct (Nat.leb (2 * a) (5 * c + 11)) eqn:E.
  - apply Nat.leb_le in E.
    rewrite (hrun_two_odd_a_shallow c0 a c hc0 hc ha hlt E) in hr. discriminate hr.
  - apply Nat.leb_gt in E.
    pose proof (Nat.div_mod c 2 (ltac:(lia))). set (qc := c / 2) in *. lia.
Qed.

(** **Every surviving odd-[a], odd-[c] [L]-start stays in [L] after step 1** with even [a']
    and odd [c'], forcing every surviving tail [L]-phase to have length at least 2. *)
Lemma surviving_L_next_in_L (c0 a c : nat) (hc0 : 2 <= c0)
    (hc : c mod 2 = 1) (ha : a mod 2 = 1) (hlt : c < a) (hs : HSurvives c0 2 a c) :
    exists a' c', step a c = Next a' c' /\ c' < a' /\ a' mod 2 = 0 /\ c' mod 2 = 1.
Proof.
  assert (hrat : 5 * c + 13 <= 2 * a) by (exact (surviving_L_start_ratio c0 a c hc0 hc ha hlt hs)).
  assert (E1c : Nat.leb a c = false) by (apply Nat.leb_gt; lia).
  assert (Hc1 : 1 <= c).
  { pose proof (Nat.div_mod c 2 (ltac:(lia))). set (qc := c / 2) in *. lia. }
  assert (Hdiv : 2 * ((c - 1) / 2) = c - 1).
  { pose proof (Nat.div_mod c 2 (ltac:(lia))) as Hdc.
    pose proof (Nat.div_mod (c - 1) 2 (ltac:(lia))) as Hd1.
    assert (Hm1 : (c - 1) mod 2 = 0).
    { set (qc := c / 2) in *. replace (c - 1) with (2 * qc) by lia.
      rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity. }
    set (q1 := (c - 1) / 2) in *. lia. }
  assert (hm : c mod 4 = 1 \/ c mod 4 = 3) by (exact (odd_c_mod4 c hc)).
  destruct hm as [h1 | h3].
  - exists (a - c - 2), (3 * ((c - 1) / 2) + 5).
    assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
      by (apply orb_mod4_false; lia).
    assert (E5 : Nat.eqb (c mod 4) 1 = true) by (apply Nat.eqb_eq; exact h1).
    assert (E6 : Nat.eqb a (c + 1) = false) by (apply Nat.eqb_neq; lia).
    split; [exact (step_b a c E1c E4 E5 E6) |].
    split; [set (q := (c - 1) / 2) in *; lia |].
    split; [exact (sub_odd_odd_even a c 2 (ltac:(lia)) ha hc (or_introl eq_refl)) |].
    exact (step_b_odd_c c h1).
  - destruct hs as [af [cf hr]].
    assert (hwide : 5 * c + 22 <= 2 * a).
    { destruct (Nat.leb (2 * a) (5 * c + 21)) eqn:Ew.
      - apply Nat.leb_le in Ew.
        rewrite (hrun_two_odd_a_mod3_wide c0 a c hc0 h3 ha hlt Ew) in hr. discriminate hr.
      - apply Nat.leb_gt in Ew. lia. }
    exists (a - c - 4), (3 * ((c - 1) / 2) + 8).
    assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
      by (apply orb_mod4_false; lia).
    assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
    assert (E6 : Nat.eqb a (c + 1) = false) by (apply Nat.eqb_neq; lia).
    assert (E7 : Nat.eqb a (c + 2) = false) by (apply Nat.eqb_neq; lia).
    assert (E8 : Nat.eqb a (c + 3) = false) by (apply Nat.eqb_neq; lia).
    split; [exact (step_c a c E1c E4 E5 E6 E7 E8) |].
    split; [set (q := (c - 1) / 2) in *; lia |].
    split; [exact (sub_odd_odd_even a c 4 (ltac:(lia)) ha hc (or_intror eq_refl)) |].
    exact (step_c_odd_c c h3).
Qed.

(** **Every surviving [J -> L] exit satisfies [5 * c + 14 <= 11 * a].** *)
Lemma surviving_J_exit_ratio (c0 a c : nat) (hc0 : 2 <= c0)
    (hc : c mod 2 = 1) (ha : a mod 2 = 1) (hle : a <= c)
    (hexit : c - a + 1 < 3 * a + 2) (hs : HSurvives c0 3 a c) :
    5 * c + 14 <= 11 * a.
Proof.
  destruct hs as [af [cf hr]].
  assert (E1 : Nat.leb a c = true) by (apply Nat.leb_le; exact hle).
  assert (E2 : Nat.eqb (a mod 2) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (E3 : Nat.eqb (c mod 2) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (hsp : step a c = Next (3 * a + 2) (c - a + 1)) by (exact (step_j a c E1 E2 E3)).
  cbn [hrun] in hr. rewrite hsp in hr.
  destruct (orb (Nat.eqb (3 * a + 2) 1) (Nat.leb (2 * (c - a + 1)) c0)) eqn:Estop.
  - discriminate hr.
  - assert (ha' : (3 * a + 2) mod 2 = 1).
    { pose proof (Nat.div_mod a 2 (ltac:(lia))). set (qa := a / 2) in *.
      replace (3 * a + 2) with (2 * (3 * qa + 2) + 1) by lia.
      rewrite Nat.add_comm, Nat.mul_comm, Nat.Div0.mod_add. reflexivity. }
    assert (hc' : (c - a + 1) mod 2 = 1) by (exact (sub_odd_odd_add1 a c hle ha hc)).
    assert (hrat : 5 * (c - a + 1) + 13 <= 2 * (3 * a + 2))
      by (exact (surviving_L_start_ratio c0 (3 * a + 2) (c - a + 1) hc0 hc' ha' hexit
                  (ex_intro _ af (ex_intro _ cf hr)))).
    lia.
Qed.

Print Assumptions hrun_two_odd_a_mod3_wide.
Print Assumptions surviving_L_start_ratio.
Print Assumptions surviving_L_next_in_L.
Print Assumptions surviving_J_exit_ratio.

(* ------------------------------------------------------------------ *)
(** ** Pass 31: Infinite Cantor-gap theorem: every surviving odd-[a] [L]-phase has even length [>= 2] *)
(* ------------------------------------------------------------------ *)

Lemma sub_odd_parity_flip (a c k : nat) (hle : c + k <= a) (hc : c mod 2 = 1)
    (hk : k = 2 \/ k = 4) : (a - c - k + a) mod 2 = 1.
Proof.
  pose proof (Nat.div_mod a 2 (ltac:(lia))) as Hda.
  pose proof (Nat.div_mod c 2 (ltac:(lia))) as Hdc.
  set (qa := a / 2) in *. set (qc := c / 2) in *.
  set (ra := a mod 2) in *.
  assert (Hra : ra = 0 \/ ra = 1).
  { subst ra. pose proof (Nat.mod_upper_bound a 2 (ltac:(lia))). lia. }
  destruct hk as [hk | hk]; subst k.
  - replace (a - c - 2 + a) with (2 * (2 * qa + ra - qc - 2) + 1) by lia.
    rewrite Nat.add_comm, Nat.mul_comm, Nat.Div0.mod_add. reflexivity.
  - replace (a - c - 4 + a) with (2 * (2 * qa + ra - qc - 3) + 1) by lia.
    rewrite Nat.add_comm, Nat.mul_comm, Nat.Div0.mod_add. reflexivity.
Qed.

Lemma Q_b_ge5 (a c q : nat) (hc1 : 1 <= c) (hge2 : c + 2 <= a) (hq : 2 * q = c - 1) :
    Q a c + 5 <= Q (a - c - 2) (3 * q + 5).
Proof. unfold Q. lia. Qed.

Lemma Q_c_ge5 (a c q : nat) (hc1 : 1 <= c) (hge4 : c + 4 <= a) (hq : 2 * q = c - 1) :
    Q a c + 5 <= Q (a - c - 4) (3 * q + 8).
Proof. unfold Q. lia. Qed.

(** A surviving [L]-step of [hrun] (with [2 <= c0] and [c] odd) cannot take rule [e],
    preserves [c mod 2 = 1], flips [a mod 2], and raises [Q] by at least 5. *)
Lemma hrun_L_one_step_parity (c0 a c a' c' : nat) (hc0 : 2 <= c0)
    (hc : c mod 2 = 1) (hlt : c < a)
    (h1 : hrun c0 1 a c = Some (a', c')) :
    c' mod 2 = 1 /\ (a' + a) mod 2 = 1 /\ Q a c + 5 <= Q a' c'.
Proof.
  assert (E1c : Nat.leb a c = false) by (apply Nat.leb_gt; lia).
  assert (Hc1 : 1 <= c).
  { pose proof (Nat.div_mod c 2 (ltac:(lia))). set (qc := c / 2) in *. lia. }
  assert (Hdiv : 2 * ((c - 1) / 2) = c - 1).
  { pose proof (Nat.div_mod c 2 (ltac:(lia))) as Hdc.
    pose proof (Nat.div_mod (c - 1) 2 (ltac:(lia))) as Hd1.
    assert (Hm1 : (c - 1) mod 2 = 0).
    { set (qc := c / 2) in *. replace (c - 1) with (2 * qc) by lia.
      rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity. }
    set (q1 := (c - 1) / 2) in *. lia. }
  assert (hm : c mod 4 = 1 \/ c mod 4 = 3) by (exact (odd_c_mod4 c hc)).
  destruct hm as [hmod1 | hmod3].
  - assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
      by (apply orb_mod4_false; lia).
    assert (E5 : Nat.eqb (c mod 4) 1 = true) by (apply Nat.eqb_eq; exact hmod1).
    destruct (Nat.eqb a (c + 1)) eqn:E6.
    + cbn [hrun] in h1. rewrite (step_f a c E1c E4 E5 E6) in h1. discriminate h1.
    + assert (Hge2 : c + 2 <= a) by (apply Nat.eqb_neq in E6; lia).
      change (match step a c with | Halt => None | Next a1 c1 => if orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0) then None else Some (a1, c1) end = Some (a', c')) in h1.
      rewrite (step_b a c E1c E4 E5 E6) in h1. cbv iota beta in h1.
      destruct (orb (Nat.eqb (a - c - 2) 1) (Nat.leb (2 * (3 * ((c - 1) / 2) + 5)) c0)); [discriminate h1|].
      inversion h1; subst.
      split; [exact (step_b_odd_c c hmod1) |].
      split; [exact (sub_odd_parity_flip a c 2 Hge2 hc (or_introl eq_refl)) |].
      exact (Q_b_ge5 a c ((c - 1) / 2) Hc1 Hge2 Hdiv).
  - assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
      by (apply orb_mod4_false; lia).
    assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
    destruct (Nat.eqb a (c + 1)) eqn:E6.
    + cbn [hrun] in h1. rewrite (step_halt1 a c E1c E4 E5 E6) in h1. discriminate h1.
    + destruct (Nat.eqb a (c + 2)) eqn:E7.
      * cbn [hrun] in h1. rewrite (step_e a c E1c E4 E5 E6 E7) in h1.
        assert (Ele : Nat.leb (2 * 1) c0 = true) by (apply Nat.leb_le; lia).
        rewrite Ele, Bool.orb_true_r in h1. discriminate h1.
      * destruct (Nat.eqb a (c + 3)) eqn:E8.
        -- cbn [hrun] in h1. rewrite (step_halt3 a c E1c E4 E5 E6 E7 E8) in h1. discriminate h1.
        -- assert (Hge4 : c + 4 <= a).
           { apply Nat.eqb_neq in E6. apply Nat.eqb_neq in E7. apply Nat.eqb_neq in E8. lia. }
           change (match step a c with | Halt => None | Next a1 c1 => if orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0) then None else Some (a1, c1) end = Some (a', c')) in h1.
           rewrite (step_c a c E1c E4 E5 E6 E7 E8) in h1. cbv iota beta in h1.
           destruct (orb (Nat.eqb (a - c - 4) 1) (Nat.leb (2 * (3 * ((c - 1) / 2) + 8)) c0)); [discriminate h1|].
           inversion h1; subst.
           split; [exact (step_c_odd_c c hmod3) |].
           split; [exact (sub_odd_parity_flip a c 4 Hge4 hc (or_intror eq_refl)) |].
           exact (Q_c_ge5 a c ((c - 1) / 2) Hc1 Hge4 Hdiv).
Qed.

Lemma parity_step_combine (an a1 a n : nat)
    (hflip : (a1 + a) mod 2 = 1) (hpar : (an + a1 + n) mod 2 = 0) :
    (an + a + S n) mod 2 = 0.
Proof.
  pose proof (Nat.div_mod (a1 + a) 2 (ltac:(lia))) as H1.
  pose proof (Nat.div_mod (an + a1 + n) 2 (ltac:(lia))) as H2.
  set (q1 := (a1 + a) / 2) in *. set (q2 := (an + a1 + n) / 2) in *.
  replace (an + a + S n) with (2 * (q1 + q2 + 1 - a1)) by lia.
  rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity.
Qed.

(** Inductive parity and [Q]-growth invariant across an [n]-step [L]-phase of [hrun]. *)
Lemma hrun_L_run_parity (c0 : nat) (hc0 : 2 <= c0) :
    forall (n a c an cn : nat),
      c mod 2 = 1 ->
      (forall i, i < n -> snd (st c0 i a c) < fst (st c0 i a c)) ->
      hrun c0 n a c = Some (an, cn) ->
      cn mod 2 = 1 /\ (an + a + n) mod 2 = 0 /\ Q a c + 5 * n <= Q an cn.
Proof.
  induction n as [|n ih]; intros a c an cn hc hL hr.
  - cbn [hrun] in hr. inversion hr; subst.
    split; [exact hc |].
    split.
    + replace (an + an + 0) with (2 * an) by lia.
      rewrite Nat.mul_comm, Nat.Div0.mod_mul. reflexivity.
    + lia.
  - assert (hlt0 : c < a) by (exact (hL 0 (ltac:(lia)))).
    cbn [hrun] in hr.
    destruct (step a c) as [|a1 c1] eqn:hs; [discriminate hr|].
    destruct (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) eqn:Estop; [discriminate hr|].
    assert (hr1 : hrun c0 1 a c = Some (a1, c1)).
    { cbn [hrun]. rewrite hs, Estop. reflexivity. }
    destruct (hrun_L_one_step_parity c0 a c a1 c1 hc0 hc hlt0 hr1) as [hc1 [hflip hQ1]].
    assert (hL' : forall i, i < n -> snd (st c0 i a1 c1) < fst (st c0 i a1 c1)).
    { intros i hi.
      pose proof (hL (S i) (ltac:(lia))) as hsi.
      cbn [st] in hsi. rewrite hs, Estop in hsi. exact hsi. }
    destruct (ih a1 c1 an cn hc1 hL' hr) as [hcn [hpar hQn]].
    split; [exact hcn |].
    split; [exact (parity_step_combine an a1 a n hflip hpar) |].
    lia.
Qed.

(** **Infinite Cantor-gap theorem**: every surviving [L]-phase starting at odd [a], odd [c]
    that closes into [J] ([an <= cn]) must have **even length [n >= 2]** and raise [Q] by
    at least 10. *)
Lemma L_phase_even_of_survives (c0 n a c an cn : nat) (hc0 : 2 <= c0)
    (hc : c mod 2 = 1) (ha : a mod 2 = 1) (hlt : c < a)
    (hL : forall i, i < n -> snd (st c0 i a c) < fst (st c0 i a c))
    (hrn : hrun c0 n a c = Some (an, cn))
    (hclose : an <= cn)
    (hsurv : HSurvives c0 (n + 1) a c) :
    n mod 2 = 0 /\ 2 <= n /\ Q a c + 10 <= Q an cn.
Proof.
  destruct (hrun_L_run_parity c0 hc0 n a c an cn hc hL hrn) as [hcn [hpar hQn]].
  assert (hne0 : n <> 0).
  { intro h0. subst n. cbn [hrun] in hrn. inversion hrn; subst. lia. }
  assert (heven : n mod 2 = 0).
  { pose proof (Nat.mod_upper_bound n 2 (ltac:(lia))) as Hmn.
    destruct (Nat.eq_dec (n mod 2) 0) as [he | hne]; [exact he |].
    assert (hodd : n mod 2 = 1) by lia.
    assert (han_even : an mod 2 = 0).
    { pose proof (Nat.div_mod an 2 (ltac:(lia))).
      pose proof (Nat.div_mod a 2 (ltac:(lia))).
      pose proof (Nat.div_mod n 2 (ltac:(lia))).
      pose proof (Nat.div_mod (an + a + n) 2 (ltac:(lia))).
      pose proof (Nat.mod_upper_bound an 2 (ltac:(lia))).
      set (qan := an / 2) in *. set (qa := a / 2) in *.
      set (qn := n / 2) in *. set (qs := (an + a + n) / 2) in *. lia. }
    assert (hdie : hrun c0 1 an cn = None)
      by (exact (hrun_stops_of_even_le c0 an cn hclose han_even)).
    destruct hsurv as [af [cf hrf]].
    rewrite (hrun_add c0 n 1 a c an cn hrn) in hrf.
    rewrite hdie in hrf. discriminate hrf. }
  assert (hge2 : 2 <= n).
  { pose proof (Nat.div_mod n 2 (ltac:(lia))). set (qn := n / 2) in *. lia. }
  split; [exact heven | split; [exact hge2 | lia]].
Qed.

Print Assumptions sub_odd_parity_flip.
Print Assumptions hrun_L_one_step_parity.
Print Assumptions parity_step_combine.
Print Assumptions hrun_L_run_parity.
Print Assumptions L_phase_even_of_survives.
