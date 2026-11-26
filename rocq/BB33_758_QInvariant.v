From Stdlib Require Import Arith Lia List ZArith.

(** Holdout #758: the [Q] invariant of the 10-rule acceleration.

    [Q(a,c)=a+2c] is twice [a/2+c].  Every non-halting rule increases [Q]
    by a fixed positive integer weight.  The base-2 pair identity is

      A(1,2m+1) --j--> A(5,2m+1),
      A(1,2m)   --i,j--> A(11,2m+1).

    If the two chains use the same rule word, their h-endpoints differ by
    exactly 3.  For arbitrary (possibly different) words,
    [pair_endpoint_length_bound] proves the quantitative bound
    [|F(11,c)-F(5,c)| <= (9*max(L5,L11)+6)/2].  The remaining input is a
    universal bound on the rule-word lengths; see BB33_758_ATTACK.md. *)

Inductive Rule := j | i | a | b | c | e | h.

Definition weight (r : Rule) : nat :=
  match r with
  | j => 4
  | i => 8
  | a => 3
  | b => 5
  | c => 9
  | e => 8
  | h => 5
  end.

Definition apply (r : Rule) (p : nat * nat) : nat * nat :=
  match r, p with
  | j, (x, y) => (3 * x + 2, y - x + 1)
  | i, (x, y) => (3 * x, y - x + 4)
  | a, (x, y) => (x - y - 1, 3 * (y / 2) + 2)
  | b, (x, y) => (x - y - 2, 3 * ((y - 1) / 2) + 5)
  | c, (x, y) => (x - y - 4, 3 * ((y - 1) / 2) + 8)
  | e, (x, y) => (3 * y + 8, 1)
  | h, (x, y) => (1, x / 2 + y + 2)
  end.

Definition Q (p : nat * nat) : nat := fst p + 2 * snd p.

Definition Valid (r : Rule) (p : nat * nat) : Prop :=
  match r, p with
  | j, (x, y) => x <= y /\ x mod 2 = 1 /\ y mod 2 = 1
  | i, (x, y) => x <= y /\ x mod 2 = 1 /\ y mod 2 = 0
  | a, (x, y) => y < x /\ (y mod 4 = 0 \/ y mod 4 = 2) /\ y mod 2 = 0
  | b, (x, y) => y < x /\ y mod 4 = 1 /\ y mod 2 = 1 /\ x <> y + 1
  | c, (x, y) => y < x /\ y mod 4 = 3 /\ y mod 2 = 1 /\ x <> y + 1 /\ x <> y + 2 /\ x <> y + 3
  | e, (x, y) => x = y + 2 /\ y mod 4 = 3
  | h, (x, y) => x <= y /\ x mod 2 = 0 /\ y mod 2 = 1
  end.

Lemma div2_even : forall y, y mod 2 = 0 -> y = 2 * (y / 2).
Proof.
  intros y H. pose proof (Nat.div_mod_eq y 2). lia.
Qed.

Lemma div2_odd : forall y, y mod 2 = 1 -> y = 2 * ((y - 1) / 2) + 1.
Proof.
  intros y H.
  assert (H1 : y = 2 * (y / 2) + 1) by
    (pose proof (Nat.div_mod_eq y 2); lia).
  assert (H2 : y - 1 = 2 * (y / 2)) by lia.
  assert (H3 : (y - 1) / 2 = y / 2).
  { rewrite H2.
    replace (2 * (y / 2)) with ((y / 2) * 2) by lia.
    exact (Nat.div_mul (y / 2) 2 (ltac:(lia))). }
  lia.
Qed.

Lemma mod2_two_mul : forall m, (2 * m) mod 2 = 0.
Proof.
  intros. rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
Qed.

Lemma mod2_two_mul_succ : forall m, (2 * m + 1) mod 2 = 1.
Proof.
  intros. rewrite Nat.Div0.add_mod. rewrite mod2_two_mul.
  reflexivity.
Qed.

Lemma Q_j : forall x y, x <= y ->
  Q (apply j (x, y)) = Q (x, y) + weight j.
Proof.
  intros. change (3 * x + 2 + 2 * (y - x + 1) = x + 2 * y + 4). lia.
Qed.

Lemma Q_i : forall x y, x <= y ->
  Q (apply i (x, y)) = Q (x, y) + weight i.
Proof.
  intros. change (3 * x + 2 * (y - x + 4) = x + 2 * y + 8). lia.
Qed.

Lemma Q_a : forall x y, y < x -> y mod 2 = 0 ->
  Q (apply a (x, y)) = Q (x, y) + weight a.
Proof.
  intros.
  change (x - y - 1 + 2 * (3 * (y / 2) + 2) = x + 2 * y + 3).
  pose proof (div2_even y H0) as Hy.
  assert (Hx : x = (x - y - 1) + (y + 1)) by lia.
  lia.
Qed.

Lemma Q_b : forall x y, y + 1 < x -> y mod 2 = 1 ->
  Q (apply b (x, y)) = Q (x, y) + weight b.
Proof.
  intros.
  change (x - y - 2 + 2 * (3 * ((y - 1) / 2) + 5) = x + 2 * y + 5).
  pose proof (div2_odd y H0) as Hy.
  assert (Hx : x = (x - y - 2) + (y + 2)) by lia.
  lia.
Qed.

Lemma Q_c : forall x y, y + 3 < x -> y mod 2 = 1 ->
  Q (apply c (x, y)) = Q (x, y) + weight c.
Proof.
  intros.
  change (x - y - 4 + 2 * (3 * ((y - 1) / 2) + 8) = x + 2 * y + 9).
  pose proof (div2_odd y H0) as Hy.
  assert (Hx : x = (x - y - 4) + (y + 4)) by lia.
  lia.
Qed.

Lemma Q_e : forall x y, x = y + 2 ->
  Q (apply e (x, y)) = Q (x, y) + weight e.
Proof.
  intros. change (3 * y + 8 + 2 * 1 = x + 2 * y + 8). lia.
Qed.

Lemma Q_h : forall x y, x mod 2 = 0 ->
  Q (apply h (x, y)) = Q (x, y) + weight h.
Proof.
  intros.
  change (1 + 2 * (x / 2 + y + 2) = x + 2 * y + 5).
  pose proof (div2_even x H) as Hx.
  lia.
Qed.

Lemma Q_apply : forall r p, Valid r p ->
  Q (apply r p) = Q p + weight r.
Proof.
  intros r [x y] H. destruct r; simpl in *.
  - apply Q_j. exact (proj1 H).
  - apply Q_i. exact (proj1 H).
  - apply Q_a.
    + exact (proj1 H).
    + destruct H as [Hx [Hmod H2]]; exact H2.
  - apply Q_b.
    + destruct H as [Hx [H4 [H2 Hne]]]. lia.
    + destruct H as [Hx [H4 [H2 Hne]]]. exact H2.
  - apply Q_c.
    + destruct H as [Hx [H4 [H2 [Hne1 [Hne2 Hne3]]]]]. lia.
    + destruct H as [Hx [H4 [H2 [Hne1 [Hne2 Hne3]]]]]. exact H2.
  - apply Q_e. exact (proj1 H).
  - apply Q_h. destruct H as [_ [Hx Hy]]. exact Hx.
Qed.

Lemma Q_cross : forall r p1 p2, Valid r p1 -> Valid r p2 ->
  Q (apply r p1) + Q p2 = Q (apply r p2) + Q p1.
Proof.
  intros. pose proof (Q_apply r p1 H). pose proof (Q_apply r p2 H0). lia.
Qed.

(** Base-2 odd branch. *)
Lemma pair_odd_apply : forall m,
  apply j (1, 2 * m + 1) = (5, 2 * m + 1).
Proof. intros. unfold apply. simpl. f_equal; lia. Qed.

Lemma pair_odd_valid : forall m, Valid j (1, 2 * m + 1).
Proof.
  intros. unfold Valid.
  change (1 <= 2 * m + 1 /\ 1 mod 2 = 1 /\ (2 * m + 1) mod 2 = 1).
  split; [lia |]. split; [reflexivity | apply mod2_two_mul_succ].
Qed.

(** Base-2 even branch, first step. *)
Lemma pair_even_i_apply : forall m, 1 <= m ->
  apply i (1, 2 * m) = (3, 2 * m + 3).
Proof. intros. unfold apply. simpl. f_equal; lia. Qed.

Lemma pair_even_i_valid : forall m, 1 <= m -> Valid i (1, 2 * m).
Proof.
  intros. unfold Valid.
  change (1 <= 2 * m /\ 1 mod 2 = 1 /\ (2 * m) mod 2 = 0).
  split; [lia |]. split; [reflexivity | apply mod2_two_mul].
Qed.

Lemma pair_even_j_apply : forall m,
  apply j (3, 2 * m + 3) = (11, 2 * m + 1).
Proof. intros. unfold apply. simpl. f_equal; lia. Qed.

Lemma pair_even_j_valid : forall m, Valid j (3, 2 * m + 3).
Proof.
  intros. unfold Valid.
  change (3 <= 2 * m + 3 /\ 3 mod 2 = 1 /\ (2 * m + 3) mod 2 = 1).
  split; [lia |]. split; [reflexivity |].
  replace (2 * m + 3) with (2 * (m + 1) + 1) by lia.
  apply mod2_two_mul_succ.
Qed.

Fixpoint run (w : list Rule) (p : nat * nat) : nat * nat :=
  match w with
  | nil => p
  | cons r rs => run rs (apply r p)
  end.

Fixpoint RunsValid (w : list Rule) (p : nat * nat) : Prop :=
  match w with
  | nil => True
  | cons r rs => Valid r p /\ RunsValid rs (apply r p)
  end.

Lemma Q_run_cross : forall w p1 p2,
  RunsValid w p1 -> RunsValid w p2 ->
  Q (run w p1) + Q p2 = Q (run w p2) + Q p1.
Proof.
  induction w as [| r rs IH]; intros p1 p2 H1 H2.
  - simpl. lia.
  - simpl in H1, H2. destruct H1 as [HV1 HT1]. destruct H2 as [HV2 HT2].
    simpl. pose proof (Q_cross r p1 p2 HV1 HV2).
    pose proof (IH (apply r p1) (apply r p2) HT1 HT2). lia.
Qed.

Lemma weight_le_nine : forall r, weight r <= 9.
Proof. intros r; destruct r; simpl; lia. Qed.

Lemma Q_run_le : forall w p, RunsValid w p ->
  Q (run w p) <= Q p + 9 * length w.
Proof.
  induction w as [| r rs IH]; intros p H.
  - simpl. lia.
  - simpl in H. destruct H as [HV HT]. simpl.
    pose proof (Q_apply r p HV) as Hstep.
    pose proof (IH (apply r p) HT) as Hih.
    pose proof (weight_le_nine r) as Hw.
    replace (9 * S (length rs)) with (9 * length rs + 9) by lia.
    lia.
Qed.

Lemma Q_run_ge : forall w p, RunsValid w p -> Q p <= Q (run w p).
Proof.
  induction w as [| r rs IH]; intros p H.
  - simpl. lia.
  - simpl in H. destruct H as [HV HT]. simpl.
    pose proof (Q_apply r p HV) as Hstep.
    pose proof (IH (apply r p) HT) as Hih.
    assert (Hw : 0 <= weight r) by lia.
    lia.
Qed.

(** Length-based fixed-perturbation endpoint bound, left side. *)
Lemma pair_endpoint_bound_left : forall w1 w2 c x1 y1 x2 y2 L1,
  RunsValid w1 (5, c) -> RunsValid w2 (11, c) ->
  run w1 (5, c) = (x1, y1) -> run w2 (11, c) = (x2, y2) ->
  x1 mod 2 = 0 -> x2 mod 2 = 0 -> length w1 <= L1 ->
  2 * (x1 / 2 + y1 + 2) <= 2 * (x2 / 2 + y2 + 2) + 9 * L1.
Proof.
  intros w1 w2 c x1 y1 x2 y2 L1 H1 H2 E1 E2 Hx1 Hx2 HL.
  pose proof (Q_run_le w1 (5, c) H1) as Hle.
  pose proof (Q_run_ge w2 (11, c) H2) as Hge.
  rewrite E1 in Hle. rewrite E2 in Hge.
  unfold Q in Hle, Hge. simpl in Hle, Hge.
  pose proof (div2_even x1 Hx1) as D1.
  pose proof (div2_even x2 Hx2) as D2.
  assert (H9 : 9 * length w1 <= 9 * L1) by lia.
  lia.
Qed.

(** Length-based fixed-perturbation endpoint bound, right side. *)
Lemma pair_endpoint_bound_right : forall w1 w2 c x1 y1 x2 y2 L2,
  RunsValid w1 (5, c) -> RunsValid w2 (11, c) ->
  run w1 (5, c) = (x1, y1) -> run w2 (11, c) = (x2, y2) ->
  x1 mod 2 = 0 -> x2 mod 2 = 0 -> length w2 <= L2 ->
  2 * (x2 / 2 + y2 + 2) <= 2 * (x1 / 2 + y1 + 2) + 6 + 9 * L2.
Proof.
  intros w1 w2 c x1 y1 x2 y2 L2 H1 H2 E1 E2 Hx1 Hx2 HL.
  pose proof (Q_run_le w2 (11, c) H2) as Hle.
  pose proof (Q_run_ge w1 (5, c) H1) as Hge.
  rewrite E1 in Hge. rewrite E2 in Hle.
  unfold Q in Hle, Hge. simpl in Hle, Hge.
  pose proof (div2_even x1 Hx1) as D1.
  pose proof (div2_even x2 Hx2) as D2.
  assert (H9 : 9 * length w2 <= 9 * L2) by lia.
  lia.
Qed.

(** Combined length bound: both endpoint differences are at most
    [(9L+6)/2] when both words have length at most [L]. *)
Lemma pair_endpoint_length_bound : forall w1 w2 c x1 y1 x2 y2 L,
  RunsValid w1 (5, c) -> RunsValid w2 (11, c) ->
  run w1 (5, c) = (x1, y1) -> run w2 (11, c) = (x2, y2) ->
  x1 mod 2 = 0 -> x2 mod 2 = 0 ->
  length w1 <= L -> length w2 <= L ->
  2 * (x1 / 2 + y1 + 2) <= 2 * (x2 / 2 + y2 + 2) + 9 * L /\
    2 * (x2 / 2 + y2 + 2) <= 2 * (x1 / 2 + y1 + 2) + 6 + 9 * L.
Proof.
  intros w1 w2 c x1 y1 x2 y2 L H1 H2 E1 E2 Hx1 Hx2 HL1 HL2.
  split.
  - eapply pair_endpoint_bound_left; eauto.
  - eapply pair_endpoint_bound_right; eauto.
Qed.

(** Conditional fixed-perturbation endpoint lemma: if the two chains use the
    same rule word, the [11]-endpoint is exactly 3 larger. *)
Lemma pair_endpoint_same_word : forall w c0 x1 y1 x2 y2,
  RunsValid w (5, c0) -> RunsValid w (11, c0) ->
  run w (5, c0) = (x1, y1) -> run w (11, c0) = (x2, y2) ->
  x1 mod 2 = 0 -> x2 mod 2 = 0 ->
  x2 / 2 + y2 + 2 = x1 / 2 + y1 + 5.
Proof.
  intros w c0 x1 y1 x2 y2 HR1 HR2 HE1 HE2 Hx1 Hx2.
  pose proof (Q_run_cross w (5, c0) (11, c0) HR1 HR2) as Hcross.
  rewrite HE1, HE2 in Hcross. unfold Q in Hcross. simpl in Hcross.
  pose proof (div2_even x1 Hx1) as D1.
  pose proof (div2_even x2 Hx2) as D2.
  lia.
Qed.

(** Pair-plus-scale reduction: the pair defect and the scale defect together
    give the constant-defect bound (S2). *)
Theorem constant_defect_of_pair_and_scale (D : nat -> nat) (Kp Ks : nat)
    (hp : forall m, D (2 * m) <= D (2 * m + 1) + Kp /\
      D (2 * m + 1) <= D (2 * m) + Kp)
    (hs : forall m, D (2 * m + 1) <= D m + Ks /\
      D m <= D (2 * m + 1) + Ks) :
    (forall m, D (2 * m) <= D m + (Kp + Ks)) /\
    (forall m, D (2 * m + 1) <= D m + (Kp + Ks)).
Proof.
  split.
  - intro m. specialize (hp m). specialize (hs m). lia.
  - intro m. specialize (hs m). lia.
Qed.

(** ** Pure [j]-run prefix *)

Fixpoint jIter (k : nat) (p : nat * nat) : nat * nat :=
  match k with
  | 0 => p
  | S k' => jIter k' (apply j p)
  end.

Fixpoint JValid (k : nat) (p : nat * nat) : Prop :=
  match k with
  | 0 => True
  | S k' => fst p <= snd p /\ JValid k' (apply j p)
  end.

Lemma jIter_fst : forall k a cc,
  fst (jIter k (a, cc)) + 1 = (a + 1) * 3 ^ k.
Proof.
  induction k as [| k IH]; intros a cc.
  - simpl. lia.
  - simpl. rewrite IH. ring.
Qed.

Lemma jIter_snd : forall k a cc, JValid k (a, cc) ->
  2 * snd (jIter k (a, cc)) + (a + 1) * 3 ^ k =
    2 * cc + 4 * k + (a + 1).
Proof.
  induction k as [| k IH]; intros a cc H.
  - simpl. lia.
  - simpl in H. destruct H as [Ha HT]. simpl.
    specialize (IH (3 * a + 2) (cc - a + 1) HT).
    ring_simplify in IH.
    ring_simplify.
    replace (a + 2 * cc + 4 * k + 5) with
      (3 * a + 2 * (cc - a) + 4 * k + 5) by lia.
    exact IH.
Qed.

Lemma jIter_a_one : forall k cc,
  fst (jIter k (1, cc)) = 2 * 3 ^ k - 1.
Proof. intros. pose proof (jIter_fst k 1 cc). lia. Qed.

Lemma jIter_c_one : forall k cc, JValid k (1, cc) ->
  cc + 2 * k + 1 = snd (jIter k (1, cc)) + 3 ^ k.
Proof.
  intros. pose proof (jIter_snd k 1 cc H). simpl in H0. lia.
Qed.

Lemma two_mul_add_one_le_pow3 : forall k, 2 * k + 1 <= 3 ^ k.
Proof.
  induction k as [| k IH]; simpl; [lia |].
  nia.
Qed.

Lemma jIter_formula : forall k cc, JValid k (1, cc) ->
  jIter k (1, cc) = (2 * 3 ^ k - 1, cc - (3 ^ k - 1 - 2 * k)).
Proof.
  intros. assert (Ha := jIter_a_one k cc).
  assert (Hc := jIter_c_one k cc H).
  assert (H2k := two_mul_add_one_le_pow3 k).
  assert (Hc' : cc = snd (jIter k (1, cc)) + (3 ^ k - 1 - 2 * k)) by lia.
  destruct (jIter k (1, cc)) as [a b]. simpl in *. subst a. f_equal. lia.
Qed.

Lemma jIter_eq_run : forall k p,
  jIter k p = run (repeat j k) p.
Proof.
  induction k as [| k IH]; intros p.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma JValid_of_RunsValid : forall k p,
  RunsValid (repeat j k) p -> JValid k p.
Proof.
  induction k as [| k IH]; intros p H.
  - exact I.
  - simpl in H. destruct H as [HV HT]. destruct p as [a cc]. simpl in *.
    split; [exact (proj1 HV) |]. apply IH. exact HT.
Qed.

Lemma JValid_prefix : forall k a cc, JValid (S k) (a, cc) -> JValid k (a, cc).
Proof.
  induction k as [| k IH]; intros a cc H.
  - exact I.
  - simpl in H. destruct H as [Ha HT]. split; [exact Ha |].
    apply IH with (a := 3 * a + 2) (cc := cc - a + 1). exact HT.
Qed.

Lemma JValid_last : forall k a cc, JValid (S k) (a, cc) ->
  fst (jIter k (a, cc)) <= snd (jIter k (a, cc)).
Proof.
  induction k as [| k IH]; intros a cc H.
  - simpl. simpl in H. exact (proj1 H).
  - simpl. simpl in H. destruct H as [Ha HT]. apply IH. exact HT.
Qed.

Lemma pow3_ge_succ : forall jj, jj + 1 <= 3 ^ jj.
Proof.
  induction jj as [| jj IH]; simpl; [lia |].
  nia.
Qed.

Lemma pow3_base : 2 ^ 463 + 586 < 3 ^ 293.
Proof.
  apply Nat2Z.inj_lt.
  rewrite Nat2Z.inj_add, Nat2Z.inj_pow, Nat2Z.inj_pow.
  vm_compute. reflexivity.
Qed.

Lemma pow3_dominates_step : forall A k, 293 <= k ->
  A + 2 * k < 3 ^ k ->
  A + 2 * (k + 1) < 3 ^ (k + 1).
Proof.
  intros A k Hk Hlt.
  replace (3 ^ (k + 1)) with (3 * 3 ^ k) by
    (replace (k + 1) with (S k) by lia;
     rewrite Nat.pow_succ_r'; reflexivity).
  assert (Hmul : 3 * (A + 2 * k) < 3 * 3 ^ k) by nia.
  assert (Hineq : A + 2 * (k + 1) <= 3 * (A + 2 * k)) by nia.
  exact (Nat.le_lt_trans (A + 2 * (k + 1))
    (3 * (A + 2 * k)) (3 * 3 ^ k) Hineq Hmul).
Qed.

Lemma pow3_dominates_gen : forall A k, A + 586 < 3 ^ 293 -> 293 <= k ->
  A + 2 * k < 3 ^ k.
Proof.
  intros A k Hbase Hk.
  assert (Hdom : forall jj, A + 2 * (293 + jj) < 3 ^ (293 + jj)).
  { intro jj. induction jj as [| jj IH].
    - replace (293 + 0) with 293 by lia.
      change (A + 2 * 293 < 3 ^ 293).
      exact Hbase.
    - replace (293 + S jj) with ((293 + jj) + 1) by lia.
      apply pow3_dominates_step; [lia | exact IH]. }
  replace k with (293 + (k - 293)) by lia.
  apply Hdom.
Qed.

Lemma pow3_dominates : forall k, 293 <= k -> 2 ^ 463 + 2 * k < 3 ^ k.
Proof.
  intros k Hk.
  apply pow3_dominates_gen with (A := 2 ^ 463); [exact pow3_base | exact Hk].
Qed.

Lemma j_run_length_le_292 : forall k cc, 1 <= k -> cc < 2 ^ 463 ->
  JValid k (1, cc) -> k <= 292.
Proof.
  intros k cc Hk Hc H.
  remember (2 ^ 463) as A eqn:HA.
  assert (HbaseA : A + 586 < 3 ^ 293) by (subst A; exact pow3_base).
  destruct k as [| jj]; [lia |].
  assert (Hpre : JValid jj (1, cc)) by (apply JValid_prefix; exact H).
  assert (Hlast := JValid_last jj 1 cc H).
  assert (Ha := jIter_a_one jj cc).
  assert (Hcj := jIter_c_one jj cc Hpre).
  rewrite Ha in Hlast.
  assert (Hpow : 3 ^ (jj + 1) = 3 * 3 ^ jj).
  { replace (jj + 1) with (S jj) by lia.
    rewrite Nat.pow_succ_r'. reflexivity. }
  assert (Hle : 3 ^ (jj + 1) <= cc + 2 * (jj + 1)).
  { rewrite Hpow. lia. }
  destruct (le_lt_dec 293 (jj + 1)) as [Hk293 | Hnot].
  - assert (Hdom := pow3_dominates_gen A (jj + 1) HbaseA Hk293).
    assert (Hlt : A + 2 * (jj + 1) < cc + 2 * (jj + 1)) by lia.
    assert (Hc' : A < cc) by lia.
    lia.
  - assert (Hle292 : jj + 1 <= 292) by lia.
    replace (S jj) with (jj + 1) by lia. exact Hle292.
Qed.

Definition HaltState (p : nat * nat) : Prop :=
  (fst p <= snd p /\ fst p mod 2 = 0 /\ snd p mod 2 = 0) \/
    (fst p = snd p + 1 /\ snd p mod 2 = 1) \/
      (fst p = snd p + 3 /\ snd p mod 4 = 3).

Definition TailBounded (B : nat) : Prop :=
  forall cc, cc < 2 ^ 463 -> forall k, JValid k (1, cc) ->
    exists w : list Rule, length w <= B /\
      RunsValid w (jIter k (1, cc)) /\
        (fst (run w (jIter k (1, cc))) = 1 \/
          HaltState (run w (jIter k (1, cc)))).

Lemma length_le_17000_of_tail : forall B, B + 292 <= 17000 ->
  TailBounded B -> forall cc, cc < 2 ^ 463 -> forall k, JValid k (1, cc) ->
    exists w : list Rule, k + length w <= 17000 /\
      RunsValid w (jIter k (1, cc)) /\
        (fst (run w (jIter k (1, cc))) = 1 \/
          HaltState (run w (jIter k (1, cc)))).
Proof.
  intros B HB Htail cc Hc k Hk.
  destruct (Htail cc Hc k Hk) as [w [Hlen [Hrun Hend]]].
  exists w. split; [| split; assumption].
  assert (Hk' : k <= 292).
  { destruct k as [| jj]; [lia |].
    apply (j_run_length_le_292 (S jj) cc); [lia | exact Hc | exact Hk]. }
  lia.
Qed.

Print Assumptions Q_apply.
Print Assumptions Q_cross.
Print Assumptions Q_run_cross.
Print Assumptions pair_endpoint_same_word.
Print Assumptions pair_endpoint_length_bound.
Print Assumptions constant_defect_of_pair_and_scale.
Print Assumptions jIter_formula.
Print Assumptions j_run_length_le_292.
Print Assumptions length_le_17000_of_tail.

Corollary length_le_17000_of_tail_16708 :
  TailBounded 16708 -> forall cc, cc < 2 ^ 463 -> forall k, JValid k (1, cc) ->
    exists w : list Rule, k + length w <= 17000 /\
      RunsValid w (jIter k (1, cc)) /\
        (fst (run w (jIter k (1, cc))) = 1 \/
          HaltState (run w (jIter k (1, cc)))).
Proof.
  intros Htail cc Hc k Hk.
  apply (length_le_17000_of_tail 16708).
  - change (17000 <= 17000). apply Nat.le_refl.
  - exact Htail.
  - exact Hc.
  - exact Hk.
Qed.

Print Assumptions length_le_17000_of_tail_16708.
