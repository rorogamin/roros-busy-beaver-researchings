(*
  rocq/JZMath.v
  Pure arithmetic of the Jacobzheng f_{ω×2} engine: recurrences `h`, `hc`, `ho`, `hoc`,
  mod-3 invariants, and FGH lower bounds.
*)

From Stdlib Require Import Arith Lia.
From BB Require Import TM FGH.

Fixpoint h (m : nat) : nat -> nat :=
  match m with
  | 0 => fun n => 4 * n + 7
  | S m' => fun n => iter (h m') (n + 1) 3
  end.

Fixpoint hc (m k n : nat) : nat :=
  match k with
  | 0 => n
  | S k' => hc (S m) k' (h m n)
  end.

Fixpoint ho (m : nat) : nat -> nat :=
  match m with
  | 0 => fun n =>
    match n mod 3 with
    | 0 => hc 0 (n / 3) 7 + 2 * (n / 3) + 3
    | 1 => n + 4
    | _ => hc 0 (n / 3) 7 + 2 * (n / 3 + 1) + 3
    end
  | S m' => fun n => iter (ho m') (n + 1) 6
  end.

Fixpoint hoc (m k n : nat) : nat :=
  match k with
  | 0 => n
  | S k' => hoc (S m) k' (ho m n)
  end.

Lemma mod3_cases : forall x,
  (exists q, x = 3 * q) \/ (exists q, x = 3 * q + 1) \/ (exists q, x = 3 * q + 2).
Proof.
  intro x.
  pose proof (Nat.div_mod x 3 ltac:(lia)) as Hdm.
  pose proof (Nat.mod_upper_bound x 3 ltac:(lia)) as Hmb.
  destruct (x mod 3) as [|[|r]] eqn:Hr.
  - left. exists (x / 3). lia.
  - right. left. exists (x / 3). lia.
  - right. right. exists (x / 3). lia.
Qed.

Lemma ho0_mod0 : forall q, ho 0 (3 * q) = hc 0 q 7 + 2 * q + 3.
Proof.
  intro q. unfold ho.
  assert (Hm : (3 * q) mod 3 = 0).
  { replace (3 * q) with (q * 3) by lia. apply Nat.Div0.mod_mul. }
  assert (Hd : (3 * q) / 3 = q).
  { replace (3 * q) with (q * 3) by lia. apply Nat.div_mul; lia. }
  rewrite Hm, Hd. reflexivity.
Qed.

Lemma ho0_mod1 : forall q, ho 0 (3 * q + 1) = 3 * q + 5.
Proof.
  intro q. unfold ho.
  assert (Hm : (3 * q + 1) mod 3 = 1).
  { replace (3 * q + 1) with (1 + q * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  rewrite Hm. lia.
Qed.

Lemma ho0_mod2 : forall q, ho 0 (3 * q + 2) = hc 0 q 7 + 2 * (q + 1) + 3.
Proof.
  intro q. unfold ho.
  assert (Hm : (3 * q + 2) mod 3 = 2).
  { replace (3 * q + 2) with (2 + q * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hd : (3 * q + 2) / 3 = q).
  { replace (3 * q + 2) with (2 + q * 3) by lia.
    rewrite Nat.div_add by lia. simpl. lia. }
  rewrite Hm, Hd. reflexivity.
Qed.

Lemma h_ge_3x1 : forall m x, 3 * x + 1 <= h m x.
Proof.
  induction m as [| m' IH]; intro x.
  - simpl. lia.
  - assert (Hstep : forall k, 3 * k + 1 <= iter (h m') k 3).
    { induction k as [| p IHp]; simpl; [lia |].
      pose proof (IH (iter (h m') p 3)). lia. }
    simpl. pose proof (Hstep (x + 1)). lia.
Qed.

Lemma h_mono : forall m x y, x <= y -> h m x <= h m y.
Proof.
  induction m as [| m' _]; intros x y Hxy.
  - simpl. lia.
  - simpl. apply iter_mono_steps; [| lia].
    intro z. pose proof (h_ge_3x1 m' z). lia.
Qed.

Lemma h_mod3 : forall m x, h m x mod 3 = (x + 1) mod 3.
Proof.
  induction m as [| m' IH]; intro x.
  - cbn [h].
    replace (4 * x + 7) with ((x + 1) + (x + 2) * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity.
  - assert (Hiter : forall k z, iter (h m') k z mod 3 = (z + k) mod 3).
    { induction k as [| p IHp]; intro z; cbn [iter].
      - replace (z + 0) with z by lia. reflexivity.
      - rewrite IH.
        rewrite <- Nat.Div0.add_mod_idemp_l, IHp, Nat.Div0.add_mod_idemp_l.
        f_equal. lia. }
    cbn [h]. rewrite Hiter.
    replace (3 + (x + 1)) with ((x + 1) + 1 * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma hc_snoc : forall m k n, hc m (S k) n = h (m + k) (hc m k n).
Proof.
  intros m k. revert m. induction k as [| p IH]; intros m n.
  - cbn [hc]. rewrite Nat.add_0_r. reflexivity.
  - change (hc m (S (S p)) n) with (hc (S m) (S p) (h m n)).
    change (hc m (S p) n) with (hc (S m) p (h m n)).
    rewrite IH. replace (S m + p) with (m + S p) by lia. reflexivity.
Qed.

Lemma hc_mod3 : forall m k n, hc m k n mod 3 = (n + k) mod 3.
Proof.
  intros m k. revert m. induction k as [| p IH]; intros m n; cbn [hc].
  - replace (n + 0) with n by lia. reflexivity.
  - rewrite IH.
    rewrite <- Nat.Div0.add_mod_idemp_l, h_mod3, Nat.Div0.add_mod_idemp_l.
    f_equal. lia.
Qed.

Lemma hc0_ge_3k : forall k, 3 * k + 7 <= hc 0 k 7.
Proof.
  induction k as [| p IH].
  - simpl. lia.
  - rewrite hc_snoc. pose proof (h_ge_3x1 (0 + p) (hc 0 p 7)). lia.
Qed.

Lemma hc0_ge_15q : forall q, 1 <= q -> 15 * q + 15 <= hc 0 q 7.
Proof.
  induction q as [| p IH]; intro Hq; [lia |].
  destruct p as [| p'].
  - simpl. lia.
  - specialize (IH ltac:(lia)).
    rewrite hc_snoc. pose proof (h_ge_3x1 (0 + S p') (hc 0 (S p') 7)). lia.
Qed.

Lemma hc0_mono : forall a b, a <= b -> hc 0 a 7 <= hc 0 b 7.
Proof.
  intros a b Hab. induction Hab as [| p _ IH].
  - lia.
  - rewrite hc_snoc. pose proof (h_ge_3x1 (0 + p) (hc 0 p 7)). lia.
Qed.

Lemma ho_ge_add4 : forall m x, x + 4 <= ho m x.
Proof.
  induction m as [| m' IH]; intro x.
  - destruct (mod3_cases x) as [[q Hq] | [[q Hq] | [q Hq]]]; subst.
    + rewrite ho0_mod0. pose proof (hc0_ge_3k q). lia.
    + rewrite ho0_mod1. lia.
    + rewrite ho0_mod2. pose proof (hc0_ge_3k q). lia.
  - assert (Hstep : forall k, k + 4 <= iter (ho m') k 6).
    { induction k as [| p IHp]; simpl; [lia |].
      pose proof (IH (iter (ho m') p 6)). lia. }
    simpl. pose proof (Hstep (x + 1)). lia.
Qed.

Lemma ho_succ_mono : forall m x y, x <= y -> ho (S m) x <= ho (S m) y.
Proof.
  intros m x y Hxy. simpl. apply iter_mono_steps; [| lia].
  intro z. pose proof (ho_ge_add4 m z). lia.
Qed.

Lemma ho_mod3 : forall m x, ho m x mod 3 = (x + 1) mod 3.
Proof.
  induction m as [| m' IH]; intro x.
  - destruct (mod3_cases x) as [[q Hq] | [[q Hq] | [q Hq]]]; subst.
    + rewrite ho0_mod0.
      replace (hc 0 q 7 + 2 * q + 3) with ((hc 0 q 7 + 2 * q) + 1 * 3) by lia.
      rewrite Nat.Div0.mod_add.
      rewrite <- Nat.Div0.add_mod_idemp_l, hc_mod3, Nat.Div0.add_mod_idemp_l.
      replace (7 + q + 2 * q) with ((3 * q + 1) + 2 * 3) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    + rewrite ho0_mod1.
      replace (3 * q + 5) with ((3 * q + 1 + 1) + 1 * 3) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    + rewrite ho0_mod2.
      replace (hc 0 q 7 + 2 * (q + 1) + 3) with (hc 0 q 7 + (2 * q + 2) + 1 * 3) by lia.
      rewrite Nat.Div0.mod_add.
      rewrite <- Nat.Div0.add_mod_idemp_l, hc_mod3, Nat.Div0.add_mod_idemp_l.
      replace (7 + q + (2 * q + 2)) with ((3 * q + 2 + 1) + 2 * 3) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
  - assert (Hiter : forall k z, iter (ho m') k z mod 3 = (z + k) mod 3).
    { induction k as [| p IHp]; intro z; cbn [iter].
      - replace (z + 0) with z by lia. reflexivity.
      - rewrite IH.
        rewrite <- Nat.Div0.add_mod_idemp_l, IHp, Nat.Div0.add_mod_idemp_l.
        f_equal. lia. }
    cbn [ho]. rewrite Hiter.
    replace (6 + (x + 1)) with ((x + 1) + 2 * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma hoc_snoc : forall m k n, hoc m (S k) n = ho (m + k) (hoc m k n).
Proof.
  intros m k. revert m. induction k as [| p IH]; intros m n.
  - cbn [hoc]. rewrite Nat.add_0_r. reflexivity.
  - change (hoc m (S (S p)) n) with (hoc (S m) (S p) (ho m n)).
    change (hoc m (S p) n) with (hoc (S m) p (ho m n)).
    rewrite IH. replace (S m + p) with (m + S p) by lia. reflexivity.
Qed.

Lemma hoc_mod3 : forall m k n, hoc m k n mod 3 = (n + k) mod 3.
Proof.
  intros m k. revert m. induction k as [| p IH]; intros m n; cbn [hoc].
  - replace (n + 0) with n by lia. reflexivity.
  - rewrite IH.
    rewrite <- Nat.Div0.add_mod_idemp_l, ho_mod3, Nat.Div0.add_mod_idemp_l.
    f_equal. lia.
Qed.

Lemma hoc_mono_k : forall k1 k2 m n, k1 <= k2 -> hoc m k1 n <= hoc m k2 n.
Proof.
  intros k1 k2 m n Hk. induction Hk as [| p _ IH].
  - lia.
  - rewrite hoc_snoc. pose proof (ho_ge_add4 (m + p) (hoc m p n)). lia.
Qed.

Lemma hoc_ge_add4 : forall m k n, n + 4 * k <= hoc m k n.
Proof.
  intros m k n. induction k as [| p IH].
  - simpl. lia.
  - rewrite hoc_snoc. pose proof (ho_ge_add4 (m + p) (hoc m p n)). lia.
Qed.

Lemma iter_le_iter : forall f g,
  (forall z, f z <= g z) ->
  (forall a b, a <= b -> g a <= g b) ->
  forall k y, iter f k y <= iter g k y.
Proof.
  intros f g Hfg Hg k. induction k as [| p IH]; intro y; simpl.
  - lia.
  - eapply Nat.le_trans; [apply Hfg | apply Hg; apply IH].
Qed.

Lemma fFin_le_h : forall m x, fFin m x <= h m (3 * x).
Proof.
  induction m as [| m' IH]; intro x.
  - rewrite f_0_eq. simpl. lia.
  - rewrite f_succ_eq. cbn [h].
    assert (Hstep : forall z, fFin m' z <= h m' (h m' z)).
    { intro z. eapply Nat.le_trans; [apply IH |].
      apply h_mono. pose proof (h_ge_3x1 m' z). lia. }
    assert (Hmono2 : forall a b, a <= b -> h m' (h m' a) <= h m' (h m' b)).
    { intros a b Hab. apply h_mono, h_mono, Hab. }
    pose proof (iter_le_iter (fFin m') (fun z => h m' (h m' z)) Hstep Hmono2 x x) as H1.
    rewrite iter_two_mul in H1.
    assert (H2 : iter (h m') (2 * x) x <= iter (h m') (2 * x) (iter (h m') (x + 1) 3)).
    { apply iter_mono_arg; [apply h_mono |].
      assert (Hst : forall k, 3 * k + 1 <= iter (h m') k 3).
      { induction k as [| p IHp]; simpl; [lia |].
        pose proof (h_ge_3x1 m' (iter (h m') p 3)). lia. }
      pose proof (Hst (x + 1)). lia. }
    rewrite <- iter_add in H2.
    replace (2 * x + (x + 1)) with (3 * x + 1) in H2 by lia.
    eapply Nat.le_trans; [exact H1 | exact H2].
Qed.

Lemma f_omega_le_hc : forall k, f_omega k <= hc 0 (S k) 7.
Proof.
  intro k. rewrite f_omega_eq, hc_snoc, Nat.add_0_l.
  eapply Nat.le_trans; [apply fFin_le_h |].
  apply h_mono. pose proof (hc0_ge_3k k). lia.
Qed.

Lemma ho0_iter2_ge_5x3 : forall z, 5 * z + 3 <= iter (ho 0) 2 z.
Proof.
  intro z. cbn [iter].
  pose proof (ho_ge_add4 0 (ho 0 z)) as Hadd.
  destruct (mod3_cases z) as [[q Hq] | [[q Hq] | [q Hq]]]; subst.
  - destruct q as [| q'].
    + rewrite ho0_mod0 in Hadd |- *. cbn [hc] in *. lia.
    + pose proof (hc0_ge_15q (S q') ltac:(lia)).
      rewrite ho0_mod0 in Hadd |- *. lia.
  - pose proof (hc0_ge_15q (S q) ltac:(lia)).
    rewrite ho0_mod1.
    replace (3 * q + 5) with (3 * S q + 2) by lia.
    rewrite ho0_mod2. lia.
  - destruct q as [| q'].
    + rewrite ho0_mod2 in Hadd |- *. cbn [hc] in *. lia.
    + pose proof (hc0_ge_15q (S q') ltac:(lia)).
      rewrite ho0_mod2 in Hadd |- *. lia.
Qed.

Lemma ho0_iter2_gt_f_omega : forall y z, 3 * y + 3 <= z -> f_omega y < iter (ho 0) 2 z.
Proof.
  intros y z Hz.
  pose proof (f_omega_le_hc y) as Hfc.
  cbn [iter]. pose proof (ho_ge_add4 0 (ho 0 z)) as Hadd.
  destruct (mod3_cases z) as [[q Hq] | [[q Hq] | [q Hq]]]; subst.
  - pose proof (hc0_mono (S y) q ltac:(lia)).
    rewrite ho0_mod0 in Hadd |- *. lia.
  - pose proof (hc0_mono (S y) (S q) ltac:(lia)).
    rewrite ho0_mod1.
    replace (3 * q + 5) with (3 * S q + 2) by lia.
    rewrite ho0_mod2. lia.
  - pose proof (hc0_mono (S y) q ltac:(lia)).
    rewrite ho0_mod2 in Hadd |- *. lia.
Qed.

Lemma ho_ge_5x3 : forall m x, 5 * x + 3 <= ho (S m) x.
Proof.
  induction m as [| m' IH]; intro x.
  - assert (Htwo : forall k, 5 * k + 3 <= iter (ho 0) (k + 1) 6 /\
                             5 * (k + 1) + 3 <= iter (ho 0) (k + 2) 6).
    { induction k as [| k IHk].
      - pose proof (ho0_mod0 2) as H06.
        change (3 * 2) with 6 in H06.
        pose proof (hc0_ge_3k 2) as Hhc.
        pose proof (ho_ge_add4 0 (ho 0 6)) as Hadd.
        split; cbn [Nat.add iter]; [rewrite H06; lia | rewrite H06 in Hadd |- *; lia].
      - split; [replace (S k + 1) with (k + 2) by lia; replace (S k) with (k + 1) by lia; exact (proj2 IHk) |].
        replace (S k + 2) with (2 + (S k)) by lia.
        rewrite iter_add.
        pose proof (ho0_iter2_ge_5x3 (iter (ho 0) (S k) 6)).
        replace (S k) with (k + 1) in * by lia.
        destruct IHk. lia. }
    cbn [ho]. exact (proj1 (Htwo x)).
  - assert (Hstep : forall k, 5 * k + 3 <= iter (ho (S m')) k 6).
    { induction k as [| p IHp]; cbn [iter]; [lia |].
      pose proof (IH (iter (ho (S m')) p 6)). lia. }
    change (ho (S (S m')) x) with (iter (ho (S m')) (x + 1) 6).
    pose proof (Hstep (x + 1)). lia.
Qed.

Lemma f_omega_lt_ho1_2 : forall y, f_omega y < ho 1 (ho 1 y).
Proof.
  intro y.
  pose proof (ho_ge_5x3 0 y) as Hy5.
  pose proof (ho0_iter2_gt_f_omega y (ho 1 y) ltac:(lia)) as Hgt.
  assert (Heq : iter (ho 0) 2 (ho 1 y) = ho 1 (y + 2)).
  { simpl (ho 1 y). simpl (ho 1 (y + 2)).
    rewrite <- iter_add. f_equal. lia. }
  rewrite Heq in Hgt.
  eapply Nat.lt_le_trans; [exact Hgt | apply ho_succ_mono; lia].
Qed.

Lemma f_omega_plus_le_ho : forall m x, 1 <= m -> f_omega_plus m x <= ho (S m) (3 * x).
Proof.
  induction m as [| m' IH]; intros x Hm; [lia |].
  assert (Hstep1 : forall g k, k + 6 <= iter (ho g) k 6).
  { intros g k. induction k as [| p IHp]; simpl; [lia |].
    pose proof (ho_ge_add4 g (iter (ho g) p 6)). lia. }
  destruct m' as [| m''].
  - rewrite f_omega_plus_succ_eq.
    change (f_omega_plus 0) with f_omega.
    cbn [ho].
    assert (Hstep : forall z, f_omega z <= ho 1 (ho 1 z)).
    { intro z. pose proof (f_omega_lt_ho1_2 z). lia. }
    assert (Hmono2 : forall a b, a <= b -> ho 1 (ho 1 a) <= ho 1 (ho 1 b)).
    { intros a b Hab. apply ho_succ_mono, ho_succ_mono, Hab. }
    pose proof (iter_le_iter f_omega (fun z => ho 1 (ho 1 z)) Hstep Hmono2 x x) as H1.
    rewrite iter_two_mul in H1.
    assert (H2 : iter (ho 1) (2 * x) x <= iter (ho 1) (2 * x) (iter (ho 1) (x + 1) 6)).
    { apply iter_mono_arg; [apply ho_succ_mono |].
      pose proof (Hstep1 1 (x + 1)). lia. }
    rewrite <- iter_add in H2.
    replace (2 * x + (x + 1)) with (3 * x + 1) in H2 by lia.
    eapply Nat.le_trans; [exact H1 | exact H2].
  - specialize (IH).
    rewrite f_omega_plus_succ_eq.
    cbn [ho].
    assert (Hstep : forall z, f_omega_plus (S m'') z <= ho (S (S m'')) (ho (S (S m'')) z)).
    { intro z. eapply Nat.le_trans; [apply IH; lia |].
      apply ho_succ_mono. pose proof (ho_ge_5x3 (S m'') z). lia. }
    assert (Hmono2 : forall a b, a <= b ->
      ho (S (S m'')) (ho (S (S m'')) a) <= ho (S (S m'')) (ho (S (S m'')) b)).
    { intros a b Hab. apply ho_succ_mono, ho_succ_mono, Hab. }
    pose proof (iter_le_iter (f_omega_plus (S m''))
      (fun z => ho (S (S m'')) (ho (S (S m'')) z)) Hstep Hmono2 x x) as H1.
    rewrite iter_two_mul in H1.
    assert (H2 : iter (ho (S (S m''))) (2 * x) x <=
                 iter (ho (S (S m''))) (2 * x) (iter (ho (S (S m''))) (x + 1) 6)).
    { apply iter_mono_arg; [apply ho_succ_mono |].
      pose proof (Hstep1 (S (S m'')) (x + 1)). lia. }
    rewrite <- iter_add in H2.
    replace (2 * x + (x + 1)) with (3 * x + 1) in H2 by lia.
    eapply Nat.le_trans; [exact H1 | exact H2].
Qed.

Lemma f_omega_mul2_pos : forall x, 1 <= f_omega_mul2 x.
Proof.
  intro x.
  assert (H0 : f_omega_mul2 0 = 1) by reflexivity.
  pose proof (fgh_mono _ (fOmegaMul_props 2 0) 0 x ltac:(lia)).
  change (fOmegaMul 2 0 0 <= fOmegaMul 2 0 x) with (f_omega_mul2 0 <= f_omega_mul2 x) in H.
  lia.
Qed.

Lemma f_omega_mul2_le_hoc : forall k n, 10 <= n -> f_omega_mul2 k <= hoc 0 (k + 2) n.
Proof.
  intros k n Hn. destruct k as [| k'].
  - change (0 + 2) with 2. pose proof (hoc_ge_add4 0 2 n).
    assert (H0 : f_omega_mul2 0 = 1) by reflexivity. lia.
  - rewrite f_omega_mul2_eq.
    pose proof (f_omega_plus_le_ho (S k') (S k') ltac:(lia)) as Hplus.
    replace (S k' + 2) with (S (S (S k'))) by lia.
    rewrite hoc_snoc. simpl (0 + S (S k')).
    pose proof (hoc_ge_add4 0 (S (S k')) n) as Hadd.
    pose proof (ho_succ_mono (S k') (3 * S k') (hoc 0 (S (S k')) n) ltac:(lia)) as Hmono.
    lia.
Qed.

Lemma hoc_round_step : forall x B, 3 * (x + 6) <= B ->
  3 * (f_omega_mul2 x + 6) + 10 <= hoc 0 (B / 3 - 2) 10.
Proof.
  intros x B HB.
  assert (Hdiv : x + 6 <= B / 3).
  { apply Nat.div_le_lower_bound; lia. }
  pose proof (hoc_mono_k (x + 4) (B / 3 - 2) 0 10 ltac:(lia)) as H2.
  pose proof (f_omega_mul2_le_hoc x 10 ltac:(lia)) as H3.
  assert (H4 : hoc 0 (x + 3) 10 = ho (x + 2) (hoc 0 (x + 2) 10)).
  { replace (x + 3) with (S (x + 2)) by lia. rewrite hoc_snoc. reflexivity. }
  assert (H5 : hoc 0 (x + 4) 10 = ho (x + 3) (hoc 0 (x + 3) 10)).
  { replace (x + 4) with (S (x + 3)) by lia. rewrite hoc_snoc. reflexivity. }
  pose proof (ho_ge_5x3 (x + 1) (hoc 0 (x + 2) 10)) as Ha.
  replace (S (x + 1)) with (x + 2) in Ha by lia.
  pose proof (ho_ge_5x3 (x + 2) (hoc 0 (x + 3) 10)) as Hb.
  replace (S (x + 2)) with (x + 3) in Hb by lia.
  pose proof (f_omega_mul2_pos x).
  lia.
Qed.

Lemma ho_succ_eq : forall m n, ho (S m) n = iter (ho m) (n + 1) 6.
Proof. reflexivity. Qed.

Lemma hoc_3_eq : forall n, hoc 0 3 n = ho 2 (ho 1 (ho 0 n)).
Proof. reflexivity. Qed.

Lemma fFin_lt_f_omega_succ : forall k, 1 <= k -> fFin k (S k) < f_omega (S k).
Proof.
  intros k Hk. rewrite f_omega_eq, f_succ_eq.
  cbn [iter].
  assert (H1k : fFin k (S k) <= iter (fFin k) k (S k)).
  { change (fFin k (S k)) with (iter (fFin k) 1 (S k)).
    apply iter_mono_steps; [exact (fgh_ge_self _ (fFin_props k)) | lia]. }
  pose proof (fgh_mono _ (fFin_props k) _ _ H1k).
  pose proof (fgh_gt_pos _ (fFin_props k) (S k) ltac:(lia)).
  pose proof (fgh_gt_pos _ (fFin_props k) (fFin k (S k)) ltac:(lia)).
  lia.
Qed.

Lemma seed_bound_hoc3 : 3 * (fFin 5 2 + 6) + 10 <= hoc 0 3 10.
Proof.
  pose proof (fgh_mono _ (fFin_props 5) 2 6 ltac:(lia)) as Hf5.
  pose proof (fFin_lt_f_omega_succ 5 ltac:(lia)) as Hf6.
  pose proof (ho0_mod0 2) as H06.
  change (3 * 2) with 6 in H06.
  pose proof (hc0_ge_15q 2 ltac:(lia)) as Hhc.
  assert (Hi3 : f_omega 6 < iter (ho 0) 3 6).
  { pose proof (iter_add (ho 0) 2 1 6) as He.
    change (2 + 1) with 3 in He.
    assert (H1 : iter (ho 0) 1 6 = ho 0 6) by reflexivity.
    rewrite H1 in He. rewrite He.
    apply ho0_iter2_gt_f_omega. rewrite H06. lia. }
  assert (Hsteps : iter (ho 0) 3 6 + 48 <= ho 1 14).
  { rewrite ho_succ_eq.
    assert (Hadd12 : forall j x, x + 4 * j <= iter (ho 0) j x).
    { induction j as [| p IHp]; intro x; cbn [iter]; [lia |].
      specialize (IHp x). pose proof (ho_ge_add4 0 (iter (ho 0) p x)). lia. }
    pose proof (iter_add (ho 0) 12 3 6) as H15.
    change (12 + 3) with (14 + 1) in H15.
    rewrite H15. pose proof (Hadd12 12 (iter (ho 0) 3 6)). lia. }
  pose proof (ho0_mod1 3) as Hh010.
  change (3 * 3 + 1) with 10 in Hh010.
  change (3 * 3 + 5) with 14 in Hh010.
  rewrite hoc_3_eq, Hh010.
  pose proof (ho_ge_5x3 1 (ho 1 14)).
  lia.
Qed.
