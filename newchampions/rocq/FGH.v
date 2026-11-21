(*
  rocq/FGH.v
  Exact, axiom-free, structurally recursive (System T) Wainer Fast-Growing Hierarchy
  up to ω^2 * c + ω * a + b with standard fundamental sequences:
    f_0(n) = n + 1
    f_{α+1}(n) = f_α^n(n)
    f_ω(n) = f_n(n)
    f_{ω*(a+1)}(n) = f_{ω*a + n}(n)
    f_{ω^2*(c+1)}(n) = f_{ω^2*c + ω*n}(n)
*)

From Stdlib Require Import Arith Lia.

Fixpoint iter (g : nat -> nat) (n : nat) (x : nat) : nat :=
  match n with
  | 0 => x
  | S k => g (iter g k x)
  end.

Definition fNext (g : nat -> nat) (n : nat) : nat := iter g n n.

Fixpoint fPlus (g : nat -> nat) (b : nat) : nat -> nat :=
  match b with
  | 0 => g
  | S k => fNext (fPlus g k)
  end.

Definition fDiag (F : nat -> nat -> nat) (n : nat) : nat := F n n.

Fixpoint fOmegaStep (g : nat -> nat) (a : nat) : nat -> nat :=
  match a with
  | 0 => g
  | S k => fDiag (fPlus (fOmegaStep g k))
  end.

Fixpoint fOmega2Step (g : nat -> nat) (c : nat) : nat -> nat :=
  match c with
  | 0 => g
  | S k => fDiag (fOmegaStep (fOmega2Step g k))
  end.

Definition fZero (n : nat) : nat := S n.
Definition fFin (k : nat) : nat -> nat := fPlus fZero k.
Definition fOmegaMul (a b : nat) : nat -> nat := fPlus (fOmegaStep fZero a) b.
Definition fOmega2 (c a b : nat) : nat -> nat := fPlus (fOmegaStep (fOmega2Step fZero c) a) b.

(* Standard Named Aliases *)
Definition f_omega (n : nat) : nat := fOmegaMul 1 0 n.
Definition f_omega_plus (k n : nat) : nat := fOmegaMul 1 k n.
Definition f_omega_mul2 (n : nat) : nat := fOmegaMul 2 0 n.
Definition f_omega_mul2_plus (k n : nat) : nat := fOmegaMul 2 k n.
Definition f_omega2 (n : nat) : nat := fOmega2 1 0 0 n.
Definition f_omega2_plus (k n : nat) : nat := fOmega2 1 0 k n.

(* Definitional Sanity Checks *)
Lemma f_0_eq : forall n, fFin 0 n = S n. Proof. reflexivity. Qed.
Lemma f_succ_eq : forall k n, fFin (S k) n = iter (fFin k) n n. Proof. reflexivity. Qed.
Lemma f_omega_eq : forall n, f_omega n = fFin n n. Proof. reflexivity. Qed.
Lemma f_omega_plus_succ_eq : forall k n, f_omega_plus (S k) n = iter (f_omega_plus k) n n. Proof. reflexivity. Qed.
Lemma f_omega_mul2_eq : forall n, f_omega_mul2 n = f_omega_plus n n. Proof. reflexivity. Qed.
Lemma f_omega_mul2_plus_succ_eq : forall k n, f_omega_mul2_plus (S k) n = iter (f_omega_mul2_plus k) n n. Proof. reflexivity. Qed.
Lemma f_omega2_eq : forall n, f_omega2 n = fOmegaMul n 0 n. Proof. reflexivity. Qed.
Lemma f_omega2_plus_succ_eq : forall k n, f_omega2_plus (S k) n = iter (f_omega2_plus k) n n. Proof. reflexivity. Qed.

(* Iteration Lemmas *)
Lemma iter_zero : forall g x, iter g 0 x = x. Proof. reflexivity. Qed.
Lemma iter_succ : forall g n x, iter g (S n) x = g (iter g n x). Proof. reflexivity. Qed.

Lemma iter_add : forall g a b x, iter g (a + b) x = iter g a (iter g b x).
Proof.
  intros g a. induction a as [| k IH]; intros b x; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma iter_mono_arg : forall g, (forall x y, x <= y -> g x <= g y) ->
  forall n x y, x <= y -> iter g n x <= iter g n y.
Proof.
  intros g Hg n. induction n as [| k IH]; intros x y Hxy; simpl.
  - exact Hxy.
  - apply Hg. apply IH. exact Hxy.
Qed.

Lemma iter_ge_self : forall g, (forall x, x <= g x) ->
  forall n x, x <= iter g n x.
Proof.
  intros g Hg n. induction n as [| k IH]; intros x; simpl.
  - lia.
  - eapply Nat.le_trans; [apply IH | apply Hg].
Qed.

Lemma iter_ge_add_pos : forall g, (forall x, 1 <= x -> S x <= g x) ->
  forall n x, 1 <= x -> x + n <= iter g n x.
Proof.
  intros g Hg n. induction n as [| k IH]; intros x Hx; simpl.
  - lia.
  - specialize (IH x Hx).
    assert (H1 : 1 <= iter g k x) by lia.
    specialize (Hg (iter g k x) H1). lia.
Qed.

Lemma iter_mono_steps : forall g, (forall x, x <= g x) ->
  forall n m x, n <= m -> iter g n x <= iter g m x.
Proof.
  intros g Hg n m x Hnm. induction Hnm as [| k Hle IH]; simpl.
  - lia.
  - eapply Nat.le_trans; [exact IH | apply Hg].
Qed.

Lemma iter_two_mul : forall g n x, iter (fun y => g (g y)) n x = iter g (2 * n) x.
Proof.
  intros g n. induction n as [| k IH]; intros x.
  - reflexivity.
  - replace (2 * S k) with (S (S (2 * k))) by lia.
    simpl. rewrite IH. reflexivity.
Qed.

(* Generic Monotonicity & Growth *)
Record FGHProps (g : nat -> nat) : Prop := mkFGHProps {
  fgh_ge_self : forall n, n <= g n;
  fgh_gt_pos  : forall n, 1 <= n -> S n <= g n;
  fgh_mono    : forall x y, x <= y -> g x <= g y
}.

Lemma fZero_props : FGHProps fZero.
Proof.
  constructor; unfold fZero; intros; lia.
Qed.

Lemma fNext_props : forall g, FGHProps g -> FGHProps (fNext g).
Proof.
  intros g [Hself Hgt Hmono]. constructor; unfold fNext.
  - intro n. apply iter_ge_self; exact Hself.
  - intros n Hn. pose proof (iter_ge_add_pos g Hgt n n Hn). lia.
  - intros x y Hxy.
    eapply Nat.le_trans.
    + apply iter_mono_steps; [exact Hself | exact Hxy].
    + apply iter_mono_arg; [exact Hmono | exact Hxy].
Qed.

Lemma fNext_ge : forall g, FGHProps g -> forall n, 1 <= n -> g n <= fNext g n.
Proof.
  intros g [Hself Hgt Hmono] n Hn. destruct n as [| m]; [lia |].
  unfold fNext. simpl. apply Hmono. apply iter_ge_self; exact Hself.
Qed.

Lemma fPlus_props : forall g, FGHProps g -> forall b, FGHProps (fPlus g b).
Proof.
  intros g Hg b. induction b as [| k IH]; simpl.
  - exact Hg.
  - apply fNext_props; exact IH.
Qed.

Lemma fPlus_mono_idx : forall g, FGHProps g ->
  forall b1 b2 n, 1 <= n -> b1 <= b2 -> fPlus g b1 n <= fPlus g b2 n.
Proof.
  intros g Hg b1 b2 n Hn Hb. induction Hb as [| k Hle IH].
  - lia.
  - eapply Nat.le_trans; [exact IH |]. apply fNext_ge; [apply fPlus_props; exact Hg | exact Hn].
Qed.

Lemma fDiag_props : forall F,
  (forall k, FGHProps (F k)) ->
  (forall k1 k2 n, 1 <= n -> k1 <= k2 -> F k1 n <= F k2 n) ->
  FGHProps (fDiag F).
Proof.
  intros F HF Hmono. constructor; unfold fDiag.
  - intro n. apply (fgh_ge_self _ (HF n)).
  - intros n Hn. apply (fgh_gt_pos _ (HF n)); exact Hn.
  - intros x y Hxy. destruct x as [| mx].
    + destruct y as [| my]; [lia |].
      eapply Nat.le_trans.
      * apply (fgh_mono _ (HF 0)); lia.
      * apply Hmono; lia.
    + assert (Hy : 1 <= y) by lia.
      eapply Nat.le_trans.
      * apply (fgh_mono _ (HF (S mx))); exact Hxy.
      * apply Hmono; lia.
Qed.

Lemma fOmegaStep_props : forall g, FGHProps g -> forall a, FGHProps (fOmegaStep g a).
Proof.
  intros g Hg a. induction a as [| k IH]; simpl.
  - exact Hg.
  - apply fDiag_props.
    + intro b. apply fPlus_props; exact IH.
    + intros k1 k2 n Hn Hk. apply fPlus_mono_idx; assumption.
Qed.

Lemma fOmegaStep_mono_idx : forall g, FGHProps g ->
  forall a1 a2 n, 1 <= n -> a1 <= a2 -> fOmegaStep g a1 n <= fOmegaStep g a2 n.
Proof.
  intros g Hg a1 a2 n Hn Ha. induction Ha as [| k Hle IH].
  - lia.
  - eapply Nat.le_trans; [exact IH |].
    simpl. unfold fDiag.
    change (fPlus (fOmegaStep g k) 0 n <= fPlus (fOmegaStep g k) n n).
    apply fPlus_mono_idx; [apply fOmegaStep_props; exact Hg | exact Hn | lia].
Qed.

Lemma fOmega2Step_props : forall g, FGHProps g -> forall c, FGHProps (fOmega2Step g c).
Proof.
  intros g Hg c. induction c as [| k IH]; simpl.
  - exact Hg.
  - apply fDiag_props.
    + intro a. apply fOmegaStep_props; exact IH.
    + intros k1 k2 n Hn Hk. apply fOmegaStep_mono_idx; assumption.
Qed.

Lemma fFin_props : forall k, FGHProps (fFin k).
Proof. intro k. apply fPlus_props, fZero_props. Qed.

Lemma fOmegaMul_props : forall a b, FGHProps (fOmegaMul a b).
Proof. intros a b. apply fPlus_props, fOmegaStep_props, fZero_props. Qed.

Lemma fOmega2_props : forall c a b, FGHProps (fOmega2 c a b).
Proof. intros c a b. apply fPlus_props, fOmegaStep_props, fOmega2Step_props, fZero_props. Qed.

(* Reusable Level-Climbing Lemma *)
Lemma climb_level :
  forall (H f : nat -> nat) (c : nat),
    2 <= c ->
    (forall x y, x <= y -> H x <= H y) ->
    (forall x, 2 <= x -> S x <= H x) ->
    (forall x, 2 <= x -> f x < H (H x)) ->
    (forall x, 2 <= x -> 3 * x <= iter H x c) ->
    FGHProps f ->
    forall x, 2 <= x -> fNext f x < iter H (iter H x c) c.
Proof.
  intros H f c Hc Hmono Hinc HH2 Hge3 [Hf_self Hf_gt Hf_mono] x Hx.
  assert (Hself : forall y, 2 <= y -> y <= H y) by (intros y Hy; specialize (Hinc y Hy); lia).
  assert (Hlb : forall k y, 2 <= y -> 2 <= iter H k y).
  { intros k y Hy. induction k as [| m IH]; simpl; [exact Hy |].
    specialize (Hself _ IH). lia. }
  assert (Hsteps : forall a b, a <= b -> iter H a c <= iter H b c).
  { intros a b Hab. induction Hab as [| k Hle IH]; simpl; [lia |].
    eapply Nat.le_trans; [exact IH | apply Hself, Hlb; exact Hc]. }
  pose proof (Hge3 x Hx) as H3x.
  pose proof (Hsteps (3 * x) (iter H x c) H3x) as Hstep1.
  replace (3 * x) with (2 * x + x) in Hstep1 by lia.
  rewrite iter_add in Hstep1.
  assert (Hxle : x <= iter H x c) by lia.
  pose proof (iter_mono_arg H Hmono (2 * x) x (iter H x c) Hxle) as Hstep2.
  assert (Hstrict : forall k y, 1 <= k -> 2 <= y -> iter f k y < iter (fun z => H (H z)) k y).
  { intros k y Hk Hy. destruct k as [| m]; [lia |].
    assert (Hle : forall j, 2 <= iter f j y /\ iter f j y <= iter (fun z => H (H z)) j y).
    { intro j. induction j as [| j' [IH1 IH2]]; simpl.
      - split; [exact Hy | lia].
      - split.
        + eapply Nat.le_trans; [exact IH1 | apply Hf_self].
        + eapply Nat.le_trans; [apply Hf_mono; exact IH2 |].
          apply Nat.lt_le_incl, HH2. lia. }
    destruct (Hle m) as [Hm1 Hm2]. simpl.
    eapply Nat.le_lt_trans; [apply Hf_mono; exact Hm2 |].
    apply HH2. lia. }
  unfold fNext.
  specialize (Hstrict x x ltac:(lia) Hx).
  rewrite iter_two_mul in Hstrict.
  lia.
Qed.

Lemma iter_strict_dom :
  forall (H f : nat -> nat) (b : nat),
    (forall z, b <= z -> f z < H z) ->
    FGHProps f ->
    forall n y, 1 <= n -> b <= y -> iter f n y < iter H n y.
Proof.
  intros H f b Hdom [Hf_self Hf_gt Hf_mono] n y Hn Hy.
  destruct n as [| m]; [lia |].
  assert (Hle : forall j, b <= iter f j y /\ iter f j y <= iter H j y).
  { intro j. induction j as [| j' [IH1 IH2]]; simpl.
    - split; [exact Hy | lia].
    - split.
      + eapply Nat.le_trans; [exact IH1 | apply Hf_self].
      + eapply Nat.le_trans; [apply Hf_mono; exact IH2 |].
        apply Nat.lt_le_incl, Hdom. lia. }
  destruct (Hle m) as [Hm1 Hm2]. simpl.
  eapply Nat.le_lt_trans; [apply Hf_mono; exact Hm2 |].
  apply Hdom. lia.
Qed.

Lemma climb_double :
  forall (H f : nat -> nat) (c : nat),
    1 <= c ->
    (forall x y, x <= y -> H x <= H y) ->
    (forall x, 1 <= x -> S x <= H x) ->
    (forall x, 1 <= x -> f x < H x) ->
    FGHProps f ->
    forall x, 1 <= x -> fNext f x < iter H (2 * x) c.
Proof.
  intros H f c Hc Hmono Hinc Hdom Hf x Hx.
  replace (2 * x) with (x + x) by lia.
  rewrite iter_add.
  assert (Hbase : x <= iter H x c).
  { pose proof (iter_ge_add_pos H Hinc x c Hc). lia. }
  pose proof (iter_mono_arg H Hmono x x (iter H x c) Hbase) as Harg.
  pose proof (iter_strict_dom H f 1 Hdom Hf x x Hx Hx) as Hlt.
  unfold fNext. lia.
Qed.

(* Structural System T extension to ω^ω and ω^ω + k:
   fOmegaPowStep g 0 = fNext g                       (α + ω^0 = α + 1)
   fOmegaPowStep g (S k) n = (fOmegaPowStep · k)^n g n  (α + ω^{k+1}[n] = α + ω^k * n)
   f_omega_omega n = fOmegaPowStep fZero n n         (f_{ω^ω}(n) = f_{ω^n}(n))
   f_omega_omega_plus k n = fPlus f_omega_omega k n  (f_{ω^ω + k}(n)) *)
Fixpoint iterF (F : (nat -> nat) -> (nat -> nat)) (n : nat) (g : nat -> nat) : nat -> nat :=
  match n with
  | 0 => g
  | S m => F (iterF F m g)
  end.

Fixpoint fOmegaPowStep (k : nat) (g : nat -> nat) : nat -> nat :=
  match k with
  | 0 => fNext g
  | S k' => fun n => iterF (fOmegaPowStep k') n g n
  end.

Definition f_omega_omega (n : nat) : nat := fOmegaPowStep n fZero n.
Definition f_omega_omega_plus (k n : nat) : nat := fPlus f_omega_omega k n.

Lemma fOmegaPowStep_props_and_ge : forall k g, FGHProps g ->
  FGHProps (fOmegaPowStep k g) /\ (forall n, 1 <= n -> g n <= fOmegaPowStep k g n).
Proof.
  induction k as [| k' IH]; intros g Hg.
  - simpl. split; [apply fNext_props; exact Hg | apply fNext_ge; exact Hg].
  - assert (Hiter : forall m, FGHProps (iterF (fOmegaPowStep k') m g)).
    { induction m as [| m' IHm]; [exact Hg | simpl; apply (proj1 (IH _ IHm))]. }
    assert (Hge_m : forall m n, 1 <= n -> g n <= iterF (fOmegaPowStep k') m g n).
    { induction m as [| m' IHm]; intros n Hn; [simpl; lia |].
      simpl. eapply Nat.le_trans; [apply IHm; exact Hn |].
      apply (proj2 (IH _ (Hiter m'))); exact Hn. }
    split.
    + constructor; simpl.
      * intro n. apply (fgh_ge_self _ (Hiter n) n).
      * intros n Hn. apply (fgh_gt_pos _ (Hiter n) n Hn).
      * intros x y Hxy.
        eapply Nat.le_trans; [apply (fgh_mono _ (Hiter x) x y Hxy) |].
        destruct y as [| y']; [assert (x = 0) by lia; subst; lia |].
        assert (Hmono_m : forall m1 m2 n, 1 <= n -> m1 <= m2 ->
                  iterF (fOmegaPowStep k') m1 g n <= iterF (fOmegaPowStep k') m2 g n).
        { intros m1 m2 n Hn Hm. induction Hm as [| m'' Hle IHm]; [lia |].
          eapply Nat.le_trans; [exact IHm |].
          simpl. apply (proj2 (IH _ (Hiter m''))); exact Hn. }
        apply Hmono_m; [lia | exact Hxy].
    + intros n Hn. simpl. apply Hge_m; exact Hn.
Qed.

Lemma fOmegaPowStep_props : forall k g, FGHProps g -> FGHProps (fOmegaPowStep k g).
Proof. intros k g Hg. exact (proj1 (fOmegaPowStep_props_and_ge k g Hg)). Qed.

Lemma fOmegaPowStep_ge : forall k g, FGHProps g -> forall n, 1 <= n -> g n <= fOmegaPowStep k g n.
Proof. intros k g Hg. exact (proj2 (fOmegaPowStep_props_and_ge k g Hg)). Qed.

Lemma f_omega_omega_props : FGHProps f_omega_omega.
Proof.
  constructor; unfold f_omega_omega.
  - intro n. apply (fgh_ge_self _ (fOmegaPowStep_props n fZero fZero_props) n).
  - intros n Hn. apply (fgh_gt_pos _ (fOmegaPowStep_props n fZero fZero_props) n Hn).
  - intros x y Hxy.
    eapply Nat.le_trans; [apply (fgh_mono _ (fOmegaPowStep_props x fZero fZero_props) x y Hxy) |].
    destruct y as [| y']; [assert (x = 0) by lia; subst; lia |].
    assert (Hmono_k : forall k1 k2 n, 1 <= n -> k1 <= k2 ->
              fOmegaPowStep k1 fZero n <= fOmegaPowStep k2 fZero n).
    { intros k1 k2 n Hn Hk. induction Hk as [| k' Hle IHk]; [lia |].
      eapply Nat.le_trans; [exact IHk |].
      simpl. destruct n as [| n']; [lia |]. simpl.
      assert (Hiter_ge : forall m h, FGHProps h ->
                fOmegaPowStep k' h (S n') <= iterF (fOmegaPowStep k') (S m) h (S n')).
      { induction m as [| m' IHm]; intros h Hh; [simpl; lia |].
        eapply Nat.le_trans; [apply (IHm h Hh) |].
        simpl. apply fOmegaPowStep_ge; [| lia].
        clear IHm. induction m' as [| m'' IHm''];
          [apply fOmegaPowStep_props; exact Hh | simpl; apply fOmegaPowStep_props; exact IHm'']. }
      apply Hiter_ge; exact fZero_props. }
    apply Hmono_k; [lia | exact Hxy].
Qed.
