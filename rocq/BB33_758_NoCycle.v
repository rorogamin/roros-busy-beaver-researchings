(** * Holdout #758: Exact 2-adic / mod-23 obstruction for all pure [L^2 J] cycles

    For the four 3-step [L^2 J] words [bbj], [bcj], [cbj], [ccj], let
    [D a c = 4 * a - 15 * c] in [Z]. We prove directly from the accelerated [step]:
      1. [4 * (23 * D a' c' - Cw w) = 27 * (23 * D a c - Cw w)]
         with [Cw = 1363, 1759, 2173, 2569].
      2. [23 * D a c - Cw w <> 0] (since [23] divides none of [1363, 1759, 2173, 2569]).
      3. After [m] consecutive repetitions of any pure [L^2 J] word [w],
         [4 ^ m | (23 * D a0 c0 - Cw w)], hence [4 ^ m <= Z.abs (23 * D a0 c0 - Cw w)].
         Therefore no integer orbit can repeat any pure [L^2 J] word forever. *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Inductive L2JWord : Type := | Wbbj | Wbcj | Wcbj | Wccj.

Definition Cw (w : L2JWord) : Z :=
  match w with
  | Wbbj => 1363
  | Wbcj => 1759
  | Wcbj => 2173
  | Wccj => 2569
  end.

Definition D (a c : Z) : Z := 4 * a - 15 * c.

Definition isB (a c a' c' : Z) : Prop :=
  c + 2 <= a /\ c mod 4 = 1 /\ a' = a - c - 2 /\ 2 * c' = 3 * c + 7.

Definition isC (a c a' c' : Z) : Prop :=
  c + 4 <= a /\ c mod 4 = 3 /\ a' = a - c - 4 /\ 2 * c' = 3 * c + 13.

Definition isJ (a c a' c' : Z) : Prop :=
  a <= c /\ a mod 2 = 1 /\ c mod 2 = 1 /\ a' = 3 * a + 2 /\ c' = c - a + 1.

Definition isCycle (w : L2JWord) (a c a' c' : Z) : Prop :=
  exists a1 c1 a2 c2,
    (match w with
     | Wbbj => isB a c a1 c1 /\ isB a1 c1 a2 c2
     | Wbcj => isB a c a1 c1 /\ isC a1 c1 a2 c2
     | Wcbj => isC a c a1 c1 /\ isB a1 c1 a2 c2
     | Wccj => isC a c a1 c1 /\ isC a1 c1 a2 c2
     end) /\ isJ a2 c2 a' c'.

Lemma cycle_D_eq (w : L2JWord) (a c a' c' : Z) (h : isCycle w a c a' c') :
    4 * D a' c' = 27 * D a c - Cw w.
Proof.
  destruct h as [a1 [c1 [a2 [c2 [h12 [_ [_ [_ [ha' hc']]]]]]]]].
  destruct w; destruct h12 as [[_ [_ [ha1 hc1]]] [_ [_ [ha2 hc2]]]];
    unfold D, Cw; lia.
Qed.

Lemma cycle_shifted_eq (w : L2JWord) (a c a' c' : Z) (h : isCycle w a c a' c') :
    4 * (23 * D a' c' - Cw w) = 27 * (23 * D a c - Cw w).
Proof.
  pose proof (cycle_D_eq w a c a' c' h). lia.
Qed.

Lemma shifted_ne_zero (w : L2JWord) (a c : Z) : 23 * D a c - Cw w <> 0.
Proof. destruct w; unfold Cw; lia. Qed.

Fixpoint iterCycle (w : L2JWord) (m : nat) (a c a' c' : Z) : Prop :=
  match m with
  | O => a' = a /\ c' = c
  | S k => exists a1 c1, isCycle w a c a1 c1 /\ iterCycle w k a1 c1 a' c'
  end.

Lemma iterCycle_shifted_eq (w : L2JWord) :
    forall (m : nat) (a0 c0 am cm : Z),
      iterCycle w m a0 c0 am cm ->
      4 ^ Z.of_nat m * (23 * D am cm - Cw w) =
        27 ^ Z.of_nat m * (23 * D a0 c0 - Cw w).
Proof.
  induction m as [|m ih]; intros a0 c0 am cm h.
  - destruct h as [ha hc]; subst; simpl; lia.
  - destruct h as [a1 [c1 [hc1 hrest]]].
    pose proof (cycle_shifted_eq w a0 c0 a1 c1 hc1) as H1.
    pose proof (ih a1 c1 am cm hrest) as H2.
    rewrite Nat2Z.inj_succ, !Z.pow_succ_r by lia.
    nia.
Qed.

Lemma four_dvd_of_mul_27 (x : Z) (h : (4 | 27 * x)) : (4 | x).
Proof.
  destruct h as [k hk]. exists (7 * x - k). lia.
Qed.

Lemma four_dvd_of_mul_27_pow (m : nat) :
    forall x : Z, (4 | 27 ^ Z.of_nat m * x) -> (4 | x).
Proof.
  induction m as [|m ih]; intros x h.
  - change (Z.of_nat 0) with 0 in h. rewrite Z.pow_0_r, Z.mul_1_l in h. exact h.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in h by lia.
    apply four_dvd_of_mul_27.
    apply ih.
    replace (27 ^ Z.of_nat m * (27 * x)) with (27 * 27 ^ Z.of_nat m * x) by lia.
    exact h.
Qed.

Lemma four_pow_dvd_of_mul_27_pow (m : nat) :
    forall (r : nat) (x : Z),
      (4 ^ Z.of_nat m | 27 ^ Z.of_nat r * x) -> (4 ^ Z.of_nat m | x).
Proof.
  induction m as [|m ih]; intros r x h.
  - simpl. exists x. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in h by lia.
    assert (H4 : (4 | 27 ^ Z.of_nat r * x)).
    { destruct h as [k hk]. exists (k * 4 ^ Z.of_nat m). nia. }
    pose proof (four_dvd_of_mul_27_pow r x H4) as [y hy].
    assert (Hm : (4 ^ Z.of_nat m | 27 ^ Z.of_nat r * y)).
    { destruct h as [k hk]. exists k. nia. }
    pose proof (ih r y Hm) as [z hz].
    exists z. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

(** **Unconditional finite upper bound on pure [L^2 J] repetitions**:
    any [m] consecutive repetitions of any pure word [w in {bbj, bcj, cbj, ccj}]
    satisfy [4 ^ m <= Z.abs (23 * D a0 c0 - Cw w)]. *)
Theorem no_long_pure_L2J (w : L2JWord) (m : nat) (a0 c0 am cm : Z)
    (h : iterCycle w m a0 c0 am cm) :
    4 ^ Z.of_nat m <= Z.abs (23 * D a0 c0 - Cw w).
Proof.
  pose proof (iterCycle_shifted_eq w m a0 c0 am cm h) as Heq.
  assert (Hdvd : (4 ^ Z.of_nat m | 27 ^ Z.of_nat m * (23 * D a0 c0 - Cw w))).
  { exists (23 * D am cm - Cw w). lia. }
  pose proof (four_pow_dvd_of_mul_27_pow m m _ Hdvd) as [q hq].
  pose proof (shifted_ne_zero w a0 c0) as Hnz.
  assert (Hpos : 0 < 4 ^ Z.of_nat m) by (apply Z.pow_pos_nonneg; lia).
  assert (Hqnz : q <> 0) by nia.
  nia.
Qed.

(** **No infinite pure [L^2 J] orbit exists anywhere in [Z^2].** *)
Theorem no_infinite_pure_L2J (w : L2JWord) (a0 c0 : Z) :
    ~ (forall m : nat, exists am cm, iterCycle w m a0 c0 am cm).
Proof.
  intro hall.
  set (B := Z.abs (23 * D a0 c0 - Cw w)).
  assert (HB : 0 <= B) by (unfold B; lia).
  destruct (hall (S (Z.to_nat B))) as [am [cm hm]].
  pose proof (no_long_pure_L2J w (S (Z.to_nat B)) a0 c0 am cm hm) as Hle.
  assert (Hgrow : forall n : nat, Z.of_nat n < 4 ^ Z.of_nat n).
  { induction n as [|n ihn].
    - simpl. lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
  pose proof (Hgrow (S (Z.to_nat B))) as Hg.
  rewrite Nat2Z.inj_succ, Z2Nat.id in Hle, Hg by lia.
  unfold B in *. lia.
Qed.

Print Assumptions cycle_D_eq.
Print Assumptions cycle_shifted_eq.
Print Assumptions shifted_ne_zero.
Print Assumptions iterCycle_shifted_eq.
Print Assumptions no_long_pure_L2J.
Print Assumptions no_infinite_pure_L2J.
