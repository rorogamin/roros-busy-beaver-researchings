(*
  Rocq counterpart of [cryptids_a6/BusyBeaver/BB33/M_758_TBudget.lean].

  BB(3,3) holdout #758 = 1RB2LC1RC_2LC---2RB_2LA0LB0RA.

  Contents (one-to-one with the Lean module):

  * the exact step function, [run], [Survives], the weighted length [Q];
  * [Q_step] / [run_Q]: every surviving step raises [Q = a + 2c] by >= 3;
  * [L_step], [Ssum], [L_budget], [L_phase_budget]: the closed L-phase budget
    [2*c0*3^n <= 2^n*(a0 + 2*c0)];
  * [L_phase_le_791] and [L_phase_le_878]: a post-[j] L phase with [k <= 292]
    has length <= 791 (sharp, via [three_pow_gt], one 1255-bit comparison
    discharged by [vm_compute] in [Z]) and, coarsely, <= 878 (from [9 > 8],
    needing no large numerals); both constants are also proved in the Lean
    module, so the two files carry the same phase constant [791];
  * [J_a_closed], [J_Q_closed], [J_phase_budget], [three_pow_dominates],
    [J_phase_le_293]: a [j] phase has length <= 293;
  * [Budget], [survives_le_of_budget], [postJ_survives_le_10000]: the residual
    hypothesis and the conditional universal halving-time bound [T <= 10000].
  * [flips], [flips_le], [phases_le], [counting_budget_le],
    [counting_budget_forces]: phase counting -- the only unconditional count
    bound, and the arithmetic showing a count cannot close the residual.
  * [hrun_phase_composition], [hrun_phase_counting], [ssum_cutLen], [cutLen],
    [phaseTag], [reg]: the phase composition over a real halving run -- the
    phase lengths are built from the run's cut sequence and sum to its length;
  * [L_phase_len_c0], [J_phase_len_own]: the per-phase budgets in terms of each
    phase's own start rather than a fixed cap.
  * [L_drop], [L_grow_a], [L_grow_b], [L_grow_c]: the per-rule arithmetic of
    [L_step], stated separately so no [lia] runs on a conjunction or on a [mod];
  * [regB], [pcnt], [witness_phase_counts], [phase_count_bound_false],
    [counting_budget_le_8], [witness_charge_exceeds]: the phase-count bound
    [NL <= 7], [NJ <= 6] is false on the family -- the run from
    [(2*3^7 - 1, 24)] visits 8 [L] and 8 [J] phases, charging
    [878*8 + 293*8 = 9368 > 9209].

  No [Admitted], no [Parameter], no [Axiom].  Every exported theorem is checked
  with [Print Assumptions] at the end of the file.
*)

From Stdlib Require Import Arith Lia Bool ZArith.

(* ------------------------------------------------------------------ *)
(** ** 0. Small helpers                                               *)
(* ------------------------------------------------------------------ *)

Lemma leb_true_le (n m : nat) (h : Nat.leb n m = true) : n <= m.
Proof.
  destruct (Nat.le_gt_cases n m) as [hle | hlt]; [exact hle | exfalso].
  assert (Hf : Nat.leb n m = false) by (apply Nat.leb_gt; exact hlt).
  rewrite Hf in h. discriminate h.
Qed.

Lemma leb_false_lt (n m : nat) (h : Nat.leb n m = false) : m < n.
Proof. exact (proj1 (Nat.leb_gt n m) h). Qed.

Lemma eqb_false_neq (n m : nat) (h : Nat.eqb n m = false) : n <> m.
Proof.
  intro H. rewrite H in h.
  assert (Ht : Nat.eqb m m = true) by (apply Nat.eqb_eq; reflexivity).
  rewrite Ht in h. discriminate h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 1. The machine                                                   *)
(* ------------------------------------------------------------------ *)

Inductive Out : Type :=
  | Halt : Out
  | Next : nat -> nat -> Out.

Definition step (a c : nat) : Out :=
  if Nat.leb a c then
    if Nat.eqb (Nat.modulo a 2) 0 then
      if Nat.eqb (Nat.modulo c 2) 0 then Halt
      else Next 1 (Nat.div a 2 + c + 2)
    else if Nat.eqb (Nat.modulo c 2) 0 then
      Next (3 * a) (c - a + 4)
    else
      Next (3 * a + 2) (c - a + 1)
  else if orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2) then
    Next (a - c - 1) (3 * (Nat.div c 2) + 2)
  else if Nat.eqb (Nat.modulo c 4) 1 then
    if Nat.eqb a (c + 1) then Halt
    else Next (a - c - 2) (3 * (Nat.div (c - 1) 2) + 5)
  else
    if Nat.eqb a (c + 1) then Halt
    else if Nat.eqb a (c + 2) then Next (3 * c + 8) 1
    else if Nat.eqb a (c + 3) then Halt
    else Next (a - c - 4) (3 * (Nat.div (c - 1) 2) + 8).

Fixpoint run (n : nat) (p : nat * nat) : option (nat * nat) :=
  match n with
  | O => Some p
  | S n' =>
      match step (fst p) (snd p) with
      | Halt => None
      | Next a' c' => run n' (a', c')
      end
  end.

Definition Survives (n a c : nat) : Prop :=
  exists a' c' : nat, run n (a, c) = Some (a', c').

(** The weighted length `a + 2*c`. *)
Definition Q (a c : nat) : nat := a + 2 * c.

(* ------------------------------------------------------------------ *)
(** ** 0b. Division helpers                                            *)
(* ------------------------------------------------------------------ *)

Lemma mod2_two_mul (k : nat) : (2 * k) mod 2 = 0.
Proof.
  destruct (Nat.div_mod_unique 2 k ((2 * k) / 2) 0 ((2 * k) mod 2)) as [_ H].
  - lia.
  - apply Nat.mod_upper_bound. lia.
  - pose proof (Nat.div_mod_eq (2 * k) 2). lia.
  - lia.
Qed.

Lemma div_two_mul (k : nat) : 2 * k / 2 = k.
Proof.
  pose proof (Nat.div_mod_eq (2 * k) 2) as H.
  rewrite mod2_two_mul, Nat.add_0_r in H. lia.
Qed.

Lemma two_div (c : nat) (h : c mod 2 = 0) : 2 * (c / 2) = c.
Proof.
  pose proof (Nat.div_mod_eq c 2) as H. rewrite h, Nat.add_0_r in H. lia.
Qed.

Lemma six_div (c : nat) (h : c mod 2 = 1) : 6 * ((c - 1) / 2) = 3 * (c - 1).
Proof.
  assert (Hc : c - 1 = 2 * (c / 2)) by (pose proof (Nat.div_mod_eq c 2); lia).
  rewrite Hc, div_two_mul. lia.
Qed.

Lemma mod2_of_mod4_even (c : nat) (h : c mod 4 = 0 \/ c mod 4 = 2) : c mod 2 = 0.
Proof.
  destruct h as [h | h].
  - pose proof (Nat.div_mod_eq c 4) as H. rewrite h, Nat.add_0_r in H.
    rewrite H. replace (4 * (c / 4)) with (2 * (2 * (c / 4))) by lia.
    apply mod2_two_mul.
  - pose proof (Nat.div_mod_eq c 4) as H. rewrite h in H.
    rewrite H. replace (4 * (c / 4) + 2) with (2 * (2 * (c / 4) + 1)) by lia.
    apply mod2_two_mul.
Qed.

Lemma mod2_of_mod4_odd (c : nat) (h : c mod 4 = 1) : c mod 2 = 1.
Proof.
  pose proof (Nat.div_mod_eq c 4) as H. rewrite h in H.
  destruct (Nat.div_mod_unique 2 (2 * (c / 4)) (c / 2) 1 (c mod 2)) as [_ H2].
  - lia.
  - apply Nat.mod_upper_bound. lia.
  - pose proof (Nat.div_mod_eq c 2). lia.
  - lia.
Qed.

Lemma mod2_of_mod4_three (c : nat) (h : c mod 4 = 3) : c mod 2 = 1.
Proof.
  pose proof (Nat.div_mod_eq c 4) as H. rewrite h in H.
  destruct (Nat.div_mod_unique 2 (2 * (c / 4) + 1) (c / 2) 1 (c mod 2)) as [_ H2].
  - lia.
  - apply Nat.mod_upper_bound. lia.
  - pose proof (Nat.div_mod_eq c 2). lia.
  - lia.
Qed.

Lemma mod4_three (c : nat) (h0 : c mod 4 <> 0) (h2 : c mod 4 <> 2)
    (h1 : c mod 4 <> 1) : c mod 4 = 3.
Proof. pose proof (Nat.mod_upper_bound c 4 (ltac:(lia))). lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** 1b. Per-rule characterisations                                  *)
(* ------------------------------------------------------------------ *)

Lemma step_g (a c : nat)
    (E1 : Nat.leb a c = true) (E2 : Nat.eqb (Nat.modulo a 2) 0 = true)
    (E3 : Nat.eqb (Nat.modulo c 2) 0 = true) : step a c = Halt.
Proof. unfold step. now rewrite E1, E2, E3. Qed.

Lemma step_h (a c : nat)
    (E1 : Nat.leb a c = true) (E2 : Nat.eqb (Nat.modulo a 2) 0 = true)
    (E3 : Nat.eqb (Nat.modulo c 2) 0 = false) :
    step a c = Next 1 (a / 2 + c + 2).
Proof. unfold step. now rewrite E1, E2, E3. Qed.

Lemma step_i (a c : nat)
    (E1 : Nat.leb a c = true) (E2 : Nat.eqb (Nat.modulo a 2) 0 = false)
    (E3 : Nat.eqb (Nat.modulo c 2) 0 = true) :
    step a c = Next (3 * a) (c - a + 4).
Proof. unfold step. now rewrite E1, E2, E3. Qed.

Lemma step_j (a c : nat)
    (E1 : Nat.leb a c = true) (E2 : Nat.eqb (Nat.modulo a 2) 0 = false)
    (E3 : Nat.eqb (Nat.modulo c 2) 0 = false) :
    step a c = Next (3 * a + 2) (c - a + 1).
Proof. unfold step. now rewrite E1, E2, E3. Qed.

Lemma step_a (a c : nat) (E1 : Nat.leb a c = false)
    (E4 : orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2) = true) :
    step a c = Next (a - c - 1) (3 * (c / 2) + 2).
Proof. unfold step. now rewrite E1, E4. Qed.

Lemma step_b (a c : nat) (E1 : Nat.leb a c = false)
    (E4 : orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2) = false)
    (E5 : Nat.eqb (Nat.modulo c 4) 1 = true)
    (E6 : Nat.eqb a (c + 1) = false) :
    step a c = Next (a - c - 2) (3 * ((c - 1) / 2) + 5).
Proof. unfold step. now rewrite E1, E4, E5, E6. Qed.

Lemma step_f (a c : nat) (E1 : Nat.leb a c = false)
    (E4 : orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2) = false)
    (E5 : Nat.eqb (Nat.modulo c 4) 1 = true)
    (E6 : Nat.eqb a (c + 1) = true) : step a c = Halt.
Proof. unfold step. now rewrite E1, E4, E5, E6. Qed.

Lemma step_halt1 (a c : nat) (E1 : Nat.leb a c = false)
    (E4 : orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2) = false)
    (E5 : Nat.eqb (Nat.modulo c 4) 1 = false)
    (E6 : Nat.eqb a (c + 1) = true) : step a c = Halt.
Proof. unfold step. now rewrite E1, E4, E5, E6. Qed.

Lemma step_e (a c : nat) (E1 : Nat.leb a c = false)
    (E4 : orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2) = false)
    (E5 : Nat.eqb (Nat.modulo c 4) 1 = false)
    (E6 : Nat.eqb a (c + 1) = false)
    (E7 : Nat.eqb a (c + 2) = true) : step a c = Next (3 * c + 8) 1.
Proof. unfold step. now rewrite E1, E4, E5, E6, E7. Qed.

Lemma step_halt3 (a c : nat) (E1 : Nat.leb a c = false)
    (E4 : orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2) = false)
    (E5 : Nat.eqb (Nat.modulo c 4) 1 = false)
    (E6 : Nat.eqb a (c + 1) = false)
    (E7 : Nat.eqb a (c + 2) = false)
    (E8 : Nat.eqb a (c + 3) = true) : step a c = Halt.
Proof. unfold step. now rewrite E1, E4, E5, E6, E7, E8. Qed.

Lemma step_c (a c : nat) (E1 : Nat.leb a c = false)
    (E4 : orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2) = false)
    (E5 : Nat.eqb (Nat.modulo c 4) 1 = false)
    (E6 : Nat.eqb a (c + 1) = false)
    (E7 : Nat.eqb a (c + 2) = false)
    (E8 : Nat.eqb a (c + 3) = false) :
    step a c = Next (a - c - 4) (3 * ((c - 1) / 2) + 8).
Proof. unfold step. now rewrite E1, E4, E5, E6, E7, E8. Qed.

(* ------------------------------------------------------------------ *)
(** ** 2. The increment invariant `Q = a + 2c`                          *)
(* ------------------------------------------------------------------ *)

Lemma Q_h (a c : nat) (Ha : 2 * (a / 2) = a) : Q a c + 3 <= Q 1 (a / 2 + c + 2).
Proof. unfold Q. lia. Qed.

Lemma Q_i (a c : nat) (hac : a <= c) : Q a c + 3 <= Q (3 * a) (c - a + 4).
Proof. unfold Q. lia. Qed.

Lemma Q_j (a c : nat) (hac : a <= c) : Q a c + 3 <= Q (3 * a + 2) (c - a + 1).
Proof. unfold Q. lia. Qed.

Lemma Q_a (a c : nat) (hca : c < a) (Hc : 2 * (c / 2) = c) :
    Q a c + 3 <= Q (a - c - 1) (3 * (c / 2) + 2).
Proof. unfold Q. lia. Qed.

Lemma Q_b (a c : nat) (hca : c < a) (hac2 : c + 2 <= a)
    (Hc : 6 * ((c - 1) / 2) = 3 * (c - 1)) :
    Q a c + 3 <= Q (a - c - 2) (3 * ((c - 1) / 2) + 5).
Proof. unfold Q. lia. Qed.

Lemma Q_e (a c : nat) (hae : a = c + 2) : Q a c + 3 <= Q (3 * c + 8) 1.
Proof. unfold Q. lia. Qed.

Lemma Q_c (a c : nat) (hca : c < a) (hac4 : c + 4 <= a)
    (Hc : 6 * ((c - 1) / 2) = 3 * (c - 1)) :
    Q a c + 3 <= Q (a - c - 4) (3 * ((c - 1) / 2) + 8).
Proof. unfold Q. lia. Qed.

Theorem Q_step (a c a' c' : nat) (h : step a c = Next a' c') : Q a c + 3 <= Q a' c'.
Proof.
  destruct (Nat.leb a c) eqn:E1.
  - assert (hac : a <= c) by (apply leb_true_le; exact E1).
    destruct (Nat.eqb (Nat.modulo a 2) 0) eqn:E2.
    + destruct (Nat.eqb (Nat.modulo c 2) 0) eqn:E3.
      * rewrite (step_g a c E1 E2 E3) in h. discriminate h.
      * rewrite (step_h a c E1 E2 E3) in h.
        injection h as H1 H2. rewrite <- H1, <- H2.
        apply Nat.eqb_eq in E2.
        exact (Q_h a c (two_div a E2)).
    + destruct (Nat.eqb (Nat.modulo c 2) 0) eqn:E3.
      * rewrite (step_i a c E1 E2 E3) in h.
        injection h as H1 H2. rewrite <- H1, <- H2.
        exact (Q_i a c hac).
      * rewrite (step_j a c E1 E2 E3) in h.
        injection h as H1 H2. rewrite <- H1, <- H2.
        exact (Q_j a c hac).
  - assert (hca : c < a) by (apply leb_false_lt; exact E1).
    destruct (orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2)) eqn:E4.
    + rewrite (step_a a c E1 E4) in h.
      injection h as H1 H2. rewrite <- H1, <- H2.
      apply orb_true_iff in E4. destruct E4 as [E4 | E4]; apply Nat.eqb_eq in E4.
      * exact (Q_a a c hca (two_div c (mod2_of_mod4_even c (or_introl E4)))).
      * exact (Q_a a c hca (two_div c (mod2_of_mod4_even c (or_intror E4)))).
    + destruct (Nat.eqb (Nat.modulo c 4) 1) eqn:E5.
      * destruct (Nat.eqb a (c + 1)) eqn:E6.
        -- rewrite (step_f a c E1 E4 E5 E6) in h. discriminate h.
        -- rewrite (step_b a c E1 E4 E5 E6) in h.
           injection h as H1 H2. rewrite <- H1, <- H2.
           assert (hn1 : a <> c + 1) by (apply eqb_false_neq; exact E6).
           assert (hac2 : c + 2 <= a) by lia.
           apply Nat.eqb_eq in E5.
           exact (Q_b a c hca hac2 (six_div c (mod2_of_mod4_odd c E5))).
      * destruct (Nat.eqb a (c + 1)) eqn:E6.
        -- rewrite (step_halt1 a c E1 E4 E5 E6) in h. discriminate h.
        -- destruct (Nat.eqb a (c + 2)) eqn:E7.
           ++ rewrite (step_e a c E1 E4 E5 E6 E7) in h.
              injection h as H1 H2. rewrite <- H1, <- H2.
              apply Nat.eqb_eq in E7.
              exact (Q_e a c E7).
           ++ destruct (Nat.eqb a (c + 3)) eqn:E8.
              ** rewrite (step_halt3 a c E1 E4 E5 E6 E7 E8) in h. discriminate h.
              ** rewrite (step_c a c E1 E4 E5 E6 E7 E8) in h.
                 injection h as H1 H2. rewrite <- H1, <- H2.
                 apply orb_false_iff in E4. destruct E4 as [E4a E4b].
                 assert (hne0 : c mod 4 <> 0) by (apply eqb_false_neq; exact E4a).
                 assert (hne2 : c mod 4 <> 2) by (apply eqb_false_neq; exact E4b).
                 assert (hne1 : c mod 4 <> 1) by (apply eqb_false_neq; exact E5).
                 assert (hn1 : a <> c + 1) by (apply eqb_false_neq; exact E6).
                 assert (hn2 : a <> c + 2) by (apply eqb_false_neq; exact E7).
                 assert (hn3 : a <> c + 3) by (apply eqb_false_neq; exact E8).
                 assert (hac4 : c + 4 <= a) by lia.
                 assert (Hc : c mod 4 = 3) by (apply mod4_three; assumption).
                 exact (Q_c a c hca hac4 (six_div c (mod2_of_mod4_three c Hc))).
Qed.

Theorem run_Q (n : nat) : forall (a c a' c' : nat),
    run n (a, c) = Some (a', c') -> Q a c + 3 * n <= Q a' c'.
Proof.
  induction n as [|n ih]; intros a c a' c' h.
  - simpl in h. injection h as H1 H2. rewrite <- H1, <- H2. lia.
  - simpl in h.
    destruct (step a c) as [|a1 c1] eqn:hs.
    + discriminate h.
    + assert (h1 : Q a c + 3 <= Q a1 c1) by (apply Q_step; exact hs).
      assert (h2 : Q a1 c1 + 3 * n <= Q a' c') by (apply ih; exact h).
      lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 3. The L-phase budget                                          *)
(* ------------------------------------------------------------------ *)

(** The [L]-region drop: [a - c - r + c <= a] for every [r], since [c < a]
    (the subtraction saturates once [r >= a - c]). *)
Lemma L_drop (a c r : nat) (h : c < a) : a - c - r + c <= a.
Proof. lia. Qed.

(** Rule [a]'s growth, from [c] even. *)
Lemma L_grow_a (c : nat) (h : c mod 2 = 0) : 3 * c <= 2 * (3 * (c / 2) + 2).
Proof.
  assert (H : 2 * (c / 2) = c) by (apply two_div; exact h).
  lia.
Qed.

(** Rule [b]'s growth, from [c] odd. *)
Lemma L_grow_b (c : nat) (h : c mod 2 = 1) : 3 * c <= 2 * (3 * ((c - 1) / 2) + 5).
Proof.
  assert (H : 6 * ((c - 1) / 2) = 3 * (c - 1)) by (apply six_div; exact h).
  lia.
Qed.

(** Rule [c]'s growth, from [c] odd. *)
Lemma L_grow_c (c : nat) (h : c mod 2 = 1) : 3 * c <= 2 * (3 * ((c - 1) / 2) + 8).
Proof.
  assert (H : 6 * ((c - 1) / 2) = 3 * (c - 1)) by (apply six_div; exact h).
  lia.
Qed.

(** In the [L] region, a non-[e] step satisfies both phase inequalities.  As in
    the Lean module the case analysis only rewrites: each branch's two
    inequalities are [L_drop] and [L_grow_{a,b,c}], applied with the parity fact
    that branch's residue supplies.  No [lia] runs on a conjunction, and no
    [lia] sees a [mod] fact it has to derive. *)
Lemma L_step (a c a' c' : nat) (hca : c < a) (hne : a <> c + 2)
    (h : step a c = Next a' c') : a' + c <= a /\ 3 * c <= 2 * c'.
Proof.
  destruct (Nat.leb a c) eqn:E1.
  - exfalso. apply leb_true_le in E1. lia.
  - destruct (orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2)) eqn:E4.
    + rewrite (step_a a c E1 E4) in h.
      injection h as H1 H2. rewrite <- H1, <- H2. split.
      * apply L_drop. exact hca.
      * apply L_grow_a. apply mod2_of_mod4_even.
        apply orb_true_iff in E4. destruct E4 as [E4 | E4]; apply Nat.eqb_eq in E4.
        -- left. exact E4.
        -- right. exact E4.
    + destruct (Nat.eqb (Nat.modulo c 4) 1) eqn:E5.
      * destruct (Nat.eqb a (c + 1)) eqn:E6.
        -- rewrite (step_f a c E1 E4 E5 E6) in h. discriminate h.
        -- rewrite (step_b a c E1 E4 E5 E6) in h.
           injection h as H1 H2. rewrite <- H1, <- H2. split.
           ++ apply L_drop. exact hca.
           ++ apply L_grow_b. apply mod2_of_mod4_odd.
              apply Nat.eqb_eq in E5. exact E5.
      * destruct (Nat.eqb a (c + 1)) eqn:E6.
        -- rewrite (step_halt1 a c E1 E4 E5 E6) in h. discriminate h.
        -- destruct (Nat.eqb a (c + 2)) eqn:E7.
           ++ apply Nat.eqb_eq in E7. exfalso. apply hne. lia.
           ++ destruct (Nat.eqb a (c + 3)) eqn:E8.
              ** rewrite (step_halt3 a c E1 E4 E5 E6 E7 E8) in h. discriminate h.
              ** rewrite (step_c a c E1 E4 E5 E6 E7 E8) in h.
                 injection h as H1 H2. rewrite <- H1, <- H2. split.
                 --- apply L_drop. exact hca.
                 --- apply L_grow_c.
                     apply orb_false_iff in E4. destruct E4 as [E4a E4b].
                     apply eqb_false_neq in E4a. apply eqb_false_neq in E4b.
                     apply eqb_false_neq in E5.
                     apply mod2_of_mod4_three. apply mod4_three; assumption.
Qed.

(** Partial sum of the `c` values along a phase. *)
Fixpoint Ssum (C : nat -> nat) (n : nat) : nat :=
  match n with
  | O => 0
  | S k => Ssum C k + C k
  end.

Lemma pow_succ_nat (a n : nat) : a ^ S n = a * a ^ n.
Proof. reflexivity. Qed.

Lemma mul_succ_nat (n m : nat) : n * S m = n * m + n.
Proof. simpl. lia. Qed.

Lemma mul_pow3_succ (D n : nat) : D * 3 ^ (S n) = 3 * (D * 3 ^ n).
Proof. rewrite pow_succ_nat. nia. Qed.

Lemma mul_pow2_succ (D n : nat) : D * 2 ^ (S n) = 2 * (D * 2 ^ n).
Proof. rewrite pow_succ_nat. nia. Qed.

Lemma pow2_mul_two (n X : nat) : 2 ^ n * (2 * X) = 2 ^ (S n) * X.
Proof. rewrite pow_succ_nat. nia. Qed.

Lemma Ssum_le (A C : nat -> nat) (n : nat)
    (h : forall i, i < n -> A (S i) + C i <= A i) : A n + Ssum C n <= A 0.
Proof.
  induction n as [|n ih].
  - simpl. lia.
  - assert (h1 : forall i, i < n -> A (S i) + C i <= A i) by (intros; apply h; lia).
    assert (h2 := ih h1).
    assert (h3 : A (S n) + C n <= A n) by (apply h; lia).
    simpl. lia.
Qed.

Lemma Ssum_two_le (C : nat -> nat) (n : nat)
    (h : forall i, i < n -> 3 * C i <= 2 * C (S i)) :
    Ssum C n + 2 * C 0 <= 2 * C n.
Proof.
  induction n as [|n ih].
  - simpl. lia.
  - assert (h1 : forall i, i < n -> 3 * C i <= 2 * C (S i)) by (intros; apply h; lia).
    assert (h2 := ih h1).
    assert (h3 : 3 * C n <= 2 * C (S n)) by (apply h; lia).
    simpl. lia.
Qed.

Lemma L_budget (C : nat -> nat) (n : nat)
    (h : forall i, i < n -> 3 * C i <= 2 * C (S i)) :
    2 * C 0 * 3 ^ n <= 2 ^ n * (Ssum C n + 2 * C 0).
Proof.
  induction n as [|n ih].
  - simpl. lia.
  - assert (h1 : forall i, i < n -> 3 * C i <= 2 * C (S i)) by (intros; apply h; lia).
    assert (h2 := ih h1).
    assert (hT : Ssum C n + 2 * C 0 <= 2 * C n) by (apply Ssum_two_le; exact h1).
    assert (hTn : Ssum C (S n) + 2 * C 0 = Ssum C n + 2 * C 0 + C n) by (simpl; lia).
    assert (key : 3 * (Ssum C n + 2 * C 0) <= 2 * (Ssum C (S n) + 2 * C 0))
      by (rewrite hTn; lia).
    rewrite mul_pow3_succ.
    transitivity (3 * (2 ^ n * (Ssum C n + 2 * C 0))).
    + apply Nat.mul_le_mono_l. exact h2.
    + assert (Heq : 3 * (2 ^ n * (Ssum C n + 2 * C 0))
                     = 2 ^ n * (3 * (Ssum C n + 2 * C 0))) by nia.
      rewrite Heq.
      transitivity (2 ^ n * (2 * (Ssum C (S n) + 2 * C 0))).
      * apply Nat.mul_le_mono_l. exact key.
      * rewrite pow2_mul_two. apply Nat.le_refl.
Qed.

Lemma L_phase_budget (A C : nat -> nat) (n : nat)
    (hdrop : forall i, i < n -> A (S i) + C i <= A i)
    (hgrow : forall i, i < n -> 3 * C i <= 2 * C (S i)) :
    2 * C 0 * 3 ^ n <= 2 ^ n * (A 0 + 2 * C 0).
Proof.
  assert (h1 := L_budget C n hgrow).
  assert (h2 := Ssum_le A C n hdrop).
  assert (h3 : Ssum C n + 2 * C 0 <= A 0 + 2 * C 0) by lia.
  transitivity (2 ^ n * (Ssum C n + 2 * C 0)).
  - exact h1.
  - apply Nat.mul_le_mono_l. exact h3.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 4. The first L phase has length <= 878                          *)
(* ------------------------------------------------------------------ *)

Lemma pow2_le_pow3 (n : nat) : 2 ^ n <= 3 ^ n.
Proof.
  induction n as [|n ih]; simpl.
  - lia.
  - nia.
Qed.

Lemma pow3_mono (m n : nat) (h : m <= n) : 3 ^ m <= 3 ^ n.
Proof.
  induction h as [|n h ih].
  - apply Nat.le_refl.
  - rewrite pow_succ_nat. nia.
Qed.

Lemma pow_add_l (a n m : nat) : a ^ (n + m) = a ^ n * a ^ m.
Proof.
  induction m as [|m ih].
  - rewrite Nat.add_0_r, Nat.pow_0_r, Nat.mul_1_r. reflexivity.
  - rewrite Nat.add_succ_r, pow_succ_nat, ih, pow_succ_nat. nia.
Qed.

Lemma pow_mul_gen (a n m : nat) : a ^ (n * m) = (a ^ n) ^ m.
Proof.
  induction m as [|m ih].
  - rewrite Nat.mul_0_r, Nat.pow_0_r. reflexivity.
  - rewrite mul_succ_nat, pow_add_l, pow_succ_nat, ih. nia.
Qed.

(** `2^(3m) <= 3^(2m)`, from `9 > 8`. *)
Lemma nine_pow_ge (m : nat) : 2 ^ (3 * m) <= 3 ^ (2 * m).
Proof.
  rewrite (pow_mul_gen 2 3 m), (pow_mul_gen 3 2 m).
  change (8 ^ m <= 9 ^ m).
  induction m as [|m ih]; simpl.
  - lia.
  - nia.
Qed.

Lemma pow3_pos (n : nat) : 0 < 3 ^ n.
Proof. assert (H : 3 ^ 0 <= 3 ^ n) by (apply pow3_mono; lia). simpl in H. lia. Qed.

Lemma pow2_mono (m n : nat) (h : m <= n) : 2 ^ m <= 2 ^ n.
Proof.
  induction h as [|n h ih].
  - apply Nat.le_refl.
  - rewrite pow_succ_nat. nia.
Qed.

Lemma mul_lt_mono_r_gen (a b : nat) (h : a < b) :
    forall c, 0 < c -> a * c < b * c.
Proof.
  intro c. induction c as [|d ih]; intros hc.
  - lia.
  - destruct d as [|e].
    + simpl. lia.
    + rewrite mul_succ_nat, mul_succ_nat.
      assert (a * S e < b * S e) by (apply ih; lia). lia.
Qed.

Lemma le_of_mul_le_mul_r (a b c : nat) (hc : 0 < c) (h : a * c <= b * c) : a <= b.
Proof.
  destruct (Nat.lt_ge_cases b a) as [hlt | hge]; [| exact hge].
  exfalso.
  assert (b * c < a * c) by (apply mul_lt_mono_r_gen; assumption). lia.
Qed.

Lemma pow2_lt (m n : nat) (h : m < n) : 2 ^ m < 2 ^ n.
Proof.
  assert (hn : n = m + (n - m)) by lia.
  rewrite hn, pow_add_l.
  assert (h3 : 1 < 2 ^ (n - m)).
  { assert (h2 : 2 ^ 1 <= 2 ^ (n - m)) by (apply pow2_mono; lia). simpl in h2. lia. }
  assert (Hp : 0 < 2 ^ m).
  { assert (H : 2 ^ 0 <= 2 ^ m) by (apply pow2_mono; lia). simpl in H. lia. }
  assert (h4 : 2 ^ m * 1 < 2 ^ m * 2 ^ (n - m)).
  { exact (proj1 (Nat.mul_lt_mono_pos_l (2 ^ m) 1 (2 ^ (n - m)) Hp) h3). }
  rewrite Nat.mul_1_r in h4. exact h4.
Qed.

(** **The [L] charge at an arbitrary phase start.**  The post-[j] shape of
    [a0] is not used: any start with [1 <= c0] and [a0 <= 2*3^292] whose [L]
    phase obeys the closed budget has length at most [878].  This is the form
    the phase composition needs, because only the first phase of a residual
    run starts at the post-[j] state. *)
Lemma L_phase_le_878_gen (n a0 c0 : nat) (ha : a0 <= 2 * 3 ^ 292) (hc : 1 <= c0)
    (h : 2 * c0 * 3 ^ n <= 2 ^ n * (a0 + 2 * c0)) : n <= 878.
Proof.
  destruct (Nat.le_gt_cases n 878) as [hle | hgt]; [exact hle | exfalso].
  assert (hpow : 2 ^ n <= 3 ^ n) by apply pow2_le_pow3.
  assert (hsplit : 2 * c0 * (3 ^ n - 2 ^ n) + 2 * c0 * 2 ^ n = 2 * c0 * 3 ^ n).
  { assert (e : 3 ^ n - 2 ^ n + 2 ^ n = 3 ^ n) by (apply Nat.sub_add; exact hpow).
    nia. }
  assert (hrhs : 2 ^ n * ((a0) + 2 * c0)
      = 2 ^ n * (a0) + 2 * c0 * 2 ^ n) by nia.
  rewrite <- hsplit, hrhs in h.
  assert (hcut : 2 * c0 * (3 ^ n - 2 ^ n) <= 2 ^ n * (a0)) by lia.
  assert (hA : 2 * (3 ^ n - 2 ^ n) <= 2 * c0 * (3 ^ n - 2 ^ n)).
  { assert (h2 : 2 * 1 <= 2 * c0) by lia.
    assert (h3 := Nat.mul_le_mono_r (2 * 1) (2 * c0) (3 ^ n - 2 ^ n) h2). nia. }
  assert (hk' : a0 <= 2 * 3 ^ 292) by exact ha.
  assert (hB : 2 * (3 ^ n - 2 ^ n) <= 2 ^ n * (2 * 3 ^ 292)).
  { assert (h1 : 2 * (3 ^ n - 2 ^ n) <= 2 ^ n * (a0)).
    { exact (Nat.le_trans (2 * (3 ^ n - 2 ^ n)) (2 * c0 * (3 ^ n - 2 ^ n))
               (2 ^ n * (a0)) hA hcut). }
    assert (hmid : 2 ^ n * (a0) <= 2 ^ n * (2 * 3 ^ 292)).
    { apply Nat.mul_le_mono_l. exact hk'. }
    exact (Nat.le_trans (2 * (3 ^ n - 2 ^ n)) (2 ^ n * (a0))
             (2 ^ n * (2 * 3 ^ 292)) h1 hmid). }
  assert (hC : 3 ^ n - 2 ^ n <= 2 ^ n * 3 ^ 292).
  { assert (e : 2 ^ n * (2 * 3 ^ 292) = 2 * (2 ^ n * 3 ^ 292)) by nia.
    rewrite e in hB.
    assert (hB2 : (3 ^ n - 2 ^ n) * 2 <= (2 ^ n * 3 ^ 292) * 2) by nia.
    exact (le_of_mul_le_mul_r (3 ^ n - 2 ^ n) (2 ^ n * 3 ^ 292) 2 (ltac:(lia)) hB2). }
  assert (hD : 2 ^ n <= 2 ^ n * 3 ^ 292).
  { assert (H1 : 2 ^ n * 1 <= 2 ^ n * 3 ^ 292)
      by (apply Nat.mul_le_mono_l; pose proof (pow3_pos 292); lia).
    rewrite Nat.mul_1_r in H1. exact H1. }
  assert (hE : 3 ^ n <= 2 ^ n * 3 ^ 292 + 2 ^ n * 3 ^ 292) by lia.
  assert (hF : 3 ^ n <= 2 ^ (S n) * 3 ^ 292).
  { rewrite pow_succ_nat. nia. }
  remember (n - 292) as m eqn:Em.
  assert (hm : n = m + 292) by lia.
  rewrite hm in hF.
  assert (hm6 : 587 <= m) by lia.
  assert (hG : 3 ^ m <= 2 ^ (m + 293)).
  { assert (e : 3 ^ (m + 292) = 3 ^ m * 3 ^ 292) by (rewrite pow_add_l; reflexivity).
    rewrite e in hF.
    replace (S (m + 292)) with (m + 293) in hF by lia.
    exact (le_of_mul_le_mul_r (3 ^ m) (2 ^ (m + 293)) (3 ^ 292) (pow3_pos 292) hF). }
  assert (hH : 3 ^ (2 * m) <= 2 ^ (2 * (m + 292) + 2)).
  { assert (e1 : 3 ^ (2 * m) = 3 ^ m * 3 ^ m).
    { assert (e : 2 * m = m + m) by lia. rewrite e. rewrite pow_add_l. reflexivity. }
    assert (e2 : 2 ^ (2 * (m + 292) + 2) = 2 ^ (m + 293) * 2 ^ (m + 293)).
    { replace (2 * (m + 292) + 2) with ((m + 293) + (m + 293)) by lia.
      rewrite pow_add_l. reflexivity. }
    rewrite e1, e2. apply Nat.mul_le_mono; exact hG. }
  assert (hI : 2 ^ (3 * m) <= 2 ^ (2 * (m + 292) + 2)).
  { exact (Nat.le_trans (2 ^ (3 * m)) (3 ^ (2 * m)) (2 ^ (2 * (m + 292) + 2))
             (nine_pow_ge m) hH). }
  assert (hJ : 3 * m <= 2 * (m + 292) + 2).
  { destruct (Nat.lt_ge_cases (2 * (m + 292) + 2) (3 * m)) as [hlt | hge]; [| exact hge].
    exfalso.
    assert (Hlt : 2 ^ (2 * (m + 292) + 2) < 2 ^ (3 * m)) by (apply pow2_lt; exact hlt).
    lia. }
  lia.
Qed.

(** A post-[j] [L] phase with [k <= 292] has length <= 878.
    Coarse version of the Lean [L_phase_le_791], using only [9 > 8]. *)
Lemma L_phase_le_878 (k n c0 : nat) (hk : k <= 292) (hc : 1 <= c0)
    (h : 2 * c0 * 3 ^ n <= 2 ^ n * ((2 * 3 ^ k - 1) + 2 * c0)) : n <= 878.
Proof.
  apply (L_phase_le_878_gen n (2 * 3 ^ k - 1) c0).
  - assert (hp : 3 ^ k <= 3 ^ 292) by (apply pow3_mono; exact hk). lia.
  - exact hc.
  - exact h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 4b. The sharp first-phase constant 791 (pairs with Lean)          *)
(* ------------------------------------------------------------------ *)

(** The base comparison [2^792 * (3^292 + 1) < 3^792], computed in binary [Z].
    [Z.pow] takes a [Z] exponent, and a single [rewrite] only fires on one
    instantiation, so the bridge below applies [Nat2Z.inj_pow] once per power;
    otherwise the remaining [Nat.pow] occurrences survive and [vm_compute] would
    try to build them unary. *)
Lemma baseZ : (Z.of_nat 2 ^ Z.of_nat 792
   * (Z.of_nat 3 ^ Z.of_nat 292 + Z.of_nat 1)
   < Z.of_nat 3 ^ Z.of_nat 792)%Z.
Proof. vm_compute. reflexivity. Qed.

(** [2^n * (3^292 + 1) < 3^n] for every [n >= 792], proved at the [Z] level:
    the corresponding induction in [nat] overflows the checker on these
    exponents, while [Z]'s [Z.pow_succ_r] handles the step directly.
    (Lean: [three_pow_gt].) *)
Lemma three_pow_gt_Z : forall n : nat, 792 <= n ->
    (2 ^ Z.of_nat n * (3 ^ Z.of_nat 292 + 1) < 3 ^ Z.of_nat n)%Z.
Proof.
  intros n. induction n as [|n ih].
  - intros hn. lia.
  - intros hn.
    destruct (Nat.lt_ge_cases n 792) as [hlt | hge].
    + assert (h792 : S n = 792) by lia.
      rewrite h792. exact baseZ.
    + assert (ih' : (2 ^ Z.of_nat n * (3 ^ Z.of_nat 292 + 1) < 3 ^ Z.of_nat n)%Z)
        by (apply ih; exact hge).
      assert (hk : (Z.of_nat (S n) = Z.succ (Z.of_nat n))%Z)
        by (rewrite Nat2Z.inj_succ; reflexivity).
      rewrite hk.
      rewrite Z.pow_succ_r.
      rewrite Z.pow_succ_r.
      assert (hp : (0 <= 3 ^ Z.of_nat n)%Z) by (apply Z.pow_nonneg; lia).
      replace ((2 ^ Z.of_nat n * 2) * (3 ^ Z.of_nat 292 + 1))%Z
        with ((2 ^ Z.of_nat n * (3 ^ Z.of_nat 292 + 1)) * 2)%Z by ring.
      all: lia.
Qed.

(** [2^n * (3^292 + 1) < 3^n] for every [n >= 792] (Lean: [three_pow_gt]). *)
Lemma three_pow_gt (n : nat) (hn : 792 <= n) :
    2 ^ n * (3 ^ 292 + 1) < 3 ^ n.
Proof.
  assert (H := three_pow_gt_Z n hn).
  apply (proj2 (Nat2Z.inj_lt _ _)).
  rewrite Nat2Z.inj_mul.
  rewrite Nat2Z.inj_add.
  rewrite Nat2Z.inj_pow.
  rewrite Nat2Z.inj_pow.
  rewrite Nat2Z.inj_pow.
  exact H.
Qed.

(** The first [L] phase of a post-[j] chain with [k <= 292] has length
<= 791.  Same constant as the Lean [L_phase_le_791]. *)
Lemma L_phase_le_791 (k n c0 : nat) (hk : k <= 292) (hc : 1 <= c0)
    (h : 2 * c0 * 3 ^ n <= 2 ^ n * ((2 * 3 ^ k - 1) + 2 * c0)) : n <= 791.
Proof.
  destruct (Nat.le_gt_cases n 791) as [hle | hgt]; [exact hle | exfalso].
  assert (hn : 792 <= n) by lia.
  assert (hpow : 2 ^ n <= 3 ^ n) by apply pow2_le_pow3.
  assert (hsplit : 2 * c0 * (3 ^ n - 2 ^ n) + 2 * c0 * 2 ^ n = 2 * c0 * 3 ^ n).
  { assert (e : 3 ^ n - 2 ^ n + 2 ^ n = 3 ^ n) by (apply Nat.sub_add; exact hpow).
    nia. }
  assert (hrhs : 2 ^ n * ((2 * 3 ^ k - 1) + 2 * c0)
      = 2 ^ n * (2 * 3 ^ k - 1) + 2 * c0 * 2 ^ n) by nia.
  rewrite <- hsplit, hrhs in h.
  assert (hcut : 2 * c0 * (3 ^ n - 2 ^ n) <= 2 ^ n * (2 * 3 ^ k - 1)) by lia.
  assert (hA : 2 * (3 ^ n - 2 ^ n) <= 2 * c0 * (3 ^ n - 2 ^ n)).
  { assert (h2 : 2 * 1 <= 2 * c0) by lia.
    assert (h3 := Nat.mul_le_mono_r (2 * 1) (2 * c0) (3 ^ n - 2 ^ n) h2). nia. }
  assert (hk' : 2 * 3 ^ k - 1 <= 2 * 3 ^ 292).
  { assert (hp : 3 ^ k <= 3 ^ 292) by (apply pow3_mono; exact hk). lia. }
  assert (hB : 2 * (3 ^ n - 2 ^ n) <= 2 ^ n * (2 * 3 ^ 292)).
  { assert (h1 : 2 * (3 ^ n - 2 ^ n) <= 2 ^ n * (2 * 3 ^ k - 1)).
    { exact (Nat.le_trans (2 * (3 ^ n - 2 ^ n)) (2 * c0 * (3 ^ n - 2 ^ n))
               (2 ^ n * (2 * 3 ^ k - 1)) hA hcut). }
    assert (hmid : 2 ^ n * (2 * 3 ^ k - 1) <= 2 ^ n * (2 * 3 ^ 292)).
    { apply Nat.mul_le_mono_l. exact hk'. }
    exact (Nat.le_trans (2 * (3 ^ n - 2 ^ n)) (2 ^ n * (2 * 3 ^ k - 1))
             (2 ^ n * (2 * 3 ^ 292)) h1 hmid). }
  assert (hC : 3 ^ n - 2 ^ n <= 2 ^ n * 3 ^ 292).
  { assert (e : 2 ^ n * (2 * 3 ^ 292) = 2 * (2 ^ n * 3 ^ 292)) by nia.
    rewrite e in hB.
    assert (hB2 : (3 ^ n - 2 ^ n) * 2 <= (2 ^ n * 3 ^ 292) * 2) by nia.
    exact (le_of_mul_le_mul_r (3 ^ n - 2 ^ n) (2 ^ n * 3 ^ 292) 2 (ltac:(lia)) hB2). }
  assert (hfin : 3 ^ n <= 2 ^ n * (3 ^ 292 + 1)).
  { assert (e : 3 ^ n = (3 ^ n - 2 ^ n) + 2 ^ n) by nia.
    rewrite e. nia. }
  assert (Hcontra := three_pow_gt n hn).
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 5. The j-phase budget                                          *)
(* ------------------------------------------------------------------ *)

Lemma J_a_closed (A : nat -> nat) (m : nat)
    (hstep : forall i, i < m -> A (S i) = 3 * A i + 2) :
    forall i, i <= m -> A i + 1 = 3 ^ i * (A 0 + 1).
Proof.
  intros i hi. induction i as [|i ih].
  - simpl. lia.
  - assert (h1 : A (S i) = 3 * A i + 2) by (apply hstep; lia).
    assert (h2 : A i + 1 = 3 ^ i * (A 0 + 1)) by (apply ih; lia).
    rewrite h1, pow_succ_nat. nia.
Qed.

Lemma J_Q_closed (A C : nat -> nat) (m : nat)
    (hstep : forall i, i < m -> A (S i) = 3 * A i + 2 /\ C (S i) = C i - A i + 1)
    (hreg : forall i, i < m -> A i <= C i) :
    forall i, i <= m -> A i + 2 * C i = A 0 + 2 * C 0 + 4 * i.
Proof.
  intros i hi. induction i as [|i ih].
  - lia.
  - assert (h1 : A (S i) = 3 * A i + 2 /\ C (S i) = C i - A i + 1)
      by (apply hstep; lia).
    assert (h2 : A i + 2 * C i = A 0 + 2 * C 0 + 4 * i) by (apply ih; lia).
    assert (h3 : A i <= C i) by (apply hreg; lia).
    destruct h1 as [e1 e2]. rewrite e1, e2. lia.
Qed.

Lemma J_phase_budget (A C : nat -> nat) (m : nat) (hm : 1 <= m)
    (hstep : forall i, i < m -> A (S i) = 3 * A i + 2 /\ C (S i) = C i - A i + 1)
    (hreg : forall i, i < m -> A i <= C i) :
    3 ^ m * (A 0 + 1) <= A 0 + 2 * C 0 + 4 * m.
Proof.
  destruct m as [|k]; [lia |].
  assert (hA : A k + 1 = 3 ^ k * (A 0 + 1)).
  { apply (J_a_closed A (S k)); [intros i hi; exact (proj1 (hstep i hi)) | lia]. }
  assert (hQ : A k + 2 * C k = A 0 + 2 * C 0 + 4 * k).
  { apply (J_Q_closed A C (S k)); [exact hstep | exact hreg | lia]. }
  assert (hle : A k <= C k) by (apply hreg; lia).
  rewrite pow_succ_nat. nia.
Qed.

(** `2*(6*3^292 + 4*j) < 2*3^j` for every `j >= 294`. *)
Lemma three_pow_dominates : forall j, 294 <= j -> 2 * (6 * 3 ^ 292 + 4 * j) < 2 * 3 ^ j.
Proof.
  intro j. induction j as [|j ih]; intros hj.
  - lia.
  - destruct (Nat.le_gt_cases 294 j) as [hle | hlt].
    + assert (ih' := ih hle).
      assert (Hone : 1 <= 3 ^ j).
      { assert (H := pow3_mono 0 j (ltac:(lia))). simpl in H. exact H. }
      assert (He : 3 ^ S j = 3 ^ j + 3 ^ j + 3 ^ j) by (rewrite pow_succ_nat; lia).
      rewrite He. lia.
    + assert (hj293 : j = 293) by lia. subst j.
      assert (HX : 392 < 3 ^ 292).
      { assert (H7 : 3 ^ 7 = 2187) by reflexivity.
        assert (Hm : 3 ^ 7 <= 3 ^ 292) by (apply pow3_mono; lia). lia. }
      assert (Hp : 3 ^ 294 = 3 ^ 292 * 9).
      { assert (e : 294 = 292 + 2) by lia. rewrite e. rewrite pow_add_l. reflexivity. }
      rewrite Hp. lia.
Qed.

(** A `j` run from the post-`j` family has length at most `293`. *)
Lemma J_phase_le_293 (m a0 c0 : nat) (hm : 1 <= m) (ha : 1 <= a0)
    (hQ : a0 + 2 * c0 <= 6 * 3 ^ 292)
    (h : 3 ^ m * (a0 + 1) <= a0 + 2 * c0 + 4 * m) : m <= 293.
Proof.
  destruct (Nat.le_gt_cases m 293) as [hle | hgt]; [exact hle | exfalso].
  assert (hm2 : 294 <= m) by lia.
  assert (hdom := three_pow_dominates m hm2).
  assert (hQq : 2 * (a0 + 2 * c0 + 4 * m) <= 2 * (6 * 3 ^ 292 + 4 * m)) by lia.
  assert (hlow : 2 * 3 ^ m <= 2 * (3 ^ m * (a0 + 1))).
  { assert (h1 : 2 * 3 ^ m * 1 <= 2 * 3 ^ m * (a0 + 1))
      by (apply Nat.mul_le_mono_l; lia).
    rewrite Nat.mul_1_r in h1.
    assert (h3 : 2 * 3 ^ m * (a0 + 1) = 2 * (3 ^ m * (a0 + 1))) by nia.
    rewrite h3 in h1. exact h1. }
  assert (h2 : 2 * (3 ^ m * (a0 + 1)) <= 2 * (a0 + 2 * c0 + 4 * m))
    by (apply Nat.mul_le_mono_l; exact h).
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 6. The budget route (superseded, kept for provenance)           *)
(**     [HBudget] is *not* the target: by [hbudget_of_length] it needs
        [T <= 3333], strictly stronger than [T <= 10000].  The direct target
        is [HalvingTimeBound] in section 7. *)
(* ------------------------------------------------------------------ *)

(** `Budget B`: no post-`j` chain ever pushes `Q` more than `B` above its start. *)
Definition Budget (B : nat) : Prop :=
  forall (k c n a' c' : nat), k <= 292 -> 1 <= c -> c < 2 * 3 ^ k ->
    run n (2 * 3 ^ k - 1, c) = Some (a', c') ->
    Q a' c' <= Q (2 * 3 ^ k - 1) c + B.

(** The `Q` budget is a halving-time budget. *)
Theorem survives_le_of_budget (B : nat) (hB : Budget B)
    (k c n a' c' : nat) (hk : k <= 292) (hc : 1 <= c) (hclt : c < 2 * 3 ^ k)
    (h : run n (2 * 3 ^ k - 1, c) = Some (a', c')) : 3 * n <= B.
Proof.
  assert (h1 : Q (2 * 3 ^ k - 1) c + 3 * n <= Q a' c') by (apply run_Q; exact h).
  unfold Budget in hB.
  assert (h2 : Q a' c' <= Q (2 * 3 ^ k - 1) c + B)
    by (exact (hB k c n a' c' hk hc hclt h)).
  lia.
Qed.

(** Conditional universal halving-time bound: if the residual `Q` budget `30000`
holds, no post-`j` chain with `k <= 292` survives `10000` steps. *)
Lemma budget30000_eq : 30000 = 3 * 10000.
Proof. vm_compute. reflexivity. Qed.

Theorem postJ_survives_le_10000 (h : Budget 30000)
    (k c n : nat) (hk : k <= 292) (hc : 1 <= c) (hclt : c < 2 * 3 ^ k)
    (hs : Survives n (2 * 3 ^ k - 1) c) : n <= 10000.
Proof.
  destruct hs as [a' [c' hr]].
  assert (h1 := survives_le_of_budget 30000 h k c n a' c' hk hc hclt hr).
  rewrite budget30000_eq in h1.
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 6b. The halving run: the correctly posed budget                *)
(* ------------------------------------------------------------------ *)

(** [run] stops only on a true halt, which never happens from the post-[j]
    family, so [Budget] above is false (see [BB33_758_BudgetRefuted.v]).
    [hrun] is [run] with the stopping rule of [BB33_758_Halving844]: stop on
    [Halt], on [a' = 1], or on [2*c' <= c0].  The halving time of [(a,c)] is
    the least [n] with [hrun c0 n a c = None]. *)
Fixpoint hrun (c0 n a c : nat) {struct n} : option (nat * nat) :=
  match n with
  | O => Some (a, c)
  | S n' =>
      match step a c with
      | Halt => None
      | Next a' c' =>
          if orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0) then None
          else hrun c0 n' a' c'
      end
  end.

(** [HSurvives c0 n a c]: the halving time of [(a,c)] exceeds [n]. *)
Definition HSurvives (c0 n a c : nat) : Prop :=
  exists a' c' : nat, hrun c0 n a c = Some (a', c').

(** One-step unfolding of [hrun] (its [Fixpoint] equation, used for rewriting). *)
Lemma hrun_S (c0 n a c : nat) :
    hrun c0 (S n) a c =
    match step a c with
    | Halt => None
    | Next a' c' =>
        if orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0) then None
        else hrun c0 n a' c'
    end.
Proof. reflexivity. Qed.

(** Every step of a surviving halving run is a genuine non-halting [step], so
    [Q] still grows by at least [3] per step. *)
Theorem hrun_Q (c0 n : nat) : forall (a c a' c' : nat),
    hrun c0 n a c = Some (a', c') -> Q a c + 3 * n <= Q a' c'.
Proof.
  induction n as [|n ih]; intros a c a' c' h.
  - simpl in h. injection h as H1 H2. rewrite <- H1, <- H2. lia.
  - rewrite hrun_S in h.
    remember (step a c) as s eqn:hs.
    destruct s as [|a1 c1].
    + discriminate h.
    + remember (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) as e eqn:E.
      destruct e.
      * discriminate h.
      * assert (h1 : Q a c + 3 <= Q a1 c1) by (apply Q_step; symmetry; exact hs).
        assert (h2 : Q a1 c1 + 3 * n <= Q a' c') by (apply ih; exact h).
        lia.
Qed.

(** Phase decomposition: a halving run of [m + n] steps splits at any
    intermediate surviving state.  This is the law that lets a pointwise
    argument chain per-phase bounds. *)
Theorem hrun_add (c0 : nat) : forall (m n a c a1 c1 : nat),
    hrun c0 m a c = Some (a1, c1) -> hrun c0 (m + n) a c = hrun c0 n a1 c1.
Proof.
  intros m. induction m as [|m ih]; intros n a c a1 c1 h.
  - simpl in h. injection h as H1 H2. rewrite <- H1, <- H2. simpl. reflexivity.
  - rewrite hrun_S in h.
    destruct (step a c) as [|a2 c2] eqn:hs.
    + discriminate h.
    + destruct (orb (Nat.eqb a2 1) (Nat.leb (2 * c2) c0)) eqn:E.
      * discriminate h.
      * assert (key : hrun c0 (m + n) a2 c2 = hrun c0 n a1 c1)
          by (apply ih; exact h).
        assert (He : S m + n = S (m + n)) by lia. rewrite He.
        assert (HL : hrun c0 (S (m + n)) a c = hrun c0 (m + n) a2 c2)
          by (rewrite hrun_S, hs, E; reflexivity).
        rewrite HL. exact key.
Qed.

(** [HBudget B]: on the halving run, [Q] never rises more than [B] above its
    start.  This is [Budget] restated over [hrun], hence well posed. *)
Definition HBudget (B : nat) : Prop :=
  forall (k c n a' c' : nat), k <= 292 -> 1 <= c -> c < 2 * 3 ^ k ->
    hrun c n (2 * 3 ^ k - 1) c = Some (a', c') ->
    Q a' c' <= Q (2 * 3 ^ k - 1) c + B.

(** [HBudget B] bounds the halving time by [B/3]. *)
Theorem hsurvives_le_of_budget (B : nat) (hB : HBudget B)
    (k c n a' c' : nat) (hk : k <= 292) (hc : 1 <= c) (hclt : c < 2 * 3 ^ k)
    (h : hrun c n (2 * 3 ^ k - 1) c = Some (a', c')) : 3 * n <= B.
Proof.
  assert (h1 : Q (2 * 3 ^ k - 1) c + 3 * n <= Q a' c') by (apply (hrun_Q c n); exact h).
  unfold HBudget in hB.
  assert (h2 : Q a' c' <= Q (2 * 3 ^ k - 1) c + B)
    by (exact (hB k c n a' c' hk hc hclt h)).
  lia.
Qed.

(** Conditional universal halving-time bound, correctly posed: if [HBudget
    30000] holds on the halving run, no post-[j] chain with [k <= 292] has
    halving time above [10000]. *)
Theorem postJ_halving_le_10000 (h : HBudget 30000)
    (k c n : nat) (hk : k <= 292) (hc : 1 <= c) (hclt : c < 2 * 3 ^ k)
    (hs : HSurvives c n (2 * 3 ^ k - 1) c) : n <= 10000.
Proof.
  destruct hs as [a' [c' hr]].
  assert (h1 := hsurvives_le_of_budget 30000 h k c n a' c' hk hc hclt hr).
  rewrite budget30000_eq in h1.
  lia.
Qed.

(** ** 6c. The budget is a length bound

    [Q] rises by at least [3] and at most [9] per step, so on any run
    [3*T <= Q_end - Q_0 <= 9*T].  Hence [HBudget 30000] is implied by
    [T <= 3333] and implies [T <= 10000]: the budget form is a target strictly
    between the two. *)

Lemma Q_h_le (a c : nat) (Ha : 2 * (a / 2) = a) : Q 1 (a / 2 + c + 2) <= Q a c + 9.
Proof. unfold Q. lia. Qed.

Lemma Q_i_le (a c : nat) (hac : a <= c) : Q (3 * a) (c - a + 4) <= Q a c + 9.
Proof. unfold Q. lia. Qed.

Lemma Q_j_le (a c : nat) (hac : a <= c) : Q (3 * a + 2) (c - a + 1) <= Q a c + 9.
Proof. unfold Q. lia. Qed.

Lemma Q_a_le (a c : nat) (hca : c < a) (Hc : 2 * (c / 2) = c) :
    Q (a - c - 1) (3 * (c / 2) + 2) <= Q a c + 9.
Proof. unfold Q. lia. Qed.

Lemma Q_b_le (a c : nat) (hca : c < a) (hac2 : c + 2 <= a)
    (Hc : 6 * ((c - 1) / 2) = 3 * (c - 1)) :
    Q (a - c - 2) (3 * ((c - 1) / 2) + 5) <= Q a c + 9.
Proof. unfold Q. lia. Qed.

Lemma Q_e_le (a c : nat) (hae : a = c + 2) : Q (3 * c + 8) 1 <= Q a c + 9.
Proof. unfold Q. lia. Qed.

Lemma mod4_three_ge (c : nat) (h : c mod 4 = 3) : 3 <= c.
Proof. pose proof (Nat.div_mod_eq c 4). lia. Qed.

Lemma Q_c_le (a c : nat) (hca : c < a) (hac4 : c + 4 <= a) (hc3 : 3 <= c)
    (Hc : 6 * ((c - 1) / 2) = 3 * (c - 1)) :
    Q (a - c - 4) (3 * ((c - 1) / 2) + 8) <= Q a c + 9.
Proof. unfold Q. lia. Qed.

(** Every non-halting step raises [Q] by at most [9]. *)
Theorem Q_step_le (a c a' c' : nat) (h : step a c = Next a' c') : Q a' c' <= Q a c + 9.
Proof.
  destruct (Nat.leb a c) eqn:E1.
  - assert (hac : a <= c) by (apply leb_true_le; exact E1).
    destruct (Nat.eqb (Nat.modulo a 2) 0) eqn:E2.
    + destruct (Nat.eqb (Nat.modulo c 2) 0) eqn:E3.
      * rewrite (step_g a c E1 E2 E3) in h. discriminate h.
      * rewrite (step_h a c E1 E2 E3) in h.
        injection h as H1 H2. rewrite <- H1, <- H2.
        apply Nat.eqb_eq in E2.
        exact (Q_h_le a c (two_div a E2)).
    + destruct (Nat.eqb (Nat.modulo c 2) 0) eqn:E3.
      * rewrite (step_i a c E1 E2 E3) in h.
        injection h as H1 H2. rewrite <- H1, <- H2.
        exact (Q_i_le a c hac).
      * rewrite (step_j a c E1 E2 E3) in h.
        injection h as H1 H2. rewrite <- H1, <- H2.
        exact (Q_j_le a c hac).
  - assert (hca : c < a) by (apply leb_false_lt; exact E1).
    destruct (orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2)) eqn:E4.
    + rewrite (step_a a c E1 E4) in h.
      injection h as H1 H2. rewrite <- H1, <- H2.
      apply orb_true_iff in E4. destruct E4 as [E4 | E4]; apply Nat.eqb_eq in E4.
      * exact (Q_a_le a c hca (two_div c (mod2_of_mod4_even c (or_introl E4)))).
      * exact (Q_a_le a c hca (two_div c (mod2_of_mod4_even c (or_intror E4)))).
    + destruct (Nat.eqb (Nat.modulo c 4) 1) eqn:E5.
      * destruct (Nat.eqb a (c + 1)) eqn:E6.
        -- rewrite (step_f a c E1 E4 E5 E6) in h. discriminate h.
        -- rewrite (step_b a c E1 E4 E5 E6) in h.
           injection h as H1 H2. rewrite <- H1, <- H2.
           assert (hn1 : a <> c + 1) by (apply eqb_false_neq; exact E6).
           assert (hac2 : c + 2 <= a) by lia.
           apply Nat.eqb_eq in E5.
           exact (Q_b_le a c hca hac2 (six_div c (mod2_of_mod4_odd c E5))).
      * destruct (Nat.eqb a (c + 1)) eqn:E6.
        -- rewrite (step_halt1 a c E1 E4 E5 E6) in h. discriminate h.
        -- destruct (Nat.eqb a (c + 2)) eqn:E7.
           ++ rewrite (step_e a c E1 E4 E5 E6 E7) in h.
              injection h as H1 H2. rewrite <- H1, <- H2.
              apply Nat.eqb_eq in E7.
              exact (Q_e_le a c E7).
           ++ destruct (Nat.eqb a (c + 3)) eqn:E8.
              ** rewrite (step_halt3 a c E1 E4 E5 E6 E7 E8) in h. discriminate h.
              ** rewrite (step_c a c E1 E4 E5 E6 E7 E8) in h.
                 injection h as H1 H2. rewrite <- H1, <- H2.
                 apply orb_false_iff in E4. destruct E4 as [E4a E4b].
                 assert (hne0 : c mod 4 <> 0) by (apply eqb_false_neq; exact E4a).
                 assert (hne2 : c mod 4 <> 2) by (apply eqb_false_neq; exact E4b).
                 assert (hne1 : c mod 4 <> 1) by (apply eqb_false_neq; exact E5).
                 assert (hn1 : a <> c + 1) by (apply eqb_false_neq; exact E6).
                 assert (hn2 : a <> c + 2) by (apply eqb_false_neq; exact E7).
                 assert (hn3 : a <> c + 3) by (apply eqb_false_neq; exact E8).
                 assert (hac4 : c + 4 <= a) by lia.
                 assert (Hc : c mod 4 = 3) by (apply mod4_three; assumption).
                 exact (Q_c_le a c hca hac4 (mod4_three_ge c Hc)
                          (six_div c (mod2_of_mod4_three c Hc))).
Qed.

(** [n] surviving halving steps raise [Q] by at most [9*n]. *)
Theorem hrun_Q_le (c0 n : nat) : forall (a c a' c' : nat),
    hrun c0 n a c = Some (a', c') -> Q a' c' <= Q a c + 9 * n.
Proof.
  induction n as [|n ih]; intros a c a' c' h.
  - simpl in h. injection h as H1 H2. rewrite <- H1, <- H2. lia.
  - rewrite hrun_S in h.
    destruct (step a c) as [|a1 c1] eqn:hs.
    + discriminate h.
    + destruct (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) eqn:E.
      * discriminate h.
      * assert (h1 : Q a1 c1 <= Q a c + 9) by (apply Q_step_le; exact hs).
        assert (h2 : Q a' c' <= Q a1 c1 + 9 * n) by (apply ih; exact h).
        lia.
Qed.

(** [HBudget] is monotone in the budget. *)
Theorem HBudget_mono (B B' : nat) (hBB : B <= B') (hB : HBudget B) : HBudget B'.
Proof.
  unfold HBudget in *.
  intros k c n a' c' hk hc hclt hr.
  assert (h2 : Q a' c' <= Q (2 * 3 ^ k - 1) c + B)
    by (exact (hB k c n a' c' hk hc hclt hr)).
  lia.
Qed.

(** A length bound gives a budget: if every post-[j] chain has halving time at
    most [B], then [Q] grows by at most [9*B] on the halving run. *)
Theorem hbudget_of_length (B : nat)
    (h : forall (k c n : nat), k <= 292 -> 1 <= c -> c < 2 * 3 ^ k ->
      HSurvives c n (2 * 3 ^ k - 1) c -> n <= B) : HBudget (9 * B).
Proof.
  unfold HBudget.
  intros k c n a' c' hk hc hclt hr.
  assert (h1 : Q a' c' <= Q (2 * 3 ^ k - 1) c + 9 * n)
    by (apply (hrun_Q_le c n); exact hr).
  assert (h2 : n <= B)
    by (apply (h k c n); [exact hk | exact hc | exact hclt | exists a', c'; exact hr]).
  assert (h3 : 9 * n <= 9 * B) by lia.
  lia.
Qed.

(** [HBudget 30000] follows from the stronger length bound [T <= 3333]. *)
Theorem hbudget_30000_of_le_3333
    (h : forall (k c n : nat), k <= 292 -> 1 <= c -> c < 2 * 3 ^ k ->
      HSurvives c n (2 * 3 ^ k - 1) c -> n <= 3333) : HBudget 30000.
Proof.
  assert (hB : HBudget (9 * 3333)) by (apply hbudget_of_length; exact h).
  assert (Hle : 9 * 3333 <= 30000) by (cbn; lia).
  exact (HBudget_mono (9 * 3333) 30000 Hle hB).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Non-vacuity: the halving rule really fires

    [(5,1)] is the smallest post-[j] state ([k = 1]).  Its halving run takes
    exactly two steps and stops at [(1,9)] because [a' = 1], so both
    [HSurvives 1 1 5 1] and [~ HSurvives 1 2 5 1] hold.  [HSurvives], unlike
    [Survives], is a real constraint. *)
Theorem hsurvives_5_1 : HSurvives 1 1 5 1.
Proof. exists 2, 5. vm_compute. reflexivity. Qed.

Theorem hrun_stops_5_1 : hrun 1 2 5 1 = None.
Proof. vm_compute. reflexivity. Qed.

Theorem not_hsurvives_5_1 : ~ HSurvives 1 2 5 1.
Proof.
  intros [a' [c' h']]. vm_compute in h'. discriminate h'.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 7. The target, stated directly over the halving time

    [HBudget] is *not* the goal: [hbudget_of_length] shows that [HBudget 30000]
    needs the strictly stronger bound [T <= 3333].  The obligation is
    [HalvingTimeBound].  [hrun_add] splits the halving run at the first [L/J]
    boundary (the first state with [a <= c], i.e. the end of the first [L]
    phase), leaving exactly one named sub-goal, [ResidualHalving]. *)

(** [HalvingTimeLe B]: every post-[j] chain has halving time at most [B]. *)
Definition HalvingTimeLe (B : nat) : Prop :=
  forall (k c n : nat), k <= 292 -> 1 <= c -> c < 2 * 3 ^ k ->
    HSurvives c n (2 * 3 ^ k - 1) c -> n <= B.

(** The target: the unconditional halving-time bound [T <= 10000]. *)
Definition HalvingTimeBound : Prop := HalvingTimeLe 10000.

(** Prefix monotonicity: surviving [m + n] steps survives [m]. *)
Lemma hsurvives_mono (c0 : nat) : forall (m n a c : nat),
    HSurvives c0 (m + n) a c -> HSurvives c0 m a c.
Proof.
  intros m. induction m as [|m ih]; intros n a c h.
  - exists a, c. reflexivity.
  - destruct h as [x [y hx]].
    assert (He : S m + n = S (m + n)) by lia.
    rewrite He in hx.
    rewrite hrun_S in hx.
    remember (step a c) as s eqn:hs.
    destruct s as [|a1 c1].
    + discriminate hx.
    + remember (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) as e eqn:E.
      destruct e.
      * discriminate hx.
      * assert (hrec : HSurvives c0 (m + n) a1 c1) by (exists x, y; exact hx).
        destruct (ih n a1 c1 hrec) as [x2 [y2 hx2]].
        exists x2, y2.
        rewrite hrun_S.
        rewrite <- hs.
        rewrite <- E.
        exact hx2.
Qed.

(** The single residual obligation: **only the residual halving time**.
    There is no crossing assumption: [m] may be any split point reached within
    [791] steps.  An earlier version required the split point to lie in the [J]
    region ([a1 <= c1]); that is *false* -- at [k = 1, c = 3] the run ends at
    [(17,1)] after one rule-[e] step, because the halving rule fires on
    [2*c' <= c0] inside the [L] region. *)
Definition ResidualHalving : Prop :=
  forall (k c m a1 c1 t : nat), k <= 292 -> 1 <= c -> c < 2 * 3 ^ k ->
    hrun c m (2 * 3 ^ k - 1) c = Some (a1, c1) -> m <= 791 ->
    HSurvives c t a1 c1 -> m + t <= 10000.

(** [T <= 10000] from the residual alone.  The split is taken at [791] steps --
    the first-phase bound of [L_phase_le_791] -- so the first phase plus any
    residual is covered without the run having to cross into [J] at all.
    [hrun_add] performs the split, [hsurvives_mono] supplies the prefix. *)
Theorem halvingTimeBound_of_residual (h : ResidualHalving) : HalvingTimeBound.
Proof.
  unfold HalvingTimeBound, HalvingTimeLe.
  intros k c n hk hc hclt hn.
  destruct hn as [x [y hx]].
  destruct (Nat.lt_ge_cases n 791) as [hlt | hge].
  - cbn. lia.
  - assert (He : 791 + (n - 791) = n) by lia.
    assert (hs791 : HSurvives c 791 (2 * 3 ^ k - 1) c).
    { apply (hsurvives_mono c 791 (n - 791)). rewrite He. exists x, y. exact hx. }
    destruct hs791 as [a1 [c1 h791]].
    assert (hrec : hrun c (n - 791) a1 c1 = Some (x, y)).
    { rewrite <- (hrun_add c 791 (n - 791) (2 * 3 ^ k - 1) c a1 c1 h791).
      rewrite He. exact hx. }
    assert (hres := h k c 791 a1 c1 (n - 791) hk hc hclt h791 ltac:(lia)
                      (ex_intro _ x (ex_intro _ y hrec))).
    rewrite He in hres. exact hres.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 8. The orbit and the phase-sequence link                        *)
(* ------------------------------------------------------------------ *)

(** The [i]-th state of the halving run, saturating once the run has stopped.
    This exposes the orbit [hrun] traverses, one state at a time, so that the
    phase budget can be applied to it. *)
Fixpoint st (c0 : nat) (n a c : nat) {struct n} : nat * nat :=
  match n with
  | O => (a, c)
  | S n' =>
      match step a c with
      | Halt => (a, c)
      | Next a' c' =>
          if orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0) then (a', c') else st c0 n' a' c'
      end
  end.

(** One unfolding of [st] through a non-stopping [Next]. *)
Lemma st_succ_next (c0 n a c a' c' : nat) :
    step a c = Next a' c' ->
    orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0) = false ->
    st c0 (S n) a c = st c0 n a' c'.
Proof.
  intros hs hf.
  change (match step a c with
          | Halt => (a, c)
          | Next p q =>
              if orb (Nat.eqb p 1) (Nat.leb (2 * q) c0) then (p, q) else st c0 n p q
          end = st c0 n a' c').
  destruct (step a c) as [|p q].
  - discriminate hs.
  - injection hs as H1 H2. subst p. subst q.
    rewrite hf. reflexivity.
Qed.

(** **Orbit-to-run link (states).**  While the halving run survives, [st] is
    exactly the state [hrun] reaches: the orbit is not a separate object, it is
    the run itself. *)
Lemma st_hrun (c0 : nat) : forall (n a c a' c' : nat),
    hrun c0 n a c = Some (a', c') -> st c0 n a c = (a', c').
Proof.
  induction n as [|n ih]; intros a c a' c' h.
  - simpl in h. injection h as H1 H2. rewrite <- H1, <- H2. reflexivity.
  - rewrite hrun_S in h.
    remember (step a c) as s eqn:hs.
    destruct s as [|a1 c1].
    + discriminate h.
    + remember (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) as e eqn:E.
      destruct e.
      * discriminate h.
      * rewrite (st_succ_next c0 n a c a1 c1 (eq_sym hs) (eq_sym E)).
        apply ih. exact h.
Qed.

(** **Orbit-to-run link (steps).**  While the run survives [S i] steps, the
    [i]-th step of the orbit really is [step], taking state [i] to state
    [S i].  This is what lets [L_step] be applied to the orbit. *)
Lemma st_next (c0 : nat) : forall (i a c : nat),
    (exists a' c', hrun c0 (S i) a c = Some (a', c')) ->
    step (fst (st c0 i a c)) (snd (st c0 i a c))
      = Next (fst (st c0 (S i) a c)) (snd (st c0 (S i) a c)).
Proof.
  induction i as [|i ih]; intros a c [a' [c' h']].
  - assert (h2 : st c0 1 a c = (a', c')) by (apply st_hrun; exact h').
    rewrite h2. cbn.
    cbn [hrun] in h'.
    destruct (step a c) as [|a1 c1] eqn:hs.
    + cbn in h'. discriminate h'.
    + remember (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) as e eqn:E.
      destruct e.
      * cbn in h'. discriminate h'.
      * cbn in h'. injection h' as H1 H2. subst a'. subst c'. reflexivity.
  - rewrite hrun_S in h'.
    remember (step a c) as s eqn:hs.
    destruct s as [|a1 c1].
    + discriminate h'.
    + remember (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) as e eqn:E.
      destruct e.
      * discriminate h'.
      * rewrite (st_succ_next c0 (S i) a c a1 c1 (eq_sym hs) (eq_sym E)).
        rewrite (st_succ_next c0 i a c a1 c1 (eq_sym hs) (eq_sym E)).
        exact (ih a1 c1 (ex_intro _ a' (ex_intro _ c' h'))).
Qed.

(** **The phase-sequence link, at the family.**  If the orbit from a post-[j]
    state [(2*3^k-1, c)] survives [n] steps, stays in the [L] region ([c < a]),
    and avoids rule [e] throughout, then those [n] steps form one [L] phase
    and [n <= 791].  This is [L_step] at every step, [L_phase_budget]
    telescoped, and [L_phase_le_791] at [k <= 292], [1 <= c]. *)
Lemma phase_le_791 (k c n : nat) (hk : k <= 292) (hc : 1 <= c)
    (hsurv : forall i, i <= n -> exists a' c', hrun c i (2 * 3 ^ k - 1) c = Some (a', c'))
    (hL : forall i, i < n -> snd (st c i (2 * 3 ^ k - 1) c) < fst (st c i (2 * 3 ^ k - 1) c))
    (hne : forall i, i < n -> fst (st c i (2 * 3 ^ k - 1) c) <> snd (st c i (2 * 3 ^ k - 1) c) + 2) :
    n <= 791.
Proof.
  assert (hstep : forall i, i < n ->
      step (fst (st c i (2 * 3 ^ k - 1) c)) (snd (st c i (2 * 3 ^ k - 1) c))
        = Next (fst (st c (S i) (2 * 3 ^ k - 1) c)) (snd (st c (S i) (2 * 3 ^ k - 1) c))).
  { intros i hi. exact (st_next c i (2 * 3 ^ k - 1) c (hsurv (S i) (ltac:(lia)))). }
  assert (hdrop : forall i, i < n ->
      fst (st c (S i) (2 * 3 ^ k - 1) c) + snd (st c i (2 * 3 ^ k - 1) c)
        <= fst (st c i (2 * 3 ^ k - 1) c)).
  { intros i hi.
    exact (proj1 (L_step (fst (st c i (2 * 3 ^ k - 1) c)) (snd (st c i (2 * 3 ^ k - 1) c))
      (fst (st c (S i) (2 * 3 ^ k - 1) c)) (snd (st c (S i) (2 * 3 ^ k - 1) c))
      (hL i hi) (hne i hi) (hstep i hi))). }
  assert (hgrow : forall i, i < n ->
      3 * snd (st c i (2 * 3 ^ k - 1) c) <= 2 * snd (st c (S i) (2 * 3 ^ k - 1) c)).
  { intros i hi.
    exact (proj2 (L_step (fst (st c i (2 * 3 ^ k - 1) c)) (snd (st c i (2 * 3 ^ k - 1) c))
      (fst (st c (S i) (2 * 3 ^ k - 1) c)) (snd (st c (S i) (2 * 3 ^ k - 1) c))
      (hL i hi) (hne i hi) (hstep i hi))). }
  assert (hb := L_phase_budget (fun j => fst (st c j (2 * 3 ^ k - 1) c))
                               (fun j => snd (st c j (2 * 3 ^ k - 1) c)) n hdrop hgrow).
  cbn in hb.
  exact (L_phase_le_791 k n c hk hc hb).
Qed.

(* ------------------------------------------------------------------ *)
(** ** 8c. The per-cycle [c]-contraction is false                      *)
(* ------------------------------------------------------------------ *)

(** A "cycle" is one maximal [J] phase (rules [i],[j]) followed by one maximal
    [L] phase (rules [a],[b],[c],[e]).  The intended contraction
    [4*c_end <= 3*c_start + K] is **false** already at tiny size: from
    [(549,1196)] rule [i] gives [(1647,651)], then two rule-[c] steps give
    [(992,983)] and [(5,1481)]; the [L] phase ends at [a = 5 <= 1481 = c], so
    [c] has grown by 24%.  No per-cycle monotone quantity of this shape exists. *)

Lemma cycle_contraction_false :
  step 549 1196 = Next 1647 651 /\
  step 1647 651 = Next 992 983 /\
  step 992 983 = Next 5 1481.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** The arithmetic side: [4*1481 = 5924 > 5588 = 3*1196 + 2000]. *)
Lemma cycle_contraction_false_arith : 3 * 1196 + 2000 < 4 * 1481.
Proof.
  vm_compute. repeat constructor.
Qed.

Print Assumptions cycle_contraction_false.
Print Assumptions cycle_contraction_false_arith.
Print Assumptions hsurvives_mono.
Print Assumptions st_hrun.
Print Assumptions st_next.
Print Assumptions phase_le_791.

(* ------------------------------------------------------------------ *)
(** ** 8d. The shallow-cone phase brick                               *)
(* ------------------------------------------------------------------ *)

(** A *phase* is a maximal run of steps taken from one region: the [J] region
    [a <= c] (rules [g],[h],[i],[j]) or the [L] region [c < a] (rules
    [a],[b],[c],[e] and the halts).

    The brick "in the shallow cone [a <= 2c] every phase has length at most 7"
    is **false as stated**: [(1, 3^n)] is shallow for every [n] and its [J]
    phase has [n] steps (each rule [j] triples [a]).  Explicitly [(1,6561)] is
    shallow and its [J] phase has eight steps (BB33_758_ATTACK.md section 22).

    What is true, and proved here (neither lemma needs any bound on [c]):

    - [L_shallow_step]: a shallow [L] step ends the phase ([a' <= c']) unless it
      is rule [e] ([a = c + 2]), which sends the shallow state [(c+2, c)] to
      [(3c+8, 1)], i.e. into the deep cone;
    - [jrun_odd_step] / [jrun_odd]: with [a] odd every [J] step is [i] or [j],
      keeps [a] odd, at least triples [a] and raises [c] by at most 3, so
      [3^n * a <= c + 3n].

    The only form of "every phase has length at most 7" that survives at all is
    a conditional one -- [c < 355]: eight [J] steps give
    [3^7 * a <= c + 21], which [c < 355 <= 2187 <= 3^7 * a] refutes.  That bound
    on [c] is a reachability invariant at phase starts, not a consequence of
    [a <= 2c]; it is not proved, and it was cut from this file.  Cutting it
    changes nothing about the target anyway: [ResidualHalving] needs a bound on
    how many phases a halving run has, and a per-phase length bound -- even the
    unconditional "7" this section was asked for -- supplies none.  The
    refutation of the literal brick is recorded in BB33_758_ATTACK.md section 22;
    the unconditional lemmas below are the handles on the missing invariant on
    [c]. *)

Fixpoint JRun (n a c : nat) {struct n} : Prop :=
  match n with
  | O => True
  | S n' => a <= c /\ (exists a' c' : nat, step a c = Next a' c' /\ JRun n' a' c')
  end.

(** [1 <= a] from [a mod 2 = 1]. *)
Lemma mod2_one_pos (a : nat) (H : a mod 2 = 1) : 1 <= a.
Proof. destruct a; [simpl in H; discriminate | lia]. Qed.

(** [a/2 <= a]. *)
Lemma div2_le (a : nat) : a / 2 <= a.
Proof. pose proof (Nat.div_mod_eq a 2). lia. Qed.


(** [c <= 3*(c/2) + 3]: rule [a] grows [c] faster than a shallow drop. *)
Lemma le_three_half (c : nat) : c <= 3 * (c / 2) + 3.
Proof.
  pose proof (Nat.div_mod_eq c 2) as H.
  pose proof (Nat.mod_upper_bound c 2 (ltac:(lia))) as H2.
  lia.
Qed.

(** [c <= 3*((c-1)/2) + 7]: rules [b] and [c]. *)
Lemma le_three_half_pred (c : nat) : c <= 3 * ((c - 1) / 2) + 7.
Proof.
  pose proof (Nat.div_mod_eq (c - 1) 2) as H.
  pose proof (Nat.mod_upper_bound (c - 1) 2 (ltac:(lia))) as H2.
  lia.
Qed.

(** Arithmetic of [L_shallow_step]: the shallow drop of [a] is dominated by the growth
    of [c] in rules [a], [b], [c]. *)
Lemma shallow_a_arith (a c : nat) (Hca : c < a) (H2c : a <= 2 * c) :
  a - c - 1 <= 3 * (c / 2) + 2.
Proof. pose proof (le_three_half c). set (k := c / 2). lia. Qed.

Lemma shallow_b_arith (a c : nat) (Hca : c < a) (H2c : a <= 2 * c) :
  a - c - 2 <= 3 * ((c - 1) / 2) + 5.
Proof. pose proof (le_three_half_pred c). set (k := (c - 1) / 2). lia. Qed.

Lemma shallow_c_arith (a c : nat) (Hca : c < a) (H2c : a <= 2 * c) :
  a - c - 4 <= 3 * ((c - 1) / 2) + 8.
Proof. pose proof (le_three_half_pred c). set (k := (c - 1) / 2). lia. Qed.

(** [c mod 4 = 3] from the three excluded residues. *)
Lemma mod4_eq_three (c : nat) (H0 : c mod 4 <> 0) (H1 : c mod 4 <> 2)
    (H2 : c mod 4 <> 1) : c mod 4 = 3.
Proof.
  assert (Hb : c mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  destruct (c mod 4) as [| [| [| [| k]]]].
  - exfalso. apply H0. reflexivity.
  - exfalso. apply H2. reflexivity.
  - exfalso. apply H1. reflexivity.
  - reflexivity.
  - exfalso. lia.
Qed.

(** [c mod 2 = 1] from [c mod 2 <> 0]. *)
Lemma mod2_eq_one (c : nat) (H : c mod 2 <> 0) : c mod 2 = 1.
Proof.
  assert (Hb : c mod 2 < 2) by (apply Nat.mod_upper_bound; lia).
  destruct (c mod 2) as [| [| k]].
  - exfalso. apply H. reflexivity.
  - reflexivity.
  - exfalso. lia.
Qed.

(** Oddness is preserved by rules [i] and [j]. *)
Lemma odd3 (a : nat) (H : a mod 2 = 1) : (3 * a) mod 2 = 1.
Proof.
  assert (He : 3 * a = 2 * a + a) by lia.
  rewrite He, Nat.add_mod, mod2_two_mul, H.
  - reflexivity.
  - lia.
Qed.

Lemma odd3_add2 (a : nat) (H : a mod 2 = 1) : (3 * a + 2) mod 2 = 1.
Proof.
  rewrite Nat.add_mod.
  - rewrite (odd3 a H). reflexivity.
  - lia.
Qed.

(** A shallow [L] step ends the phase unless it is rule [e]. *)
Lemma L_shallow_step (a c a' c' : nat) (Hca : c < a) (H2c : a <= 2 * c)
    (H : step a c = Next a' c') :
    a' <= c' \/ (a = c + 2 /\ c mod 4 = 3 /\ c' = 1).
Proof.
  assert (E1 : Nat.leb a c = false) by (apply Nat.leb_gt; lia).
  destruct (orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2)) eqn:E4.
  - assert (Hm : c mod 4 = 0 \/ c mod 4 = 2).
    { apply orb_true_iff in E4. destruct E4 as [E | E].
      - left. apply Nat.eqb_eq. exact E.
      - right. apply Nat.eqb_eq. exact E. }
    rewrite (step_a a c E1 E4) in H. injection H as Ha Hc. subst a' c'. left.
    exact (shallow_a_arith a c Hca H2c).
  - destruct (Nat.eqb (Nat.modulo c 4) 1) eqn:E5.
    + destruct (Nat.eqb a (c + 1)) eqn:E6.
      * rewrite (step_f a c E1 E4 E5 E6) in H. discriminate H.
      * rewrite (step_b a c E1 E4 E5 E6) in H. injection H as Ha Hc. subst a' c'. left.
        exact (shallow_b_arith a c Hca H2c).
    + destruct (Nat.eqb a (c + 1)) eqn:E6.
      * rewrite (step_halt1 a c E1 E4 E5 E6) in H. discriminate H.
      * destruct (Nat.eqb a (c + 2)) eqn:E7.
        -- assert (Ha2 : a = c + 2) by (apply Nat.eqb_eq; exact E7).
           rewrite (step_e a c E1 E4 E5 E6 E7) in H. injection H as Ha Hc. subst a' c'.
           right. split; [exact Ha2 | split; [ | reflexivity]].
           apply orb_false_iff in E4. destruct E4 as [E40 E42].
           apply Nat.eqb_neq in E40. apply Nat.eqb_neq in E42.
           apply Nat.eqb_neq in E5. exact (mod4_eq_three c E40 E42 E5).
        -- destruct (Nat.eqb a (c + 3)) eqn:E8.
           ++ rewrite (step_halt3 a c E1 E4 E5 E6 E7 E8) in H. discriminate H.
           ++ rewrite (step_c a c E1 E4 E5 E6 E7 E8) in H. injection H as Ha Hc. subst a' c'. left.
              exact (shallow_c_arith a c Hca H2c).
Qed.

(** With [a] odd every [J] step is [i] or [j]: [a] stays odd, at least triples,
    and [c] rises by at most 3. *)
Lemma jrun_odd_step (a c a' c' : nat) (H1 : a <= c) (H2 : a mod 2 = 1)
    (H : step a c = Next a' c') :
    a' mod 2 = 1 /\ 3 * a <= a' /\ c' <= c + 3.
Proof.
  assert (E1 : Nat.leb a c = true) by (apply Nat.leb_le; exact H1).
  assert (E2 : Nat.eqb (Nat.modulo a 2) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (Ha1 : 1 <= a) by (apply mod2_one_pos; exact H2).
  destruct (Nat.eqb (Nat.modulo c 2) 0) eqn:E3.
  - rewrite (step_i a c E1 E2 E3) in H. injection H as Ha Hc. subst a' c'.
    split.
    + exact (odd3 a H2).
    + split; lia.
  - rewrite (step_j a c E1 E2 E3) in H. injection H as Ha Hc. subst a' c'.
    split.
    + exact (odd3_add2 a H2).
    + split; lia.
Qed.

(** A [J] phase of length [n+1] from an odd [a] satisfies [3^n * a <= c + 3n]. *)
Lemma jrun_odd (n a c : nat) (H : JRun (S n) a c) (Ha : a mod 2 = 1) :
    3 ^ n * a <= c + 3 * n.
Proof.
  revert a c H Ha.
  induction n as [| n IH]; intros a c H Ha.
  - simpl in H. destruct H as [H1 _]. simpl. lia.
  - simpl in H. destruct H as [H1 [a' [c' [Hstep Hrest]]]].
    destruct (jrun_odd_step a c a' c' H1 Ha Hstep) as [Ha' [H3a Hc]].
    specialize (IH a' c' Hrest Ha').
    assert (Hpow : 3 ^ S n = 3 * 3 ^ n) by (simpl; ring).
    rewrite Hpow.
    assert (Heq : 3 * 3 ^ n * a = 3 ^ n * (3 * a)) by ring.
    rewrite Heq.
    assert (Hmono : 3 ^ n * (3 * a) <= 3 ^ n * a') by (apply Nat.mul_le_mono_l; exact H3a).
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 8e. Phase counting: the only unconditional bound, and why a count
    cannot close

    A *phase* is a maximal same-region run, so a phase boundary is a step whose
    result lies in the other region.  [flips n a c] counts those boundaries
    along the next [n] steps.

    [flips_le] is the only phase-count bound available without further
    hypotheses: a run of [n] steps has at most [n] boundaries.  One-step phases
    exist, so this is sharp as a general statement, and it is why a count cannot
    replace a length bound.

    [counting_budget_le]: [ResidualHalving] has to fit the residual in
    [10000 - 791 = 9209] steps.  The proved per-phase budgets are [878] for a
    post-[j] [L] phase ([L_phase_le_878]) and [293] for a [j] phase
    ([J_phase_le_293]), so a residual with [NL] [L] phases and [NJ] [j] phases is
    only bounded by [878*NL + 293*NJ].  At the measured worst residual
    (_pc.py: [NL = NJ = 9], total length 53) that budget is [10539 > 9209]:
    even exact knowledge of the phase counts does not fit.
    [counting_budget_forces]: nine [L] phases leave room for at most four [j]
    phases.

    So the counting route cannot close [ResidualHalving] with the present
    per-phase budgets.  Making it fit needs the per-phase bounds two orders of
    magnitude smaller (actual: 39 [L] steps and 14 [j] steps in that residual),
    which is the phase-length brick of section 8d, false in its unconditional
    form. *)

(** Region changes ([J]: [a <= c] versus [L]: [c < a]) along the next [n] steps,
    stopping at a halt. *)
Fixpoint flips (n a c : nat) {struct n} : nat :=
  match n with
  | O => 0
  | S n' =>
      match step a c with
      | Halt => 0
      | Next a' c' =>
          (if (if Nat.leb a c then negb (Nat.leb a' c') else Nat.leb a' c')
           then 1 else 0) + flips n' a' c'
      end
  end.

(** [n] steps contain at most [n] phase boundaries. *)
Lemma flips_le (n a c : nat) : flips n a c <= n.
Proof.
  revert a c.
  induction n as [| n IH]; intros a c.
  - simpl. lia.
  - simpl. destruct (step a c) as [| a' c'].
    + lia.
    + assert (H := IH a' c').
      destruct (Nat.leb a c); destruct (Nat.leb a' c'); simpl; lia.
Qed.

(** A run of [n] steps has at most [n + 1] phases. *)
Lemma phases_le (n a c : nat) : flips n a c + 1 <= n + 1.
Proof. pose proof (flips_le n a c). lia. Qed.

(** The counting route's budget at the measured worst residual counts
    ([NL = NJ = 9]) already exceeds the [9209] steps available. *)
(* [lia] cannot parse numerals >= 1000 in this Stdlib (they elaborate to
   [Nat.of_num_uint]), so the two budget lemmas below are built from small-numeral
   facts and [Nat.lt_le_trans], with the large comparisons discharged by
   [vm_compute]. *)

Lemma counting_budget_le (NL NJ : nat) (hL : 9 <= NL) (hJ : 9 <= NJ) :
  9209 < 878 * NL + 293 * NJ.
Proof.
  assert (h1 : 878 * 9 <= 878 * NL)
    by (apply Nat.mul_le_mono_l; exact hL).
  assert (h2 : 293 * 9 <= 293 * NJ)
    by (apply Nat.mul_le_mono_l; exact hJ).
  assert (e1 : 878 * 9 = 7902) by (vm_compute; reflexivity).
  assert (e2 : 293 * 9 = 2637) by (vm_compute; reflexivity).
  rewrite e1 in h1. rewrite e2 in h2.
  assert (hsum : 7902 + 2637 <= 878 * NL + 293 * NJ) by lia.
  assert (hbig : 9209 < 7902 + 2637)
    by (apply leb_true_le; vm_compute; reflexivity).
  exact (Nat.lt_le_trans 9209 (7902 + 2637) (878 * NL + 293 * NJ) hbig hsum).
Qed.

(** Nine [L] phases leave room for at most four [j] phases inside [9209] steps,
    under the proved per-phase budgets. *)
Lemma counting_budget_forces (NL NJ : nat) (hL : 9 <= NL)
    (h : 878 * NL + 293 * NJ <= 9209) : NJ <= 4.
Proof.
  destruct (Nat.le_gt_cases NJ 4) as [hle | hgt].
  - exact hle.
  - exfalso.
    assert (h5 : 5 <= NJ) by lia.
    assert (h1 : 878 * 9 <= 878 * NL)
      by (apply Nat.mul_le_mono_l; exact hL).
    assert (h2 : 293 * 5 <= 293 * NJ)
      by (apply Nat.mul_le_mono_l; exact h5).
    assert (e1 : 878 * 9 = 7902) by (vm_compute; reflexivity).
    assert (e2 : 293 * 5 = 1465) by (vm_compute; reflexivity).
    rewrite e1 in h1. rewrite e2 in h2.
    assert (hsum : 7902 + 1465 <= 878 * NL + 293 * NJ) by lia.
    assert (h3 : 7902 + 1465 <= 9209)
      by (apply (Nat.le_trans (7902 + 1465) (878 * NL + 293 * NJ) 9209 hsum h)).
    apply Nat.leb_le in h3.
    vm_compute in h3.
    discriminate h3.
Qed.


(* ------------------------------------------------------------------ *)
(** ** 8f. The phase-composition lemma, and the phase that breaks it

    Section 8e proved the counting arithmetic, section 8b the two per-phase
    budgets; neither composes them.  [phase_composition] is the composition:
    a sequence of [N] phases, each tagged [L] ([tag i = 1], charged [878]) or
    [j] ([tag i = 0], charged [293]), has total length at most
    [878*NL + 293*NJ] (Lean: [phase_composition]).
    Section 8g rebuilds [len] and [tag] from the run itself.

    The charges hold at the post-[j] start ([postJ_charge]) and fail one step
    later ([phase_two_breaks]): from [(2*3^292-1, 2*3^292-1)] a rule-[j] step
    gives [(2*3^293-1, 1)], where [a0 > 2*3^292] and
    [a0 + 2*c0 = 2*3^293+1 > 6*3^292].  So the composition cannot be charged
    past phase 1 -- the phase that breaks it is the second -- and the residual
    starts 791 steps in.  This is the obstruction of BB33_758_ATTACK.md
    section 23, not a proof of it. *)

Fixpoint ssum (len : nat -> nat) (N : nat) {struct N} : nat :=
  match N with O => 0 | S k => ssum len k + len k end.

Fixpoint sL (tag : nat -> nat) (N : nat) {struct N} : nat :=
  match N with O => 0 | S k => sL tag k + tag k end.

Fixpoint sJ (tag : nat -> nat) (N : nat) {struct N} : nat :=
  match N with O => 0 | S k => sJ tag k + (1 - tag k) end.

Lemma ssum_succ (len : nat -> nat) (k : nat) : ssum len (S k) = ssum len k + len k.
Proof. reflexivity. Qed.

Lemma sL_succ (tag : nat -> nat) (k : nat) : sL tag (S k) = sL tag k + tag k.
Proof. reflexivity. Qed.

Lemma sJ_succ (tag : nat -> nat) (k : nat) : sJ tag (S k) = sJ tag k + (1 - tag k).
Proof. reflexivity. Qed.

(** **The phase-composition lemma.**  Charging every [L] phase [878] and every
    [j] phase [293] bounds the total length by [878*NL + 293*NJ]. *)
Theorem phase_composition : forall (len tag : nat -> nat) (N : nat),
    (forall i, i < N -> tag i = 0 \/ tag i = 1) ->
    (forall i, i < N -> tag i = 1 -> len i <= 878) ->
    (forall i, i < N -> tag i = 0 -> len i <= 293) ->
    ssum len N <= 878 * sL tag N + 293 * sJ tag N.
Proof.
  intros len tag N.
  induction N as [|N ih].
  - intros htag hL hJ. cbn. lia.
  - intros htag hL hJ.
    assert (hrec : ssum len N <= 878 * sL tag N + 293 * sJ tag N).
    { apply ih.
      - intros i hi. apply htag. lia.
      - intros i hi h1. apply hL; [lia | exact h1].
      - intros i hi h0. apply hJ; [lia | exact h0]. }
    rewrite (ssum_succ len N), (sL_succ tag N), (sJ_succ tag N).
    destruct (htag N (ltac:(lia))) as [H0 | H1].
    + assert (hlen : len N <= 293) by (apply (hJ N (ltac:(lia)) H0)).
      rewrite H0. lia.
    + assert (hlen : len N <= 878) by (apply (hL N (ltac:(lia)) H1)).
      rewrite H1. lia.
Qed.

(** **The post-[j] hypothesis discharges the per-phase caps.** *)
Lemma postJ_charge (k c : nat) (hk : k <= 292) (hc : 1 <= c) (hclt : c < 2 * 3 ^ k) :
    1 <= 2 * 3 ^ k - 1 /\ 2 * 3 ^ k - 1 <= 2 * 3 ^ 292 /\
    (2 * 3 ^ k - 1) + 2 * c <= 6 * 3 ^ 292.
Proof.
  assert (hle : c <= 2 * 3 ^ k - 1) by lia.
  assert (hpow : 1 <= 3 ^ k).
  { assert (H := pow3_mono 0 k (ltac:(lia))). simpl in H. exact H. }
  assert (h292 : 3 ^ k <= 3 ^ 292) by (apply pow3_mono; exact hk).
  assert (h6 : 6 * 3 ^ k <= 6 * 3 ^ 292) by (apply Nat.mul_le_mono_l; exact h292).
  set (x := 3 ^ k) in *.
  repeat split; lia.
Qed.

(** The extremal post-[j] state is exactly chargeable: [Q0 <= 6*3^292]. *)
Lemma postJ_charge_extremal :
    (2 * 3 ^ 292 - 1) + 2 * (2 * 3 ^ 292 - 1) <= 6 * 3 ^ 292.
Proof.
  apply (proj2 (proj2 (postJ_charge 292 (2 * 3 ^ 292 - 1)
    ltac:(lia) ltac:(pose proof (pow3_pos 292); lia)
    ltac:(pose proof (pow3_pos 292); lia)))).
Qed.

(** [3^293 = 3*3^292], the only exponent identity the crossing needs. *)
(** [3^(S n) = 3*3^n], symbolic in [n] so that no closed 465-bit numeral is
    ever unfolded. *)
Lemma pow3_succ (n : nat) : 3 ^ S n = 3 * 3 ^ n.
Proof. rewrite pow_succ_nat. ring. Qed.

Lemma pow3_293 : 3 ^ 293 = 3 * 3 ^ 292.
Proof. exact (pow3_succ 292). Qed.

(** [(2*u - 1) mod 2 = 1]: the post-[j] [a] value is odd.  Proved by hand, not
    by [vm_compute] on the 464-bit literal, which exhausts memory. *)
Lemma two_mul_pred_odd (u : nat) (hu : 1 <= u) : (2 * u - 1) mod 2 = 1.
Proof.
  assert (H : 2 * u - 1 = 2 * (u - 1) + 1) by lia.
  rewrite H.
  rewrite Nat.add_mod by lia.
  rewrite mod2_two_mul, Nat.add_0_l.
  reflexivity.
Qed.

(** **The crossing, symbolically in [u] = [3^292].**  All four claims are proved
    for an abstract [u >= 1]; only [u = 3^292] is substituted below, so no
    tactic ever touches the 465-bit numeral. *)
Lemma phase_two_breaks_gen (u : nat) (hu : 1 <= u) :
    (2 * u - 1) + 2 * (2 * u - 1) <= 6 * u /\
    step (2 * u - 1) (2 * u - 1) = Next (3 * (2 * u - 1) + 2) 1 /\
    2 * u < 2 * (3 * u) - 1 /\
    6 * u < (2 * (3 * u) - 1) + 2.
Proof.
  assert (Hodd := two_mul_pred_odd u hu).
  assert (Hs : step (2 * u - 1) (2 * u - 1)
      = Next (3 * (2 * u - 1) + 2) ((2 * u - 1) - (2 * u - 1) + 1)).
  { apply step_j.
    - apply Nat.leb_le. lia.
    - rewrite Hodd. reflexivity.
    - rewrite Hodd. reflexivity. }
  assert (H2 : step (2 * u - 1) (2 * u - 1) = Next (3 * (2 * u - 1) + 2) 1).
  { rewrite Hs, Nat.sub_diag. reflexivity. }
  assert (H3 : 2 * u < 2 * (3 * u) - 1) by lia.
  assert (H4 : 6 * u < (2 * (3 * u) - 1) + 2) by lia.
  split; [lia | split; [exact H2 | split; [exact H3 | exact H4]]].
Qed.

(** **The charging stops at phase 2.**  From `(2*3^292-1, 2*3^292-1)` one
    rule-[j] step gives `(2*3^293-1, 1)`, where both caps fail.  The first
    conjunct says the extremal state is still chargeable; the other three say
    the next one is not. *)
Lemma phase_two_breaks :
    (2 * 3 ^ 292 - 1) + 2 * (2 * 3 ^ 292 - 1) <= 6 * 3 ^ 292 /\
    step (2 * 3 ^ 292 - 1) (2 * 3 ^ 292 - 1) = Next (2 * 3 ^ 293 - 1) 1 /\
    2 * 3 ^ 292 < 2 * 3 ^ 293 - 1 /\
    6 * 3 ^ 292 < (2 * 3 ^ 293 - 1) + 2.
Proof.
  assert (hpos : 1 <= 3 ^ 292) by (apply pow3_pos).
  destruct (phase_two_breaks_gen (3 ^ 292) hpos) as [A1 [A2 [A3 A4]]].
  assert (Hval : 3 * (2 * 3 ^ 292 - 1) + 2 = 2 * 3 ^ 293 - 1)
    by (rewrite pow3_293; lia).
  rewrite Hval in A2.
  assert (Hval3 : 2 * (3 * 3 ^ 292) - 1 = 2 * 3 ^ 293 - 1)
    by (rewrite pow3_293; reflexivity).
  rewrite Hval3 in A3, A4.
  split; [exact A1 | split; [exact A2 | split; [exact A3 | exact A4]]].
Qed.

Print Assumptions L_phase_le_878.
Print Assumptions L_phase_le_878_gen.
Print Assumptions phase_composition.
Print Assumptions postJ_charge.
Print Assumptions pow3_succ.
Print Assumptions pow3_293.
Print Assumptions phase_two_breaks_gen.
Print Assumptions two_mul_pred_odd.
Print Assumptions postJ_charge_extremal.
Print Assumptions phase_two_breaks.

(* ------------------------------------------------------------------ *)
(** ** 8g. The phase list of a real run

    Section 8f composed an *abstract* phase sequence: [len] and [tag] were
    arbitrary functions and the total was [ssum len N].  Here the sequence is
    built from the run.  [b : nat -> nat] is the phase-start index sequence of
    the halving run of length [n] ([b 0 = 0], [b N = n], monotone),
    [cutLen b i = b (i+1) - b i] is the length of phase [i], and
    [phaseTag c0 a c b i] is the region of the state the run is in at index
    [b i] -- a real state of the run, because [st] agrees with [hrun] on every
    surviving prefix ([st_hrun]).  [ssum_cutLen] proves the phase lengths add
    up to [b N = n], so [phase_composition] becomes a statement about the run's
    length instead of an abstract total, with the charges attached to actual
    phase starts. *)

Definition reg (a c : nat) : nat := if Nat.leb a c then 1 else 0.

Lemma reg_mem (a c : nat) : reg a c = 0 \/ reg a c = 1.
Proof.
  unfold reg. destruct (Nat.leb a c); [right | left]; reflexivity.
Qed.

Definition cutLen (b : nat -> nat) (i : nat) : nat := b (S i) - b i.

Definition phaseTag (c0 a c : nat) (b : nat -> nat) (i : nat) : nat :=
  reg (fst (st c0 (b i) a c)) (snd (st c0 (b i) a c)).

Lemma cut_mono_le (b : nat -> nat) (j : nat) :
    (forall k, k < j -> b k <= b (S k)) -> forall i, i <= j -> b i <= b j.
Proof.
  induction j as [| j ih].
  - intros h i hi. assert (i = 0) by lia. subst i. apply Nat.le_refl.
  - intros h i hi.
    destruct (Nat.lt_ge_cases i (S j)) as [hlt | hge].
    + assert (h1 : b i <= b j)
        by (apply ih; [ intros k hk; apply h; lia | lia ]).
      assert (h2 : b j <= b (S j)) by (apply h; lia).
      lia.
    + assert (i = S j) by lia. subst i. apply Nat.le_refl.
Qed.

Lemma ssum_cutLen (b : nat -> nat) (N : nat) :
    (forall i, i < N -> b i <= b (S i)) -> ssum (cutLen b) N = b N - b 0.
Proof.
  induction N as [| N ih].
  - intros h. cbn. lia.
  - intros hmono.
    assert (h1 : forall i, i < N -> b i <= b (S i))
      by (intros i hi; apply hmono; lia).
    assert (h2 : ssum (cutLen b) N = b N - b 0) by (apply ih; exact h1).
    assert (h3 : b N <= b (S N)) by (apply hmono; lia).
    assert (h4 : b 0 <= b N) by (apply (cut_mono_le b N h1 0); lia).
    rewrite ssum_succ, h2. unfold cutLen. lia.
Qed.

(** **The composition over a real run.**  If the halving run of length [n] is
    cut into [N] phases at the indices [b 0 <= ... <= b N = n], and every phase
    is charged by its region ([878] for [L], [293] for [j]), then the run's
    length is bounded by its charge, and the orbit at the end of the run is the
    run's own end state. *)
Theorem hrun_phase_composition (c0 n a c a' c' : nat)
    (hr : hrun c0 n a c = Some (a', c')) (b : nat -> nat) (N : nat)
    (hb0 : b 0 = 0) (hbN : b N = n)
    (hmono : forall i, i < N -> b i <= b (S i))
    (hL : forall i, i < N -> phaseTag c0 a c b i = 1 -> cutLen b i <= 878)
    (hJ : forall i, i < N -> phaseTag c0 a c b i = 0 -> cutLen b i <= 293) :
    n <= 878 * sL (phaseTag c0 a c b) N + 293 * sJ (phaseTag c0 a c b) N /\
    st c0 n a c = (a', c').
Proof.
  assert (hsum : ssum (cutLen b) N = n).
  { rewrite (ssum_cutLen b N hmono), hbN, hb0. lia. }
  assert (hcomp := phase_composition (cutLen b) (phaseTag c0 a c b) N
    (fun i hi => reg_mem (fst (st c0 (b i) a c)) (snd (st c0 (b i) a c))) hL hJ).
  split.
  - lia.
  - apply (st_hrun c0 n a c a' c'). exact hr.
Qed.

(** **The residual window at run level.**  If the charge fits in the [9209]
    steps left after the first phase and there are at least nine [L] phases,
    the run itself fits and has at most four [j] phases. *)
Theorem hrun_phase_counting (c0 n a c a' c' : nat)
    (hr : hrun c0 n a c = Some (a', c')) (b : nat -> nat) (N : nat)
    (hb0 : b 0 = 0) (hbN : b N = n)
    (hmono : forall i, i < N -> b i <= b (S i))
    (hL : forall i, i < N -> phaseTag c0 a c b i = 1 -> cutLen b i <= 878)
    (hJ : forall i, i < N -> phaseTag c0 a c b i = 0 -> cutLen b i <= 293)
    (hfit : 878 * sL (phaseTag c0 a c b) N + 293 * sJ (phaseTag c0 a c b) N <= 9209)
    (h9 : 9 <= sL (phaseTag c0 a c b) N) :
    n <= 9209 /\ sJ (phaseTag c0 a c b) N <= 4.
Proof.
  assert (h1 := proj1 (hrun_phase_composition c0 n a c a' c' hr b N hb0 hbN hmono hL hJ)).
  split.
  - lia.
  - apply (counting_budget_forces (sL (phaseTag c0 a c b) N) (sJ (phaseTag c0 a c b) N) h9 hfit).
Qed.

(** Cancellation of a positive common factor on the left, from
    [le_of_mul_le_mul_r]. *)
Lemma le_of_mul_le_mul_l (a b c : nat) (hc : 0 < c) (h : c * a <= c * b) : a <= b.
Proof.
  apply (le_of_mul_le_mul_r a b c hc).
  rewrite (Nat.mul_comm a c), (Nat.mul_comm b c). exact h.
Qed.

(** [n * 2^n <= 2 * 3^n]: [3^n] beats the linear factor, which is what turns a
    ratio budget into a linear one. *)
Lemma n_mul_pow2_le (n : nat) : n * 2 ^ n <= 2 * 3 ^ n.
Proof.
  induction n as [| n ih].
  - cbn. lia.
  - assert (h2 : 2 ^ n <= 3 ^ n) by (apply pow2_le_pow3).
    assert (ih2 : 2 * (n * 2 ^ n) <= 2 * (2 * 3 ^ n))
      by (apply Nat.mul_le_mono_l; exact ih).
    assert (h3 : 2 * 2 ^ n <= 2 * 3 ^ n) by (apply Nat.mul_le_mono_l; exact h2).
    assert (e1 : S n * 2 ^ S n = 2 * (n * 2 ^ n) + 2 * 2 ^ n)
      by (rewrite pow_succ_nat; ring).
    assert (e2 : 2 * 3 ^ S n = 2 * (3 * 3 ^ n))
      by (rewrite pow_succ_nat; reflexivity).
    rewrite e1, e2.
    assert (e3 : 2 * (2 * 3 ^ n) = 4 * 3 ^ n) by ring.
    assert (e4 : 2 * (3 * 3 ^ n) = 6 * 3 ^ n) by ring.
    rewrite e3 in ih2. rewrite e4. lia.
Qed.

(** **The [L] phase budget at its own start.**  An [L] phase of length [n] from
    [(a0, c0)] with [c0 >= 1] obeys [n * c0 <= a0 + 2*c0]: the length is
    bounded by the start's [Q]-value in units of its own [c0], not by a fixed
    constant.  No bound on [a0] is used. *)
Lemma L_phase_len_c0 (n a0 c0 : nat) (hc : 1 <= c0)
    (h : 2 * c0 * 3 ^ n <= 2 ^ n * (a0 + 2 * c0)) :
    n * c0 <= a0 + 2 * c0.
Proof.
  assert (h1 := n_mul_pow2_le n).
  assert (h2 : n * 2 ^ n * (2 * c0) <= 2 * 3 ^ n * (2 * c0))
    by (apply Nat.mul_le_mono_r; exact h1).
  assert (e1 : n * 2 ^ n * (2 * c0) = 2 ^ n * (n * (2 * c0))) by ring.
  assert (e2 : 2 * 3 ^ n * (2 * c0) = 2 * (2 * c0 * 3 ^ n)) by ring.
  assert (e3 : 2 * (2 ^ n * (a0 + 2 * c0)) = 2 ^ n * (2 * (a0 + 2 * c0))) by ring.
  rewrite e1 in h2. rewrite e2 in h2.
  assert (h3 : 2 * (2 * c0 * 3 ^ n) <= 2 * (2 ^ n * (a0 + 2 * c0)))
    by (apply Nat.mul_le_mono_l; exact h).
  rewrite e3 in h3.
  assert (h4 : 2 ^ n * (n * (2 * c0)) <= 2 ^ n * (2 * (a0 + 2 * c0))) by lia.
  assert (h5 : n * (2 * c0) <= 2 * (a0 + 2 * c0)).
  { refine (le_of_mul_le_mul_l (n * (2 * c0)) (2 * (a0 + 2 * c0)) (2 ^ n) _ h4).
    assert (H : 2 ^ 0 <= 2 ^ n) by (apply pow2_mono; lia).
    simpl in H. lia. }
  assert (e4 : n * (2 * c0) = 2 * (n * c0)) by ring.
  rewrite e4 in h5. lia.
Qed.

(** [1 + 2*m <= 3^m]: [3^m] beats the linear term. *)
Lemma three_pow_ge_lin (m : nat) : 1 + 2 * m <= 3 ^ m.
Proof.
  induction m as [| m ih].
  - cbn. lia.
  - rewrite pow_succ_nat.
    assert (h : 3 * (1 + 2 * m) <= 3 * 3 ^ m) by (apply Nat.mul_le_mono_l; exact ih).
    lia.
Qed.

(** **The [j] phase budget at its own start.**  A [j] run of length [m >= 1]
    from [(a0, c0)] with [a0 >= 1] obeys [2*(m*a0) <= a0 + 2*c0 + 2*m]: every
    rule-[j] step triples [a], so the run can only be as long as the start's
    [Q]-value in units of [a0].  No bound on [a0] or [c0] is used. *)
Lemma J_phase_len_own (m a0 c0 : nat) (hm : 1 <= m) (ha : 1 <= a0)
    (h : 3 ^ m * (a0 + 1) <= a0 + 2 * c0 + 4 * m) :
    2 * (m * a0) <= a0 + 2 * c0 + 2 * m.
Proof.
  assert (hlin : 1 + 2 * m <= 3 ^ m) by (apply three_pow_ge_lin).
  assert (hmul : (1 + 2 * m) * (a0 + 1) <= 3 ^ m * (a0 + 1))
    by (apply Nat.mul_le_mono_r; exact hlin).
  assert (h2 : (1 + 2 * m) * (a0 + 1) <= a0 + 2 * c0 + 4 * m) by lia.
  assert (hexp : (1 + 2 * m) * (a0 + 1) = a0 + 1 + 2 * (m * a0) + 2 * m) by ring.
  rewrite hexp in h2. lia.
Qed.

Print Assumptions hrun_phase_composition.
Print Assumptions hrun_phase_counting.
Print Assumptions ssum_cutLen.
Print Assumptions cut_mono_le.
Print Assumptions reg_mem.
Print Assumptions le_of_mul_le_mul_l.
Print Assumptions n_mul_pow2_le.
Print Assumptions L_phase_len_c0.
Print Assumptions three_pow_ge_lin.
Print Assumptions J_phase_len_own.
(* ------------------------------------------------------------------ *)
(** ** 8h. The parity invariants of the tail                          *)
(* ------------------------------------------------------------------ *)

(** **8h-a. Parity arithmetic.**  The tail's parity walk needs four families
    of facts: the parity of [c] from [c mod 4], the parity of the half
    [(c-1)/2], the parity of [3*m+5] and [3*m+8] from the parity of [m], and
    the parity of [a' + a] when [a' = a - c - r] with [c] odd and [r] even.
    They are kept separate so that the step case analysis only rewrites. *)

Lemma mod2_two_mul_succ (k : nat) : (2 * k + 1) mod 2 = 1.
Proof.
  rewrite Nat.add_mod by lia.
  rewrite mod2_two_mul. rewrite Nat.add_0_l. reflexivity.
Qed.

Lemma mod2_add_even (x y : nat) (hx : x mod 2 = 0) (hy : y mod 2 = 0) :
    (x + y) mod 2 = 0.
Proof. rewrite Nat.add_mod by lia. rewrite hx, hy. reflexivity. Qed.

Lemma mod2_add_odd_odd (x y : nat) (hx : x mod 2 = 1) (hy : y mod 2 = 1) :
    (x + y) mod 2 = 0.
Proof. rewrite Nat.add_mod by lia. rewrite hx, hy. reflexivity. Qed.

Lemma mod2_add_even_odd (x y : nat) (hx : x mod 2 = 0) (hy : y mod 2 = 1) :
    (x + y) mod 2 = 1.
Proof. rewrite Nat.add_mod by lia. rewrite hx, hy. reflexivity. Qed.

Lemma mod2_add4_of_odd (x : nat) (h : x mod 2 = 1) : (x + 4) mod 2 = 1.
Proof. rewrite Nat.add_mod by lia. rewrite h. reflexivity. Qed.

Lemma mod2_add1_of_even (x : nat) (h : x mod 2 = 0) : (x + 1) mod 2 = 1.
Proof. rewrite Nat.add_mod by lia. rewrite h. reflexivity. Qed.

Lemma mod2_sub_even_odd (a c : nat) (hle : a <= c) (ha : a mod 2 = 1)
    (hc : c mod 2 = 0) : (c - a) mod 2 = 1.
Proof.
  assert (H : c = (c - a) + a) by lia.
  assert (H2 : ((c - a) + a) mod 2 = 0) by (rewrite <- H; exact hc).
  rewrite Nat.add_mod in H2 by lia.
  rewrite ha in H2.
  destruct ((c - a) mod 2) as [|[|k]] eqn:E.
  - simpl in H2. discriminate H2.
  - reflexivity.
  - exfalso.
    assert (Hb : (c - a) mod 2 < 2) by (apply Nat.mod_upper_bound; lia).
    rewrite E in Hb. lia.
Qed.

Lemma mod2_sub_odd_odd (a c : nat) (hle : a <= c) (ha : a mod 2 = 1)
    (hc : c mod 2 = 1) : (c - a) mod 2 = 0.
Proof.
  assert (H : c = (c - a) + a) by lia.
  assert (H2 : ((c - a) + a) mod 2 = 1) by (rewrite <- H; exact hc).
  rewrite Nat.add_mod in H2 by lia.
  rewrite ha in H2.
  destruct ((c - a) mod 2) as [|[|k]] eqn:E.
  - reflexivity.
  - exfalso. simpl in H2. discriminate H2.
  - exfalso.
    assert (Hb : (c - a) mod 2 < 2) by (apply Nat.mod_upper_bound; lia).
    rewrite E in Hb. lia.
Qed.

Lemma half_mod2_of_mod4_one (c : nat) (h : c mod 4 = 1) : ((c - 1) / 2) mod 2 = 0.
Proof.
  assert (hc : c = 4 * (c / 4) + 1).
  { pose proof (Nat.div_mod_eq c 4) as H. rewrite h in H. rewrite Nat.mul_comm in H. lia. }
  assert (h1 : c - 1 = 4 * (c / 4)) by lia.
  rewrite h1.
  replace (4 * (c / 4)) with ((2 * (c / 4)) * 2) by lia.
  rewrite Nat.div_mul by lia.
  apply mod2_two_mul.
Qed.

Lemma half_mod2_of_mod4_three (c : nat) (h : c mod 4 = 3) : ((c - 1) / 2) mod 2 = 1.
Proof.
  assert (hc : c = 4 * (c / 4) + 3).
  { pose proof (Nat.div_mod_eq c 4) as H. rewrite h in H. rewrite Nat.mul_comm in H. lia. }
  assert (h1 : c - 1 = 4 * (c / 4) + 2) by lia.
  rewrite h1.
  replace (4 * (c / 4) + 2) with ((2 * (c / 4) + 1) * 2) by lia.
  rewrite Nat.div_mul by lia.
  apply mod2_two_mul_succ.
Qed.

Lemma three_mul_add5_odd (m : nat) (h : m mod 2 = 0) : (3 * m + 5) mod 2 = 1.
Proof.
  assert (h3 : 3 * m = 2 * m + m) by lia.
  rewrite h3.
  assert (h5 : (2 * m + m) mod 2 = 0).
  { rewrite Nat.add_mod by lia. rewrite mod2_two_mul, h. reflexivity. }
  rewrite Nat.add_mod by lia.
  rewrite h5, Nat.add_0_l. reflexivity.
Qed.

Lemma three_mul_add8_odd (m : nat) (h : m mod 2 = 1) : (3 * m + 8) mod 2 = 1.
Proof.
  assert (h3 : 3 * m = 2 * m + m) by lia.
  rewrite h3.
  assert (h5 : (2 * m + m) mod 2 = 1).
  { rewrite Nat.add_mod by lia. rewrite mod2_two_mul, h. rewrite Nat.add_0_l. reflexivity. }
  rewrite Nat.add_mod by lia.
  rewrite h5.
  assert (h8 : 8 mod 2 = 0) by reflexivity.
  rewrite h8, Nat.add_0_r. reflexivity.
Qed.

Lemma flip_two (a c : nat) (hca : c < a) (hc : c mod 2 = 1) (hne : a <> c + 1) :
    (a - c - 2 + a) mod 2 = 1.
Proof.
  assert (hge : c + 2 <= a) by lia.
  set (a' := a - c - 2).
  assert (hsum : a = a' + (c + 2)) by lia.
  assert (hassoc : a' + (a' + (c + 2)) = 2 * a' + (c + 2)) by lia.
  rewrite hsum, hassoc.
  assert (hc2 : (c + 2) mod 2 = 1).
  { rewrite (Nat.add_mod c 2 2) by lia. rewrite hc.
    assert (h2 : 2 mod 2 = 0) by reflexivity. rewrite h2, Nat.add_0_r. reflexivity. }
  rewrite (Nat.add_mod (2 * a') (c + 2) 2) by lia.
  rewrite mod2_two_mul, Nat.add_0_l.
  rewrite hc2. reflexivity.
Qed.

Lemma flip_four (a c : nat) (hca : c < a) (hc : c mod 2 = 1) (hne1 : a <> c + 1)
    (hne2 : a <> c + 2) (hne3 : a <> c + 3) :
    (a - c - 4 + a) mod 2 = 1.
Proof.
  assert (hge : c + 4 <= a) by lia.
  set (a' := a - c - 4).
  assert (hsum : a = a' + (c + 4)) by lia.
  assert (hassoc : a' + (a' + (c + 4)) = 2 * a' + (c + 4)) by lia.
  rewrite hsum, hassoc.
  assert (hc4 : (c + 4) mod 2 = 1).
  { rewrite (Nat.add_mod c 4 2) by lia. rewrite hc.
    assert (h4 : 4 mod 2 = 0) by reflexivity. rewrite h4, Nat.add_0_r. reflexivity. }
  rewrite (Nat.add_mod (2 * a') (c + 4) 2) by lia.
  rewrite mod2_two_mul, Nat.add_0_l.
  rewrite hc4. reflexivity.
Qed.

(** **8h-b. The tail's parity walk.** *)

(** A surviving [J] state has odd [a]: an even [a] with [a <= c] stops the run
    at once, by [step_g] when [c] is even and [step_h] when [c] is odd. *)
Lemma hrun_odd_of_le (c0 n a c a' c' : nat)
    (h : hrun c0 (S n) a c = Some (a', c')) (hle : a <= c) : a mod 2 = 1.
Proof.
  rewrite hrun_S in h.
  remember (step a c) as s eqn:hs.
  destruct s as [|a1 c1].
  - discriminate h.
  - destruct (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0)) eqn:E.
    + discriminate h.
    + destruct (Nat.eqb (Nat.modulo a 2) 0) eqn:E2.
      * destruct (Nat.eqb (Nat.modulo c 2) 0) eqn:E3.
        -- exfalso.
           assert (E1 : Nat.leb a c = true) by (apply Nat.leb_le; exact hle).
           assert (HG : step a c = Halt) by (apply step_g; [exact E1 | exact E2 | exact E3]).
           rewrite HG in hs. discriminate hs.
        -- exfalso.
           assert (E1 : Nat.leb a c = true) by (apply Nat.leb_le; exact hle).
           assert (HH : step a c = Next 1 (a / 2 + c + 2))
             by (apply step_h; [exact E1 | exact E2 | exact E3]).
           rewrite HH in hs. injection hs as H1 H2. subst a1.
           rewrite Nat.eqb_refl in E. simpl in E. discriminate E.
      * apply mod2_eq_one. intro H0. rewrite H0 in E2. discriminate E2.
Qed.

(** [J] steps keep both parities odd. *)
Lemma J_step_odd (a c a' c' : nat) (hac : a <= c) (ha : a mod 2 = 1)
    (h : step a c = Next a' c') : a' mod 2 = 1 /\ c' mod 2 = 1.
Proof.
  destruct (Nat.eqb (Nat.modulo c 2) 0) eqn:E3.
  - assert (E1 : Nat.leb a c = true) by (apply Nat.leb_le; exact hac).
    assert (E2 : Nat.eqb (Nat.modulo a 2) 0 = false)
      by (apply Nat.eqb_neq; intro H0; rewrite H0 in ha; discriminate ha).
    assert (HH : step a c = Next (3 * a) (c - a + 4))
      by (apply step_i; [exact E1 | exact E2 | exact E3]).
    rewrite HH in h. injection h as H1 H2. subst a' c'. split.
    + apply odd3. exact ha.
    + assert (Hc0 : c mod 2 = 0) by (apply Nat.eqb_eq; exact E3).
      assert (Hsub : (c - a) mod 2 = 1)
        by (apply mod2_sub_even_odd; [exact hac | exact ha | exact Hc0]).
      exact (mod2_add4_of_odd (c - a) Hsub).
  - assert (Hc1 : c mod 2 = 1)
      by (apply mod2_eq_one; intro H0; rewrite H0 in E3; discriminate E3).
    assert (E1 : Nat.leb a c = true) by (apply Nat.leb_le; exact hac).
    assert (E2 : Nat.eqb (Nat.modulo a 2) 0 = false)
      by (apply Nat.eqb_neq; intro H0; rewrite H0 in ha; discriminate ha).
    assert (E3' : Nat.eqb (Nat.modulo c 2) 0 = false) by exact E3.
    assert (HH : step a c = Next (3 * a + 2) (c - a + 1))
      by (apply step_j; [exact E1 | exact E2 | exact E3']).
    rewrite HH in h. injection h as H1 H2. subst a' c'. split.
    + apply odd3_add2. exact ha.
    + assert (Hsub : (c - a) mod 2 = 0)
        by (apply mod2_sub_odd_odd; [exact hac | exact ha | exact Hc1]).
      exact (mod2_add1_of_even (c - a) Hsub).
Qed.

(** [L] steps keep [c] odd and flip [a]'s parity (the two parities differ),
    except rule [e] which lands on [c' = 1]. *)
Lemma L_step_odd (a c a' c' : nat) (hca : c < a) (hc : c mod 2 = 1)
    (h : step a c = Next a' c') :
    c' mod 2 = 1 /\ (c' = 1 \/ (a' + a) mod 2 = 1).
Proof.
  assert (E1 : Nat.leb a c = false) by (apply Nat.leb_gt; exact hca).
  destruct (orb (Nat.eqb (Nat.modulo c 4) 0) (Nat.eqb (Nat.modulo c 4) 2)) eqn:E4.
  - assert (H4 : c mod 4 = 0 \/ c mod 4 = 2).
    { destruct (proj1 (orb_true_iff _ _) E4) as [E | E].
      - left. apply Nat.eqb_eq. exact E.
      - right. apply Nat.eqb_eq. exact E. }
    rewrite (step_a a c E1 E4) in h. injection h as H1 H2. subst a' c'.
    exfalso. assert (Hc0 : c mod 2 = 0) by (apply mod2_of_mod4_even; exact H4).
    rewrite Hc0 in hc. discriminate hc.
  - assert (E4a : Nat.eqb (Nat.modulo c 4) 0 = false).
    { destruct (Nat.eqb (Nat.modulo c 4) 0) eqn:Ea; [| reflexivity].
      rewrite orb_true_l in E4. discriminate E4. }
    assert (E4b : Nat.eqb (Nat.modulo c 4) 2 = false).
    { destruct (Nat.eqb (Nat.modulo c 4) 2) eqn:Eb; [| reflexivity].
      rewrite orb_true_r in E4. discriminate E4. }
    assert (Hn0 : c mod 4 <> 0) by (apply Nat.eqb_neq; exact E4a).
    assert (Hn2 : c mod 4 <> 2) by (apply Nat.eqb_neq; exact E4b).
    destruct (Nat.eqb (Nat.modulo c 4) 1) eqn:E5.
    + assert (H5 : c mod 4 = 1) by (apply Nat.eqb_eq; exact E5).
      destruct (Nat.eqb a (c + 1)) eqn:E6.
      * rewrite (step_f a c E1 E4 E5 E6) in h. discriminate h.
      * assert (Hne : a <> c + 1) by (apply Nat.eqb_neq; exact E6).
        rewrite (step_b a c E1 E4 E5 E6) in h. injection h as H1 H2. subst a' c'.
        split.
        -- exact (three_mul_add5_odd ((c - 1) / 2) (half_mod2_of_mod4_one c H5)).
        -- right. exact (flip_two a c hca hc Hne).
    + destruct (Nat.eqb a (c + 1)) eqn:E6.
      * rewrite (step_halt1 a c E1 E4 E5 E6) in h. discriminate h.
      * destruct (Nat.eqb a (c + 2)) eqn:E7.
        -- rewrite (step_e a c E1 E4 E5 E6 E7) in h.
           injection h as H1 H2. subst a' c'. split.
           ++ reflexivity.
           ++ left. reflexivity.
        -- destruct (Nat.eqb a (c + 3)) eqn:E8.
           ++ rewrite (step_halt3 a c E1 E4 E5 E6 E7 E8) in h. discriminate h.
           ++ assert (Hn1 : c mod 4 <> 1) by (apply Nat.eqb_neq; exact E5).
              assert (H3 : c mod 4 = 3)
                by (apply mod4_eq_three; [exact Hn0 | exact Hn2 | exact Hn1]).
              assert (Hne1 : a <> c + 1) by (apply Nat.eqb_neq; exact E6).
              assert (Hne2 : a <> c + 2) by (apply Nat.eqb_neq; exact E7).
              assert (Hne3 : a <> c + 3) by (apply Nat.eqb_neq; exact E8).
              rewrite (step_c a c E1 E4 E5 E6 E7 E8) in h.
              injection h as H1 H2. subst a' c'. split.
              ** exact (three_mul_add8_odd ((c - 1) / 2) (half_mod2_of_mod4_three c H3)).
              ** right. exact (flip_four a c hca hc Hne1 Hne2 Hne3).
Qed.

(** An even [a] in the [J] region stops the halving run on the next step. *)
Lemma hrun_stops_of_even_le (c0 a c : nat) (hle : a <= c) (h2 : a mod 2 = 0) :
    hrun c0 1 a c = None.
Proof.
  assert (E2 : Nat.eqb (Nat.modulo a 2) 0 = true) by (apply Nat.eqb_eq; exact h2).
  assert (E1 : Nat.leb a c = true) by (apply Nat.leb_le; exact hle).
  destruct (Nat.eqb (Nat.modulo c 2) 0) eqn:E3.
  - cbn [hrun]. rewrite (step_g a c E1 E2 E3). reflexivity.
  - cbn [hrun]. rewrite (step_h a c E1 E2 E3). cbn. reflexivity.
Qed.

(** The exit at an [L]-phase close: a [J] state reached after [n] steps with
    even [a] cannot survive one more step. *)
Lemma hrun_stop_of_L_close (c0 n a c : nat)
    (hJ : fst (st c0 n a c) <= snd (st c0 n a c))
    (heven : fst (st c0 n a c) mod 2 = 0) :
    ~ HSurvives c0 (n + 1) a c.
Proof.
  intro hs.
  destruct hs as [x [y hx]].
  assert (hpre : HSurvives c0 n a c)
    by (apply (hsurvives_mono c0 n 1 a c); exists x, y; exact hx).
  destruct hpre as [A [B hA]].
  assert (Hst : st c0 n a c = (A, B)) by (apply st_hrun; exact hA).
  rewrite Hst in hJ, heven.
  change (A <= B) in hJ. change (A mod 2 = 0) in heven.
  assert (H1 : hrun c0 1 A B = Some (x, y)).
  { assert (H2 := hrun_add c0 n 1 a c A B hA). rewrite H2 in hx. exact hx. }
  assert (Hodd : A mod 2 = 1) by (apply (hrun_odd_of_le c0 0 A B x y H1 hJ)).
  rewrite Hodd in heven. discriminate heven.
Qed.

(** The tail's parity walk on the run's own orbit. *)
Lemma tail_step_odd (c0 i a c : nat)
    (hsurv : exists a' c', hrun c0 (i + 2) a c = Some (a', c')) :
    ((fst (st c0 i a c) <= snd (st c0 i a c) -> fst (st c0 i a c) mod 2 = 1 ->
        fst (st c0 (S i) a c) mod 2 = 1 /\ snd (st c0 (S i) a c) mod 2 = 1) /\
     (snd (st c0 i a c) < fst (st c0 i a c) -> snd (st c0 i a c) mod 2 = 1 ->
        snd (st c0 (S i) a c) mod 2 = 1 /\
        (snd (st c0 (S i) a c) = 1 \/
         (fst (st c0 (S i) a c) + fst (st c0 i a c)) mod 2 = 1))).
Proof.
  assert (h2 : HSurvives c0 (S i + 1) a c).
  { replace (S i + 1) with (i + 2) by lia. exact hsurv. }
  assert (h1 : HSurvives c0 (S i) a c)
    by (apply (hsurvives_mono c0 (S i) 1 a c h2)).
  assert (h1' : exists a' c', hrun c0 (S i) a c = Some (a', c')).
  { unfold HSurvives in h1. exact h1. }
  assert (hs := st_next c0 i a c h1').
  split.
  - intros hJ hodd. exact (J_step_odd _ _ _ _ hJ hodd hs).
  - intros hL hodd. exact (L_step_odd _ _ _ _ hL hodd hs).
Qed.

(** **Why the phase budget cannot count wrong-parity closes.**  The [L]-phase
    budget is downward closed in the phase length, so it bounds the *size* of a
    phase and says nothing about the parity of its length. *)
Lemma L_budget_down (n a c : nat)
    (h : 2 * c * 3 ^ (n + 1) <= 2 ^ (n + 1) * (a + 2 * c)) :
    2 * c * 3 ^ n <= 2 ^ n * (a + 2 * c).
Proof.
  replace (n + 1) with (S n) in h by lia.
  rewrite pow_succ_nat in h.
  rewrite pow_succ_nat in h.
  assert (h1 : 2 * c * (3 * 3 ^ n) = 3 * (2 * c * 3 ^ n)) by ring.
  assert (h2 : 2 * (2 ^ n) * (a + 2 * c) = 2 * (2 ^ n * (a + 2 * c))) by ring.
  rewrite h1, h2 in h.
  assert (h3 : 2 * (2 * c * 3 ^ n) <= 2 * (2 ^ n * (a + 2 * c))).
  { apply Nat.le_trans with (3 * (2 * c * 3 ^ n)); [| exact h].
    apply Nat.mul_le_mono_r. lia. }
  lia.
Qed.

(** **8h-c. The sharp bound on wrong-parity closes.** *)

(** A surviving run has no wrong-parity close: every [L] phase that closes on
    even [a] ends the run, so in a run of length [L] no state before the last
    one is a wrong-parity close.  A run of length [L] therefore has none before
    step [L], and at most one, the terminal one. *)
Lemma survives_forbids_wrong_close (c0 L a c a' c' : nat)
    (h : hrun c0 L a c = Some (a', c')) :
    forall k, k < L ->
      ~ (fst (st c0 k a c) <= snd (st c0 k a c) /\
         fst (st c0 k a c) mod 2 = 0).
Proof.
  intros k hk [hJ heven].
  assert (hL : (k + 1) + (L - (k + 1)) = L) by lia.
  assert (hsurv : HSurvives c0 ((k + 1) + (L - (k + 1))) a c).
  { rewrite hL. exists a', c'. exact h. }
  apply (hrun_stop_of_L_close c0 k a c hJ heven).
  apply (hsurvives_mono c0 (k + 1) (L - (k + 1)) a c hsurv).
Qed.

Print Assumptions mod2_two_mul_succ.
Print Assumptions mod2_add_even.
Print Assumptions mod2_add_odd_odd.
Print Assumptions mod2_add_even_odd.
Print Assumptions mod2_add4_of_odd.
Print Assumptions mod2_add1_of_even.
Print Assumptions mod2_sub_even_odd.
Print Assumptions mod2_sub_odd_odd.
Print Assumptions half_mod2_of_mod4_one.
Print Assumptions half_mod2_of_mod4_three.
Print Assumptions three_mul_add5_odd.
Print Assumptions three_mul_add8_odd.
Print Assumptions flip_two.
Print Assumptions flip_four.
Print Assumptions hrun_odd_of_le.
Print Assumptions J_step_odd.
Print Assumptions L_step_odd.
Print Assumptions hrun_stops_of_even_le.
Print Assumptions hrun_stop_of_L_close.
Print Assumptions tail_step_odd.
Print Assumptions L_budget_down.
Print Assumptions survives_forbids_wrong_close.
Print Assumptions div2_le.
Print Assumptions shallow_a_arith.
Print Assumptions shallow_b_arith.
Print Assumptions shallow_c_arith.
Print Assumptions mod4_eq_three.
Print Assumptions mod2_eq_one.
Print Assumptions odd3.
Print Assumptions odd3_add2.
Print Assumptions mod2_one_pos.
Print Assumptions le_three_half.
Print Assumptions le_three_half_pred.
Print Assumptions L_shallow_step.
Print Assumptions jrun_odd_step.
Print Assumptions jrun_odd.
Print Assumptions flips_le.
Print Assumptions phases_le.
Print Assumptions counting_budget_le.
Print Assumptions counting_budget_forces.

(** ** 7. Assumption audit                                             *)
(* ------------------------------------------------------------------ *)

Print Assumptions Q_step.
Print Assumptions run_Q.
Print Assumptions L_step.
Print Assumptions mul_pow3_succ.
Print Assumptions mul_pow2_succ.
Print Assumptions pow2_mul_two.
Print Assumptions Ssum_le.
Print Assumptions Ssum_two_le.
Print Assumptions L_budget.
Print Assumptions L_phase_budget.
Print Assumptions pow2_le_pow3.
Print Assumptions pow3_mono.
Print Assumptions pow_add_l.
Print Assumptions pow_mul_gen.
Print Assumptions nine_pow_ge.
Print Assumptions pow2_mono.
Print Assumptions pow2_lt.
Print Assumptions L_phase_le_878.
Print Assumptions three_pow_gt.
Print Assumptions L_phase_le_791.
Print Assumptions J_a_closed.
Print Assumptions J_Q_closed.
Print Assumptions J_phase_budget.
Print Assumptions three_pow_dominates.
Print Assumptions J_phase_le_293.
Print Assumptions survives_le_of_budget.
Print Assumptions postJ_survives_le_10000.
Print Assumptions hrun_S.
Print Assumptions Q_step_le.
Print Assumptions hrun_Q_le.
Print Assumptions HBudget_mono.
Print Assumptions hbudget_of_length.
Print Assumptions hbudget_30000_of_le_3333.
Print Assumptions halvingTimeBound_of_residual.
Print Assumptions hrun_add.
Print Assumptions hrun_Q.
Print Assumptions hsurvives_le_of_budget.
Print Assumptions postJ_halving_le_10000.
Print Assumptions hsurvives_5_1.
Print Assumptions hrun_stops_5_1.
Print Assumptions not_hsurvives_5_1.

(* ------------------------------------------------------------------ *)
(** ** 9. The phase-count bound NL <= 7, NJ <= 6 is false              *)
(* ------------------------------------------------------------------ *)

(** The region of a state as a computable boolean: [true] in the [J] region
    ([a <= c]). *)
Definition regB (a c : nat) : bool := Nat.leb a c.

(** **The phase counter.**  Walk [step] from [(a, c)] for at most [n] steps,
    stopping exactly where [hrun] stops (a true halt, [a' = 1], or
    [2*c' <= c0]), and count the phases of the states the run visits: the first
    state starts a phase, and every step whose result lies in the other region
    starts another.  [fst] is the number of [L] phases ([c < a]), [snd] the
    number of [J] phases ([a <= c]). *)
Fixpoint pcnt (c0 n a c : nat) {struct n} : nat * nat :=
  match n with
  | O => if regB a c then (0, 1) else (1, 0)
  | S n' =>
      match step a c with
      | Halt => if regB a c then (0, 1) else (1, 0)
      | Next a' c' =>
          if orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0)
          then (if regB a c then (0, 1) else (1, 0))
          else if regB a c then
                 (if regB a' c' then pcnt c0 n' a' c'
                  else (fst (pcnt c0 n' a' c'), S (snd (pcnt c0 n' a' c'))))
               else
                 (if regB a' c' then (S (fst (pcnt c0 n' a' c')), snd (pcnt c0 n' a' c'))
                  else pcnt c0 n' a' c')
      end
  end.

(** **The witness's phase counts.**  The halving run from [(2*3^7 - 1, 24)]
    visits 8 [L] phases and 8 [J] phases. *)
Lemma witness_phase_counts : pcnt 24 41 (2 * 3 ^ 7 - 1) 24 = (8, 8).
Proof. vm_compute. reflexivity. Qed.

(** The witness run survives 40 steps and stops on the next one. *)
Lemma witness_run_stops :
    hrun 24 40 (2 * 3 ^ 7 - 1) 24 = Some (782, 1937) /\
    hrun 24 41 (2 * 3 ^ 7 - 1) 24 = None.
Proof. split; vm_compute; reflexivity. Qed.

(** **[NL <= 7] and [NJ <= 6] are false on the family.** *)
Lemma phase_count_bound_false :
  exists k c a' c' : nat,
    k <= 292 /\ 1 <= c /\ c < 2 * 3 ^ k /\
    hrun c 40 (2 * 3 ^ k - 1) c = Some (a', c') /\
    7 < fst (pcnt c 41 (2 * 3 ^ k - 1) c) /\
    6 < snd (pcnt c 41 (2 * 3 ^ k - 1) c).
Proof.
  exists 7, 24, 782, 1937.
  repeat split; vm_compute; try reflexivity; try lia.
Qed.

(** Eight [L] phases and eight [J] phases overflow the residual window whatever
    the phase lengths are: [878*8 + 293*8 = 9368 > 9209]. *)
Lemma counting_budget_le_8 (NL NJ : nat) (hL : 8 <= NL) (hJ : 8 <= NJ) :
    9209 < 878 * NL + 293 * NJ.
Proof.
  apply Nat.lt_le_trans with (m := 878 * 8 + 293 * 8).
  - vm_compute. lia.
  - apply Nat.add_le_mono; apply Nat.mul_le_mono_l; assumption.
Qed.

(** The witness's own charge exceeds [9209]: the counting route fails on a real
    family run, not only on hypothetical counts. *)
Lemma witness_charge_exceeds :
    9209 < 878 * fst (pcnt 24 41 (2 * 3 ^ 7 - 1) 24)
          + 293 * snd (pcnt 24 41 (2 * 3 ^ 7 - 1) 24).
Proof. vm_compute. lia. Qed.

Print Assumptions L_drop.
Print Assumptions L_grow_a.
Print Assumptions L_grow_b.
Print Assumptions L_grow_c.
Print Assumptions L_step.
Print Assumptions regB.
Print Assumptions pcnt.
Print Assumptions witness_phase_counts.
Print Assumptions witness_run_stops.
Print Assumptions phase_count_bound_false.
Print Assumptions counting_budget_le_8.
Print Assumptions witness_charge_exceeds.

(* ------------------------------------------------------------------ *)
(** ** 10. The retargeted residual: per-phase length at each phase's own
    start                                                             *)
(* ------------------------------------------------------------------ *)

(** Section 8f charged every [L] phase [878] and every [j] phase [293].
    Both are post-[j] constants: [L_phase_le_878] needs
    [a_0 <= 2*3^292], which fails from the second phase on
    ([phase_two_breaks]), and section 9 showed the counts that actually
    occur are already too large for any [878*NL + 293*NJ] charge.  What a
    composition needs instead is a charge every phase start can pay: the
    phase's length read off its *own* [(a_0, c_0)].

    The two budgets already say exactly that, in ratio form:

    - an [L] phase of length [n] from [(a_0,c_0)]:
      [2*c_0*3^n <= 2^n*(a_0+2*c_0)];
    - a [j] phase of length [m] from [(a_0,c_0)]:
      [3^m*(a_0+1) <= a_0+2*c_0+4*m].

    [lLen] and [jLen] below are those ratios read as the largest *integer*
    number of steps they allow, by bounded search.  [l_phase_len_at] and
    [j_phase_len_at] prove a real phase of a halving run is at most that
    long -- unconditionally, at *every* start, with no cap like [878]/[293].

    [PhaseLedger] is the retargeted residual: a statement about a *sum*,
    not a cap.  [halvingTimeBound_of_phase_ledger] proves
    [PhaseLedger -> T <= 10000], so what is left is exactly the sum of the
    own-start charges over the phases of a family run. *)

(** [L] admissibility of a phase length [n] at its own start [(a0,c0)]. *)
Definition lAdm (a0 c0 n : nat) : Prop := 2 * c0 * 3 ^ n <= 2 ^ n * (a0 + 2 * c0).

(** [j] admissibility of a phase length [m] at its own start [(a0,c0)]. *)
Definition jAdm (a0 c0 m : nat) : Prop := 3 ^ m * (a0 + 1) <= a0 + 2 * c0 + 4 * m.

(** Bounded search for the largest [L]-admissible length at [(a0,c0)]. *)
Fixpoint lScan (a0 c0 fuel k : nat) {struct fuel} : nat :=
  match fuel with
  | O => k
  | S f =>
      if Nat.leb (2 * c0 * 3 ^ (S k)) (2 ^ (S k) * (a0 + 2 * c0))
      then lScan a0 c0 f (S k)
      else k
  end.

(** Bounded search for the largest [j]-admissible length at [(a0,c0)]. *)
Fixpoint jScan (a0 c0 fuel k : nat) {struct fuel} : nat :=
  match fuel with
  | O => k
  | S f =>
      if Nat.leb (3 ^ (S k) * (a0 + 1)) (a0 + 2 * c0 + 4 * (S k))
      then jScan a0 c0 f (S k)
      else k
  end.

(** The sharp [L] charge: [log_{3/2}((a0+2*c0)/(2*c0))] as an integer. *)
Definition lLen (a0 c0 : nat) : nat := lScan a0 c0 (a0 + 2 * c0 + 2) 0.

(** The sharp [j] charge: [log_3] of the [j] budget, as an integer. *)
Definition jLen (a0 c0 : nat) : nat := jScan a0 c0 (a0 + 2 * c0 + 2) 1.

(** [L] admissibility is downward closed in the phase length. *)
Lemma lAdm_down (a0 c0 : nat) :
    forall n m, lAdm a0 c0 n -> m <= n -> lAdm a0 c0 m.
Proof.
  induction n as [|n ih]; intros m h hm.
  - assert (m = 0) by lia. subst m. exact h.
  - destruct (Nat.lt_ge_cases m (S n)) as [hlt | hge].
    + apply ih.
      * replace (S n) with (n + 1) in h by lia.
        unfold lAdm in h. unfold lAdm.
        apply (L_budget_down n a0 c0). exact h.
      * lia.
    + assert (m = S n) by lia. subst m. exact h.
Qed.

(** [j] admissibility is downward closed, from [a0 >= 2].  The [j] budget's
    right-hand side grows with [m], so this is not a monotonicity of the
    left-hand side alone: one step down costs [2] and
    [3^k*(a0+1) >= 4]. *)
Lemma jAdm_step_down (a0 c0 k : nat) (ha : 2 <= a0)
    (h : jAdm a0 c0 (S k)) : jAdm a0 c0 k.
Proof.
  unfold jAdm in *.
  assert (hX : 2 <= 3 ^ k * (a0 + 1)).
  { replace 2 with (1 * 2) by lia.
    apply Nat.mul_le_mono; [ apply pow3_pos | lia ]. }
  assert (hE : 3 * (3 ^ k * (a0 + 1)) = 3 ^ (S k) * (a0 + 1)).
  { rewrite pow_succ_nat. ring. }
  rewrite <- hE in h.
  lia.
Qed.

Lemma jAdm_down (a0 c0 : nat) (ha : 2 <= a0) :
    forall n m, jAdm a0 c0 n -> m <= n -> jAdm a0 c0 m.
Proof.
  induction n as [|n ih]; intros m h hm.
  - assert (m = 0) by lia. subst m. exact h.
  - destruct (Nat.lt_ge_cases m (S n)) as [hlt | hge].
    + apply ih.
      * apply (jAdm_step_down a0 c0 n ha). exact h.
      * lia.
    + assert (m = S n) by lia. subst m. exact h.
Qed.

Lemma lScan_ge (a0 c0 : nat) : forall fuel k, k <= lScan a0 c0 fuel k.
Proof.
  induction fuel as [|fuel ih]; intros k.
  - cbn [lScan]. lia.
  - cbn [lScan].
    destruct (Nat.leb (2 * c0 * 3 ^ (S k)) (2 ^ (S k) * (a0 + 2 * c0))).
    + apply Nat.le_trans with (S k); [ lia | apply ih ].
    + lia.
Qed.

Lemma jScan_ge (a0 c0 : nat) : forall fuel k, k <= jScan a0 c0 fuel k.
Proof.
  induction fuel as [|fuel ih]; intros k.
  - cbn [jScan]. lia.
  - cbn [jScan].
    destruct (Nat.leb (3 ^ (S k) * (a0 + 1)) (a0 + 2 * c0 + 4 * (S k))).
    + apply Nat.le_trans with (S k); [ lia | apply ih ].
    + lia.
Qed.

(** The bounded scan reaches every admissible length it has fuel for. *)
Lemma lScan_reaches (a0 c0 : nat) (fuel : nat) :
    forall k n, lAdm a0 c0 n -> k <= n -> n - k <= fuel ->
                n <= lScan a0 c0 fuel k.
Proof.
  induction fuel as [|fuel ih]; intros k n hadm hkn hfuel.
  - cbn [lScan]. assert (n = k) by lia. subst n. lia.
  - cbn [lScan].
    destruct (Nat.leb (2 * c0 * 3 ^ (S k)) (2 ^ (S k) * (a0 + 2 * c0))) eqn:E.
    + destruct (Nat.lt_ge_cases k n) as [hlt | hge].
      * apply (ih (S k) n); [ exact hadm | lia | lia ].
      * assert (k = n) by lia. subst n.
        apply Nat.le_trans with (S k); [ lia | apply lScan_ge ].
    + assert (Hf : ~ lAdm a0 c0 (S k)).
      { unfold lAdm. intros hS.
        assert (Hlt := leb_false_lt _ _ E). lia. }
      assert (Hnk : n <= k).
      { destruct (Nat.lt_ge_cases k n) as [hlt | hge].
        - exfalso. apply Hf. apply (lAdm_down a0 c0 n); [ exact hadm | lia ].
        - lia. }
      exact Hnk.
Qed.

Lemma jScan_reaches (a0 c0 : nat) (ha : 2 <= a0) (fuel : nat) :
    forall k n, jAdm a0 c0 n -> k <= n -> n - k <= fuel ->
                n <= jScan a0 c0 fuel k.
Proof.
  induction fuel as [|fuel ih]; intros k n hadm hkn hfuel.
  - cbn [jScan]. assert (n = k) by lia. subst n. lia.
  - cbn [jScan].
    destruct (Nat.leb (3 ^ (S k) * (a0 + 1)) (a0 + 2 * c0 + 4 * (S k))) eqn:E.
    + destruct (Nat.lt_ge_cases k n) as [hlt | hge].
      * apply (ih (S k) n); [ exact hadm | lia | lia ].
      * assert (k = n) by lia. subst n.
        apply Nat.le_trans with (S k); [ lia | apply jScan_ge ].
    + assert (Hf : ~ jAdm a0 c0 (S k)).
      { unfold jAdm. intros hS.
        assert (Hlt := leb_false_lt _ _ E). lia. }
      assert (Hnk : n <= k).
      { destruct (Nat.lt_ge_cases k n) as [hlt | hge].
        - exfalso. apply Hf. apply (jAdm_down a0 c0 ha n); [ exact hadm | lia ].
        - lia. }
      exact Hnk.
Qed.

(** The sharp [L] charge bounds every admissible [L] length. *)
Lemma lLen_spec (a0 c0 n : nat) (hc : 1 <= c0) (h : lAdm a0 c0 n) :
    n <= lLen a0 c0.
Proof.
  assert (hlin : n * c0 <= a0 + 2 * c0)
    by (apply (L_phase_len_c0 n a0 c0 hc h)).
  assert (hfuel : n <= a0 + 2 * c0 + 2).
  { destruct n as [|n'].
    - lia.
    - assert (hle1 : S n' * 1 <= S n' * c0)
        by (apply Nat.mul_le_mono_l; exact hc).
      rewrite Nat.mul_1_r in hle1. lia. }
  unfold lLen.
  exact (lScan_reaches a0 c0 (a0 + 2 * c0 + 2) 0 n h (ltac:(lia)) (ltac:(lia))).
Qed.

(** [4*m <= 2*(m*a0)] for [a0 >= 2]. *)
Lemma four_m_le (m a0 : nat) (ha : 2 <= a0) : 4 * m <= 2 * (m * a0).
Proof.
  assert (h1 : m * 2 <= m * a0) by (apply Nat.mul_le_mono_l; exact ha).
  assert (h2 : 2 * (m * 2) <= 2 * (m * a0)) by (apply Nat.mul_le_mono_l; exact h1).
  assert (e : 2 * (m * 2) = 4 * m) by ring.
  rewrite e in h2. exact h2.
Qed.

(** The sharp [j] charge bounds every admissible [j] length. *)
Lemma jLen_spec (a0 c0 m : nat) (ha : 2 <= a0) (hm : 1 <= m)
    (h : jAdm a0 c0 m) : m <= jLen a0 c0.
Proof.
  assert (hlin : 2 * (m * a0) <= a0 + 2 * c0 + 2 * m)
    by (apply (J_phase_len_own m a0 c0 hm ltac:(lia) h)).
  assert (h4 := four_m_le m a0 ha).
  assert (hfuel : m - 1 <= a0 + 2 * c0 + 2) by lia.
  unfold jLen.
  exact (jScan_reaches a0 c0 ha (a0 + 2 * c0 + 2) 1 m h hm hfuel).
Qed.

(** An [L] phase of a halving run, at its own start [(a0,c0)]: the run
    survives all [n] steps, the orbit is in [L] ([c < a]) throughout, and
    rule [e] never fires.  [1 <= c0] holds at every state of a halving run
    from the family: no rule drives [c] to [0]. *)
Record LPhaseAt (C n a0 c0 : nat) : Prop := {
  lhc : 1 <= c0;
  lsurv : forall i, i <= n -> exists a' c', hrun C i a0 c0 = Some (a', c');
  lreg : forall i, i < n -> snd (st C i a0 c0) < fst (st C i a0 c0);
  lne : forall i, i < n -> fst (st C i a0 c0) <> snd (st C i a0 c0) + 2
}.

(** A [j] phase of a halving run, at its own start: every step is rule [j]. *)
Record JPhaseAt (C m a0 c0 : nat) : Prop := {
  jha : 2 <= a0;
  jhsurv : forall i, i <= m -> exists a' c', hrun C i a0 c0 = Some (a', c');
  jhreg : forall i, i < m -> fst (st C i a0 c0) <= snd (st C i a0 c0);
  jhj : forall i, i < m ->
          step (fst (st C i a0 c0)) (snd (st C i a0 c0))
            = Next (3 * fst (st C i a0 c0) + 2)
                   (snd (st C i a0 c0) - fst (st C i a0 c0) + 1)
}.

(** **The per-phase length bound at its own start, [L] region.**  A real
    [L] phase of a halving run, of length [n] from [(a_0,c_0)], satisfies
    [n <= lLen a_0 c_0] -- the sharp [log_{3/2}] charge of its own start,
    not the post-[j] cap [878]. *)
Lemma l_phase_len_at (C n a0 c0 : nat) (h : LPhaseAt C n a0 c0) :
    n <= lLen a0 c0.
Proof.
  destruct h as [hc hsurv hreg hne].
  assert (hstep : forall i, i < n ->
      step (fst (st C i a0 c0)) (snd (st C i a0 c0))
        = Next (fst (st C (S i) a0 c0)) (snd (st C (S i) a0 c0)))
    by (intros i hi; apply (st_next C i a0 c0); exact (hsurv (S i) (ltac:(lia)))).
  assert (hdrop : forall i, i < n ->
      fst (st C (S i) a0 c0) + snd (st C i a0 c0) <= fst (st C i a0 c0))
    by (intros i hi;
        exact (proj1 (L_step _ _ _ _ (hreg i hi) (hne i hi) (hstep i hi)))).
  assert (hgrow : forall i, i < n ->
      3 * snd (st C i a0 c0) <= 2 * snd (st C (S i) a0 c0))
    by (intros i hi;
        exact (proj2 (L_step _ _ _ _ (hreg i hi) (hne i hi) (hstep i hi)))).
  assert (hb := L_phase_budget (fun i => fst (st C i a0 c0))
                               (fun i => snd (st C i a0 c0)) n hdrop hgrow).
  cbn in hb.
  exact (lLen_spec a0 c0 n hc hb).
Qed.

(** **The per-phase length bound at its own start, [J] region.**  A real [j]
    phase of a halving run, of length [m] from [(a_0,c_0)], satisfies
    [m <= jLen a_0 c_0] -- the sharp [log_3] charge of its own start, not
    the post-[j] cap [293]. *)
Lemma j_phase_len_at (C m a0 c0 : nat) (hm : 1 <= m) (h : JPhaseAt C m a0 c0) :
    m <= jLen a0 c0.
Proof.
  destruct h as [ha hsurv hreg hj].
  assert (hstep : forall i, i < m ->
      step (fst (st C i a0 c0)) (snd (st C i a0 c0))
        = Next (fst (st C (S i) a0 c0)) (snd (st C (S i) a0 c0)))
    by (intros i hi; apply (st_next C i a0 c0); exact (hsurv (S i) (ltac:(lia)))).
  assert (hA : forall i, i < m ->
      fst (st C (S i) a0 c0) = 3 * fst (st C i a0 c0) + 2).
  { intros i hi. assert (hsi := hstep i hi). rewrite (hj i hi) in hsi.
    injection hsi as H1 H2. exact (eq_sym H1). }
  assert (hC : forall i, i < m ->
      snd (st C (S i) a0 c0) = snd (st C i a0 c0) - fst (st C i a0 c0) + 1).
  { intros i hi. assert (hsi := hstep i hi). rewrite (hj i hi) in hsi.
    injection hsi as H1 H2. exact (eq_sym H2). }
  assert (hb := J_phase_budget (fun i => fst (st C i a0 c0))
                               (fun i => snd (st C i a0 c0)) m hm
                 (fun i hi => conj (hA i hi) (hC i hi))
                 (fun i hi => hreg i hi)).
  cbn in hb.
  exact (jLen_spec a0 c0 m ha hm hb).
Qed.

(** The own-start charge of a phase: [lLen] in [L], [jLen] in [J]. *)
Definition phaseCharge (a c : nat) : nat :=
  if Nat.leb (S c) a then lLen a c else jLen a c.

Lemma phaseCharge_L (a c : nat) (h : c < a) : phaseCharge a c = lLen a c.
Proof.
  unfold phaseCharge.
  assert (E : Nat.leb (S c) a = true)
    by (apply (proj2 (Nat.leb_le (S c) a)); lia).
  rewrite E. reflexivity.
Qed.

Lemma phaseCharge_J (a c : nat) (h : a <= c) : phaseCharge a c = jLen a c.
Proof.
  unfold phaseCharge.
  assert (E : Nat.leb (S c) a = false).
  { destruct (Nat.leb (S c) a) eqn:E; [| reflexivity].
    assert (H : S c <= a) by (apply (proj1 (Nat.leb_le (S c) a)); exact E).
    lia. }
  rewrite E. reflexivity.
Qed.

Lemma ssum_mono (f g : nat -> nat) (N : nat)
    (h : forall i, i < N -> f i <= g i) : ssum f N <= ssum g N.
Proof.
  induction N as [|N ih].
  - cbn. lia.
  - rewrite ssum_succ, ssum_succ.
    apply Nat.add_le_mono.
    + apply ih. intros i hi. apply h. lia.
    + apply h. lia.
Qed.

(** **The retargeted residual: the phase ledger.**  Every post-[j] family
    member's halving run admits a phase-aligned cut, every phase an
    [LPhaseAt] or a [JPhaseAt] at its own start, whose own-start charges
    sum to at most [10000].  The sum is the only content: the cut is the
    run's own phase decomposition ([pcnt] in section 9 shows the phases
    are disjoint and cover the run), and [phaseCharge] at a phase's own
    start is the sharp charge of [l_phase_len_at]/[j_phase_len_at]. *)
Definition PhaseLedger : Prop :=
  forall (k c n : nat), k <= 292 -> 1 <= c -> c < 2 * 3 ^ k ->
    HSurvives c n (2 * 3 ^ k - 1) c ->
    exists (b : nat -> nat) (N : nat),
      b 0 = 0 /\ b N = n /\
      (forall i, i < N -> b i < b (S i)) /\
      (forall i, i < N ->
        LPhaseAt c (cutLen b i) (fst (st c (b i) (2 * 3 ^ k - 1) c))
                                 (snd (st c (b i) (2 * 3 ^ k - 1) c)) \/
        JPhaseAt c (cutLen b i) (fst (st c (b i) (2 * 3 ^ k - 1) c))
                                 (snd (st c (b i) (2 * 3 ^ k - 1) c))) /\
      ssum (fun i => phaseCharge (fst (st c (b i) (2 * 3 ^ k - 1) c))
                                 (snd (st c (b i) (2 * 3 ^ k - 1) c))) N <= 10000.

(** **[T <= 10000] from the phase ledger.**  Pure bookkeeping: the cut's
    phase lengths add up to the run length ([ssum_cutLen]), each is at most
    its own start's charge ([l_phase_len_at], [j_phase_len_at]), and the
    charges sum to at most [10000].  No phase *count* is used and no fixed
    cap appears. *)
Theorem halvingTimeBound_of_phase_ledger (h : PhaseLedger) : HalvingTimeBound.
Proof.
  unfold HalvingTimeBound, HalvingTimeLe.
  intros k c n hk hc hclt hn.
  destruct (h k c n hk hc hclt hn) as
    [b [N [hb0 [hbN [hmono [hphase hfit]]]]]].
  assert (hlen : forall i, i < N ->
      cutLen b i <= phaseCharge (fst (st c (b i) (2 * 3 ^ k - 1) c))
                                (snd (st c (b i) (2 * 3 ^ k - 1) c))).
  { intros i hi.
    assert (hpos : 0 < cutLen b i)
      by (unfold cutLen; assert (hb := hmono i hi); lia).
    destruct (hphase i hi) as [hL | hJ].
    - assert (hlt : snd (st c (b i) (2 * 3 ^ k - 1) c)
                     < fst (st c (b i) (2 * 3 ^ k - 1) c))
        by (apply (lreg _ _ _ _ hL 0 hpos)).
      rewrite (phaseCharge_L _ _ hlt).
      exact (l_phase_len_at c (cutLen b i) _ _ hL).
    - assert (hle : fst (st c (b i) (2 * 3 ^ k - 1) c)
                    <= snd (st c (b i) (2 * 3 ^ k - 1) c))
        by (apply (jhreg _ _ _ _ hJ 0 hpos)).
      rewrite (phaseCharge_J _ _ hle).
      exact (j_phase_len_at c (cutLen b i) _ _ hpos hJ). }
  assert (hsum : ssum (cutLen b) N = n).
  { rewrite (ssum_cutLen b N (fun i hi => ltac:(pose proof (hmono i hi); lia))).
    rewrite hbN, hb0. lia. }
  assert (hmono_sum := ssum_mono (cutLen b)
    (fun i => phaseCharge (fst (st c (b i) (2 * 3 ^ k - 1) c))
                          (snd (st c (b i) (2 * 3 ^ k - 1) c))) N hlen).
  rewrite hsum in hmono_sum.
  lia.
Qed.

Print Assumptions lAdm.
Print Assumptions jAdm.
Print Assumptions lScan.
Print Assumptions jScan.
Print Assumptions lLen.
Print Assumptions jLen.
Print Assumptions lAdm_down.
Print Assumptions jAdm_step_down.
Print Assumptions jAdm_down.
Print Assumptions lScan_ge.
Print Assumptions jScan_ge.
Print Assumptions lScan_reaches.
Print Assumptions jScan_reaches.
Print Assumptions lLen_spec.
Print Assumptions four_m_le.
Print Assumptions jLen_spec.
Print Assumptions LPhaseAt.
Print Assumptions JPhaseAt.
Print Assumptions l_phase_len_at.
Print Assumptions j_phase_len_at.
Print Assumptions phaseCharge.
Print Assumptions phaseCharge_L.
Print Assumptions phaseCharge_J.
Print Assumptions ssum_mono.
Print Assumptions PhaseLedger.
Print Assumptions halvingTimeBound_of_phase_ledger.

(* ------------------------------------------------------------------ *)
(** ** 11. Near states stop at once                                     *)
(* ------------------------------------------------------------------ *)

(** An [L] step replaces [a] by [a - c - r], so a *small drop* -- the only way
    the ratio [a/c] of a phase start can collapse -- can only happen when
    [a - c] is small.  This section proves that a near state cannot be
    survived: for [2 <= c0], no state with [c < a <= c + 3] lives two halving
    steps.  With [hrun_stops_of_even_le] this leaves [a = c + 4] with [c mod 4]
    even as the only near-state case that can continue. *)

(** [hrun] at length two: a halting step ends it. *)
Lemma hrun_two_halt (c0 a c : nat) (hs : step a c = Halt) :
    hrun c0 2 a c = None.
Proof.
  rewrite hrun_S, hs. reflexivity.
Qed.

(** [hrun] at length two: a next state that passes the stop test ends it. *)
Lemma hrun_two_stop (c0 a c a' c' : nat) (hs : step a c = Next a' c')
    (hstop : a' = 1 \/ 2 * c' <= c0) : hrun c0 2 a c = None.
Proof.
  assert (E : orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0) = true).
  { apply orb_true_iff. destruct hstop as [h | h].
    - left. apply Nat.eqb_eq. exact h.
    - right. apply Nat.leb_le. exact h. }
  rewrite hrun_S, hs. rewrite E. reflexivity.
Qed.

(** [hrun] at length two: a next state that stops in one step ends it. *)
Lemma hrun_two_step (c0 a c a' c' : nat) (hs : step a c = Next a' c')
    (h : hrun c0 1 a' c' = None) : hrun c0 2 a c = None.
Proof.
  destruct (orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0)) eqn:E.
  - rewrite hrun_S, hs. rewrite E. reflexivity.
  - rewrite hrun_S, hs. rewrite E. exact h.
Qed.

(** [c mod 4 = 0] satisfies the rule-[a] test. *)
Lemma orb_mod4_zero (c : nat) (h : c mod 4 = 0) :
    orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true.
Proof. apply orb_true_iff. left. apply Nat.eqb_eq. exact h. Qed.

(** [c mod 4 = 2] satisfies the rule-[a] test. *)
Lemma orb_mod4_two (c : nat) (h : c mod 4 = 2) :
    orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true.
Proof. apply orb_true_iff. right. apply Nat.eqb_eq. exact h. Qed.

(** [c mod 4] odd fails the rule-[a] test. *)
Lemma orb_mod4_false (c : nat) (h0 : c mod 4 <> 0) (h2 : c mod 4 <> 2) :
    orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false.
Proof.
  assert (A : Nat.eqb (c mod 4) 0 = false) by (apply Nat.eqb_neq; exact h0).
  assert (B : Nat.eqb (c mod 4) 2 = false) by (apply Nat.eqb_neq; exact h2).
  rewrite A, B. reflexivity.
Qed.

(** **A near state stops in at most two steps.**  For [2 <= c0], no state with
    [c < a <= c + 3] survives two halving steps: the [L]-region rules either
    halt ([a = c+1], [a = c+3]), pass the stop test, or land on [a' = 0] or
    [a' = 2] in the [J] region, which [hrun_stops_of_even_le] kills. *)
Lemma hrun_near (c0 a c : nat) (hc0 : 2 <= c0) (hm : c < a) (h3 : a <= c + 3) :
    hrun c0 2 a c = None.
Proof.
  assert (E1c : Nat.leb a c = false) by (apply Nat.leb_gt; lia).
  assert (hm4 : c mod 4 = 0 \/ c mod 4 = 1 \/ c mod 4 = 2 \/ c mod 4 = 3).
  { pose proof (Nat.mod_upper_bound c 4 (ltac:(lia))). lia. }
  assert (hd : a = c + 1 \/ a = c + 2 \/ a = c + 3) by lia.
  destruct hd as [hd | [hd | hd]].
  - (* a = c + 1 *)
    subst a.
    destruct hm4 as [h4 | [h4 | [h4 | h4]]].
    + (* c mod 4 = 0: rule a, a' = 0, J region *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true)
        by (apply orb_mod4_zero; exact h4).
      assert (hstep : step (c + 1) c = Next 0 (3 * (c / 2) + 2)).
      { rewrite (step_a (c + 1) c E1c E4).
        replace ((c + 1) - c - 1) with 0 by lia. reflexivity. }
      apply (hrun_two_step c0 (c + 1) c 0 (3 * (c / 2) + 2) hstep).
      apply (hrun_stops_of_even_le c0 0 (3 * (c / 2) + 2)); [lia | reflexivity].
    + (* c mod 4 = 1: rule f, halt *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
        by (apply orb_mod4_false; lia).
      assert (E5 : Nat.eqb (c mod 4) 1 = true) by (apply Nat.eqb_eq; exact h4).
      assert (E6 : Nat.eqb (c + 1) (c + 1) = true) by (apply Nat.eqb_eq; reflexivity).
      exact (hrun_two_halt c0 (c + 1) c (step_f (c + 1) c E1c E4 E5 E6)).
    + (* c mod 4 = 2: rule a, a' = 0 *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true)
        by (apply orb_mod4_two; exact h4).
      assert (hstep : step (c + 1) c = Next 0 (3 * (c / 2) + 2)).
      { rewrite (step_a (c + 1) c E1c E4).
        replace ((c + 1) - c - 1) with 0 by lia. reflexivity. }
      apply (hrun_two_step c0 (c + 1) c 0 (3 * (c / 2) + 2) hstep).
      apply (hrun_stops_of_even_le c0 0 (3 * (c / 2) + 2)); [lia | reflexivity].
    + (* c mod 4 = 3: rule halt1, halt *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
        by (apply orb_mod4_false; lia).
      assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
      assert (E6 : Nat.eqb (c + 1) (c + 1) = true) by (apply Nat.eqb_eq; reflexivity).
      exact (hrun_two_halt c0 (c + 1) c (step_halt1 (c + 1) c E1c E4 E5 E6)).
  - (* a = c + 2 *)
    subst a.
    destruct hm4 as [h4 | [h4 | [h4 | h4]]].
    + (* c mod 4 = 0: rule a, a' = 1, stop test *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true)
        by (apply orb_mod4_zero; exact h4).
      assert (hstep : step (c + 2) c = Next 1 (3 * (c / 2) + 2)).
      { rewrite (step_a (c + 2) c E1c E4).
        replace ((c + 2) - c - 1) with 1 by lia. reflexivity. }
      exact (hrun_two_stop c0 (c + 2) c 1 (3 * (c / 2) + 2) hstep (or_introl eq_refl)).
    + (* c mod 4 = 1: rule b, a' = 0 *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
        by (apply orb_mod4_false; lia).
      assert (E5 : Nat.eqb (c mod 4) 1 = true) by (apply Nat.eqb_eq; exact h4).
      assert (E6 : Nat.eqb (c + 2) (c + 1) = false) by (apply Nat.eqb_neq; lia).
      assert (hstep : step (c + 2) c = Next 0 (3 * ((c - 1) / 2) + 5)).
      { rewrite (step_b (c + 2) c E1c E4 E5 E6).
        replace ((c + 2) - c - 2) with 0 by lia. reflexivity. }
      apply (hrun_two_step c0 (c + 2) c 0 (3 * ((c - 1) / 2) + 5) hstep).
      apply (hrun_stops_of_even_le c0 0 (3 * ((c - 1) / 2) + 5)); [lia | reflexivity].
    + (* c mod 4 = 2: rule a, a' = 1, stop test *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true)
        by (apply orb_mod4_two; exact h4).
      assert (hstep : step (c + 2) c = Next 1 (3 * (c / 2) + 2)).
      { rewrite (step_a (c + 2) c E1c E4).
        replace ((c + 2) - c - 1) with 1 by lia. reflexivity. }
      exact (hrun_two_stop c0 (c + 2) c 1 (3 * (c / 2) + 2) hstep (or_introl eq_refl)).
    + (* c mod 4 = 3: rule e, c' = 1, stop test via c0 >= 2 *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
        by (apply orb_mod4_false; lia).
      assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
      assert (E6 : Nat.eqb (c + 2) (c + 1) = false) by (apply Nat.eqb_neq; lia).
      assert (E7 : Nat.eqb (c + 2) (c + 2) = true) by (apply Nat.eqb_eq; reflexivity).
      assert (hstep : step (c + 2) c = Next (3 * c + 8) 1).
      { exact (step_e (c + 2) c E1c E4 E5 E6 E7). }
      assert (hstop2 : 2 * 1 <= c0) by lia.
      exact (hrun_two_stop c0 (c + 2) c (3 * c + 8) 1 hstep (or_intror hstop2)).
  - (* a = c + 3 *)
    subst a.
    destruct hm4 as [h4 | [h4 | [h4 | h4]]].
    + (* c mod 4 = 0: rule a, a' = 2 *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true)
        by (apply orb_mod4_zero; exact h4).
      assert (hstep : step (c + 3) c = Next 2 (3 * (c / 2) + 2)).
      { rewrite (step_a (c + 3) c E1c E4).
        replace ((c + 3) - c - 1) with 2 by lia. reflexivity. }
      apply (hrun_two_step c0 (c + 3) c 2 (3 * (c / 2) + 2) hstep).
      apply (hrun_stops_of_even_le c0 2 (3 * (c / 2) + 2)); [lia | reflexivity].
    + (* c mod 4 = 1: rule b, a' = 1, stop test *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
        by (apply orb_mod4_false; lia).
      assert (E5 : Nat.eqb (c mod 4) 1 = true) by (apply Nat.eqb_eq; exact h4).
      assert (E6 : Nat.eqb (c + 3) (c + 1) = false) by (apply Nat.eqb_neq; lia).
      assert (hstep : step (c + 3) c = Next 1 (3 * ((c - 1) / 2) + 5)).
      { rewrite (step_b (c + 3) c E1c E4 E5 E6).
        replace ((c + 3) - c - 2) with 1 by lia. reflexivity. }
      exact (hrun_two_stop c0 (c + 3) c 1 (3 * ((c - 1) / 2) + 5) hstep (or_introl eq_refl)).
    + (* c mod 4 = 2: rule a, a' = 2 *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true)
        by (apply orb_mod4_two; exact h4).
      assert (hstep : step (c + 3) c = Next 2 (3 * (c / 2) + 2)).
      { rewrite (step_a (c + 3) c E1c E4).
        replace ((c + 3) - c - 1) with 2 by lia. reflexivity. }
      apply (hrun_two_step c0 (c + 3) c 2 (3 * (c / 2) + 2) hstep).
      apply (hrun_stops_of_even_le c0 2 (3 * (c / 2) + 2)); [lia | reflexivity].
    + (* c mod 4 = 3: rule halt3, halt *)
      assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
        by (apply orb_mod4_false; lia).
      assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
      assert (E6 : Nat.eqb (c + 3) (c + 1) = false) by (apply Nat.eqb_neq; lia).
      assert (E7 : Nat.eqb (c + 3) (c + 2) = false) by (apply Nat.eqb_neq; lia).
      assert (E8 : Nat.eqb (c + 3) (c + 3) = true) by (apply Nat.eqb_eq; reflexivity).
      exact (hrun_two_halt c0 (c + 3) c (step_halt3 (c + 3) c E1c E4 E5 E6 E7 E8)).
Qed.

Print Assumptions hrun_two_halt.
Print Assumptions hrun_two_stop.
Print Assumptions hrun_two_step.
Print Assumptions orb_mod4_zero.
Print Assumptions orb_mod4_two.
Print Assumptions orb_mod4_false.
Print Assumptions hrun_near.

(* ------------------------------------------------------------------ *)
(** ** 12. The phase-start gap: [hrun_near] reduces it to [a = c + 4] *)
(* ------------------------------------------------------------------ *)

(** In the [a = c + 4] case with [c] odd the run is dead within two steps: rule [b]
    ([c mod 4 = 1]) lands on [a' = 2] and rule [c] ([c mod 4 = 3]) on [a' = 0], both even
    in the [J] region, which [hrun_stops_of_even_le] kills. *)
Lemma hrun_two_gap_four_odd (c0 c : nat) (h4 : c mod 4 = 1 \/ c mod 4 = 3) :
    hrun c0 2 (c + 4) c = None.
Proof.
  assert (E1c : Nat.leb (c + 4) c = false) by (apply Nat.leb_gt; lia).
  destruct h4 as [h4 | h4].
  - assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
      by (apply orb_mod4_false; lia).
    assert (E5 : Nat.eqb (c mod 4) 1 = true) by (apply Nat.eqb_eq; exact h4).
    assert (E6 : Nat.eqb (c + 4) (c + 1) = false) by (apply Nat.eqb_neq; lia).
    assert (hstep : step (c + 4) c = Next 2 (3 * ((c - 1) / 2) + 5)).
    { rewrite (step_b (c + 4) c E1c E4 E5 E6).
      replace ((c + 4) - c - 2) with 2 by lia. reflexivity. }
    apply (hrun_two_step c0 (c + 4) c 2 (3 * ((c - 1) / 2) + 5) hstep).
    apply (hrun_stops_of_even_le c0 2 (3 * ((c - 1) / 2) + 5)); [lia | reflexivity].
  - assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false)
      by (apply orb_mod4_false; lia).
    assert (E5 : Nat.eqb (c mod 4) 1 = false) by (apply Nat.eqb_neq; lia).
    assert (E6 : Nat.eqb (c + 4) (c + 1) = false) by (apply Nat.eqb_neq; lia).
    assert (E7 : Nat.eqb (c + 4) (c + 2) = false) by (apply Nat.eqb_neq; lia).
    assert (E8 : Nat.eqb (c + 4) (c + 3) = false) by (apply Nat.eqb_neq; lia).
    assert (hstep : step (c + 4) c = Next 0 (3 * ((c - 1) / 2) + 8)).
    { rewrite (step_c (c + 4) c E1c E4 E5 E6 E7 E8).
      replace ((c + 4) - c - 4) with 0 by lia. reflexivity. }
    apply (hrun_two_step c0 (c + 4) c 0 (3 * ((c - 1) / 2) + 8) hstep).
    apply (hrun_stops_of_even_le c0 0 (3 * ((c - 1) / 2) + 8)); [lia | reflexivity].
Qed.

(** **The gap is at least four.**  [hrun_near] contrapositive: no surviving [L] state has
    [c < a <= c + 3]. *)
Lemma L_gap_ge_four (c0 a c : nat) (hc0 : 2 <= c0) (hlt : c < a)
    (hs : HSurvives c0 2 a c) : c + 4 <= a.
Proof.
  destruct hs as [a' [c' h]].
  destruct (Nat.leb a (c + 3)) eqn:E.
  - apply Nat.leb_le in E.
    assert (hN : hrun c0 2 a c = None) by (apply (hrun_near c0 a c hc0 hlt E)).
    rewrite hN in h. discriminate h.
  - apply Nat.leb_gt in E. lia.
Qed.

(** **The collapse shape.**  A surviving [L] state with [a = c + 4] has [c] even, and its
    first step lands on [(3, 3*(c/2)+2)] -- the unique small-[a] entrance to the tail. *)
Lemma L_gap_four_shape (c0 a c : nat) (hlt : c < a) (hg : a = c + 4)
    (hs : HSurvives c0 2 a c) :
    (c mod 4 = 0 \/ c mod 4 = 2) /\ st c0 1 a c = (3, 3 * (c / 2) + 2).
Proof.
  subst a.
  destruct hs as [a' [c' hr]].
  assert (hm4 : c mod 4 = 0 \/ c mod 4 = 1 \/ c mod 4 = 2 \/ c mod 4 = 3).
  { pose proof (Nat.mod_upper_bound c 4 (ltac:(lia))). lia. }
  assert (hmod : c mod 4 = 0 \/ c mod 4 = 2).
  { destruct hm4 as [h0 | [h1 | [h2 | h3]]].
    - left. exact h0.
    - exfalso.
      assert (hN : hrun c0 2 (c + 4) c = None)
        by (apply (hrun_two_gap_four_odd c0 c); left; exact h1).
      rewrite hN in hr. discriminate hr.
    - right. exact h2.
    - exfalso.
      assert (hN : hrun c0 2 (c + 4) c = None)
        by (apply (hrun_two_gap_four_odd c0 c); right; exact h3).
      rewrite hN in hr. discriminate hr. }
  split; [exact hmod |].
  assert (E1c : Nat.leb (c + 4) c = false) by (apply Nat.leb_gt; lia).
  assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true).
  { apply orb_true_iff. destruct hmod as [h | h]; [left | right]; apply Nat.eqb_eq; exact h. }
  assert (hsp : step (c + 4) c = Next 3 (3 * (c / 2) + 2)).
  { rewrite (step_a (c + 4) c E1c E4).
    replace ((c + 4) - c - 1) with 3 by lia. reflexivity. }
  assert (Egen : forall (b : bool) (p : nat * nat),
      ((if b then p else p) = p) /\ (p = (if b then p else p)))
    by (intros b p; destruct b; split; reflexivity).
  cbn [st]. rewrite hsp. cbn.
  first [ apply (proj1 (Egen _ _)) | apply (proj2 (Egen _ _)) ].
Qed.

(** The scan stops as soon as the next length is inadmissible. *)
Lemma lScan_stop (a0 c0 k : nat) (h : ~ lAdm a0 c0 (S k)) :
    forall f, lScan a0 c0 f k = k.
Proof.
  intro f. destruct f as [|f].
  - reflexivity.
  - cbn [lScan].
    assert (E : Nat.leb (2 * c0 * 3 ^ (S k)) (2 ^ (S k) * (a0 + 2 * c0)) = false).
    { apply Nat.leb_gt. unfold lAdm in h. lia. }
    rewrite E. reflexivity.
Qed.

(** The scan takes an admissible step. *)
Lemma lScan_step (a0 c0 k : nat) (h : lAdm a0 c0 (S k)) :
    forall f, lScan a0 c0 (S f) k = lScan a0 c0 f (S k).
Proof.
  intro f. cbn [lScan].
  assert (E : Nat.leb (2 * c0 * 3 ^ (S k)) (2 ^ (S k) * (a0 + 2 * c0)) = true).
  { apply Nat.leb_le. unfold lAdm in h. exact h. }
  rewrite E. reflexivity.
Qed.

(** **The collapse phase is charged exactly one step.** *)
Lemma lLen_gap_four (c : nat) (hc : 3 <= c) : lLen (c + 4) c = 1.
Proof.
  assert (h0 : lAdm (c + 4) c 1).
  { unfold lAdm. cbn. lia. }
  assert (h1 : ~ lAdm (c + 4) c 2).
  { unfold lAdm. cbn. lia. }
  unfold lLen.
  replace (c + 4 + 2 * c + 2) with (S (c + 4 + 2 * c + 1)) by lia.
  rewrite (lScan_step (c + 4) c 0 h0 (c + 4 + 2 * c + 1)).
  apply (lScan_stop (c + 4) c 1 h1 (c + 4 + 2 * c + 1)).
Qed.

(** The ledger charge at the collapse state is one. *)
Lemma phaseCharge_gap_four (c : nat) (hc : 3 <= c) : phaseCharge (c + 4) c = 1.
Proof.
  rewrite (phaseCharge_L (c + 4) c (ltac:(lia))).
  apply lLen_gap_four. exact hc.
Qed.

(** **The collapse is a ledger entry.**  A surviving gap-4 [L] state has [c] even, steps
    onto [(3, 3*(c/2)+2)], and the [L] phase it starts is charged exactly one: the formal
    link from the collapse shape to [phaseCharge], not prose. *)
Lemma L_gap_four_ledger (c0 c : nat) (hc : 3 <= c) (hs : HSurvives c0 2 (c + 4) c) :
    (c mod 4 = 0 \/ c mod 4 = 2) /\ st c0 1 (c + 4) c = (3, 3 * (c / 2) + 2) /\
      phaseCharge (c + 4) c = 1.
Proof.
  destruct (L_gap_four_shape c0 (c + 4) c (ltac:(lia)) eq_refl hs) as [hmod hst].
  split; [exact hmod | split; [exact hst | apply phaseCharge_gap_four; exact hc]].
Qed.

Print Assumptions hrun_two_gap_four_odd.
Print Assumptions L_gap_ge_four.
Print Assumptions L_gap_four_shape.
Print Assumptions lScan_stop.
Print Assumptions lScan_step.
Print Assumptions lLen_gap_four.
Print Assumptions phaseCharge_gap_four.
Print Assumptions L_gap_four_ledger.

(* ------------------------------------------------------------------ *)
(** ** 13. How many gap-4 collapses can a halving run have? *)
(* ------------------------------------------------------------------ *)

(** A **gap-4 collapse candidate**: an [L] state whose gap is exactly four. *)
Definition g4 (a c : nat) : Prop := c < a /\ a = c + 4.

(** Boolean form of [g4], for counting along the run. *)
Definition g4b (a c : nat) : bool := Nat.leb (S c) a && Nat.eqb a (c + 4).

Lemma g4b_spec (a c : nat) : g4b a c = true <-> g4 a c.
Proof.
  unfold g4b, g4. split; intro H.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply Nat.leb_le in H1. apply Nat.eqb_eq in H2. lia.
  - apply andb_true_iff. split.
    + apply Nat.leb_le. lia.
    + apply Nat.eqb_eq. lia.
Qed.

(** Count of gap-4 collapse candidates along the first [n] states of the halving run. *)
Fixpoint g4cnt (c0 : nat) (n a c : nat) {struct n} : nat :=
  match n with
  | O => 0
  | S n' =>
      (if g4b a c then 1 else 0) +
        (match step a c with
         | Halt => 0
         | Next a' c' =>
             if orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0) then 0
             else g4cnt c0 n' a' c'
         end)
  end.

(** From a gap-4 state the next state has [a' <= 3]. *)
Lemma g4_step_le_three (a c a' c' : nat) (h : g4 a c)
    (hs : step a c = Next a' c') : a' <= 3.
Proof.
  destruct h as [hlt hgap].
  assert (E1 : Nat.leb a c = false) by (apply Nat.leb_gt; lia).
  destruct (Nat.eqb (Nat.modulo c 4) 0) eqn:E0.
  - assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true)
      by (apply orb_true_iff; left; exact E0).
    rewrite (step_a a c E1 E4) in hs. injection hs as H1 H2. rewrite <- H1. lia.
  - destruct (Nat.eqb (Nat.modulo c 4) 2) eqn:E2.
    + assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = true)
        by (apply orb_true_iff; right; exact E2).
      rewrite (step_a a c E1 E4) in hs. injection hs as H1 H2. rewrite <- H1. lia.
    + assert (E4 : orb (Nat.eqb (c mod 4) 0) (Nat.eqb (c mod 4) 2) = false).
      { apply orb_false_iff. split; assumption. }
      destruct (Nat.eqb (Nat.modulo c 4) 1) eqn:E5.
      * assert (E6 : Nat.eqb a (c + 1) = false) by (apply Nat.eqb_neq; lia).
        rewrite (step_b a c E1 E4 E5 E6) in hs. injection hs as H1 H2. rewrite <- H1. lia.
      * destruct (Nat.eqb a (c + 1)) eqn:E6.
        -- rewrite (step_halt1 a c E1 E4 E5 E6) in hs. discriminate hs.
        -- destruct (Nat.eqb a (c + 2)) eqn:E7.
           ++ rewrite (step_e a c E1 E4 E5 E6 E7) in hs. injection hs as H1 H2.
              apply Nat.eqb_eq in E7. lia.
           ++ destruct (Nat.eqb a (c + 3)) eqn:E8.
              ** rewrite (step_halt3 a c E1 E4 E5 E6 E7 E8) in hs. discriminate hs.
              ** rewrite (step_c a c E1 E4 E5 E6 E7 E8) in hs. injection hs as H1 H2.
                 rewrite <- H1. lia.
Qed.

(** **A gap-4 state is never followed by a gap-4 state.** *)
Lemma g4_succ_not (a c a' c' : nat) (h : g4 a c)
    (hs : step a c = Next a' c') : ~ g4 a' c'.
Proof.
  intro h'.
  assert (h3 : a' <= 3) by (apply (g4_step_le_three a c a' c' h); exact hs).
  destruct h' as [_ hgap]. lia.
Qed.

(** **The counting bound, division-free**: along [n] states of a halving run at most
    [(n+1)/2] are gap-4 candidates, written as [2 * count <= n + 1]. *)
Lemma g4cnt_le (c0 : nat) : forall (n a c : nat),
    2 * g4cnt c0 n a c <= n + 1 /\
    (~ g4 a c -> 2 * g4cnt c0 n a c <= n).
Proof.
  intro n. induction n as [|n ih]; intros a c.
  - cbn [g4cnt]. split; lia.
  - cbn [g4cnt].
    destruct (step a c) as [|a' c'] eqn:hs.
    + cbn.
      destruct (g4b a c) eqn:E; cbn.
      * split.
        -- lia.
        -- intro hng. exfalso. apply hng. apply (proj1 (g4b_spec a c)); exact E.
      * split; lia.
    + destruct (orb (Nat.eqb a' 1) (Nat.leb (2 * c') c0)) eqn:Es.
      * cbn.
        destruct (g4b a c) eqn:E; cbn.
        -- split.
           ++ lia.
           ++ intro hng. exfalso. apply hng. apply (proj1 (g4b_spec a c)); exact E.
        -- split; lia.
      * cbn.
        destruct (g4b a c) eqn:E; cbn.
        -- assert (hg : g4 a c) by (apply (proj1 (g4b_spec a c)); exact E).
           assert (hng' : ~ g4 a' c') by (apply (g4_succ_not a c a' c' hg); exact hs).
           assert (H2 : 2 * g4cnt c0 n a' c' <= n) by (apply (proj2 (ih a' c')); exact hng').
           split.
           ++ lia.
           ++ intro hng. exfalso. apply hng. exact hg.
        -- assert (H1 : 2 * g4cnt c0 n a' c' <= n + 1) by (apply (proj1 (ih a' c'))).
           split; lia.
Qed.

(** **At most half of a run's states are gap-4 collapses.** *)
Lemma g4cnt_le_half (c0 a c n : nat) : 2 * g4cnt c0 n a c <= n + 1.
Proof. apply (proj1 (g4cnt_le c0 n a c)). Qed.

(** **Every surviving gap-4 candidate is a ledger entry.** *)
Lemma g4_charge (c0 a c : nat) (h : g4 a c) (hc : 3 <= c)
    (hs : HSurvives c0 2 a c) :
    st c0 1 a c = (3, 3 * (c / 2) + 2) /\ phaseCharge a c = 1.
Proof.
  destruct h as [hlt hgap]. subst a.
  destruct (L_gap_four_ledger c0 c hc hs) as [_ [hst hch]].
  split; assumption.
Qed.

Print Assumptions g4b_spec.
Print Assumptions g4_step_le_three.
Print Assumptions g4_succ_not.
Print Assumptions g4cnt_le.
Print Assumptions g4cnt_le_half.
Print Assumptions g4_charge.
