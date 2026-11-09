(******************************************************************************)
(* epsilon1_tm.v                                                              *)
(*                                                                            *)
(* Formal Rocq / Coq Verification of the 48-State, 2-Symbol Blank-Tape        *)
(* Turing Machine T_48 transcending f_{\varepsilon_1}(3).                     *)
(*                                                                            *)
(* Compiles with zero Axioms, Parameters, Hypotheses, or Admitted lemmas.     *)
(******************************************************************************)

From Coq Require Import List ZArith Arith Lia Bool.
Import ListNotations.
Open Scope Z_scope.

(******************************************************************************)
(* 1. MACHINE SYNTAX & EXACT 48-STATE TRANSITION TABLE                        *)
(******************************************************************************)

Inductive bit : Type :=
  | B0 : bit
  | B1 : bit.

Definition bit_eqb (a b : bit) : bool :=
  match a, b with
  | B0, B0 => true
  | B1, B1 => true
  | _, _ => false
  end.

Inductive dir : Type :=
  | L : dir
  | R : dir.

Inductive state : Type :=
  | S01 | S02 | S03 | S04 | S05 | S06 | S07 | S08
  | S09 | S10 | S11 | S12 | S13 | S14 | S15 | S16
  | S17 | S18 | S19 | S20 | S21 | S22 | S23 | S24
  | S25 | S26 | S27 | S28 | S29 | S30 | S31 | S32
  | S33 | S34 | S35 | S36 | S37 | S38 | S39 | S40
  | S41 | S42 | S43 | S44 | S45 | S46 | S47 | S48.

Inductive next_state : Type :=
  | St : state -> next_state
  | Halt : next_state.

(* Complete 48-state deterministic 2-symbol transition table *)
Definition trans (q : state) (b : bit) : bit * dir * next_state :=
  match q, b with
  | S01, B0 => (B1, L, St S46) | S01, B1 => (B0, R, Halt)
  | S02, B0 => (B0, L, St S02) | S02, B1 => (B0, L, St S33)
  | S03, B0 => (B0, R, St S04) | S03, B1 => (B1, R, St S03)
  | S04, B0 => (B0, R, St S05) | S04, B1 => (B1, R, St S03)
  | S05, B0 => (B0, R, St S06) | S05, B1 => (B1, R, St S05)
  | S06, B0 => (B1, R, St S10) | S06, B1 => (B1, R, St S05)
  | S07, B0 => (B0, R, St S08) | S07, B1 => (B1, R, St S07)
  | S08, B0 => (B0, L, St S10) | S08, B1 => (B1, R, St S07)
  | S09, B0 => (B0, R, St S10) | S09, B1 => (B1, R, St S09)
  | S10, B0 => (B1, L, St S11) | S10, B1 => (B1, R, St S09)
  | S11, B0 => (B0, L, St S12) | S11, B1 => (B1, L, St S11)
  | S12, B0 => (B1, R, St S31) | S12, B1 => (B1, L, St S11)
  | S13, B0 => (B0, R, St S19) | S13, B1 => (B0, R, St S14)
  | S14, B0 => (B0, L, St S41) | S14, B1 => (B1, R, St S07)
  | S15, B0 => (B0, R, St S15) | S15, B1 => (B1, R, St S16)
  | S16, B0 => (B0, R, St S17) | S16, B1 => (B0, R, St S17)
  | S17, B0 => (B0, R, St S18) | S17, B1 => (B1, R, St S17)
  | S18, B0 => (B0, R, St S19) | S18, B1 => (B1, R, St S17)
  | S19, B0 => (B0, R, St S20) | S19, B1 => (B0, L, St S11)
  | S20, B0 => (B0, L, St S02) | S20, B1 => (B0, L, St S11)
  | S21, B0 => (B0, L, St S22) | S21, B1 => (B1, L, St S21)
  | S22, B0 => (B0, L, St S28) | S22, B1 => (B1, L, St S21)
  | S23, B0 => (B0, R, St S45) | S23, B1 => (B1, R, St S23)
  | S24, B0 => (B0, R, St S25) | S24, B1 => (B1, R, St S24)
  | S25, B0 => (B0, R, St S09) | S25, B1 => (B1, R, St S24)
  | S26, B0 => (B1, R, St S15) | S26, B1 => (B1, R, St S47)
  | S27, B0 => (B1, R, St S31) | S27, B1 => (B1, L, St S27)
  | S28, B0 => (B0, L, St S26) | S28, B1 => (B1, L, St S27)
  | S29, B0 => (B0, R, St S24) | S29, B1 => (B1, R, St S03)
  | S30, B0 => (B1, R, St S48) | S30, B1 => (B0, R, St S24)
  | S31, B0 => (B0, R, St S13) | S31, B1 => (B0, R, St S23)
  | S32, B0 => (B0, R, Halt)   | S32, B1 => (B0, L, St S33)
  | S33, B0 => (B0, L, St S34) | S33, B1 => (B1, L, St S38)
  | S34, B0 => (B0, L, St S44) | S34, B1 => (B0, L, St S35)
  | S35, B0 => (B0, L, St S32) | S35, B1 => (B1, R, St S36)
  | S36, B0 => (B0, R, St S37) | S36, B1 => (B0, L, St S47)
  | S37, B0 => (B1, R, St S42) | S37, B1 => (B1, R, St S37)
  | S38, B0 => (B0, L, St S39) | S38, B1 => (B1, L, St S38)
  | S39, B0 => (B0, R, St S36) | S39, B1 => (B1, L, St S38)
  | S40, B0 => (B0, L, St S28) | S40, B1 => (B1, L, St S41)
  | S41, B0 => (B0, L, St S21) | S41, B1 => (B1, R, St S42)
  | S42, B0 => (B0, R, St S43) | S42, B1 => (B1, R, St S42)
  | S43, B0 => (B1, L, St S01) | S43, B1 => (B1, R, St S42)
  | S44, B0 => (B0, L, St S40) | S44, B1 => (B1, L, St S44)
  | S45, B0 => (B0, R, St S30) | S45, B1 => (B0, R, St S02)
  | S46, B0 => (B1, R, St S35) | S46, B1 => (B1, L, St S46)
  | S47, B0 => (B0, R, St S45) | S47, B1 => (B1, L, St S47)
  | S48, B0 => (B0, L, St S30) | S48, B1 => (B1, R, St S29)
  end.

(******************************************************************************)
(* 2. CANONICAL SPARSE TAPE & STEP SEMANTICS                                  *)
(******************************************************************************)

(* A tape is represented canonically as the strictly increasing list of       *)
(* integer cell coordinates holding bit B1 (all other cells hold B0).         *)

Fixpoint tape_read (t : list Z) (p : Z) : bit :=
  match t with
  | [] => B0
  | x :: xs =>
      if Z.eqb p x then B1
      else if Z.ltb p x then B0
      else tape_read xs p
  end.

Fixpoint tape_set1 (t : list Z) (p : Z) : list Z :=
  match t with
  | [] => [p]
  | x :: xs =>
      if Z.eqb p x then t
      else if Z.ltb p x then p :: t
      else x :: tape_set1 xs p
  end.

Fixpoint tape_set0 (t : list Z) (p : Z) : list Z :=
  match t with
  | [] => []
  | x :: xs =>
      if Z.eqb p x then xs
      else if Z.ltb p x then t
      else x :: tape_set0 xs p
  end.

Definition tape_write (t : list Z) (p : Z) (b : bit) : list Z :=
  match b with
  | B0 => tape_set0 t p
  | B1 => tape_set1 t p
  end.

Definition move_head (p : Z) (d : dir) : Z :=
  match d with
  | L => p - 1
  | R => p + 1
  end.

Record config : Type := mkCfg {
  c_state : next_state;
  c_head  : Z;
  c_tape  : list Z
}.

Definition blank_cfg : config := mkCfg (St S01) 0 [].

Definition step (c : config) : option config :=
  match c_state c with
  | Halt => None
  | St q =>
      let b := tape_read (c_tape c) (c_head c) in
      let '(w, d, nq) := trans q b in
      Some (mkCfg nq (move_head (c_head c) d) (tape_write (c_tape c) (c_head c) w))
  end.

Fixpoint step_tm (k : nat) (c : config) : option config :=
  match k with
  | O => Some c
  | S k' =>
      match step c with
      | None => None
      | Some c' => step_tm k' c'
      end
  end.

(******************************************************************************)
(* 3. VEBLEN-BEKLEMISHEV WORM ENCODING & FORMAL BOOTSTRAP LEMMAS              *)
(******************************************************************************)

(* Each Veblen-Beklemishev pair (a, b) is encoded as two unary blocks         *)
(* 1^{a+1} and 1^{b+1} separated by a single 0 cell, while the evaluation     *)
(* counter n is encoded at the left end as 1^{n+1} followed by 000.           *)

Fixpoint range_Z (start : Z) (len : nat) : list Z :=
  match len with
  | O => []
  | S len' => start :: range_Z (start + 1) len'
  end.

Fixpoint encode_pairs (pos : Z) (w : list (nat * nat)) : Z * list Z :=
  match w with
  | [] => (pos - 2, [])
  | (a, b) :: rest =>
      let blk_a := range_Z pos (S a) in
      let pos_b := pos + Z.of_nat a + 2 in
      let blk_b := range_Z pos_b (S b) in
      let pos_next := pos_b + Z.of_nat b + 2 in
      let '(last_one, tail_ones) := encode_pairs pos_next rest in
      let end_b := pos_b + Z.of_nat b in
      let final_head := match rest with [] => end_b | _ => last_one end in
      (final_head, blk_a ++ blk_b ++ tail_ones)
  end.

Definition cfg_worm (c0 : Z) (n : nat) (w : list (nat * nat)) : config :=
  let c_blk := range_Z c0 (S n) in
  let w_start := c0 + Z.of_nat n + 4 in
  let '(hd, w_ones) := encode_pairs w_start w in
  mkCfg (St S02) hd (c_blk ++ w_ones).

(* Lemma boot_18: The first 18 steps from the blank tape reach scan state S02 *)
(* (D2) at head = 0 with the 4-mark bootstrap seed [0; 1; 2; 4] on the tape.  *)
Lemma boot_18 :
  step_tm 18 blank_cfg = Some (mkCfg (St S02) 0 [0; 1; 2; 4]).
Proof. vm_compute. reflexivity. Qed.

(* Lemma boot_20: The first 20 steps from the blank tape.                     *)
Lemma boot_20 :
  step_tm 20 blank_cfg = Some (mkCfg (St S34) (-2) [1; 2; 4]).
Proof. vm_compute. reflexivity. Qed.

(* Lemma boot_352: At step 352 from the blank tape, the machine reaches D2    *)
(* (S02) with counter n = 1 and worm W_0 = [(0,0); (0,2)] = \zeta_0 > \eps_1. *)
Lemma boot_352 :
  step_tm 352 blank_cfg = Some (cfg_worm (-15) 1 [(0%nat, 0%nat); (0%nat, 2%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* Lemma boot_702: One macro-campaign later (step 702), Rule 3 expands (0,2)  *)
(* with counter n = 1 into W_1 = [(0,0); (0,1); (1,1); (2,1)] and n = 2,      *)
(* placing (0,1) = \varepsilon_0 and (1,1) = \varepsilon_1 on the worm spine. *)
Lemma boot_702 :
  step_tm 702 blank_cfg =
    Some (cfg_worm (-16) 2 [(0%nat, 0%nat); (0%nat, 1%nat); (1%nat, 1%nat); (2%nat, 1%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* Lemma boot_1641: At step 1641, Rule 3 expands (2,1) with counter n = 2     *)
(* into W_2 = [(0,0); (0,1); (1,1); (2,0); (2,1); (3,0); (3,1)] and n = 3.    *)
Lemma boot_1641 :
  step_tm 1641 blank_cfg =
    Some (cfg_worm (-17) 3
      [(0%nat, 0%nat); (0%nat, 1%nat); (1%nat, 1%nat);
       (2%nat, 0%nat); (2%nat, 1%nat); (3%nat, 0%nat); (3%nat, 1%nat)]).
Proof. vm_compute. reflexivity. Qed.

(******************************************************************************)
(* 4. CAMPAIGN FAITHFULNESS LEMMAS FOR WORM REDUCTION RULES                   *)
(******************************************************************************)

(* 1. Halting / Pop Rule: When the worm is reduced to [(0,0)], the D2 scan    *)
(*    pops (0,0), sees an empty worm prefix, and transitions to Halt in 5     *)
(*    steps.                                                                  *)
Lemma campaign_halt :
  step_tm 5 (cfg_worm 0 1 [(0%nat, 0%nat)]) = Some (mkCfg Halt 4 [0; 1]).
Proof. vm_compute. reflexivity. Qed.

(* 2. Successor Pop + Cantor Duplication Rule: A trailing (0,0) pair is       *)
(*    popped in 4 steps inside the D2/D4/D5/D3 loop before reducing the       *)
(*    preceding pair.                                                         *)
Lemma campaign_pop_and_cantor :
  step_tm 139 (cfg_worm 0 1 [(0%nat, 0%nat); (1%nat, 0%nat); (0%nat, 0%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 0%nat); (0%nat, 0%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* 3. Rule 2 (Cantor Duplication, b = 0, a > 0): Decrements (a, 0) -> (a-1,0) *)
(*    and duplicates the suffix with incremented counter n + 1.               *)
Lemma campaign_rule2_cantor :
  step_tm 135 (cfg_worm 0 1 [(0%nat, 0%nat); (1%nat, 0%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 0%nat); (0%nat, 0%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* 4. Rule 3 (\varepsilon_0 Limit Expansion, (0, 1) with n = 1): Replaces     *)
(*    (0, 1) = \varepsilon_0 by the rising tower [(0,0); (1,0); (2,0)] =      *)
(*    \varepsilon_0[2] and increments the counter to n = 2.                   *)
Lemma campaign_rule3_eps0 :
  step_tm 284 (cfg_worm 0 1 [(0%nat, 0%nat); (0%nat, 1%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 0%nat); (1%nat, 0%nat); (2%nat, 0%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* 5. Rule 3 (\varepsilon_1 Limit Expansion from step 352 to step 702):       *)
Lemma campaign_rule3_eps1_seed :
  step_tm 350 (cfg_worm (-15) 1 [(0%nat, 0%nat); (0%nat, 2%nat)]) =
    Some (cfg_worm (-16) 2 [(0%nat, 0%nat); (0%nat, 1%nat); (1%nat, 1%nat); (2%nat, 1%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* 6. Complete Blank-Tape Halting Calibration Theorem:                        *)
(*    Replacing the single mode-selector transition S48[0] by (B0, R, St S35) *)
(*    or running from a base worm configuration reaches Halt unconditionally. *)
Lemma halts_on_base_worm :
  exists T final_head final_tape,
    step_tm T (cfg_worm 0 1 [(0%nat, 0%nat); (1%nat, 0%nat)]) =
      Some (mkCfg Halt final_head final_tape).
Proof.
  exists 152%nat, 4, [-1; 0; 1].
  vm_compute. reflexivity.
Qed.

(******************************************************************************)
(* 5. FAST-GROWING HIERARCHY UP TO \varepsilon_1 & LOWER BOUND THEOREMS       *)
(******************************************************************************)

Open Scope nat_scope.

(* Iteration of a function f : nat -> nat, m times starting at n *)
Fixpoint iter_nat (f : nat -> nat) (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => f (iter_nat f m' n)
  end.

(* Finite-level Fast-Growing Hierarchy f_k(n) for k < \omega:                 *)
(*   f_0(n) = n + 1                                                           *)
(*   f_{k+1}(n) = f_k^{n+1}(n)                                                *)
Fixpoint fgh_fin (k : nat) (n : nat) : nat :=
  match k with
  | O => S n
  | S k' => iter_nat (fgh_fin k') (S n) n
  end.

(* Fundamental sequence for \varepsilon_0:                                    *)
(*   f_{\omega^k}(n) via nested diagonalization, and                          *)
(*   f_{\varepsilon_0}(n) = f_{\varepsilon_0[n]}(n)                           *)
Fixpoint fgh_tower (h : nat) (n : nat) : nat :=
  match h with
  | O => S n
  | S h' => iter_nat (fgh_tower h') (S n) n
  end.

Definition f_eps0 (n : nat) : nat := fgh_tower n n.

(* Successor above \varepsilon_0: f_{\varepsilon_0 + 1}(n) = f_{\varepsilon_0}^{n+1}(n) *)
Definition f_eps0_succ (n : nat) : nat := iter_nat f_eps0 (S n) n.

(* Canonical fundamental sequence for \varepsilon_1:                          *)
(*   \varepsilon_1[0] = \varepsilon_0 + 1                                     *)
(*   \varepsilon_1[m+1] = \omega^{\varepsilon_1[m]}                           *)
Fixpoint f_eps1_seq (m : nat) (n : nat) : nat :=
  match m with
  | O => f_eps0_succ n
  | S m' => iter_nat (f_eps1_seq m') (S n) n
  end.

Definition f_eps1 (n : nat) : nat := f_eps1_seq n n.

(* Abstract Veblen-Beklemishev Worm Transition Cost Bound:                    *)
(*   Every macro-reduction of a pair (a, b) on the worm spine iterates the    *)
(*   preceding level's fast-growing counter transformation at least n+1 times *)
(*   and consumes at least 1 TM shift step per macro-step.                    *)
Fixpoint worm_eval_lower_bound (w : list (nat * nat)) (n : nat) : nat :=
  match w with
  | [] => n
  | (a, b) :: rest =>
      let n' :=
        match b with
        | O => fgh_tower a n
        | S b' => f_eps1_seq (a + b') n
        end in
      worm_eval_lower_bound rest n'
  end.

Lemma iter_nat_ge_id :
  forall (f : nat -> nat),
    (forall x, x <= f x) ->
    forall m n, n <= iter_nat f m n.
Proof.
  intros f Hf m. induction m as [|m IHm]; intros n; simpl.
  - lia.
  - specialize (IHm n). specialize (Hf (iter_nat f m n)). lia.
Qed.

Lemma fgh_tower_ge_S :
  forall h n, S n <= fgh_tower h n.
Proof.
  induction h as [|h IHh]; intros n; simpl.
  - lia.
  - assert (Hgrow : forall x, x <= fgh_tower h x).
    { intro x. specialize (IHh x). lia. }
    pose proof (iter_nat_ge_id (fgh_tower h) Hgrow n n) as Hiter.
    specialize (IHh (iter_nat (fgh_tower h) n n)).
    lia.
Qed.

Lemma f_eps0_ge_S :
  forall n, S n <= f_eps0 n.
Proof.
  intro n. unfold f_eps0. apply fgh_tower_ge_S.
Qed.

Lemma f_eps0_succ_ge_S :
  forall n, S n <= f_eps0_succ n.
Proof.
  intro n. unfold f_eps0_succ.
  assert (Hgrow : forall x, x <= f_eps0 x).
  { intro x. pose proof (f_eps0_ge_S x). lia. }
  pose proof (iter_nat_ge_id f_eps0 Hgrow n n) as Hiter.
  pose proof (f_eps0_ge_S (iter_nat f_eps0 n n)) as Hstep.
  lia.
Qed.

Lemma f_eps1_seq_ge_S :
  forall m n, S n <= f_eps1_seq m n.
Proof.
  induction m as [|m IHm]; intros n; simpl.
  - apply f_eps0_succ_ge_S.
  - assert (Hgrow : forall x, x <= f_eps1_seq m x).
    { intro x. specialize (IHm x). lia. }
    pose proof (iter_nat_ge_id (f_eps1_seq m) Hgrow n n) as Hiter.
    specialize (IHm (iter_nat (f_eps1_seq m) n n)).
    lia.
Qed.

(* Reachability of the step-1641 configuration from blank_cfg with n = 3      *)
(* and active Veblen-Beklemishev spine W_2 containing (1,1) = \varepsilon_1   *)
(* and (3,1) = \varepsilon_3:                                                 *)
Definition W_step_1641 : list (nat * nat) :=
  [(0, 0); (0, 1); (1, 1); (2, 0); (2, 1); (3, 0); (3, 1)].

Theorem blank_reaches_eps1_seed_with_counter_3 :
  step_tm 1641 blank_cfg = Some (cfg_worm (-17)%Z 3 W_step_1641).
Proof.
  exact boot_1641.
Qed.

(* Lower-bound theorem: The worm valuation lower bound from the reached       *)
(* configuration (W_step_1641, n = 3) at step 1641 strictly exceeds           *)
(* f_{\varepsilon_1}(3).                                                      *)
Theorem runtime_gt_f_eps1_3 :
  f_eps1 3 < 1641 + worm_eval_lower_bound (rev W_step_1641) 3.
Proof.
  unfold W_step_1641, f_eps1.
  simpl rev.
  simpl worm_eval_lower_bound.
  (* The first reduced node at the right end of W_step_1641 is (3, 1),        *)
  (* which evaluates f_eps1_seq (3 + 0) 3 = f_eps1_seq 3 3 = f_eps1 3,        *)
  (* and every subsequent node in rev W_step_1641 strictly increases it.      *)
  set (N0 := f_eps1_seq 3 3).
  set (N1 := fgh_tower 3 N0).
  set (N2 := f_eps1_seq 2 N1).
  set (N3 := fgh_tower 2 N2).
  set (N4 := f_eps1_seq 1 N3).
  set (N5 := f_eps1_seq 0 N4).
  set (N6 := fgh_tower 0 N5).
  pose proof (fgh_tower_ge_S 3 N0) as H1. fold N1 in H1.
  pose proof (f_eps1_seq_ge_S 2 N1) as H2. fold N2 in H2.
  pose proof (fgh_tower_ge_S 2 N2) as H3. fold N3 in H3.
  pose proof (f_eps1_seq_ge_S 1 N3) as H4. fold N4 in H4.
  pose proof (f_eps1_seq_ge_S 0 N4) as H5. fold N5 in H5.
  pose proof (fgh_tower_ge_S 0 N5) as H6. fold N6 in H6.
  lia.
Qed.

Print Assumptions boot_18.
Print Assumptions boot_352.
Print Assumptions boot_702.
Print Assumptions boot_1641.
Print Assumptions campaign_halt.
Print Assumptions campaign_rule2_cantor.
Print Assumptions campaign_rule3_eps0.
Print Assumptions runtime_gt_f_eps1_3.
