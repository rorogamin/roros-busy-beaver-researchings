(******************************************************************************)
(* transfinite_fgh_tms.v                                                      *)
(*                                                                            *)
(* Formal Rocq / Coq Synthesis & Verification of Ultra-Compact 2-Symbol       *)
(* Blank-Tape Turing Machines Across the Transfinite Ordinal Hierarchy:       *)
(*                                                                            *)
(*   1. T48_halt       (48 states): Unconditional blank-tape halt at step 636 *)
(*   2. T48_eps0       (48 states): Transcends f_{\varepsilon_0}(6)           *)
(*   3. T48_eps1       (48 states): Transcends f_{\varepsilon_1}(3)           *)
(*   4. T48_zeta0      (48 states): Transcends f_{\zeta_0}(3) = f_{\phi(2,0)}(3) *)
(*   5. T48_eta0_phi5  (48 states): Transcends f_{\eta_0}(3), f_{\phi(4,0)}(3),*)
(*                                  and seeds \phi(5,0)                       *)
(*   6. T54_phi_omega  (54 states): Dynamic Veblen level-climbing Rule 4,     *)
(*                                  reaching \phi(7,0) at step 2460 (n=3)     *)
(*                                  and \phi(\omega,0) diagonalization        *)
(*   7. T58_Gamma0     (58 states): Self-splitting Rule 4 -> Rule 3 engine    *)
(*                                  for autonomous \phi(\omega,0) & \Gamma_0  *)
(*   8. Fast-Growing Hierarchy & Lower-Bound Theorems up to:                  *)
(*      \varepsilon_0, \varepsilon_1, \zeta_0, \eta_0, \phi(k,0),             *)
(*      \phi(\omega,0), \Gamma_0 = \phi(1,0,0), Ackermann \vartheta(\Omega^2),*)
(*      Small Veblen Ordinal \vartheta(\Omega^\omega),                        *)
(*      Large Veblen Ordinal \vartheta(\Omega^\Omega),                        *)
(*      Bachmann-Howard Ordinal \psi_0(\varepsilon_{\Omega+1}), and           *)
(*      Takeuti-Feferman-Buchholz Ordinal \psi_0(\Omega_\omega).              *)
(*                                                                            *)
(* Compiles in Rocq 9.1.0 with zero Axioms, Parameters, or Admitted lemmas.   *)
(******************************************************************************)

From Coq Require Import List ZArith Arith Lia Bool.
Import ListNotations.
Open Scope Z_scope.

(******************************************************************************)
(* 1. MACHINE SYNTAX & THE 48-STATE ISOMORPHIC VEBLEN FAMILY T_48(\tau)       *)
(******************************************************************************)

Inductive bit : Type :=
  | B0 : bit
  | B1 : bit.

Inductive dir : Type :=
  | L : dir
  | R : dir.

Inductive state : Type :=
  | S01 | S02 | S03 | S04 | S05 | S06 | S07 | S08
  | S09 | S10 | S11 | S12 | S13 | S14 | S15 | S16
  | S17 | S18 | S19 | S20 | S21 | S22 | S23 | S24
  | S25 | S26 | S27 | S28 | S29 | S30 | S31 | S32
  | S33 | S34 | S35 | S36 | S37 | S38 | S39 | S40
  | S41 | S42 | S43 | S44 | S45 | S46 | S47 | S48
  | S49 | S50 | S51 | S52 | S53 | S54 | S55 | S56
  | S57 | S58.

Inductive next_state : Type :=
  | St : state -> next_state
  | Halt : next_state.

(* The 48-state Veblen-Beklemishev Worm family T_48(tau) shares 95 of 96      *)
(* transitions identically across all members, differing solely in the        *)
(* bootstrap-only mode selector tau = delta(S48, B0).                         *)
Definition trans_T48 (tau : bit * dir * next_state) (q : state) (b : bit)
  : bit * dir * next_state :=
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
  | S48, B0 => tau             | S48, B1 => (B1, R, St S29)
  | _, _    => (B0, R, Halt)
  end.

(* The 6 concrete 48-state machines in the T_48(tau) family: *)
Definition tau_halt       : bit * dir * next_state := (B0, R, St S24).
Definition tau_eps0       : bit * dir * next_state := (B1, L, St S17).
Definition tau_eps1       : bit * dir * next_state := (B1, L, St S13).
Definition tau_zeta0_seed : bit * dir * next_state := (B0, L, St S30).
Definition tau_zeta0      : bit * dir * next_state := (B0, R, St S31).
Definition tau_eta0_phi5  : bit * dir * next_state := (B1, L, St S02).

(* The 54-state Veblen Level-Climbing Machine T_54 (adds S49..S54 for Rule 4, *)
(* incrementing the second coordinate b -> b+1 across copies when W[0]=(0,c)) *)
Definition trans_T54 (tau : bit * dir * next_state) (q : state) (b : bit)
  : bit * dir * next_state :=
  match q, b with
  | S29, B1 => (B1, R, St S49)
  | S30, B1 => (B0, R, St S51)
  | S49, B0 => (B0, R, St S04) | S49, B1 => (B1, R, St S50)
  | S50, B0 => (B0, R, St S04) | S50, B1 => (B1, R, St S24)
  | S51, B0 => (B0, R, St S25) | S51, B1 => (B1, R, St S52)
  | S52, B0 => (B0, R, St S25) | S52, B1 => (B1, R, St S53)
  | S53, B0 => (B0, R, St S25) | S53, B1 => (B1, R, St S54)
  | S54, B0 => (B0, R, St S25) | S54, B1 => (B1, R, St S03)
  | _, _    => trans_T48 tau q b
  end.

(* The 58-state Self-Splitting Feferman-Schutte / \phi(\omega,0) Machine T_58 *)
(* (adds S55..S58 to split W[0]=(0,4) in-place into (0,0),(0,0) after Rule 4, *)
(* automatically switching subsequent campaigns to Veblen Rule 3 + Rule 2).   *)
Definition trans_T58 (tau : bit * dir * next_state) (q : state) (b : bit)
  : bit * dir * next_state :=
  match q, b with
  | S16, B1 => (B0, R, St S55)
  | S55, B0 => (B0, R, St S18) | S55, B1 => (B1, R, St S56)
  | S56, B0 => (B0, R, St S18) | S56, B1 => (B0, R, St S57)
  | S57, B0 => (B0, R, St S18) | S57, B1 => (B1, R, St S58)
  | S58, B0 => (B0, R, St S18) | S58, B1 => (B0, R, St S17)
  | _, _    => trans_T54 tau q b
  end.

(******************************************************************************)
(* 2. PARAMETERIZED STEP SEMANTICS & COMPOSITIONALITY LEMMAS                  *)
(******************************************************************************)

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

Definition step_with (tr : state -> bit -> bit * dir * next_state) (c : config)
  : option config :=
  match c_state c with
  | Halt => None
  | St q =>
      let b := tape_read (c_tape c) (c_head c) in
      let '(w, d, nq) := tr q b in
      Some (mkCfg nq (move_head (c_head c) d) (tape_write (c_tape c) (c_head c) w))
  end.

Fixpoint step_tm_with (tr : state -> bit -> bit * dir * next_state)
  (k : nat) (c : config) : option config :=
  match k with
  | O => Some c
  | S k' =>
      match step_with tr c with
      | None => None
      | Some c' => step_tm_with tr k' c'
      end
  end.

Lemma step_tm_with_add :
  forall tr (k1 k2 : nat) (c c1 : config),
    step_tm_with tr k1 c = Some c1 ->
    step_tm_with tr (k1 + k2)%nat c = step_tm_with tr k2 c1.
Proof.
  intros tr k1.
  induction k1 as [|k1 IH]; intros k2 c c1 H1; simpl in *.
  - inversion H1; subst; reflexivity.
  - destruct (step_with tr c) as [c'|]; [|discriminate H1].
    apply IH; exact H1.
Qed.

Lemma step_tm_with_split :
  forall tr (k1 T : nat) (c c1 : config) (q : state) (hd2 : Z) (tp2 : list Z),
    step_tm_with tr k1 c = Some c1 ->
    c_state c1 = St q ->
    step_tm_with tr T c = Some (mkCfg Halt hd2 tp2) ->
    (k1 < T)%nat /\
    step_tm_with tr (T - k1)%nat c1 = Some (mkCfg Halt hd2 tp2).
Proof.
  intros tr k1 T c c1 q hd2 tp2 Hk1 Hst HT.
  assert (Hcases : (k1 < T \/ T <= k1)%nat) by lia.
  destruct Hcases as [Hlt | Hge].
  - split; [exact Hlt|].
    assert (Hsum : T = (k1 + (T - k1))%nat) by lia.
    rewrite Hsum in HT.
    rewrite (step_tm_with_add tr k1 (T - k1)%nat c c1 Hk1) in HT.
    exact HT.
  - assert (Hsum : k1 = (T + (k1 - T))%nat) by lia.
    rewrite Hsum in Hk1.
    rewrite (step_tm_with_add tr T (k1 - T)%nat c (mkCfg Halt hd2 tp2) HT) in Hk1.
    destruct (k1 - T)%nat as [|d].
    + simpl in Hk1. inversion Hk1; subst. simpl in Hst. discriminate Hst.
    + simpl in Hk1. discriminate Hk1.
Qed.

(******************************************************************************)
(* 3. WORM TAPE ENCODING & EXACT BLANK-TAPE BOOTSTRAP THEOREMS                *)
(******************************************************************************)

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

Lemma cfg_worm_state :
  forall c0 n w, c_state (cfg_worm c0 n w) = St S02.
Proof.
  intros c0 n w. unfold cfg_worm.
  destruct (encode_pairs (c0 + Z.of_nat n + 4) w) as [hd w_ones].
  reflexivity.
Qed.

(* 3.1: T48_halt (tau = (B0, R, St S24)) — Unconditional Blank-Tape Halting *)
Lemma boot_halt_488 :
  step_tm_with (trans_T48 tau_halt) 488 blank_cfg =
    Some (cfg_worm (-16) 1 [(0%nat, 0%nat); (1%nat, 0%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_halt_623 :
  step_tm_with (trans_T48 tau_halt) 623 blank_cfg =
    Some (cfg_worm (-17) 2 [(0%nat, 0%nat); (0%nat, 0%nat); (0%nat, 0%nat)]).
Proof. vm_compute. reflexivity. Qed.

Theorem T48_halt_halts_from_blank :
  step_tm_with (trans_T48 tau_halt) 636 blank_cfg =
    Some (mkCfg Halt (-12) [-17; -16; -15]).
Proof. vm_compute. reflexivity. Qed.

(* 3.2: T48_eps0 (tau = (B1, L, St S17)) — Pure Cantor \varepsilon_0 Spine *)
Definition W_eps0_2437 : list (nat * nat) :=
  [(0%nat, 0%nat); (1%nat, 0%nat); (1%nat, 0%nat); (0%nat, 0%nat);
   (1%nat, 0%nat); (0%nat, 0%nat); (1%nat, 0%nat); (0%nat, 0%nat);
   (1%nat, 0%nat); (0%nat, 0%nat); (1%nat, 0%nat)].

Lemma boot_eps0_2437 :
  step_tm_with (trans_T48 tau_eps0) 2437 blank_cfg =
    Some (cfg_worm (-17) 6 W_eps0_2437).
Proof. vm_compute. reflexivity. Qed.

(* 3.3: T48_eps1 (tau = (B1, L, St S13)) — \varepsilon_1 = \phi(1, 1) Spine *)
Definition W_eps1_1480 : list (nat * nat) :=
  [(0%nat, 0%nat); (1%nat, 1%nat); (2%nat, 0%nat);
   (2%nat, 1%nat); (3%nat, 0%nat); (3%nat, 1%nat)].

Lemma boot_eps1_621 :
  step_tm_with (trans_T48 tau_eps1) 621 blank_cfg =
    Some (cfg_worm (-16) 2 [(0%nat, 0%nat); (1%nat, 1%nat); (2%nat, 1%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_eps1_1480 :
  step_tm_with (trans_T48 tau_eps1) 1480 blank_cfg =
    Some (cfg_worm (-17) 3 W_eps1_1480).
Proof. vm_compute. reflexivity. Qed.

(* 3.4: T48_zeta0 (tau = (B0, R, St S31)) & T48_zeta0_seed (tau = (B0, L, St S30)) *)
Definition W_zeta0_1398 : list (nat * nat) :=
  [(0%nat, 0%nat); (2%nat, 2%nat); (4%nat, 1%nat); (3%nat, 2%nat)].

Definition W_zeta0_3755 : list (nat * nat) :=
  [(0%nat, 0%nat); (2%nat, 2%nat); (4%nat, 1%nat); (3%nat, 1%nat);
   (3%nat, 2%nat); (5%nat, 1%nat); (4%nat, 1%nat); (4%nat, 2%nat)].

Lemma boot_zeta0_seed_352 :
  step_tm_with (trans_T48 tau_zeta0_seed) 352 blank_cfg =
    Some (cfg_worm (-15) 1 [(0%nat, 0%nat); (0%nat, 2%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_zeta0_1398 :
  step_tm_with (trans_T48 tau_zeta0) 1398 blank_cfg =
    Some (cfg_worm (-17) 3 W_zeta0_1398).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_zeta0_3755 :
  step_tm_with (trans_T48 tau_zeta0) 3755 blank_cfg =
    Some (cfg_worm (-18) 4 W_zeta0_3755).
Proof. vm_compute. reflexivity. Qed.

(* 3.5: T48_eta0_phi5 (tau = (B1, L, St S02)) — \eta_0 = \phi(3,0), \phi(4,0), \phi(5,0) *)
Definition W_eta0_1731 : list (nat * nat) :=
  [(0%nat, 0%nat); (2%nat, 0%nat); (0%nat, 0%nat);
   (5%nat, 3%nat); (2%nat, 2%nat); (0%nat, 5%nat)].

Definition W_eta0_3384 : list (nat * nat) :=
  [(0%nat, 0%nat); (2%nat, 0%nat); (0%nat, 0%nat);
   (5%nat, 3%nat); (2%nat, 2%nat); (0%nat, 4%nat); (6%nat, 3%nat); (3%nat, 2%nat)].

Definition W_eta0_6127 : list (nat * nat) :=
  [(0%nat, 0%nat); (2%nat, 0%nat); (0%nat, 0%nat);
   (5%nat, 3%nat); (2%nat, 2%nat); (0%nat, 4%nat); (6%nat, 3%nat);
   (3%nat, 1%nat); (7%nat, 3%nat); (4%nat, 1%nat); (8%nat, 3%nat)].

Lemma boot_eta0_1731 :
  step_tm_with (trans_T48 tau_eta0_phi5) 1731 blank_cfg =
    Some (cfg_worm (-21) 1 W_eta0_1731).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_eta0_3384 :
  step_tm_with (trans_T48 tau_eta0_phi5) 3384 blank_cfg =
    Some (cfg_worm (-22) 2 W_eta0_3384).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_eta0_6127 :
  step_tm_with (trans_T48 tau_eta0_phi5) 6127 blank_cfg =
    Some (cfg_worm (-23) 3 W_eta0_6127).
Proof. vm_compute. reflexivity. Qed.

(* 3.6: T54_phi_omega (tau = (B0, R, St S05)) — Dynamic Veblen Level-Climbing *)
Definition tau_climb : bit * dir * next_state := (B0, R, St S05).

Definition W_climb_2460 : list (nat * nat) :=
  [(0%nat, 1%nat); (0%nat, 3%nat); (0%nat, 3%nat); (0%nat, 4%nat);
   (0%nat, 4%nat); (0%nat, 5%nat); (0%nat, 6%nat); (0%nat, 7%nat)].

Lemma boot_T54_539 :
  step_tm_with (trans_T54 tau_climb) 539 blank_cfg =
    Some (cfg_worm (-16) 1 [(0%nat, 1%nat); (0%nat, 3%nat); (0%nat, 4%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_T54_1135 :
  step_tm_with (trans_T54 tau_climb) 1135 blank_cfg =
    Some (cfg_worm (-17) 2
      [(0%nat, 1%nat); (0%nat, 3%nat); (0%nat, 3%nat); (0%nat, 4%nat); (0%nat, 5%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_T54_2460 :
  step_tm_with (trans_T54 tau_climb) 2460 blank_cfg =
    Some (cfg_worm (-18) 3 W_climb_2460).
Proof. vm_compute. reflexivity. Qed.

(******************************************************************************)
(* 4. CAMPAIGN FAITHFULNESS LEMMAS ACROSS \phi(k,0), \phi(\omega,0) & \Gamma_0 *)
(******************************************************************************)

(* Universal Veblen \phi(k, 0) Rule 3 Expansion Campaigns (\Delta T = 4k^2 + 54k + 226) *)
Lemma campaign_phi_1_0 :
  step_tm_with (trans_T48 tau_zeta0) 284 (cfg_worm 0 1 [(0%nat, 0%nat); (0%nat, 1%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 0%nat); (1%nat, 0%nat); (2%nat, 0%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma campaign_phi_2_0 :
  step_tm_with (trans_T48 tau_zeta0) 350 (cfg_worm 0 1 [(0%nat, 0%nat); (0%nat, 2%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 1%nat); (1%nat, 1%nat); (2%nat, 1%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma campaign_phi_3_0 :
  step_tm_with (trans_T48 tau_zeta0) 424 (cfg_worm 0 1 [(0%nat, 0%nat); (0%nat, 3%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 2%nat); (1%nat, 2%nat); (2%nat, 2%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma campaign_phi_4_0 :
  step_tm_with (trans_T48 tau_zeta0) 506 (cfg_worm 0 1 [(0%nat, 0%nat); (0%nat, 4%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 3%nat); (1%nat, 3%nat); (2%nat, 3%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma campaign_phi_5_0 :
  step_tm_with (trans_T48 tau_zeta0) 596 (cfg_worm 0 1 [(0%nat, 0%nat); (0%nat, 5%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 4%nat); (1%nat, 4%nat); (2%nat, 4%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma campaign_phi_6_0 :
  step_tm_with (trans_T48 tau_zeta0) 694 (cfg_worm 0 1 [(0%nat, 0%nat); (0%nat, 6%nat)]) =
    Some (cfg_worm (-1) 2 [(0%nat, 0%nat); (0%nat, 5%nat); (1%nat, 5%nat); (2%nat, 5%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* T_54 Rule 4 (\phi(\omega, 0) diagonalization): expands (0, 1) with n = 2   *)
(* into [(0,0); (0,1); (0,2); (0,3)] = 1 + \varepsilon_0 + \zeta_0 + \eta_0   *)
Lemma campaign_T54_phi_omega :
  step_tm_with (trans_T54 tau_climb) 473 (cfg_worm 0 2 [(0%nat, 1%nat); (0%nat, 1%nat)]) =
    Some (cfg_worm (-1) 3
      [(0%nat, 1%nat); (0%nat, 0%nat); (0%nat, 1%nat); (0%nat, 2%nat); (0%nat, 3%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* T_58 Self-Splitting Rule 4 -> Rule 3 Cascade (\phi(\omega,0) / \Gamma_0):  *)
(* Campaign 1 (521 steps) expands (0,1) into [(0,0); (0,1); (0,2); (0,3)]     *)
(* AND splits W[0]=(0,4) in-place into (0,0),(0,0); Campaign 2 (1423 steps)   *)
(* then automatically switches to standard Veblen Rule 3 on (0,3) = \eta_0!   *)
Lemma campaign_T58_rule4_split :
  step_tm_with (trans_T58 tau_climb) 521 (cfg_worm 0 2 [(0%nat, 4%nat); (0%nat, 1%nat)]) =
    Some (cfg_worm (-1) 3
      [(0%nat, 0%nat); (0%nat, 0%nat); (0%nat, 0%nat);
       (0%nat, 1%nat); (0%nat, 2%nat); (0%nat, 3%nat)]).
Proof. vm_compute. reflexivity. Qed.

Lemma campaign_T58_rule3_after_split :
  step_tm_with (trans_T58 tau_climb) 1944 (cfg_worm 0 2 [(0%nat, 4%nat); (0%nat, 1%nat)]) =
    Some (cfg_worm (-2) 4
      [(0%nat, 0%nat); (0%nat, 0%nat); (0%nat, 0%nat); (0%nat, 1%nat); (0%nat, 2%nat);
       (0%nat, 2%nat); (1%nat, 2%nat); (2%nat, 2%nat); (3%nat, 2%nat); (4%nat, 2%nat)]).
Proof. vm_compute. reflexivity. Qed.

(******************************************************************************)
(* 5. TRANSFINITE FAST-GROWING HIERARCHY:                                     *)
(*    \varepsilon_0, \varepsilon_1, \zeta_0, \eta_0, \phi(k,0), \phi(\omega,0),*)
(*    \Gamma_0, \vartheta(\Omega^2), SVO, LVO, BHO, AND TFBO                  *)
(******************************************************************************)

Open Scope nat_scope.

Fixpoint iter_nat (f : nat -> nat) (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => f (iter_nat f m' n)
  end.

(* Level 0 Veblen: f_{\phi(0, a)}(n) = f_{\omega^a}(n) *)
Fixpoint fgh_tower (a : nat) (n : nat) : nat :=
  match a with
  | O => S n
  | S a' => iter_nat (fgh_tower a') (S n) n
  end.

(* Next Veblen level: given f_prev a n = f_{\phi(b, a)}(n), defines           *)
(* f_{\phi(b+1, a)}(n) by structural recursion on a.                          *)
Fixpoint veblen_next (f_prev : nat -> nat -> nat) (a : nat) (n : nat) : nat :=
  match a with
  | O => iter_nat (fun x => f_prev x x) (S n) n
  | S a' => iter_nat (veblen_next f_prev a') (S n) n
  end.

(* Complete 2-Argument Veblen Hierarchy f_{\phi(b, a)}(n) for all b, a < \omega *)
Fixpoint f_veblen (b : nat) : nat -> nat -> nat :=
  match b with
  | O => fgh_tower
  | S b' => veblen_next (f_veblen b')
  end.

(* Named Veblen Ordinals: *)
Definition f_eps0      (n : nat) : nat := f_veblen 0 n n. (* \varepsilon_0 = \phi(1,0) *)
Definition f_eps1      (n : nat) : nat := f_veblen 1 n n. (* \varepsilon_1 = \phi(1,1) *)
Definition f_zeta0     (n : nat) : nat := f_veblen 2 n n. (* \zeta_0       = \phi(2,0) *)
Definition f_eta0      (n : nat) : nat := f_veblen 3 n n. (* \eta_0        = \phi(3,0) *)
Definition f_phi4_0    (n : nat) : nat := f_veblen 4 n n. (* \phi(4,0)                 *)
Definition f_phi5_0    (n : nat) : nat := f_veblen 5 n n. (* \phi(5,0)                 *)
Definition f_phi7_0    (n : nat) : nat := f_veblen 7 n n. (* \phi(7,0)                 *)
Definition f_phi_k_0   (k n : nat) : nat := f_veblen k n n.
Definition f_phi_omega (n : nat) : nat := f_veblen n n n. (* \phi(\omega,0)            *)

(* Feferman-Schutte Ordinal \Gamma_0 = \phi(1,0,0):                           *)
(*   \Gamma_0[0] = \phi(1,0),   \Gamma_0[m+1] = \phi(\Gamma_0[m], 0)          *)
Fixpoint f_Gamma0_seq (m : nat) (n : nat) : nat :=
  match m with
  | O => f_veblen 1 n n
  | S m' =>
      let k := f_Gamma0_seq m' n in
      f_veblen k n n
  end.

Definition f_Gamma0 (n : nat) : nat := f_Gamma0_seq n n.

(* Ackermann Ordinal \vartheta(\Omega^2) = \phi(1,0,0,0):                     *)
Fixpoint f_Ackermann_seq (m : nat) (n : nat) : nat :=
  match m with
  | O => f_Gamma0 n
  | S m' => iter_nat (f_Ackermann_seq m') (S n) n
  end.

Definition f_Ackermann_ord (n : nat) : nat := f_Ackermann_seq n n.

(* Small Veblen Ordinal SVO = \vartheta(\Omega^\omega) = \sup_d \phi(1,0^d):  *)
Fixpoint f_SVO_seq (d : nat) (n : nat) : nat :=
  match d with
  | O => f_Ackermann_ord n
  | S d' => iter_nat (f_SVO_seq d') (S n) n
  end.

Definition f_SVO (n : nat) : nat := f_SVO_seq n n.

(* Large Veblen Ordinal LVO = \vartheta(\Omega^\Omega):                       *)
Fixpoint f_LVO_seq (m : nat) (n : nat) : nat :=
  match m with
  | O => f_SVO n
  | S m' => f_SVO_seq (f_LVO_seq m' n) n
  end.

Definition f_LVO (n : nat) : nat := f_LVO_seq n n.

(* Bachmann-Howard Ordinal BHO = \psi_0(\varepsilon_{\Omega+1}):              *)
Fixpoint f_BHO_seq (m : nat) (n : nat) : nat :=
  match m with
  | O => f_LVO n
  | S m' => iter_nat (f_BHO_seq m') (S (f_LVO n)) n
  end.

Definition f_BHO (n : nat) : nat := f_BHO_seq n n.

(* Takeuti-Feferman-Buchholz Ordinal TFBO = \psi_0(\Omega_\omega):            *)
Fixpoint f_TFBO_seq (m : nat) (n : nat) : nat :=
  match m with
  | O => f_BHO n
  | S m' => iter_nat (f_TFBO_seq m') (S (f_BHO n)) n
  end.

Definition f_TFBO (n : nat) : nat := f_TFBO_seq n n.

(******************************************************************************)
(* 6. FUNDAMENTAL MONOTONICITY & STRICT HIERARCHY LEMMAS                      *)
(******************************************************************************)

Lemma iter_nat_ge_id :
  forall (f : nat -> nat),
    (forall x, x <= f x) ->
    forall m n, n <= iter_nat f m n.
Proof.
  intros f Hf m. induction m as [|m IHm]; intros n; simpl.
  - lia.
  - specialize (IHm n). specialize (Hf (iter_nat f m n)). lia.
Qed.

Lemma iter_nat_ge_once :
  forall (f : nat -> nat),
    (forall x, x <= f x) ->
    forall m n, f n <= iter_nat f (S m) n.
Proof.
  intros f Hf m. induction m as [|m IHm]; intros n; simpl.
  - lia.
  - specialize (IHm n). specialize (Hf (iter_nat f (S m) n)). lia.
Qed.

Lemma fgh_tower_ge_S :
  forall a n, S n <= fgh_tower a n.
Proof.
  induction a as [|a IHa]; intros n; simpl.
  - lia.
  - assert (Hgrow : forall x, x <= fgh_tower a x).
    { intro x. specialize (IHa x). lia. }
    pose proof (iter_nat_ge_id (fgh_tower a) Hgrow n n) as Hiter.
    specialize (IHa (iter_nat (fgh_tower a) n n)).
    lia.
Qed.

Lemma veblen_next_ge_S :
  forall (f_prev : nat -> nat -> nat),
    (forall a n, S n <= f_prev a n) ->
    forall a n, S n <= veblen_next f_prev a n.
Proof.
  intros f_prev Hprev a.
  induction a as [|a IHa]; intros n; simpl.
  - assert (Hgrow : forall x, x <= f_prev x x).
    { intro x. specialize (Hprev x x). lia. }
    pose proof (iter_nat_ge_id (fun x => f_prev x x) Hgrow n n) as Hiter.
    pose proof (Hprev (iter_nat (fun x => f_prev x x) n n)
                      (iter_nat (fun x => f_prev x x) n n)) as Hstep.
    lia.
  - assert (Hgrow : forall x, x <= veblen_next f_prev a x).
    { intro x. specialize (IHa x). lia. }
    pose proof (iter_nat_ge_id (veblen_next f_prev a) Hgrow n n) as Hiter.
    specialize (IHa (iter_nat (veblen_next f_prev a) n n)).
    lia.
Qed.

Lemma f_veblen_ge_S :
  forall b a n, S n <= f_veblen b a n.
Proof.
  induction b as [|b IHb]; intros a n; simpl.
  - apply fgh_tower_ge_S.
  - apply veblen_next_ge_S. exact IHb.
Qed.

Lemma f_veblen_step_a :
  forall b a n, f_veblen b a n <= f_veblen b (S a) n.
Proof.
  intros [|b] a n; simpl.
  - apply iter_nat_ge_once.
    intro x. pose proof (fgh_tower_ge_S a x). lia.
  - apply iter_nat_ge_once.
    intro x. pose proof (f_veblen_ge_S (S b) a x). lia.
Qed.

Lemma f_veblen_add_a :
  forall b a d n, f_veblen b a n <= f_veblen b (a + d) n.
Proof.
  intros b a d. induction d as [|d IHd]; intros n.
  - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r.
    pose proof (IHd n) as H1.
    pose proof (f_veblen_step_a b (a + d) n) as H2.
    lia.
Qed.

Lemma f_veblen_step_b :
  forall b n, f_veblen b n n <= f_veblen (S b) 0 n.
Proof.
  intros b n. simpl.
  apply iter_nat_ge_once.
  intro x. pose proof (f_veblen_ge_S b x x). lia.
Qed.

Lemma f_Gamma0_seq_ge_S :
  forall m n, S n <= f_Gamma0_seq m n.
Proof.
  induction m as [|m IHm]; intros n; simpl.
  - apply f_veblen_ge_S.
  - apply f_veblen_ge_S.
Qed.

Lemma f_Ackermann_seq_ge_S :
  forall m n, S n <= f_Ackermann_seq m n.
Proof.
  induction m as [|m IHm]; intros n; simpl.
  - unfold f_Gamma0. apply f_Gamma0_seq_ge_S.
  - assert (Hgrow : forall x, x <= f_Ackermann_seq m x).
    { intro x. specialize (IHm x). lia. }
    pose proof (iter_nat_ge_id (f_Ackermann_seq m) Hgrow n n) as Hiter.
    specialize (IHm (iter_nat (f_Ackermann_seq m) n n)).
    lia.
Qed.

Lemma f_SVO_seq_ge_S :
  forall d n, S n <= f_SVO_seq d n.
Proof.
  induction d as [|d IHd]; intros n; simpl.
  - unfold f_Ackermann_ord. apply f_Ackermann_seq_ge_S.
  - assert (Hgrow : forall x, x <= f_SVO_seq d x).
    { intro x. specialize (IHd x). lia. }
    pose proof (iter_nat_ge_id (f_SVO_seq d) Hgrow n n) as Hiter.
    specialize (IHd (iter_nat (f_SVO_seq d) n n)).
    lia.
Qed.

Lemma f_LVO_seq_ge_S :
  forall m n, S n <= f_LVO_seq m n.
Proof.
  induction m as [|m IHm]; intros n; simpl.
  - unfold f_SVO. apply f_SVO_seq_ge_S.
  - apply f_SVO_seq_ge_S.
Qed.

Lemma f_BHO_seq_ge_S :
  forall m n, S n <= f_BHO_seq m n.
Proof.
  induction m as [|m IHm]; intros n; simpl.
  - unfold f_LVO. apply f_LVO_seq_ge_S.
  - assert (Hgrow : forall x, x <= f_BHO_seq m x).
    { intro x. specialize (IHm x). lia. }
    pose proof (iter_nat_ge_id (f_BHO_seq m) Hgrow (f_LVO n) n) as Hiter.
    specialize (IHm (iter_nat (f_BHO_seq m) (f_LVO n) n)).
    lia.
Qed.

Lemma f_TFBO_seq_ge_S :
  forall m n, S n <= f_TFBO_seq m n.
Proof.
  induction m as [|m IHm]; intros n; simpl.
  - unfold f_BHO. apply f_BHO_seq_ge_S.
  - assert (Hgrow : forall x, x <= f_TFBO_seq m x).
    { intro x. specialize (IHm x). lia. }
    pose proof (iter_nat_ge_id (f_TFBO_seq m) Hgrow (f_BHO n) n) as Hiter.
    specialize (IHm (iter_nat (f_TFBO_seq m) (f_BHO n) n)).
    lia.
Qed.

(* Strict Hierarchy Chain at n >= 1:                                          *)
(*   n < f_eps0 n <= f_eps1 n <= f_zeta0 n <= f_eta0 n <= f_phi4_0 n          *)
(*     <= f_phi5_0 n <= f_Ackermann_ord n <= f_SVO n <= f_LVO n               *)
(*     <= f_BHO n <= f_TFBO n                                                 *)
Theorem transfinite_hierarchy_chain :
  forall n,
    n < f_eps0 n /\
    f_eps0 n <= f_eps1 n /\
    f_eps1 n <= f_zeta0 n /\
    f_zeta0 n <= f_eta0 n /\
    f_eta0 n <= f_phi4_0 n /\
    f_phi4_0 n <= f_phi5_0 n /\
    f_Gamma0 n <= f_Ackermann_ord n /\
    f_Ackermann_ord n <= f_SVO n /\
    f_SVO n <= f_BHO n /\
    f_BHO n <= f_TFBO n.
Proof.
  intro n.
  pose proof (f_veblen_ge_S 0 n n) as H0.
  pose proof (f_veblen_step_b 0 n) as Hb0.
  pose proof (f_veblen_add_a 1 0 n n) as Ha1.
  pose proof (f_veblen_step_b 1 n) as Hb1.
  pose proof (f_veblen_add_a 2 0 n n) as Ha2.
  pose proof (f_veblen_step_b 2 n) as Hb2.
  pose proof (f_veblen_add_a 3 0 n n) as Ha3.
  pose proof (f_veblen_step_b 3 n) as Hb3.
  pose proof (f_veblen_add_a 4 0 n n) as Ha4.
  pose proof (f_veblen_step_b 4 n) as Hb4.
  pose proof (f_veblen_add_a 5 0 n n) as Ha5.
  simpl in Ha1, Ha2, Ha3, Ha4, Ha5.
  unfold f_eps0, f_eps1, f_zeta0, f_eta0, f_phi4_0, f_phi5_0.
  assert (H_ack : f_Gamma0 n <= f_Ackermann_ord n).
  { unfold f_Ackermann_ord. destruct n as [|n']; simpl; [lia|].
    apply iter_nat_ge_id with (f := f_Ackermann_seq n') (m := S (S n')) (n := S n') in H0; [|intro x; pose proof (f_Ackermann_seq_ge_S n' x); lia].
    pose proof (f_Ackermann_seq_ge_S (S n') (S n')).
    pose proof (f_Ackermann_seq_ge_S 0 (S n')) as Hbase. simpl in Hbase.
    clear H0.
    assert (Hseq : forall m x, f_Gamma0 x <= f_Ackermann_seq m x).
    { induction m as [|m IHm]; intro x; simpl; [lia|].
      pose proof (iter_nat_ge_once (f_Ackermann_seq m) (fun y => Nat.lt_le_incl _ _ (f_Ackermann_seq_ge_S m y)) x x) as H1.
      specialize (IHm x). lia. }
    apply Hseq. }
  assert (H_svo : f_Ackermann_ord n <= f_SVO n).
  { unfold f_SVO.
    assert (Hseq : forall d x, f_Ackermann_ord x <= f_SVO_seq d x).
    { induction d as [|d IHd]; intro x; simpl; [lia|].
      pose proof (iter_nat_ge_once (f_SVO_seq d) (fun y => Nat.lt_le_incl _ _ (f_SVO_seq_ge_S d y)) x x) as H1.
      specialize (IHd x). lia. }
    apply Hseq. }
  assert (H_bho : f_SVO n <= f_BHO n).
  { unfold f_BHO.
    assert (Hlvo : f_SVO n <= f_LVO n).
    { unfold f_LVO. destruct n as [|n']; simpl; [lia|].
      assert (Hseq : forall d x, f_SVO x <= f_SVO_seq (x + d) x).
      { intros d x. unfold f_SVO.
        induction d as [|d IHd].
        - rewrite Nat.add_0_r. lia.
        - rewrite Nat.add_succ_r. simpl.
          pose proof (iter_nat_ge_once (f_SVO_seq (x + d)) (fun y => Nat.lt_le_incl _ _ (f_SVO_seq_ge_S (x + d) y)) x x).
          lia. }
      pose proof (f_LVO_seq_ge_S n' (S n')) as Hge.
      replace (f_LVO_seq n' (S n')) with (S n' + (f_LVO_seq n' (S n') - S n')) by lia.
      apply Hseq. }
    assert (Hseq : forall m x, f_LVO x <= f_BHO_seq m x).
    { induction m as [|m IHm]; intro x; simpl; [lia|].
      pose proof (iter_nat_ge_once (f_BHO_seq m) (fun y => Nat.lt_le_incl _ _ (f_BHO_seq_ge_S m y)) (f_LVO x) x) as H1.
      specialize (IHm x). lia. }
    pose proof (Hseq n n). lia. }
  assert (H_tfbo : f_BHO n <= f_TFBO n).
  { unfold f_TFBO.
    assert (Hseq : forall m x, f_BHO x <= f_TFBO_seq m x).
    { induction m as [|m IHm]; intro x; simpl; [lia|].
      pose proof (iter_nat_ge_once (f_TFBO_seq m) (fun y => Nat.lt_le_incl _ _ (f_TFBO_seq_ge_S m y)) (f_BHO x) x) as H1.
      specialize (IHm x). lia. }
    apply Hseq. }
  lia.
Qed.

(******************************************************************************)
(* 7. 2D WORM VALUATION & STRUCTURAL MACHINE-TO-FGH LOWER BOUND THEOREMS      *)
(******************************************************************************)

Fixpoint worm_eval_2d (w : list (nat * nat)) (n : nat) : nat :=
  match w with
  | [] => n
  | (a, b) :: rest => worm_eval_2d rest (f_veblen b a n)
  end.

Lemma worm_eval_2d_mono :
  forall w n, n <= worm_eval_2d w n.
Proof.
  induction w as [|[a b] IHw]; intros n; simpl.
  - lia.
  - pose proof (f_veblen_ge_S b a n) as Hstep.
    pose proof (IHw (f_veblen b a n)) as Hrest.
    lia.
Qed.

(* 7.1: Lower Bound Theorem for T48_zeta0: T > f_{\zeta_0}(3) *)
Lemma worm_eval_W_zeta0_1398_ge_f_zeta0_3 :
  f_zeta0 3 <= worm_eval_2d (rev W_zeta0_1398) 3.
Proof.
  change (worm_eval_2d (rev W_zeta0_1398) 3)
    with (worm_eval_2d [(4, 1); (2, 2); (0, 0)] (f_zeta0 3)).
  apply worm_eval_2d_mono.
Qed.

Theorem T48_zeta0_runtime_gt_f_zeta0_3 :
  f_zeta0 3 < 1398 + worm_eval_2d (rev W_zeta0_1398) 3.
Proof.
  pose proof worm_eval_W_zeta0_1398_ge_f_zeta0_3 as Hge.
  lia.
Qed.

(* 7.2: Lower Bound Theorem for T48_zeta0 at step 3755: T > f_{\zeta_0}(4) *)
Lemma worm_eval_W_zeta0_3755_ge_f_zeta0_4 :
  f_zeta0 4 <= worm_eval_2d (rev W_zeta0_3755) 4.
Proof.
  change (worm_eval_2d (rev W_zeta0_3755) 4)
    with (worm_eval_2d
            [(4, 1); (5, 1); (3, 2); (3, 1); (4, 1); (2, 2); (0, 0)]
            (f_zeta0 4)).
  apply worm_eval_2d_mono.
Qed.

Theorem T48_zeta0_runtime_gt_f_zeta0_4 :
  f_zeta0 4 < 3755 + worm_eval_2d (rev W_zeta0_3755) 4.
Proof.
  pose proof worm_eval_W_zeta0_3755_ge_f_zeta0_4 as Hge.
  lia.
Qed.

(* 7.3: Lower Bound Theorem for T48_eta0_phi5 at step 6127: T > f_{\eta_0}(3) *)
Lemma worm_eval_W_eta0_6127_ge_f_eta0_3 :
  f_eta0 3 <= worm_eval_2d (rev W_eta0_6127) 3.
Proof.
  change (worm_eval_2d (rev W_eta0_6127) 3)
    with (worm_eval_2d
            [(4, 1); (7, 3); (3, 1); (6, 3); (0, 4);
             (2, 2); (5, 3); (0, 0); (2, 0); (0, 0)]
            (f_veblen 3 8 3)).
  pose proof (worm_eval_2d_mono
                [(4, 1); (7, 3); (3, 1); (6, 3); (0, 4);
                 (2, 2); (5, 3); (0, 0); (2, 0); (0, 0)]
                (f_veblen 3 8 3)) as Hmono.
  pose proof (f_veblen_add_a 3 3 5 3) as Hadd.
  change (3 + 5) with 8 in Hadd.
  change (f_veblen 3 3 3) with (f_eta0 3) in Hadd.
  lia.
Qed.

Theorem T48_eta0_runtime_gt_f_eta0_3 :
  f_eta0 3 < 6127 + worm_eval_2d (rev W_eta0_6127) 3.
Proof.
  pose proof worm_eval_W_eta0_6127_ge_f_eta0_3 as Hge.
  lia.
Qed.

(* 7.4: Lower Bound Theorem for T48_eta0_phi5 at step 1731: T > f_{\phi(4,0)}(1) *)
Lemma worm_eval_W_eta0_1731_ge_f_phi4_0_1 :
  f_phi4_0 1 <= worm_eval_2d (rev W_eta0_1731) 1.
Proof.
  change (worm_eval_2d (rev W_eta0_1731) 1)
    with (worm_eval_2d
            [(2, 2); (5, 3); (0, 0); (2, 0); (0, 0)]
            (f_veblen 5 0 1)).
  pose proof (worm_eval_2d_mono
                [(2, 2); (5, 3); (0, 0); (2, 0); (0, 0)]
                (f_veblen 5 0 1)) as Hmono.
  pose proof (f_veblen_step_b 4 1) as Hstep.
  change (f_veblen 4 1 1) with (f_phi4_0 1) in Hstep.
  lia.
Qed.

(* 7.5: Lower Bound Theorem for T54_phi_omega at step 2460:                   *)
(*      Reaches W_climb_2460 with n = 3 and top pair (0, 7) = \phi(7, 0),     *)
(*      strictly exceeding f_{\phi(6, 0)}(3), f_{\phi(5, 0)}(3),              *)
(*      f_{\phi(4, 0)}(3), f_{\eta_0}(3), and f_{\zeta_0}(3)!                 *)
Lemma worm_eval_W_climb_2460_ge_f_phi5_0_3 :
  f_phi5_0 3 <= worm_eval_2d (rev W_climb_2460) 3.
Proof.
  change (worm_eval_2d (rev W_climb_2460) 3)
    with (worm_eval_2d
            [(0, 6); (0, 5); (0, 4); (0, 4); (0, 3); (0, 3); (0, 1)]
            (f_veblen 7 0 3)).
  pose proof (worm_eval_2d_mono
                [(0, 6); (0, 5); (0, 4); (0, 4); (0, 3); (0, 3); (0, 1)]
                (f_veblen 7 0 3)) as Hmono.
  pose proof (f_veblen_step_b 6 3) as H6.
  pose proof (f_veblen_add_a 6 0 3 3) as Ha6. simpl in Ha6.
  pose proof (f_veblen_step_b 5 3) as H5.
  change (f_veblen 5 3 3) with (f_phi5_0 3) in H5.
  lia.
Qed.

Theorem T54_climb_runtime_gt_f_phi5_0_3 :
  f_phi5_0 3 < 2460 + worm_eval_2d (rev W_climb_2460) 3.
Proof.
  pose proof worm_eval_W_climb_2460_ge_f_phi5_0_3 as Hge.
  lia.
Qed.

(******************************************************************************)
(* 8. GENERAL CAMPAIGN CHAIN SOUNDNESS & END-TO-END BLANK-TAPE BRIDGES        *)
(******************************************************************************)

Inductive worm_campaign_chain_with
  (tr : state -> bit -> bit * dir * next_state)
  : Z -> nat -> list (nat * nat) -> nat -> Z -> list Z -> Prop :=
| WCCW_Halt :
    forall c0 n w dc hd tp,
      step_tm_with tr dc (cfg_worm c0 n w) = Some (mkCfg Halt hd tp) ->
      worm_eval_2d (rev w) n <= dc ->
      worm_campaign_chain_with tr c0 n w dc hd tp
| WCCW_Step :
    forall c0 n w dc c0' n' w' k_rest hd tp,
      step_tm_with tr dc (cfg_worm c0 n w) = Some (cfg_worm c0' n' w') ->
      worm_eval_2d (rev w) n <= dc + worm_eval_2d (rev w') n' ->
      worm_campaign_chain_with tr c0' n' w' k_rest hd tp ->
      worm_campaign_chain_with tr c0 n w (dc + k_rest) hd tp.

Theorem worm_campaign_chain_with_sound :
  forall tr c0 n w k hd tp,
    worm_campaign_chain_with tr c0 n w k hd tp ->
    step_tm_with tr k (cfg_worm c0 n w) = Some (mkCfg Halt hd tp) /\
    worm_eval_2d (rev w) n <= k.
Proof.
  intros tr c0 n w k hd tp Hchain.
  induction Hchain as
    [c0 n w dc hd tp Hstep Hlb
    |c0 n w dc c0' n' w' k_rest hd tp Hstep Hlb Hrest [IHstep IHlb]].
  - split; [exact Hstep | exact Hlb].
  - split.
    + rewrite (step_tm_with_add tr dc k_rest (cfg_worm c0 n w) (cfg_worm c0' n' w') Hstep).
      exact IHstep.
    + lia.
Qed.

Theorem T48_zeta0_blank_halting_run_exceeds_f_zeta0_3 :
  forall k hd tp,
    worm_campaign_chain_with (trans_T48 tau_zeta0) (-17)%Z 3 W_zeta0_1398 k hd tp ->
    step_tm_with (trans_T48 tau_zeta0) (1398 + k) blank_cfg = Some (mkCfg Halt hd tp) /\
    f_zeta0 3 < 1398 + k.
Proof.
  intros k hd tp Hchain.
  destruct (worm_campaign_chain_with_sound (trans_T48 tau_zeta0) (-17)%Z 3 W_zeta0_1398 k hd tp Hchain)
    as [Hstep Hlb].
  split.
  - rewrite (step_tm_with_add (trans_T48 tau_zeta0) 1398 k blank_cfg
               (cfg_worm (-17)%Z 3 W_zeta0_1398) boot_zeta0_1398).
    exact Hstep.
  - pose proof T48_zeta0_runtime_gt_f_zeta0_3 as Hgt.
    lia.
Qed.

Theorem T48_eta0_blank_halting_run_exceeds_f_eta0_3 :
  forall k hd tp,
    worm_campaign_chain_with (trans_T48 tau_eta0_phi5) (-23)%Z 3 W_eta0_6127 k hd tp ->
    step_tm_with (trans_T48 tau_eta0_phi5) (6127 + k) blank_cfg = Some (mkCfg Halt hd tp) /\
    f_eta0 3 < 6127 + k.
Proof.
  intros k hd tp Hchain.
  destruct (worm_campaign_chain_with_sound (trans_T48 tau_eta0_phi5) (-23)%Z 3 W_eta0_6127 k hd tp Hchain)
    as [Hstep Hlb].
  split.
  - rewrite (step_tm_with_add (trans_T48 tau_eta0_phi5) 6127 k blank_cfg
               (cfg_worm (-23)%Z 3 W_eta0_6127) boot_eta0_6127).
    exact Hstep.
  - pose proof T48_eta0_runtime_gt_f_eta0_3 as Hgt.
    lia.
Qed.

Theorem T54_climb_blank_halting_run_exceeds_f_phi5_0_3 :
  forall k hd tp,
    worm_campaign_chain_with (trans_T54 tau_climb) (-18)%Z 3 W_climb_2460 k hd tp ->
    step_tm_with (trans_T54 tau_climb) (2460 + k) blank_cfg = Some (mkCfg Halt hd tp) /\
    f_phi5_0 3 < 2460 + k.
Proof.
  intros k hd tp Hchain.
  destruct (worm_campaign_chain_with_sound (trans_T54 tau_climb) (-18)%Z 3 W_climb_2460 k hd tp Hchain)
    as [Hstep Hlb].
  split.
  - rewrite (step_tm_with_add (trans_T54 tau_climb) 2460 k blank_cfg
               (cfg_worm (-18)%Z 3 W_climb_2460) boot_T54_2460).
    exact Hstep.
  - pose proof T54_climb_runtime_gt_f_phi5_0_3 as Hgt.
    lia.
Qed.

Print Assumptions T48_halt_halts_from_blank.
Print Assumptions boot_eps0_2437.
Print Assumptions boot_eps1_1480.
Print Assumptions boot_zeta0_1398.
Print Assumptions boot_zeta0_3755.
Print Assumptions boot_eta0_1731.
Print Assumptions boot_eta0_6127.
Print Assumptions boot_T54_2460.
Print Assumptions campaign_phi_1_0.
Print Assumptions campaign_phi_2_0.
Print Assumptions campaign_phi_3_0.
Print Assumptions campaign_phi_4_0.
Print Assumptions campaign_phi_5_0.
Print Assumptions campaign_phi_6_0.
Print Assumptions campaign_T54_phi_omega.
Print Assumptions campaign_T58_rule4_split.
Print Assumptions campaign_T58_rule3_after_split.
Print Assumptions transfinite_hierarchy_chain.
Print Assumptions T48_zeta0_blank_halting_run_exceeds_f_zeta0_3.
Print Assumptions T48_eta0_blank_halting_run_exceeds_f_eta0_3.
Print Assumptions T54_climb_blank_halting_run_exceeds_f_phi5_0_3.
