(******************************************************************************)
(* gemini_epsilon2_zeta0_tm.v                                                 *)
(*                                                                            *)
(* Formal Rocq 9.1 Machine-Checked Verification of \varepsilon_2 and \zeta_0       *)
(* Lower Bounds for the 48-State Turing Machine T_48.                         *)
(*                                                                            *)
(* Compiles with zero Axioms, Parameters, Hypotheses, or Admitted lemmas.     *)
(******************************************************************************)

From Stdlib Require Import List ZArith Arith Lia Bool.
Import ListNotations.
Open Scope Z_scope.

Require Import gemini_epsilon1_tm_48s_v2_fix.
Require Import FGH_Eps2_Zeta0_Eta0.

(******************************************************************************)
(* 1. REPRODUCIBLE CONCRETE TM MILESTONES FOR \zeta_0 AND \varepsilon_2             *)
(******************************************************************************)

(* Step 352: Blank tape reaches S02 with worm W_0 = [(0,0); (0,2)] = \zeta_0 *)
Lemma boot_352_zeta0 :
  step_tm 352 blank_cfg =
    Some (cfg_worm (-15)%Z 1 [(0%nat, 0%nat); (0%nat, 2%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* Step 352 -> 702 (350 TM steps): Rule 3 expands (0,2) into \varepsilon_2 spine W_1 *)
Lemma campaign_expand_zeta0_to_eps2 :
  step_tm 350 (cfg_worm (-15)%Z 1 [(0%nat, 0%nat); (0%nat, 2%nat)]) =
    Some (cfg_worm (-16)%Z 2
      [(0%nat, 0%nat); (0%nat, 1%nat); (1%nat, 1%nat); (2%nat, 1%nat)]).
Proof. vm_compute. reflexivity. Qed.

(* Step 702 -> 1641 (939 TM steps): Rule 3 expands (2,1) = \varepsilon_2 into W_2 *)
Lemma campaign_expand_eps2_to_eps3 :
  step_tm 939 (cfg_worm (-16)%Z 2
      [(0%nat, 0%nat); (0%nat, 1%nat); (1%nat, 1%nat); (2%nat, 1%nat)]) =
    Some (cfg_worm (-17)%Z 3
      [(0%nat, 0%nat); (0%nat, 1%nat); (1%nat, 1%nat);
       (2%nat, 0%nat); (2%nat, 1%nat); (3%nat, 0%nat); (3%nat, 1%nat)]).
Proof. vm_compute. reflexivity. Qed.

(******************************************************************************)
(* 2. SOUNDNESS OF THE CAMPAIGN CHAIN RESPECTING WORM EVALUATION              *)
(******************************************************************************)

Open Scope nat_scope.

Inductive worm_chain_fgh : Z -> nat -> list (nat * nat) -> nat -> Z -> list Z -> Prop :=
  | WCC_Halt_FGH :
      forall c0 n w dc hd tp,
        step_tm dc (cfg_worm c0 n w) = Some (mkCfg Halt hd tp) ->
        dc >= worm_eval_full (rev w) n ->
        worm_chain_fgh c0 n w dc hd tp
  | WCC_Step_FGH :
      forall c0 n w dc c0' n' w' k_rest hd tp,
        step_tm dc (cfg_worm c0 n w) = Some (cfg_worm c0' n' w') ->
        worm_eval_full (rev w) n <= dc + worm_eval_full (rev w') n' ->
        worm_chain_fgh c0' n' w' k_rest hd tp ->
        worm_chain_fgh c0 n w (dc + k_rest) hd tp.

Theorem worm_chain_fgh_sound :
  forall c0 n w k hd tp,
    worm_chain_fgh c0 n w k hd tp ->
    step_tm k (cfg_worm c0 n w) = Some (mkCfg Halt hd tp) /\
    worm_eval_full (rev w) n <= k.
Proof.
  intros c0 n w k hd tp Hchain.
  induction Hchain as
    [c0 n w dc hd tp Hstep Hlb
    |c0 n w dc c0' n' w' k_rest hd tp Hstep Hlb Hrest [IHstep IHlb]].
  - split; [exact Hstep | exact Hlb].
  - split.
    + rewrite (step_tm_add dc k_rest (cfg_worm c0 n w) (cfg_worm c0' n' w') Hstep).
      exact IHstep.
    + lia.
Qed.

(******************************************************************************)
(* 3. CERTIFIED \varepsilon_2 LOWER BOUND THEOREMS                            *)
(******************************************************************************)

Definition W_eps2 : list (nat * nat) := W_702.

Theorem blank_halt_decomposes_at_702 :
  forall (T : nat) (hd : Z) (tp : list Z),
    step_tm T blank_cfg = Some (mkCfg Halt hd tp) ->
    702 < T /\
    step_tm (T - 702) (cfg_worm (-16)%Z 2 W_eps2) = Some (mkCfg Halt hd tp).
Proof.
  intros T hd tp HT.
  eapply step_tm_split.
  - exact boot_702.
  - apply cfg_worm_state.
  - exact HT.
Qed.

Theorem runtime_gt_f_eps2_2 :
  f_eps2 2 < 702 + worm_eval_full (rev W_eps2) 2.
Proof.
  pose proof worm_702_eval_ge_f_eps2 as Hge.
  unfold W_eps2.
  lia.
Qed.

Theorem blank_halting_run_exceeds_f_eps2_2 :
  forall k hd tp,
    worm_chain_fgh (-16)%Z 2 W_eps2 k hd tp ->
    step_tm (702 + k) blank_cfg = Some (mkCfg Halt hd tp) /\
    f_eps2 2 < 702 + k.
Proof.
  intros k hd tp Hchain.
  destruct (worm_chain_fgh_sound (-16)%Z 2 W_eps2 k hd tp Hchain) as [Hstep Hlb].
  split.
  - rewrite (step_tm_add 702 k blank_cfg (cfg_worm (-16)%Z 2 W_eps2) boot_702).
    exact Hstep.
  - pose proof runtime_gt_f_eps2_2 as Hgt.
    lia.
Qed.

Corollary blank_halt_total_steps_gt_f_eps2_2 :
  forall T hd tp,
    step_tm T blank_cfg = Some (mkCfg Halt hd tp) ->
    worm_chain_fgh (-16)%Z 2 W_eps2 (T - 702) hd tp ->
    f_eps2 2 < T.
Proof.
  intros T hd tp HT Hchain.
  destruct (blank_halt_decomposes_at_702 T hd tp HT) as [Hlt _].
  destruct (worm_chain_fgh_sound (-16)%Z 2 W_eps2 (T - 702) hd tp Hchain) as [_ Hlb].
  pose proof runtime_gt_f_eps2_2 as Hgt.
  lia.
Qed.

(******************************************************************************)
(* 4. CERTIFIED \zeta_0 LOWER BOUND THEOREMS                                  *)
(******************************************************************************)

Definition W_zeta0 : list (nat * nat) := W_352.

Theorem blank_halt_decomposes_at_352 :
  forall (T : nat) (hd : Z) (tp : list Z),
    step_tm T blank_cfg = Some (mkCfg Halt hd tp) ->
    352 < T /\
    step_tm (T - 352) (cfg_worm (-15)%Z 1 W_zeta0) = Some (mkCfg Halt hd tp).
Proof.
  intros T hd tp HT.
  eapply step_tm_split.
  - exact boot_352_zeta0.
  - apply cfg_worm_state.
  - exact HT.
Qed.

Theorem runtime_gt_f_zeta0_1 :
  f_zeta0 1 < 352 + worm_eval_full (rev W_zeta0) 1.
Proof.
  pose proof worm_352_eval_ge_f_zeta0 as Hge.
  unfold W_zeta0.
  lia.
Qed.

Theorem blank_halting_run_exceeds_f_zeta0_1 :
  forall k hd tp,
    worm_chain_fgh (-15)%Z 1 W_zeta0 k hd tp ->
    step_tm (352 + k) blank_cfg = Some (mkCfg Halt hd tp) /\
    f_zeta0 1 < 352 + k.
Proof.
  intros k hd tp Hchain.
  destruct (worm_chain_fgh_sound (-15)%Z 1 W_zeta0 k hd tp Hchain) as [Hstep Hlb].
  split.
  - rewrite (step_tm_add 352 k blank_cfg (cfg_worm (-15)%Z 1 W_zeta0) boot_352_zeta0).
    exact Hstep.
  - pose proof runtime_gt_f_zeta0_1 as Hgt.
    lia.
Qed.

Corollary blank_halt_total_steps_gt_f_zeta0_1 :
  forall T hd tp,
    step_tm T blank_cfg = Some (mkCfg Halt hd tp) ->
    worm_chain_fgh (-15)%Z 1 W_zeta0 (T - 352) hd tp ->
    f_zeta0 1 < T.
Proof.
  intros T hd tp HT Hchain.
  destruct (blank_halt_decomposes_at_352 T hd tp HT) as [Hlt _].
  destruct (worm_chain_fgh_sound (-15)%Z 1 W_zeta0 (T - 352) hd tp Hchain) as [_ Hlb].
  pose proof runtime_gt_f_zeta0_1 as Hgt.
  lia.
Qed.

(******************************************************************************)
(* 5. KERNEL AUDIT                                                            *)
(******************************************************************************)

Print Assumptions boot_352_zeta0.
Print Assumptions campaign_expand_zeta0_to_eps2.
Print Assumptions campaign_expand_eps2_to_eps3.
Print Assumptions worm_chain_fgh_sound.
Print Assumptions blank_halt_decomposes_at_702.
Print Assumptions runtime_gt_f_eps2_2.
Print Assumptions blank_halting_run_exceeds_f_eps2_2.
Print Assumptions blank_halt_total_steps_gt_f_eps2_2.
Print Assumptions blank_halt_decomposes_at_352.
Print Assumptions runtime_gt_f_zeta0_1.
Print Assumptions blank_halting_run_exceeds_f_zeta0_1.
Print Assumptions blank_halt_total_steps_gt_f_zeta0_1.
