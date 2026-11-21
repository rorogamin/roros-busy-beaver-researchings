(*
  rocq/Fwpw_5.v
  Reusable, axiom-free Rocq 9.1 formalization of the 12-state 5-symbol f_{ω^ω} core
  (parameterized by state indices sA..sL so it works directly for A-, B-, and H-based variants).
  Powers 10 champions: BB(13..16,5), BB(13..16,6), BB(13..14,7).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8.
Import ListNotations.

Record Fwpw_5Core (tm : TM) (sA sB sC sD sE sF sG sH sI sJ sK sL : nat) : Prop := mkFwpw_5Core {
  w5_A1 : tm sA 1 = Some (mkAction 3 DL (Some sB));
  w5_A3 : tm sA 3 = Some (mkAction 2 DR (Some sA));
  w5_A4 : tm sA 4 = Some (mkAction 3 DL (Some sL));
  w5_B1 : tm sB 1 = Some (mkAction 3 DR (Some sB));
  w5_B2 : tm sB 2 = Some (mkAction 1 DL (Some sD));
  w5_B3 : tm sB 3 = Some (mkAction 2 DR (Some sA));
  w5_C0 : tm sC 0 = Some (mkAction 3 DR (Some sB));
  w5_C1 : tm sC 1 = Some (mkAction 1 DL (Some sB));
  w5_C2 : tm sC 2 = Some (mkAction 3 DL (Some sC));
  w5_C3 : tm sC 3 = Some (mkAction 2 DR (Some sC));
  w5_D0 : tm sD 0 = Some (mkAction 2 DR (Some sE));
  w5_D2 : tm sD 2 = Some (mkAction 3 DL (Some sC));
  w5_D3 : tm sD 3 = Some (mkAction 2 DR (Some sC));
  w5_E0 : tm sE 0 = Some (mkAction 3 DR (Some sB));
  w5_E1 : tm sE 1 = Some (mkAction 2 DR (Some sE));
  w5_E2 : tm sE 2 = Some (mkAction 2 DR (Some sE));
  w5_E3 : tm sE 3 = Some (mkAction 4 DR (Some sF));
  w5_F0 : tm sF 0 = Some (mkAction 1 DL (Some sG));
  w5_F1 : tm sF 1 = Some (mkAction 1 DR (Some sF));
  w5_F2 : tm sF 2 = Some (mkAction 3 DL (Some sG));
  w5_F3 : tm sF 3 = Some (mkAction 3 DR (Some sF));
  w5_F4 : tm sF 4 = Some (mkAction 4 DL (Some sG));
  w5_G0 : tm sG 0 = Some (mkAction 2 DR (Some sJ));
  w5_G1 : tm sG 1 = Some (mkAction 0 DL (Some sH));
  w5_G2 : tm sG 2 = Some (mkAction 2 DL (Some sG));
  w5_G3 : tm sG 3 = Some (mkAction 2 DL (Some sI));
  w5_G4 : tm sG 4 = Some (mkAction 4 DL (Some sK));
  w5_H1 : tm sH 1 = Some (mkAction 1 DL (Some sH));
  w5_H2 : tm sH 2 = Some (mkAction 1 DL (Some sG));
  w5_H3 : tm sH 3 = Some (mkAction 3 DL (Some sH));
  w5_H4 : tm sH 4 = Some (mkAction 4 DL (Some sH));
  w5_I1 : tm sI 1 = Some (mkAction 1 DL (Some sI));
  w5_I2 : tm sI 2 = Some (mkAction 3 DL (Some sG));
  w5_I3 : tm sI 3 = Some (mkAction 3 DL (Some sI));
  w5_I4 : tm sI 4 = Some (mkAction 4 DL (Some sI));
  w5_J1 : tm sJ 1 = Some (mkAction 1 DR (Some sJ));
  w5_J2 : tm sJ 2 = Some (mkAction 2 DR (Some sJ));
  w5_J3 : tm sJ 3 = Some (mkAction 3 DR (Some sJ));
  w5_J4 : tm sJ 4 = Some (mkAction 4 DR (Some sF));
  w5_K1 : tm sK 1 = Some (mkAction 1 DL (Some sK));
  w5_K2 : tm sK 2 = Some (mkAction 3 DL (Some sE));
  w5_K3 : tm sK 3 = Some (mkAction 3 DL (Some sK));
  w5_L0 : tm sL 0 = Some (mkAction 3 DR (Some sB));
  w5_L1 : tm sL 1 = Some (mkAction 1 DL (Some sL));
  w5_L2 : tm sL 2 = Some (mkAction 1 DL (Some sL));
  w5_L3 : tm sL 3 = Some (mkAction 1 DL (Some sL))
}.

Definition H5cfg (sA n k : nat) (R : list nat) : Config :=
  mkCfgR (Some sA) (rep k 2 (rep n 3 [])) R.

Section Fwpw_5_Lemmas.
  Variable tm : TM.
  Variables sA sB sC sD sE sF sG sH sI sJ sK sL : nat.
  Hypothesis hc : Fwpw_5Core tm sA sB sC sD sE sF sG sH sI sJ sK sL.

  (* Rule 1: 3^n 2^k A> 4 R -> 3^{n+k+1} 2^1 A> R *)
  Lemma w5_L_left : forall L s R,
    (s = 2 \/ s = 3) -> Forall (fun x => x = 2 \/ x = 3) L ->
    Reaches tm (mkCfgR (Some sL) L (s :: R)) (mkCfgR (Some sL) [] (0 :: rep (S (length L)) 1 R)) (S (length L)).
  Proof.
    induction L as [| x L' IH]; intros s R Hs Hfa.
    - simpl length. apply steps_one. unfold step, mkCfgR; simpl.
      destruct Hs as [-> | ->]; [rewrite (w5_L2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) | rewrite (w5_L3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc)]; reflexivity.
    - inversion Hfa as [| ? ? Hx Hfa']; subst.
      assert (H1 : Reaches tm (mkCfgR (Some sL) (x :: L') (s :: R)) (mkCfgR (Some sL) L' (x :: 1 :: R)) 1).
      { apply steps_one. unfold step, mkCfgR; simpl.
        destruct Hs as [-> | ->]; [rewrite (w5_L2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) | rewrite (w5_L3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc)]; reflexivity. }
      pose proof (IH x (1 :: R) Hx Hfa') as H2.
      simpl length. replace (S (S (length L'))) with (1 + S (length L')) by lia.
      eapply reaches_trans; [exact H1 | rewrite rep_r8 in H2; exact H2].
  Qed.

  Lemma w5_B1_right : forall m L R,
    Reaches tm (mkCfgR (Some sB) L (rep m 1 R)) (mkCfgR (Some sB) (rep m 3 L) R) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    change (Reaches tm (mkCfgR (Some sB) L (1 :: rep m' 1 R)) (mkCfgR (Some sB) (rep (S m') 3 L) R) (1 + m')).
    eapply reaches_trans; [apply (w8_step_R tm sB 1 2 (Some sB) L (rep m' 1 R) (w5_B1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc)) |].
    specialize (IH (3 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w5_rule_4 : forall n k R, 1 <= k ->
    exists t, Reaches tm (H5cfg sA n k (4 :: R)) (H5cfg sA (n + k + 1) 1 R) t /\ n + k + 1 <= t.
  Proof.
    intros n k R Hk. destruct k as [| k']; [lia |].
    assert (Hfa : Forall (fun x => x = 2 \/ x = 3) (rep k' 2 (rep n 3 []))).
    { assert (Hfr : forall m v L, (v = 2 \/ v = 3) -> Forall (fun x => x = 2 \/ x = 3) L -> Forall (fun x => x = 2 \/ x = 3) (rep m v L))
        by (induction m; intros; [exact H0 | constructor; [exact H | apply IHm; assumption]]).
      apply Hfr; [left; reflexivity | apply Hfr; [right; reflexivity | constructor]]. }
    assert (H1 : Reaches tm (H5cfg sA n (S k') (4 :: R)) (mkCfgR (Some sL) (rep k' 2 (rep n 3 [])) (2 :: 3 :: R)) 1)
      by (unfold H5cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_A4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
    pose proof (w5_L_left (rep k' 2 (rep n 3 [])) 2 (3 :: R) (or_introl eq_refl) Hfa) as H2.
    assert (Hlen : length (rep k' 2 (rep n 3 [])) = k' + n).
    { assert (Hlr : forall m v L, length (rep m v L) = m + length L) by (induction m; intros; [reflexivity | simpl; f_equal; apply IHm]).
      rewrite !Hlr; simpl; lia. }
    rewrite Hlen in H2.
    assert (H3 : Reaches tm (mkCfgR (Some sL) [] (0 :: rep (S (k' + n)) 1 (3 :: R)))
                            (mkCfgR (Some sB) [3] (rep (S (k' + n)) 1 (3 :: R))) 1)
      by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_L0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
    pose proof (w5_B1_right (S (k' + n)) [3] (3 :: R)) as H4.
    assert (H5 : Reaches tm (mkCfgR (Some sB) (rep (S (k' + n)) 3 [3]) (3 :: R)) (H5cfg sA (n + S k' + 1) 1 R) 1).
    { unfold H5cfg. rewrite rep_r8. replace (S (S (k' + n))) with (n + S k' + 1) by lia.
      apply (w8_step_R tm sB 3 1 (Some sA) _ _ (w5_B3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc)). }
    exists (1 + S (k' + n) + 1 + S (k' + n) + 1).
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | lia].
  Qed.

  (* Rule 2: 3^n 2^k A> 3 R -> 3^n 2^{k+1} A> R *)
  Lemma w5_rule_3 : forall n k R,
    Reaches tm (H5cfg sA n k (3 :: R)) (H5cfg sA n (S k) R) 1.
  Proof.
    intros n k R. unfold H5cfg. apply (w8_step_R tm sA 3 1 (Some sA) _ _ (w5_A3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc)).
  Qed.

  Lemma w5_rule_3_rep : forall m n k R,
    Reaches tm (H5cfg sA n k (rep m 3 R)) (H5cfg sA n (m + k) R) m.
  Proof.
    induction m as [| m' IH]; intros n k R; [apply reaches_zero |].
    change (Reaches tm (H5cfg sA n k (3 :: rep m' 3 R)) (H5cfg sA n (S m' + k) R) (1 + m')).
    eapply reaches_trans; [apply w5_rule_3 |].
    replace (S m' + k) with (m' + S k) by lia. apply IH.
  Qed.

  (* Rule 3: 3^n 2^{k+1} A> 1 R -> 3^1 2^k A> 1^{n+1} 3 R (for k >= 1) *)
  Lemma w5_C2_left : forall m L R,
    Reaches tm (mkCfgR (Some sC) (rep m 2 L) (2 :: R)) (mkCfgR (Some sC) L (2 :: rep m 3 R)) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    change (Reaches tm (mkCfgR (Some sC) (2 :: rep m' 2 L) (2 :: R)) (mkCfgR (Some sC) L (2 :: rep (S m') 3 R)) (1 + m')).
    eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity |].
    specialize (IH L (3 :: R)). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w5_C3_right : forall m L R,
    Reaches tm (mkCfgR (Some sC) L (rep m 3 R)) (mkCfgR (Some sC) (rep m 2 L) R) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    change (Reaches tm (mkCfgR (Some sC) L (3 :: rep m' 3 R)) (mkCfgR (Some sC) (rep (S m') 2 L) R) (1 + m')).
    eapply reaches_trans; [apply (w8_step_R tm sC 3 1 (Some sC) _ _ (w5_C3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc)) |].
    specialize (IH (2 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w5_rule_1_high : forall n k R, 1 <= k ->
    exists t, Reaches tm (H5cfg sA n (S k) (1 :: R)) (H5cfg sA 1 k (rep (S n) 1 (3 :: R))) t /\ 1 <= t.
  Proof.
    intros n k R Hk. destruct k as [| k']; [lia |].
    assert (H1 : Reaches tm (H5cfg sA n (S (S k')) (1 :: R))
                            (mkCfgR (Some sB) (rep (S k') 2 (rep n 3 [])) (2 :: 3 :: R)) 1)
      by (unfold H5cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_A1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
    assert (Hloop : forall a m,
      exists t, Reaches tm (mkCfgR (Some sB) (rep (S k') 2 (rep a 3 [])) (2 :: rep m 1 (3 :: R)))
                           (H5cfg sA 1 (S k') (rep (a + S m) 1 (3 :: R))) t /\ 1 <= t).
    { induction a as [| a' IHa]; intros m.
      - destruct k' as [| k''].
        + assert (Hs1 : Reaches tm (mkCfgR (Some sB) [2] (2 :: rep m 1 (3 :: R))) (mkCfgR (Some sD) [] (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          assert (Hs2 : Reaches tm (mkCfgR (Some sD) [] (2 :: 1 :: rep m 1 (3 :: R))) (mkCfgR (Some sC) [] (0 :: 3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_D2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          assert (Hs3 : Reaches tm (mkCfgR (Some sC) [] (0 :: 3 :: 1 :: rep m 1 (3 :: R))) (mkCfgR (Some sB) [3] (3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          assert (Hs4 : Reaches tm (mkCfgR (Some sB) [3] (3 :: 1 :: rep m 1 (3 :: R))) (H5cfg sA 1 1 (rep (S m) 1 (3 :: R))) 1)
            by (unfold H5cfg; apply (w8_step_R tm sB 3 1 (Some sA) _ _ (w5_B3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc))).
          exists 4. split; [replace 4 with (1 + 1 + 1 + 1) by lia; eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | lia].
        + assert (Hs1 : Reaches tm (mkCfgR (Some sB) (2 :: 2 :: rep k'' 2 []) (2 :: rep m 1 (3 :: R))) (mkCfgR (Some sD) (2 :: rep k'' 2 []) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          assert (Hs2 : Reaches tm (mkCfgR (Some sD) (2 :: rep k'' 2 []) (2 :: 1 :: rep m 1 (3 :: R))) (mkCfgR (Some sC) (rep k'' 2 []) (2 :: 3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_D2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          pose proof (w5_C2_left k'' [] (3 :: 1 :: rep m 1 (3 :: R))) as Hs3.
          assert (Hs4 : Reaches tm (mkCfgR (Some sC) [] (2 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) (mkCfgR (Some sC) [] (0 :: 3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          assert (Hs5 : Reaches tm (mkCfgR (Some sC) [] (0 :: 3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) (mkCfgR (Some sB) [3] (3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          assert (Hs6 : Reaches tm (mkCfgR (Some sB) [3] (3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) (H5cfg sA 1 1 (rep (S k'') 3 (rep (S m) 1 (3 :: R)))) 1)
            by (unfold H5cfg; rewrite rep_r8; apply (w8_step_R tm sB 3 1 (Some sA) _ _ (w5_B3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc))).
          pose proof (w5_rule_3_rep (S k'') 1 1 (rep (S m) 1 (3 :: R))) as Hs7.
          replace (S k'' + 1) with (S (S k'')) in Hs7 by lia.
          exists (1 + 1 + k'' + 1 + 1 + 1 + S k'').
          split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | exact Hs5] | exact Hs6] | exact Hs7] | lia].
      - destruct k' as [| k''].
        + assert (Hs1 : Reaches tm (mkCfgR (Some sB) (2 :: 3 :: rep a' 3 []) (2 :: rep m 1 (3 :: R))) (mkCfgR (Some sD) (3 :: rep a' 3 []) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          assert (Hs2 : Reaches tm (mkCfgR (Some sD) (3 :: rep a' 3 []) (2 :: 1 :: rep m 1 (3 :: R))) (mkCfgR (Some sC) (rep a' 3 []) (3 :: 3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_D2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          pose proof (w5_C3_right 2 (rep a' 3 []) (1 :: rep m 1 (3 :: R))) as Hs3.
          assert (Hs4 : Reaches tm (mkCfgR (Some sC) (2 :: 2 :: rep a' 3 []) (1 :: rep m 1 (3 :: R))) (mkCfgR (Some sB) (2 :: rep a' 3 []) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          destruct (IHa (S m)) as [t2 [H2 _]].
          exists (1 + 1 + 2 + 1 + t2).
          split; [replace (S a' + S m) with (a' + S (S m)) by lia;
                  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | exact H2] | lia].
        + assert (Hs1 : Reaches tm (mkCfgR (Some sB) (2 :: 2 :: rep k'' 2 (3 :: rep a' 3 [])) (2 :: rep m 1 (3 :: R))) (mkCfgR (Some sD) (2 :: rep k'' 2 (3 :: rep a' 3 [])) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          assert (Hs2 : Reaches tm (mkCfgR (Some sD) (2 :: rep k'' 2 (3 :: rep a' 3 [])) (2 :: 1 :: rep m 1 (3 :: R))) (mkCfgR (Some sC) (rep k'' 2 (3 :: rep a' 3 [])) (2 :: 3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_D2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          pose proof (w5_C2_left k'' (3 :: rep a' 3 []) (3 :: 1 :: rep m 1 (3 :: R))) as Hs3.
          assert (Hs4 : Reaches tm (mkCfgR (Some sC) (3 :: rep a' 3 []) (2 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) (mkCfgR (Some sC) (rep a' 3 []) (3 :: 3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          pose proof (w5_C3_right (S (S (S k''))) (rep a' 3 []) (1 :: rep m 1 (3 :: R))) as Hs5.
          assert (Hs6 : Reaches tm (mkCfgR (Some sC) (rep (S (S (S k''))) 2 (rep a' 3 [])) (1 :: rep m 1 (3 :: R))) (mkCfgR (Some sB) (rep (S (S k'')) 2 (rep a' 3 [])) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          destruct (IHa (S m)) as [t2 [H2 _]].
          exists (1 + 1 + k'' + 1 + S (S (S k'')) + 1 + t2).
          split; [replace (S a' + S m) with (a' + S (S m)) by lia; rewrite rep_r8 in Hs3, Hs4;
                  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | exact Hs5] | exact Hs6] | exact H2] | lia]. }
    destruct (Hloop n 0) as [t2 [H2 _]]. replace (n + 1) with (S n) in H2 by lia.
    exists (1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | lia].
  Qed.

  (* Sweeps for Rule 4 (no encoding needed!) *)
  Lemma w5_E1_right : forall m L R,
    Reaches tm (mkCfgR (Some sE) L (rep m 1 R)) (mkCfgR (Some sE) (rep m 2 L) R) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    change (Reaches tm (mkCfgR (Some sE) L (1 :: rep m' 1 R)) (mkCfgR (Some sE) (rep (S m') 2 L) R) (1 + m')).
    eapply reaches_trans; [apply (w8_step_R tm sE 1 1 (Some sE) _ _ (w5_E1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc)) |].
    specialize (IH (2 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w5_G2_left : forall m R,
    Reaches tm (mkCfgR (Some sG) (rep m 2 []) (2 :: R)) (mkCfgR (Some sG) [] (0 :: rep (S m) 2 R)) (S m).
  Proof.
    induction m as [| m' IH]; intros R.
    - apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_G2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity.
    - replace (S (S m')) with (1 + S m') by lia.
      eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_G2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity |].
      specialize (IH (2 :: R)). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w5_J2_right : forall m L R,
    Reaches tm (mkCfgR (Some sJ) L (rep m 2 R)) (mkCfgR (Some sJ) (rep m 2 L) R) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    change (Reaches tm (mkCfgR (Some sJ) L (2 :: rep m' 2 R)) (mkCfgR (Some sJ) (rep (S m') 2 L) R) (1 + m')).
    eapply reaches_trans; [apply (w8_step_R tm sJ 2 1 (Some sJ) _ _ (w5_J2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc)) |].
    specialize (IH (2 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w5_right_13 : forall st,
    tm st 1 = Some (mkAction 1 DR (Some st)) ->
    tm st 3 = Some (mkAction 3 DR (Some st)) ->
    forall w L R, W8Word w ->
    Reaches tm (mkCfgR (Some st) L (w ++ R)) (mkCfgR (Some st) (rev w ++ L) R) (length w).
  Proof.
    intros st H1 H3 w. induction w as [| s w' IH]; intros L R Hw; [apply reaches_zero |].
    inversion Hw as [| ? ? Hs Hw']; subst.
    simpl length. replace (S (length w')) with (1 + length w') by lia.
    destruct Hs as [-> | ->].
    - eapply reaches_trans; [apply (w8_step_R tm st 1 0 (Some st) L (w' ++ R) H1) |].
      specialize (IH (1 :: L) R Hw'). simpl rev. rewrite <- app_assoc. exact IH.
    - eapply reaches_trans; [apply (w8_step_R tm st 3 2 (Some st) L (w' ++ R) H3) |].
      specialize (IH (3 :: L) R Hw'). simpl rev. rewrite <- app_assoc. exact IH.
  Qed.

  Lemma w5_left_13 : forall st,
    tm st 1 = Some (mkAction 1 DL (Some st)) ->
    tm st 3 = Some (mkAction 3 DL (Some st)) ->
    forall u L x R, W8Word u ->
    Reaches tm (match u with [] => mkCfgR (Some st) L (x :: R) | h :: t => mkCfgR (Some st) (t ++ x :: L) (h :: R) end)
               (mkCfgR (Some st) L (x :: rev u ++ R)) (length u).
  Proof.
    intros st H1 H3 u. induction u as [| s u' IH]; intros L x R Hu; [apply reaches_zero |].
    inversion Hu as [| ? ? Hs Hu']; subst.
    simpl length. replace (S (length u')) with (1 + length u') by lia.
    destruct Hs as [-> | ->]; [specialize (IH L x (1 :: R) Hu') | specialize (IH L x (3 :: R) Hu')];
    destruct u' as [| h' t'];
      (eapply reaches_trans;
       [apply steps_one; unfold step, mkCfgR; simpl; first [rewrite H1 | rewrite H3]; reflexivity
       | simpl rev; try rewrite <- app_assoc; exact IH]).
  Qed.

  (* Copy step: 2^m rev(v) 4 u G> (s :: v ++ 4 :: R) -> 2^m rev(rev u ++ v) G> (4 :: (rev u ++ v) ++ 4 :: R) *)
  Lemma w5_copy_step : forall m u v R, 1 <= m -> W8Word u -> W8Word v ->
    exists t, Reaches tm (match u with
                          | [] => mkCfgR (Some sG) (rev v ++ rep m 2 []) (4 :: v ++ 4 :: R)
                          | h :: t0 => mkCfgR (Some sG) (t0 ++ 4 :: rev v ++ rep m 2 []) (h :: v ++ 4 :: R)
                          end)
                         (mkCfgR (Some sG) (rev (rev u ++ v) ++ rep m 2 []) (4 :: (rev u ++ v) ++ 4 :: R)) t.
  Proof.
    intros m u. induction u as [| s u' IH]; intros v R Hm Hu Hv; [simpl; exists 0; apply reaches_zero |].
    inversion Hu as [| ? ? Hs Hu']; subst. destruct m as [| m']; [lia |].
    assert (Huv : W8Word (s :: v)) by (constructor; assumption).
    assert (Hrevv : W8Word (rev v)) by (apply Forall_rev; exact Hv).
    assert (Hrevu : W8Word (rev u')) by (apply Forall_rev; exact Hu').
    destruct Hs as [-> | ->].
    - (* s = 1: G1=0LH, H left u', H4=4LH, H left v, H2=1LG, G2_left, G0=2RJ, J2_right, J right (1::v), J4=4RF, F right (rev u'), F0=1LG *)
      assert (H1 : Reaches tm (mkCfgR (Some sG) (u' ++ 4 :: rev v ++ rep (S m') 2 []) (1 :: v ++ 4 :: R))
                              (match u' with [] => mkCfgR (Some sH) (rev v ++ rep (S m') 2 []) (4 :: 0 :: v ++ 4 :: R)
                               | h' :: t' => mkCfgR (Some sH) (t' ++ 4 :: rev v ++ rep (S m') 2 []) (h' :: 0 :: v ++ 4 :: R) end) 1)
        by (apply steps_one; destruct u'; unfold step, mkCfgR; simpl; rewrite (w5_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); destruct v; reflexivity).
      pose proof (w5_left_13 sH (w5_H1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_H3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) u' (rev v ++ rep (S m') 2 []) 4 (0 :: v ++ 4 :: R) Hu') as H2.
      assert (H3 : Reaches tm (mkCfgR (Some sH) (rev v ++ rep (S m') 2 []) (4 :: rev u' ++ 0 :: v ++ 4 :: R))
                              (match rev v with [] => mkCfgR (Some sH) (rep m' 2 []) (2 :: 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                               | h' :: t' => mkCfgR (Some sH) (t' ++ 2 :: rep m' 2 []) (h' :: 4 :: rev u' ++ 0 :: v ++ 4 :: R) end) 1)
        by (apply steps_one; destruct (rev v); unfold step, mkCfgR; simpl; rewrite (w5_H4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      pose proof (w5_left_13 sH (w5_H1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_H3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (rev v) (rep m' 2 []) 2 (4 :: rev u' ++ 0 :: v ++ 4 :: R) Hrevv) as H4.
      rewrite rev_involutive in H4.
      assert (H5 : Reaches tm (mkCfgR (Some sH) (rep m' 2 []) (2 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R))
                              (match m' with 0 => mkCfgR (Some sG) [] (0 :: 1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                               | S m'' => mkCfgR (Some sG) (rep m'' 2 []) (2 :: 1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R) end) 1)
        by (apply steps_one; destruct m'; unfold step, mkCfgR; simpl; rewrite (w5_H2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (H6 : exists t6, Reaches tm (match m' with 0 => mkCfgR (Some sG) [] (0 :: 1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                                          | S m'' => mkCfgR (Some sG) (rep m'' 2 []) (2 :: 1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R) end)
                                         (mkCfgR (Some sJ) (rep (S m') 2 []) (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)) t6).
      { destruct m' as [| m''].
        - exists 1. apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity.
        - pose proof (w5_G2_left m'' (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)) as Hg.
          assert (Hg0 : Reaches tm (mkCfgR (Some sG) [] (0 :: rep (S m'') 2 (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)))
                                   (mkCfgR (Some sJ) [2] (rep (S m'') 2 (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          pose proof (w5_J2_right (S m'') [2] (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)) as Hj.
          rewrite rep_r8 in Hj.
          exists (S m'' + 1 + S m''). eapply reaches_trans; [eapply reaches_trans; [exact Hg | exact Hg0] | exact Hj]. }
      destruct H6 as [t6 H6].
      pose proof (w5_right_13 sJ (w5_J1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_J3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (1 :: v) (rep (S m') 2 []) (4 :: rev u' ++ 0 :: v ++ 4 :: R) Huv) as H7.
      assert (H8 : Reaches tm (mkCfgR (Some sJ) (rev (1 :: v) ++ rep (S m') 2 []) (4 :: rev u' ++ 0 :: v ++ 4 :: R))
                              (mkCfgR (Some sF) (4 :: rev (1 :: v) ++ rep (S m') 2 []) (rev u' ++ 0 :: v ++ 4 :: R)) 1)
        by (apply (w8_step_R tm sJ 4 3 (Some sF) _ _ (w5_J4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc))).
      pose proof (w5_right_13 sF (w5_F1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_F3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (rev u') (4 :: rev (1 :: v) ++ rep (S m') 2 []) (0 :: v ++ 4 :: R) Hrevu) as H9.
      assert (H10 : Reaches tm (mkCfgR (Some sF) (rev (rev u') ++ 4 :: rev (1 :: v) ++ rep (S m') 2 []) (0 :: v ++ 4 :: R))
                               (match u' with [] => mkCfgR (Some sG) (rev (1 :: v) ++ rep (S m') 2 []) (4 :: (1 :: v) ++ 4 :: R)
                                | h' :: t' => mkCfgR (Some sG) (t' ++ 4 :: rev (1 :: v) ++ rep (S m') 2 []) (h' :: (1 :: v) ++ 4 :: R) end) 1)
        by (rewrite rev_involutive; apply steps_one; destruct u'; unfold step, mkCfgR; simpl; rewrite (w5_F0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      destruct (IH (1 :: v) R ltac:(lia) Hu' Huv) as [t11 H11].
      exists (1 + length u' + 1 + length (rev v) + 1 + t6 + length (1 :: v) + 1 + length (rev u') + 1 + t11).
      simpl rev. rewrite <- app_assoc.
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | exact H10] | exact H11].
    - (* s = 3: G3=2LI, I left u', I4=4LI, I left v, I2=3LG, G2_left, G0=2RJ, J2_right, J right (3::v), J4=4RF, F right (rev u'), F2=3LG *)
      assert (H1 : Reaches tm (mkCfgR (Some sG) (u' ++ 4 :: rev v ++ rep (S m') 2 []) (3 :: v ++ 4 :: R))
                              (match u' with [] => mkCfgR (Some sI) (rev v ++ rep (S m') 2 []) (4 :: 2 :: v ++ 4 :: R)
                               | h' :: t' => mkCfgR (Some sI) (t' ++ 4 :: rev v ++ rep (S m') 2 []) (h' :: 2 :: v ++ 4 :: R) end) 1)
        by (apply steps_one; destruct u'; unfold step, mkCfgR; simpl; rewrite (w5_G3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      pose proof (w5_left_13 sI (w5_I1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_I3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) u' (rev v ++ rep (S m') 2 []) 4 (2 :: v ++ 4 :: R) Hu') as H2.
      assert (H3 : Reaches tm (mkCfgR (Some sI) (rev v ++ rep (S m') 2 []) (4 :: rev u' ++ 2 :: v ++ 4 :: R))
                              (match rev v with [] => mkCfgR (Some sI) (rep m' 2 []) (2 :: 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                               | h' :: t' => mkCfgR (Some sI) (t' ++ 2 :: rep m' 2 []) (h' :: 4 :: rev u' ++ 2 :: v ++ 4 :: R) end) 1)
        by (apply steps_one; destruct (rev v); unfold step, mkCfgR; simpl; rewrite (w5_I4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      pose proof (w5_left_13 sI (w5_I1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_I3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (rev v) (rep m' 2 []) 2 (4 :: rev u' ++ 2 :: v ++ 4 :: R) Hrevv) as H4.
      rewrite rev_involutive in H4.
      assert (H5 : Reaches tm (mkCfgR (Some sI) (rep m' 2 []) (2 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R))
                              (match m' with 0 => mkCfgR (Some sG) [] (0 :: 3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                               | S m'' => mkCfgR (Some sG) (rep m'' 2 []) (2 :: 3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R) end) 1)
        by (apply steps_one; destruct m'; unfold step, mkCfgR; simpl; rewrite (w5_I2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (H6 : exists t6, Reaches tm (match m' with 0 => mkCfgR (Some sG) [] (0 :: 3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                                          | S m'' => mkCfgR (Some sG) (rep m'' 2 []) (2 :: 3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R) end)
                                         (mkCfgR (Some sJ) (rep (S m') 2 []) (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)) t6).
      { destruct m' as [| m''].
        - exists 1. apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity.
        - pose proof (w5_G2_left m'' (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)) as Hg.
          assert (Hg0 : Reaches tm (mkCfgR (Some sG) [] (0 :: rep (S m'') 2 (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)))
                                   (mkCfgR (Some sJ) [2] (rep (S m'') 2 (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
          pose proof (w5_J2_right (S m'') [2] (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)) as Hj.
          rewrite rep_r8 in Hj.
          exists (S m'' + 1 + S m''). eapply reaches_trans; [eapply reaches_trans; [exact Hg | exact Hg0] | exact Hj]. }
      destruct H6 as [t6 H6].
      pose proof (w5_right_13 sJ (w5_J1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_J3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (3 :: v) (rep (S m') 2 []) (4 :: rev u' ++ 2 :: v ++ 4 :: R) Huv) as H7.
      assert (H8 : Reaches tm (mkCfgR (Some sJ) (rev (3 :: v) ++ rep (S m') 2 []) (4 :: rev u' ++ 2 :: v ++ 4 :: R))
                              (mkCfgR (Some sF) (4 :: rev (3 :: v) ++ rep (S m') 2 []) (rev u' ++ 2 :: v ++ 4 :: R)) 1)
        by (apply (w8_step_R tm sJ 4 3 (Some sF) _ _ (w5_J4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc))).
      pose proof (w5_right_13 sF (w5_F1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_F3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (rev u') (4 :: rev (3 :: v) ++ rep (S m') 2 []) (2 :: v ++ 4 :: R) Hrevu) as H9.
      assert (H10 : Reaches tm (mkCfgR (Some sF) (rev (rev u') ++ 4 :: rev (3 :: v) ++ rep (S m') 2 []) (2 :: v ++ 4 :: R))
                               (match u' with [] => mkCfgR (Some sG) (rev (3 :: v) ++ rep (S m') 2 []) (4 :: (3 :: v) ++ 4 :: R)
                                | h' :: t' => mkCfgR (Some sG) (t' ++ 4 :: rev (3 :: v) ++ rep (S m') 2 []) (h' :: (3 :: v) ++ 4 :: R) end) 1)
        by (rewrite rev_involutive; apply steps_one; destruct u'; unfold step, mkCfgR; simpl; rewrite (w5_F2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      destruct (IH (3 :: v) R ltac:(lia) Hu' Huv) as [t11 H11].
      exists (1 + length u' + 1 + length (rev v) + 1 + t6 + length (3 :: v) + 1 + length (rev u') + 1 + t11).
      simpl rev. rewrite <- app_assoc.
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | exact H10] | exact H11].
  Qed.

  (* Repeat loop: 2^{S m} E> 3 w 4 R -> 3^1 2^1 A> (w 4)^{S (S m)} R *)
  Lemma w5_repeat_E : forall m w R, W8Word w ->
    exists t, Reaches tm (mkCfgR (Some sE) (rep (S m) 2 []) (3 :: w ++ 4 :: R))
                         (H5cfg sA 1 1 (rep_app (S (S m)) (w ++ [4]) R)) t /\ 1 <= t.
  Proof.
    induction m as [| m' IH]; intros w R Hw.
    - assert (H1 : Reaches tm (mkCfgR (Some sE) [2] (3 :: w ++ 4 :: R)) (mkCfgR (Some sF) [4; 2] (w ++ 4 :: R)) 1)
        by (apply (w8_step_R tm sE 3 3 (Some sF) _ _ (w5_E3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc))).
      pose proof (w5_right_13 sF (w5_F1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_F3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) w [4; 2] (4 :: R) Hw) as H2.
      assert (H3 : Reaches tm (mkCfgR (Some sF) (rev w ++ [4; 2]) (4 :: R))
                              (match rev w with [] => mkCfgR (Some sG) [2] (4 :: 4 :: R) | h :: t0 => mkCfgR (Some sG) (t0 ++ [4; 2]) (h :: 4 :: R) end) 1)
        by (apply steps_one; destruct (rev w); unfold step, mkCfgR; simpl; rewrite (w5_F4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (Hrevw : W8Word (rev w)) by (apply Forall_rev; exact Hw).
      destruct (w5_copy_step 1 (rev w) [] R ltac:(lia) Hrevw (Forall_nil _)) as [t4 H4].
      rewrite rev_involutive, app_nil_r in H4.
      assert (H5 : Reaches tm (mkCfgR (Some sG) (rev w ++ [2]) (4 :: w ++ 4 :: R))
                              (match rev w with [] => mkCfgR (Some sK) [] (2 :: 4 :: w ++ 4 :: R) | h :: t0 => mkCfgR (Some sK) (t0 ++ [2]) (h :: 4 :: w ++ 4 :: R) end) 1)
        by (apply steps_one; destruct (rev w); unfold step, mkCfgR; simpl; rewrite (w5_G4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      pose proof (w5_left_13 sK (w5_K1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_K3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (rev w) [] 2 (4 :: w ++ 4 :: R) Hrevw) as H6.
      rewrite rev_involutive in H6.
      assert (H7 : Reaches tm (mkCfgR (Some sK) [] (2 :: w ++ 4 :: w ++ 4 :: R)) (mkCfgR (Some sE) [] (0 :: 3 :: w ++ 4 :: w ++ 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_K2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (H8 : Reaches tm (mkCfgR (Some sE) [] (0 :: 3 :: w ++ 4 :: w ++ 4 :: R)) (mkCfgR (Some sB) [3] (3 :: w ++ 4 :: w ++ 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_E0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (H9 : Reaches tm (mkCfgR (Some sB) [3] (3 :: w ++ 4 :: w ++ 4 :: R)) (H5cfg sA 1 1 (rep_app 2 (w ++ [4]) R)) 1)
        by (unfold H5cfg; simpl rep_app; rewrite <- !app_assoc; simpl; apply (w8_step_R tm sB 3 1 (Some sA) _ _ (w5_B3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc))).
      exists (1 + length w + 1 + t4 + 1 + length (rev w) + 1 + 1 + 1).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | lia].
    - assert (H1 : Reaches tm (mkCfgR (Some sE) (rep (S (S m')) 2 []) (3 :: w ++ 4 :: R)) (mkCfgR (Some sF) (4 :: rep (S (S m')) 2 []) (w ++ 4 :: R)) 1)
        by (apply (w8_step_R tm sE 3 3 (Some sF) _ _ (w5_E3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc))).
      pose proof (w5_right_13 sF (w5_F1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_F3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) w (4 :: rep (S (S m')) 2 []) (4 :: R) Hw) as H2.
      assert (H3 : Reaches tm (mkCfgR (Some sF) (rev w ++ 4 :: rep (S (S m')) 2 []) (4 :: R))
                              (match rev w with [] => mkCfgR (Some sG) (rep (S (S m')) 2 []) (4 :: 4 :: R) | h :: t0 => mkCfgR (Some sG) (t0 ++ 4 :: rep (S (S m')) 2 []) (h :: 4 :: R) end) 1)
        by (apply steps_one; destruct (rev w); unfold step, mkCfgR; simpl; rewrite (w5_F4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (Hrevw : W8Word (rev w)) by (apply Forall_rev; exact Hw).
      destruct (w5_copy_step (S (S m')) (rev w) [] R ltac:(lia) Hrevw (Forall_nil _)) as [t4 H4].
      rewrite rev_involutive, app_nil_r in H4.
      assert (H5 : Reaches tm (mkCfgR (Some sG) (rev w ++ rep (S (S m')) 2 []) (4 :: w ++ 4 :: R))
                              (match rev w with [] => mkCfgR (Some sK) (rep (S m') 2 []) (2 :: 4 :: w ++ 4 :: R) | h :: t0 => mkCfgR (Some sK) (t0 ++ 2 :: rep (S m') 2 []) (h :: 4 :: w ++ 4 :: R) end) 1)
        by (apply steps_one; destruct (rev w); unfold step, mkCfgR; simpl; rewrite (w5_G4 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      pose proof (w5_left_13 sK (w5_K1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (w5_K3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc) (rev w) (rep (S m') 2 []) 2 (4 :: w ++ 4 :: R) Hrevw) as H6.
      rewrite rev_involutive in H6.
      assert (H7 : Reaches tm (mkCfgR (Some sK) (rep (S m') 2 []) (2 :: w ++ 4 :: w ++ 4 :: R)) (mkCfgR (Some sE) (rep m' 2 []) (2 :: 3 :: w ++ 4 :: w ++ 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_K2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (H8 : Reaches tm (mkCfgR (Some sE) (rep m' 2 []) (2 :: 3 :: w ++ 4 :: w ++ 4 :: R)) (mkCfgR (Some sE) (rep (S m') 2 []) (3 :: w ++ 4 :: w ++ 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_E2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      destruct (IH w (w ++ 4 :: R) Hw) as [t9 [H9 _]].
      assert (Hra : rep_app (S (S m')) (w ++ [4]) (w ++ 4 :: R) = rep_app (S (S (S m'))) (w ++ [4]) R).
      { assert (Haux : forall k A B, rep_app k A (A ++ B) = rep_app (S k) A B) by (induction k; intros; [reflexivity | simpl; rewrite IHk; reflexivity]).
        replace (w ++ 4 :: R) with ((w ++ [4]) ++ R) by (rewrite <- app_assoc; reflexivity); apply Haux. }
      rewrite Hra in H9.
      exists (1 + length w + 1 + t4 + 1 + length (rev w) + 1 + 1 + t9).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | lia].
  Qed.

  (* Rule 4: 3^n 2^1 A> 1 w 4 R -> 3^1 2^1 A> (w 4)^{n+3} R *)
  Lemma w5_rule_1_low : forall n w R, W8Word w ->
    exists t, Reaches tm (H5cfg sA n 1 (1 :: w ++ 4 :: R))
                         (H5cfg sA 1 1 (rep_app (n + 3) (w ++ [4]) R)) t /\ 1 <= t.
  Proof.
    intros n w R Hw.
    assert (H1 : Reaches tm (H5cfg sA n 1 (1 :: w ++ 4 :: R)) (mkCfgR (Some sB) (rep n 3 []) (2 :: 3 :: w ++ 4 :: R)) 1)
      by (unfold H5cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_A1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
    assert (Hloop : forall a m,
      Reaches tm (mkCfgR (Some sB) (rep a 3 []) (2 :: rep m 1 (3 :: w ++ 4 :: R)))
                 (mkCfgR (Some sB) [] (2 :: rep (a + m) 1 (3 :: w ++ 4 :: R))) (3 * a)).
    { induction a as [| a' IHa]; intros m; [apply reaches_zero |].
      replace (3 * S a') with (1 + 1 + 1 + 3 * a') by lia.
      assert (Hs1 : Reaches tm (mkCfgR (Some sB) (3 :: rep a' 3 []) (2 :: rep m 1 (3 :: w ++ 4 :: R))) (mkCfgR (Some sD) (rep a' 3 []) (3 :: 1 :: rep m 1 (3 :: w ++ 4 :: R))) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (Hs2 : Reaches tm (mkCfgR (Some sD) (rep a' 3 []) (3 :: 1 :: rep m 1 (3 :: w ++ 4 :: R))) (mkCfgR (Some sC) (2 :: rep a' 3 []) (1 :: rep m 1 (3 :: w ++ 4 :: R))) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_D3 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      assert (Hs3 : Reaches tm (mkCfgR (Some sC) (2 :: rep a' 3 []) (1 :: rep m 1 (3 :: w ++ 4 :: R))) (mkCfgR (Some sB) (rep a' 3 []) (2 :: 1 :: rep m 1 (3 :: w ++ 4 :: R))) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_C1 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
      specialize (IHa (S m)). replace (a' + S m) with (S a' + m) in IHa by lia.
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact IHa]. }
    pose proof (Hloop n 0) as H2. rewrite Nat.add_0_r in H2.
    assert (H3 : Reaches tm (mkCfgR (Some sB) [] (2 :: rep n 1 (3 :: w ++ 4 :: R))) (mkCfgR (Some sD) [] (0 :: 1 :: rep n 1 (3 :: w ++ 4 :: R))) 1)
      by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
    assert (H4 : Reaches tm (mkCfgR (Some sD) [] (0 :: 1 :: rep n 1 (3 :: w ++ 4 :: R))) (mkCfgR (Some sE) [2] (rep (S n) 1 (3 :: w ++ 4 :: R))) 1)
      by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w5_D0 _ _ _ _ _ _ _ _ _ _ _ _ _ hc); reflexivity).
    pose proof (w5_E1_right (S n) [2] (3 :: w ++ 4 :: R)) as H5. rewrite rep_r8 in H5.
    destruct (w5_repeat_E (S n) w R Hw) as [t6 [H6 _]]. replace (S (S (S n))) with (n + 3) in H6 by lia.
    exists (1 + 3 * n + 1 + 1 + S n + t6).
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | lia].
  Qed.

  (* Semantic evaluation predicate RunW5 k w f — reuses F8_step from Fwpw_8! *)
  Definition RunW5 (k : nat) (w : list nat) (f : nat -> nat) : Prop :=
    forall m R, 1 <= m ->
      exists n' t, Reaches tm (H5cfg sA m k (w ++ 4 :: R)) (H5cfg sA n' 1 R) t /\
                   f m <= n' /\ n' <= t.

  Lemma runW5_nil : forall k, 1 <= k -> RunW5 k [] (fun m => m + 2).
  Proof.
    intros k Hk m R Hm. destruct (w5_rule_4 m k R Hk) as [t [H1 Ht]].
    exists (m + k + 1), t. split; [exact H1 | lia].
  Qed.

  Lemma runW5_3 : forall k w f, RunW5 (S k) w f -> RunW5 k (3 :: w) f.
  Proof.
    intros k w f Hw m R Hm. pose proof (w5_rule_3 m k (w ++ 4 :: R)) as H1.
    destruct (Hw m R Hm) as [n' [t2 [H2 [Hf Ht2]]]].
    exists n', (1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | lia].
  Qed.

  Lemma runW5_rep_app : forall f w,
    (forall x y, x <= y -> f x <= f y) -> (forall x, x <= f x) -> RunW5 1 w f ->
    forall c m R, 1 <= m ->
      exists n' t, Reaches tm (H5cfg sA m 1 (rep_app c (w ++ [4]) R)) (H5cfg sA n' 1 R) t /\
                   iter f c m <= n' /\ (1 <= c -> n' <= t).
  Proof.
    intros f w Hmono Hself Hw. induction c as [| c' IH]; intros m R Hm.
    - exists m, 0. split; [apply reaches_zero | simpl; lia].
    - simpl rep_app. rewrite <- app_assoc. simpl.
      destruct (Hw m (rep_app c' (w ++ [4]) R) Hm) as [n1 [t1 [H1 [Hf1 Ht1]]]].
      destruct c' as [| c''].
      + exists n1, t1. simpl in *. split; [exact H1 | lia].
      + assert (Hn1 : 1 <= n1) by (pose proof (Hself m); lia).
        destruct (IH n1 R Hn1) as [n2 [t2 [H2 [Hf2 Ht2]]]].
        exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
        split.
        * assert (Hsh : f (iter f (S c'') m) = iter f (S c'') (f m)).
          { change (iter f (S (S c'')) m = iter f (S c'') (f m)).
            replace (S (S c'')) with (S c'' + 1) by lia. rewrite iter_add. reflexivity. }
          rewrite Hsh. eapply Nat.le_trans; [apply iter_mono_arg; [exact Hmono | exact Hf1] | exact Hf2].
        * intros _. specialize (Ht2 ltac:(lia)). lia.
  Qed.

  Theorem w5_run_F8 : forall k w f,
    W8Word w -> (forall x y, x <= y -> f x <= f y) -> (forall x, x + 2 <= f x) ->
    RunW5 (S k) w f ->
    RunW5 (S k) (1 :: w) (F8_step k f).
  Proof.
    induction k as [| k' IH]; intros w f Hw Hmono Hinc Hrun m R Hm.
    - destruct (w5_rule_1_low m w R Hw) as [t1 [H1 _]].
      destruct (runW5_rep_app f w Hmono (fun x => ltac:(pose proof (Hinc x); lia)) Hrun (m + 3) 1 R ltac:(lia))
        as [n' [t2 [H2 [Hf2 Ht2]]]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | split; [exact Hf2 | specialize (Ht2 ltac:(lia)); lia]].
    - destruct (w5_rule_1_high m (S k') (w ++ 4 :: R) ltac:(lia)) as [t1 [H1 _]].
      assert (Hrep1 : forall c,
        RunW5 (S k') (rep c 1 (3 :: w)) (iterF (F8_step k') c f) /\
        (forall x y, x <= y -> iterF (F8_step k') c f x <= iterF (F8_step k') c f y) /\
        (forall x, x + 2 <= iterF (F8_step k') c f x)).
      { induction c as [| c' [IHr [IHm IHi]]].
        - repeat split; [apply runW5_3; exact Hrun | exact Hmono | exact Hinc].
        - simpl. destruct (F8_step_props k' _ IHm IHi) as [A [B _]].
          repeat split; [| exact A | exact B].
          apply IH; [| exact IHm | exact IHi | exact IHr].
          assert (Hwr : forall j u, W8Word u -> W8Word (rep j 1 u))
            by (induction j; intros; [exact H | constructor; [left; reflexivity | apply IHj; exact H]]).
          apply Hwr; constructor; [right; reflexivity | exact Hw]. }
      assert (Hra : rep (S m) 1 (3 :: w ++ 4 :: R) = rep (S m) 1 (3 :: w) ++ 4 :: R)
        by (clear; induction (S m); simpl; [reflexivity | f_equal; exact IHn]).
      rewrite Hra in H1.
      destruct (proj1 (Hrep1 (S m)) 1 R ltac:(lia)) as [n' [t2 [H2 [Hf2 Ht2]]]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | split; [exact Hf2 | lia]].
  Qed.

End Fwpw_5_Lemmas.
