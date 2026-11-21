(*
  rocq/Fwpw_8.v
  Reusable, axiom-free Rocq 9.1 formalization of the 8-state 8-symbol f_{ω^ω} core (A..H)
  plus state I (8) for H2 = 4LE (f_{ω^ω+1}).
  Powers 12 champions: BB(10..16,8), BB(11..14,9), BB(16,9).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

Record Fwpw_8Core (tm : TM) : Prop := mkFwpw_8Core {
  w8_A1 : tm 0 1 = Some (mkAction 5 DR (Some 0));
  w8_A3 : tm 0 3 = Some (mkAction 6 DR (Some 0));
  w8_A4 : tm 0 4 = Some (mkAction 4 DR (Some 5));
  w8_A7 : tm 0 7 = Some (mkAction 7 DR (Some 0));
  w8_B0 : tm 1 0 = Some (mkAction 7 DR (Some 0));
  w8_B1 : tm 1 1 = Some (mkAction 3 DR (Some 1));
  w8_B2 : tm 1 2 = Some (mkAction 1 DL (Some 3));
  w8_B3 : tm 1 3 = Some (mkAction 2 DR (Some 7));
  w8_B4 : tm 1 4 = Some (mkAction 4 DL (Some 5));
  w8_B5 : tm 1 5 = Some (mkAction 0 DL (Some 2));
  w8_B6 : tm 1 6 = Some (mkAction 2 DL (Some 3));
  w8_B7 : tm 1 7 = Some (mkAction 7 DL (Some 1));
  w8_C0 : tm 2 0 = Some (mkAction 3 DR (Some 1));
  w8_C1 : tm 2 1 = Some (mkAction 1 DL (Some 1));
  w8_C2 : tm 2 2 = Some (mkAction 3 DL (Some 2));
  w8_C3 : tm 2 3 = Some (mkAction 2 DR (Some 2));
  w8_C4 : tm 2 4 = Some (mkAction 4 DL (Some 2));
  w8_C5 : tm 2 5 = Some (mkAction 1 DL (Some 2));
  w8_C6 : tm 2 6 = Some (mkAction 3 DL (Some 2));
  w8_C7 : tm 2 7 = Some (mkAction 1 DL (Some 1));
  w8_D0 : tm 3 0 = Some (mkAction 7 DR (Some 4));
  w8_D2 : tm 3 2 = Some (mkAction 3 DL (Some 2));
  w8_D3 : tm 3 3 = Some (mkAction 2 DR (Some 2));
  w8_D4 : tm 3 4 = Some (mkAction 4 DL (Some 3));
  w8_D5 : tm 3 5 = Some (mkAction 1 DL (Some 3));
  w8_D6 : tm 3 6 = Some (mkAction 3 DL (Some 3));
  w8_D7 : tm 3 7 = Some (mkAction 3 DL (Some 1));
  w8_E0 : tm 4 0 = Some (mkAction 3 DR (Some 1));
  w8_E1 : tm 4 1 = Some (mkAction 7 DR (Some 4));
  w8_E3 : tm 4 3 = Some (mkAction 4 DR (Some 5));
  w8_E7 : tm 4 7 = Some (mkAction 7 DR (Some 4));
  w8_F0 : tm 5 0 = Some (mkAction 1 DL (Some 1));
  w8_F1 : tm 5 1 = Some (mkAction 5 DR (Some 5));
  w8_F2 : tm 5 2 = Some (mkAction 3 DL (Some 1));
  w8_F3 : tm 5 3 = Some (mkAction 6 DR (Some 5));
  w8_F4 : tm 5 4 = Some (mkAction 4 DL (Some 1));
  w8_F5 : tm 5 5 = Some (mkAction 1 DL (Some 5));
  w8_F6 : tm 5 6 = Some (mkAction 3 DL (Some 5));
  w8_F7 : tm 5 7 = Some (mkAction 3 DL (Some 4));
  w8_G0 : tm 6 0 = Some (mkAction 3 DR (Some 1));
  w8_G1 : tm 6 1 = Some (mkAction 1 DL (Some 6));
  w8_G2 : tm 6 2 = Some (mkAction 1 DL (Some 6));
  w8_G3 : tm 6 3 = Some (mkAction 1 DL (Some 6));
  w8_H1 : tm 7 1 = Some (mkAction 3 DL (Some 1));
  w8_H3 : tm 7 3 = Some (mkAction 2 DR (Some 7));
  w8_H4 : tm 7 4 = Some (mkAction 3 DL (Some 6))
}.

Record Fwpw_8_ICore (tm : TM) : Prop := mkFwpw_8_ICore {
  w8i_core : Fwpw_8Core tm;
  w8i_E2 : tm 4 2 = Some (mkAction 1 DL (Some 8));
  w8i_H2 : tm 7 2 = Some (mkAction 4 DL (Some 4));
  w8i_I0 : tm 8 0 = Some (mkAction 3 DR (Some 8));
  w8i_I1 : tm 8 1 = Some (mkAction 3 DL (Some 1));
  w8i_I2 : tm 8 2 = Some (mkAction 2 DR (Some 8));
  w8i_I3 : tm 8 3 = Some (mkAction 2 DL (Some 8))
}.

Definition H8cfg (n k : nat) (R : list nat) : Config :=
  mkCfgR (Some 7) (rep k 2 (rep n 3 [])) R.

Definition W8Word (w : list nat) : Prop := Forall (fun s => s = 1 \/ s = 3) w.

Definition enc_sym (s : nat) : nat := if Nat.eqb s 1 then 5 else 6.
Definition enc_word (w : list nat) : list nat := map enc_sym w.

Lemma rev_enc_word : forall w, rev (enc_word w) = enc_word (rev w).
Proof. intro w; unfold enc_word; symmetry; apply map_rev. Qed.

Fixpoint rep_app (n : nat) (w R : list nat) : list nat :=
  match n with
  | 0 => R
  | S k => w ++ rep_app k w R
  end.

Lemma rep_r8 : forall n v R, rep n v (v :: R) = rep (S n) v R.
Proof. induction n as [| n' IH]; intros; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma rep_add8 : forall a b v R, rep (a + b) v R = rep a v (rep b v R).
Proof. induction a as [| a' IH]; intros; [reflexivity | simpl; f_equal; apply IH]. Qed.

Section Fwpw_8_Lemmas.
  Variable tm : TM.
  Hypothesis hc : Fwpw_8Core tm.

  Lemma w8_step_R : forall st s w nxt L R,
    tm st s = Some (mkAction (S w) DR nxt) ->
    Reaches tm (mkCfgR (Some st) L (s :: R)) (mkCfgR nxt (S w :: L) R) 1.
  Proof.
    intros st s w nxt L R H. apply steps_one.
    unfold step, mkCfgR; simpl; rewrite H; destruct R; reflexivity.
  Qed.

  (* Basic sweeps *)
  Lemma w8_G_left : forall L s R,
    (s = 2 \/ s = 3) -> Forall (fun x => x = 2 \/ x = 3) L ->
    Reaches tm (mkCfgR (Some 6) L (s :: R)) (mkCfgR (Some 6) [] (0 :: rep (S (length L)) 1 R)) (S (length L)).
  Proof.
    induction L as [| x L' IH]; intros s R Hs Hfa.
    - simpl length. apply steps_one. unfold step, mkCfgR; simpl.
      destruct Hs as [-> | ->]; [rewrite (w8_G2 tm hc) | rewrite (w8_G3 tm hc)]; reflexivity.
    - inversion Hfa as [| ? ? Hx Hfa']; subst.
      assert (H1 : Reaches tm (mkCfgR (Some 6) (x :: L') (s :: R)) (mkCfgR (Some 6) L' (x :: 1 :: R)) 1).
      { apply steps_one. unfold step, mkCfgR; simpl.
        destruct Hs as [-> | ->]; [rewrite (w8_G2 tm hc) | rewrite (w8_G3 tm hc)]; reflexivity. }
      pose proof (IH x (1 :: R) Hx Hfa') as H2.
      simpl length. replace (S (S (length L'))) with (1 + S (length L')) by lia.
      eapply reaches_trans; [exact H1 | rewrite rep_r8 in H2; exact H2].
  Qed.

  Lemma w8_B1_right : forall m L R,
    Reaches tm (mkCfgR (Some 1) L (rep m 1 R)) (mkCfgR (Some 1) (rep m 3 L) R) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    replace (S m') with (1 + m') by lia.
    eapply reaches_trans; [apply (w8_step_R 1 1 2 (Some 1) L (rep m' 1 R) (w8_B1 tm hc)) |].
    specialize (IH (3 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  (* Rule 1: 3^n 2^k H> 4 R -> 3^{n+k+1} 2^1 H> R (for k >= 1) *)
  Lemma w8_rule_4 : forall n k R, 1 <= k ->
    exists t, Reaches tm (H8cfg n k (4 :: R)) (H8cfg (n + k + 1) 1 R) t /\ n + k + 1 <= t.
  Proof.
    intros n k R Hk. destruct k as [| k']; [lia |].
    assert (Hfa : Forall (fun x => x = 2 \/ x = 3) (rep k' 2 (rep n 3 []))).
    { assert (Hfr : forall m v L, (v = 2 \/ v = 3) -> Forall (fun x => x = 2 \/ x = 3) L -> Forall (fun x => x = 2 \/ x = 3) (rep m v L)).
      { induction m; intros; [exact H0 | constructor; [exact H | apply IHm; assumption]]. }
      apply Hfr; [left; reflexivity | apply Hfr; [right; reflexivity | constructor]]. }
    assert (H1 : Reaches tm (H8cfg n (S k') (4 :: R)) (mkCfgR (Some 6) (rep k' 2 (rep n 3 [])) (2 :: 3 :: R)) 1).
    { unfold H8cfg. apply steps_one. unfold step, mkCfgR; simpl; rewrite (w8_H4 tm hc); reflexivity. }
    pose proof (w8_G_left (rep k' 2 (rep n 3 [])) 2 (3 :: R) (or_introl eq_refl) Hfa) as H2.
    assert (Hlen : length (rep k' 2 (rep n 3 [])) = k' + n).
    { assert (Hlr : forall m v L, length (rep m v L) = m + length L) by (induction m; intros; [reflexivity | simpl; f_equal; apply IHm]).
      rewrite !Hlr; simpl; lia. }
    rewrite Hlen in H2.
    assert (H3 : Reaches tm (mkCfgR (Some 6) [] (0 :: rep (S (k' + n)) 1 (3 :: R)))
                            (mkCfgR (Some 1) [3] (rep (S (k' + n)) 1 (3 :: R))) 1).
    { apply steps_one. unfold step, mkCfgR; simpl; rewrite (w8_G0 tm hc); reflexivity. }
    pose proof (w8_B1_right (S (k' + n)) [3] (3 :: R)) as H4.
    assert (H5 : Reaches tm (mkCfgR (Some 1) (rep (S (k' + n)) 3 [3]) (3 :: R)) (H8cfg (n + S k' + 1) 1 R) 1).
    { unfold H8cfg. rewrite rep_r8. replace (S (S (k' + n))) with (n + S k' + 1) by lia.
      apply (w8_step_R 1 3 1 (Some 7) _ _ (w8_B3 tm hc)). }
    exists (1 + S (k' + n) + 1 + S (k' + n) + 1).
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | lia].
  Qed.

  (* Rule 2: 3^n 2^k H> 3 R -> 3^n 2^{k+1} H> R *)
  Lemma w8_rule_3 : forall n k R,
    Reaches tm (H8cfg n k (3 :: R)) (H8cfg n (S k) R) 1.
  Proof.
    intros n k R. unfold H8cfg. apply (w8_step_R 7 3 1 (Some 7) _ _ (w8_H3 tm hc)).
  Qed.

  Lemma w8_rule_3_rep : forall m n k R,
    Reaches tm (H8cfg n k (rep m 3 R)) (H8cfg n (m + k) R) m.
  Proof.
    induction m as [| m' IH]; intros n k R; [apply reaches_zero |].
    change (Reaches tm (H8cfg n k (3 :: rep m' 3 R)) (H8cfg n (S m' + k) R) (1 + m')).
    eapply reaches_trans; [apply w8_rule_3 |].
    replace (S m' + k) with (m' + S k) by lia. apply IH.
  Qed.

  (* Sweeps for Rule 3 *)
  Lemma w8_C2_left : forall m L R,
    Reaches tm (mkCfgR (Some 2) (rep m 2 L) (2 :: R)) (mkCfgR (Some 2) L (2 :: rep m 3 R)) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    replace (S m') with (1 + m') by lia.
    eapply reaches_trans.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (w8_C2 tm hc); reflexivity.
    - specialize (IH L (3 :: R)). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w8_C3_right : forall m L R,
    Reaches tm (mkCfgR (Some 2) L (rep m 3 R)) (mkCfgR (Some 2) (rep m 2 L) R) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    replace (S m') with (1 + m') by lia.
    eapply reaches_trans.
    - apply (w8_step_R 2 3 1 (Some 2) _ _ (w8_C3 tm hc)).
    - specialize (IH (2 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  (* Rule 3: 3^n 2^{k+1} H> 1 R -> 3^1 2^k H> 1^{n+1} 3 R (for k >= 1) *)
  Lemma w8_rule_1_high : forall n k R, 1 <= k ->
    exists t, Reaches tm (H8cfg n (S k) (1 :: R)) (H8cfg 1 k (rep (S n) 1 (3 :: R))) t /\ 1 <= t.
  Proof.
    intros n k R Hk. destruct k as [| k']; [lia |].
    assert (H1 : Reaches tm (H8cfg n (S (S k')) (1 :: R))
                            (mkCfgR (Some 1) (rep (S k') 2 (rep n 3 [])) (2 :: 3 :: R)) 1).
    { unfold H8cfg. apply steps_one. unfold step, mkCfgR; simpl; rewrite (w8_H1 tm hc); reflexivity. }
    assert (Hloop : forall a m,
      exists t, Reaches tm (mkCfgR (Some 1) (rep (S k') 2 (rep a 3 [])) (2 :: rep m 1 (3 :: R)))
                           (H8cfg 1 (S k') (rep (a + S m) 1 (3 :: R))) t /\ 1 <= t).
    { induction a as [| a' IHa]; intros m.
      - destruct k' as [| k''].
        + (* k'=0: B2=1LD, D2=3LC, C0=3RB, B3=2RH -> H8cfg 1 1 (1^{S m} 3 R) *)
          assert (Hs1 : Reaches tm (mkCfgR (Some 1) [2] (2 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 3) [] (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B2 tm hc); reflexivity).
          assert (Hs2 : Reaches tm (mkCfgR (Some 3) [] (2 :: 1 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 2) [] (0 :: 3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_D2 tm hc); reflexivity).
          assert (Hs3 : Reaches tm (mkCfgR (Some 2) [] (0 :: 3 :: 1 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 1) [3] (3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C0 tm hc); reflexivity).
          assert (Hs4 : Reaches tm (mkCfgR (Some 1) [3] (3 :: 1 :: rep m 1 (3 :: R)))
                                   (H8cfg 1 1 (rep (S m) 1 (3 :: R))) 1)
            by (unfold H8cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B3 tm hc); reflexivity).
          exists 4. split; [replace 4 with (1 + 1 + 1 + 1) by lia; eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | lia].
        + (* k' = S k'': B2=1LD, D2=3LC, C2_left k'', C2=3LC, C0=3RB, B3=2RH, rule_3_rep (S k'') *)
          assert (Hs1 : Reaches tm (mkCfgR (Some 1) (2 :: 2 :: rep k'' 2 []) (2 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 3) (2 :: rep k'' 2 []) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B2 tm hc); reflexivity).
          assert (Hs2 : Reaches tm (mkCfgR (Some 3) (2 :: rep k'' 2 []) (2 :: 1 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 2) (rep k'' 2 []) (2 :: 3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_D2 tm hc); reflexivity).
          pose proof (w8_C2_left k'' [] (3 :: 1 :: rep m 1 (3 :: R))) as Hs3.
          assert (Hs4 : Reaches tm (mkCfgR (Some 2) [] (2 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R))))
                                   (mkCfgR (Some 2) [] (0 :: 3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C2 tm hc); reflexivity).
          assert (Hs5 : Reaches tm (mkCfgR (Some 2) [] (0 :: 3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R))))
                                   (mkCfgR (Some 1) [3] (3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C0 tm hc); reflexivity).
          assert (Hs6 : Reaches tm (mkCfgR (Some 1) [3] (3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R))))
                                   (H8cfg 1 1 (rep (S k'') 3 (rep (S m) 1 (3 :: R)))) 1).
          { unfold H8cfg. rewrite rep_r8. apply (w8_step_R 1 3 1 (Some 7) _ _ (w8_B3 tm hc)). }
          pose proof (w8_rule_3_rep (S k'') 1 1 (rep (S m) 1 (3 :: R))) as Hs7.
          replace (S k'' + 1) with (S (S k'')) in Hs7 by lia.
          exists (1 + 1 + k'' + 1 + 1 + 1 + S k'').
          split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | exact Hs5] | exact Hs6] | exact Hs7] | lia].
      - (* a = S a': B2=1LD, D2=3LC, C2_left k', C3=2RC, C3_right (S k'), C1=1LB -> IHa (S m) *)
        destruct k' as [| k''].
        + assert (Hs1 : Reaches tm (mkCfgR (Some 1) (2 :: 3 :: rep a' 3 []) (2 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 3) (3 :: rep a' 3 []) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B2 tm hc); reflexivity).
          assert (Hs2 : Reaches tm (mkCfgR (Some 3) (3 :: rep a' 3 []) (2 :: 1 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 2) (rep a' 3 []) (3 :: 3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_D2 tm hc); reflexivity).
          pose proof (w8_C3_right 2 (rep a' 3 []) (1 :: rep m 1 (3 :: R))) as Hs3.
          assert (Hs4 : Reaches tm (mkCfgR (Some 2) (2 :: 2 :: rep a' 3 []) (1 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 1) (2 :: rep a' 3 []) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C1 tm hc); reflexivity).
          destruct (IHa (S m)) as [t2 [H2 _]].
          exists (1 + 1 + 2 + 1 + t2).
          split; [replace (S a' + S m) with (a' + S (S m)) by lia;
                  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | exact H2] | lia].
        + assert (Hs1 : Reaches tm (mkCfgR (Some 1) (2 :: 2 :: rep k'' 2 (3 :: rep a' 3 [])) (2 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 3) (2 :: rep k'' 2 (3 :: rep a' 3 [])) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B2 tm hc); reflexivity).
          assert (Hs2 : Reaches tm (mkCfgR (Some 3) (2 :: rep k'' 2 (3 :: rep a' 3 [])) (2 :: 1 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 2) (rep k'' 2 (3 :: rep a' 3 [])) (2 :: 3 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_D2 tm hc); reflexivity).
          pose proof (w8_C2_left k'' (3 :: rep a' 3 []) (3 :: 1 :: rep m 1 (3 :: R))) as Hs3.
          assert (Hs4 : Reaches tm (mkCfgR (Some 2) (3 :: rep a' 3 []) (2 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R))))
                                   (mkCfgR (Some 2) (rep a' 3 []) (3 :: 3 :: rep k'' 3 (3 :: 1 :: rep m 1 (3 :: R)))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C2 tm hc); reflexivity).
          pose proof (w8_C3_right (S (S (S k''))) (rep a' 3 []) (1 :: rep m 1 (3 :: R))) as Hs5.
          assert (Hs6 : Reaches tm (mkCfgR (Some 2) (rep (S (S (S k''))) 2 (rep a' 3 [])) (1 :: rep m 1 (3 :: R)))
                                   (mkCfgR (Some 1) (rep (S (S k'')) 2 (rep a' 3 [])) (2 :: 1 :: rep m 1 (3 :: R))) 1)
            by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C1 tm hc); reflexivity).
          destruct (IHa (S m)) as [t2 [H2 _]].
          exists (1 + 1 + k'' + 1 + S (S (S k'')) + 1 + t2).
          split.
          * replace (S a' + S m) with (a' + S (S m)) by lia.
            rewrite rep_r8 in Hs3, Hs4.
            eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | exact Hs5] | exact Hs6] | exact H2].
          * lia. }
    destruct (Hloop n 0) as [t2 [H2 Ht2]].
    replace (n + 1) with (S n) in H2 by lia.
    exists (1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | lia].
  Qed.

  (* Sweeps for Rule 4 *)
  Lemma w8_E1_right : forall m L R,
    Reaches tm (mkCfgR (Some 4) L (rep m 1 R)) (mkCfgR (Some 4) (rep m 7 L) R) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    replace (S m') with (1 + m') by lia.
    eapply reaches_trans; [apply (w8_step_R 4 1 6 (Some 4) _ _ (w8_E1 tm hc)) |].
    specialize (IH (7 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w8_B7_left : forall m R,
    Reaches tm (mkCfgR (Some 1) (rep m 7 []) (7 :: R)) (mkCfgR (Some 1) [] (0 :: rep (S m) 7 R)) (S m).
  Proof.
    induction m as [| m' IH]; intros R.
    - apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B7 tm hc); reflexivity.
    - replace (S (S m')) with (1 + S m') by lia.
      eapply reaches_trans; [apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B7 tm hc); reflexivity |].
      specialize (IH (7 :: R)). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w8_A7_right : forall m L R,
    Reaches tm (mkCfgR (Some 0) L (rep m 7 R)) (mkCfgR (Some 0) (rep m 7 L) R) m.
  Proof.
    induction m as [| m' IH]; intros L R; [apply reaches_zero |].
    replace (S m') with (1 + m') by lia.
    eapply reaches_trans; [apply (w8_step_R 0 7 6 (Some 0) _ _ (w8_A7 tm hc)) |].
    specialize (IH (7 :: L) R). rewrite rep_r8 in IH. exact IH.
  Qed.

  Lemma w8_F_enc_right : forall w L R, W8Word w ->
    Reaches tm (mkCfgR (Some 5) L (w ++ R)) (mkCfgR (Some 5) (rev (enc_word w) ++ L) R) (length w).
  Proof.
    induction w as [| s w' IH]; intros L R Hw; [apply reaches_zero |].
    inversion Hw as [| ? ? Hs Hw']; subst.
    simpl length. replace (S (length w')) with (1 + length w') by lia.
    destruct Hs as [-> | ->].
    - eapply reaches_trans; [apply (w8_step_R 5 1 4 (Some 5) L (w' ++ R) (w8_F1 tm hc)) |].
      specialize (IH (5 :: L) R Hw'). simpl rev. rewrite <- app_assoc. exact IH.
    - eapply reaches_trans; [apply (w8_step_R 5 3 5 (Some 5) L (w' ++ R) (w8_F3 tm hc)) |].
      specialize (IH (6 :: L) R Hw'). simpl rev. rewrite <- app_assoc. exact IH.
  Qed.

  Lemma w8_A_enc_right : forall w L R, W8Word w ->
    Reaches tm (mkCfgR (Some 0) L (w ++ R)) (mkCfgR (Some 0) (rev (enc_word w) ++ L) R) (length w).
  Proof.
    induction w as [| s w' IH]; intros L R Hw; [apply reaches_zero |].
    inversion Hw as [| ? ? Hs Hw']; subst.
    simpl length. replace (S (length w')) with (1 + length w') by lia.
    destruct Hs as [-> | ->].
    - eapply reaches_trans; [apply (w8_step_R 0 1 4 (Some 0) L (w' ++ R) (w8_A1 tm hc)) |].
      specialize (IH (5 :: L) R Hw'). simpl rev. rewrite <- app_assoc. exact IH.
    - eapply reaches_trans; [apply (w8_step_R 0 3 5 (Some 0) L (w' ++ R) (w8_A3 tm hc)) |].
      specialize (IH (6 :: L) R Hw'). simpl rev. rewrite <- app_assoc. exact IH.
  Qed.

  Lemma w8_dec_left : forall st,
    tm st 5 = Some (mkAction 1 DL (Some st)) ->
    tm st 6 = Some (mkAction 3 DL (Some st)) ->
    forall u L x R, W8Word u ->
    Reaches tm (match enc_word u with
                | [] => mkCfgR (Some st) L (x :: R)
                | h :: t => mkCfgR (Some st) (t ++ x :: L) (h :: R)
                end)
               (mkCfgR (Some st) L (x :: rev u ++ R)) (length u).
  Proof.
    intros st H5 H6 u. induction u as [| s u' IH]; intros L x R Hu.
    - apply reaches_zero.
    - inversion Hu as [| ? ? Hs Hu']; subst.
      simpl length. replace (S (length u')) with (1 + length u') by lia.
      simpl enc_word.
      destruct Hs as [-> | ->]; [specialize (IH L x (1 :: R) Hu') | specialize (IH L x (3 :: R) Hu')];
      destruct (enc_word u') as [| h' t'] eqn:Heq;
        (eapply reaches_trans;
         [apply steps_one; unfold step, mkCfgR, enc_sym; simpl; first [rewrite H5 | rewrite H6]; reflexivity
         | simpl rev; rewrite <- app_assoc; exact IH]).
  Qed.

  (* Copy loop: 7^{S m} enc(v) 4 enc(u) B> (s :: v ++ 4 :: R) -> 7^{S m} enc(w) B> (4 :: w ++ 4 :: R)
     where w = rev u ++ v. We state it directly on reversed u! *)
  Lemma w8_copy_step : forall m u v R, 1 <= m -> W8Word u -> W8Word v ->
    exists t, Reaches tm (match enc_word u with
                          | [] => mkCfgR (Some 1) (rev (enc_word v) ++ rep m 7 []) (4 :: v ++ 4 :: R)
                          | h :: t0 => mkCfgR (Some 1) (t0 ++ 4 :: rev (enc_word v) ++ rep m 7 []) (h :: v ++ 4 :: R)
                          end)
                         (mkCfgR (Some 1) (rev (enc_word (rev u ++ v)) ++ rep m 7 []) (4 :: (rev u ++ v) ++ 4 :: R)) t.
  Proof.
    intros m u. induction u as [| s u' IH]; intros v R Hm Hu Hv.
    - simpl. exists 0. apply reaches_zero.
    - inversion Hu as [| ? ? Hs Hu']; subst.
      destruct m as [| m']; [lia |].
      assert (Huv : W8Word (s :: v)) by (constructor; assumption).
      destruct Hs as [-> | ->].
      + (* s = 1 -> enc_sym 1 = 5, B5 = 0LC, C decodes u', C4=4LC, C decodes v, C7=1LB, B7_left, B0=7RA, A7_right, A_enc (1::v), A4=4RF, F_enc (rev u'), F0=1LB *)
        assert (H1 : Reaches tm (mkCfgR (Some 1) (enc_word u' ++ 4 :: rev (enc_word v) ++ rep (S m') 7 []) (5 :: v ++ 4 :: R))
                                (match enc_word u' with
                                 | [] => mkCfgR (Some 2) (rev (enc_word v) ++ rep (S m') 7 []) (4 :: 0 :: v ++ 4 :: R)
                                 | h' :: t' => mkCfgR (Some 2) (t' ++ 4 :: rev (enc_word v) ++ rep (S m') 7 []) (h' :: 0 :: v ++ 4 :: R)
                                 end) 1).
        { apply steps_one. destruct (enc_word u'); unfold step, mkCfgR; simpl; rewrite (w8_B5 tm hc); destruct v; reflexivity. }
        pose proof (w8_dec_left 2 (w8_C5 tm hc) (w8_C6 tm hc) u' (rev (enc_word v) ++ rep (S m') 7 []) 4 (0 :: v ++ 4 :: R) Hu') as H2.
        assert (H3 : Reaches tm (mkCfgR (Some 2) (rev (enc_word v) ++ rep (S m') 7 []) (4 :: rev u' ++ 0 :: v ++ 4 :: R))
                                (match enc_word (rev v) with
                                 | [] => mkCfgR (Some 2) (rep m' 7 []) (7 :: 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                                 | h' :: t' => mkCfgR (Some 2) (t' ++ 7 :: rep m' 7 []) (h' :: 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                                 end) 1).
        { rewrite rev_enc_word. apply steps_one.
          destruct (enc_word (rev v)); unfold step, mkCfgR; simpl; rewrite (w8_C4 tm hc); reflexivity. }
        assert (Hrevv : W8Word (rev v)) by (apply Forall_rev; exact Hv).
        pose proof (w8_dec_left 2 (w8_C5 tm hc) (w8_C6 tm hc) (rev v) (rep m' 7 []) 7 (4 :: rev u' ++ 0 :: v ++ 4 :: R) Hrevv) as H4.
        rewrite rev_involutive in H4.
        assert (H5 : Reaches tm (mkCfgR (Some 2) (rep m' 7 []) (7 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R))
                                (match m' with
                                 | 0 => mkCfgR (Some 1) [] (0 :: 1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                                 | S m'' => mkCfgR (Some 1) (rep m'' 7 []) (7 :: 1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                                 end) 1).
        { apply steps_one. destruct m'; unfold step, mkCfgR; simpl; rewrite (w8_C7 tm hc); reflexivity. }
        assert (H6 : exists t6, Reaches tm (match m' with
                                            | 0 => mkCfgR (Some 1) [] (0 :: 1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                                            | S m'' => mkCfgR (Some 1) (rep m'' 7 []) (7 :: 1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)
                                            end)
                                           (mkCfgR (Some 0) (rep (S m') 7 []) (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)) t6).
        { destruct m' as [| m''].
          - exists 1. apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B0 tm hc); reflexivity.
          - pose proof (w8_B7_left m'' (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)) as Hb.
            assert (Hb0 : Reaches tm (mkCfgR (Some 1) [] (0 :: rep (S m'') 7 (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)))
                                     (mkCfgR (Some 0) [7] (rep (S m'') 7 (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R))) 1)
              by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B0 tm hc); reflexivity).
            pose proof (w8_A7_right (S m'') [7] (1 :: v ++ 4 :: rev u' ++ 0 :: v ++ 4 :: R)) as Ha.
            rewrite rep_r8 in Ha.
            exists (S m'' + 1 + S m''). eapply reaches_trans; [eapply reaches_trans; [exact Hb | exact Hb0] | exact Ha]. }
        destruct H6 as [t6 H6].
        pose proof (w8_A_enc_right (1 :: v) (rep (S m') 7 []) (4 :: rev u' ++ 0 :: v ++ 4 :: R) Huv) as H7.
        assert (H8 : Reaches tm (mkCfgR (Some 0) (rev (enc_word (1 :: v)) ++ rep (S m') 7 []) (4 :: rev u' ++ 0 :: v ++ 4 :: R))
                                (mkCfgR (Some 5) (4 :: rev (enc_word (1 :: v)) ++ rep (S m') 7 []) (rev u' ++ 0 :: v ++ 4 :: R)) 1)
          by (apply (w8_step_R 0 4 3 (Some 5) _ _ (w8_A4 tm hc))).
        assert (Hrevu : W8Word (rev u')) by (apply Forall_rev; exact Hu').
        pose proof (w8_F_enc_right (rev u') (4 :: rev (enc_word (1 :: v)) ++ rep (S m') 7 []) (0 :: v ++ 4 :: R) Hrevu) as H9.
        assert (H10 : Reaches tm (mkCfgR (Some 5) (rev (enc_word (rev u')) ++ 4 :: rev (enc_word (1 :: v)) ++ rep (S m') 7 []) (0 :: v ++ 4 :: R))
                                 (match enc_word u' with
                                  | [] => mkCfgR (Some 1) (rev (enc_word (1 :: v)) ++ rep (S m') 7 []) (4 :: (1 :: v) ++ 4 :: R)
                                  | h' :: t' => mkCfgR (Some 1) (t' ++ 4 :: rev (enc_word (1 :: v)) ++ rep (S m') 7 []) (h' :: (1 :: v) ++ 4 :: R)
                                  end) 1).
        { rewrite rev_enc_word, rev_involutive. apply steps_one.
          destruct (enc_word u'); unfold step, mkCfgR; simpl; rewrite (w8_F0 tm hc); reflexivity. }
        destruct (IH (1 :: v) R ltac:(lia) Hu' Huv) as [t11 H11].
        exists (1 + length u' + 1 + length (rev v) + 1 + t6 + length (1 :: v) + 1 + length (rev u') + 1 + t11).
        simpl rev. rewrite <- app_assoc.
        eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | exact H10] | exact H11].
      + (* s = 3 -> enc_sym 3 = 6, B6 = 2LD, D decodes u', D4=4LD, D decodes v, D7=3LB, B7_left, B0=7RA, A7_right, A_enc (3::v), A4=4RF, F_enc (rev u'), F2=3LB *)
        assert (H1 : Reaches tm (mkCfgR (Some 1) (enc_word u' ++ 4 :: rev (enc_word v) ++ rep (S m') 7 []) (6 :: v ++ 4 :: R))
                                (match enc_word u' with
                                 | [] => mkCfgR (Some 3) (rev (enc_word v) ++ rep (S m') 7 []) (4 :: 2 :: v ++ 4 :: R)
                                 | h' :: t' => mkCfgR (Some 3) (t' ++ 4 :: rev (enc_word v) ++ rep (S m') 7 []) (h' :: 2 :: v ++ 4 :: R)
                                 end) 1).
        { apply steps_one. destruct (enc_word u'); unfold step, mkCfgR; simpl; rewrite (w8_B6 tm hc); reflexivity. }
        pose proof (w8_dec_left 3 (w8_D5 tm hc) (w8_D6 tm hc) u' (rev (enc_word v) ++ rep (S m') 7 []) 4 (2 :: v ++ 4 :: R) Hu') as H2.
        assert (H3 : Reaches tm (mkCfgR (Some 3) (rev (enc_word v) ++ rep (S m') 7 []) (4 :: rev u' ++ 2 :: v ++ 4 :: R))
                                (match enc_word (rev v) with
                                 | [] => mkCfgR (Some 3) (rep m' 7 []) (7 :: 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                                 | h' :: t' => mkCfgR (Some 3) (t' ++ 7 :: rep m' 7 []) (h' :: 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                                 end) 1).
        { rewrite rev_enc_word. apply steps_one.
          destruct (enc_word (rev v)); unfold step, mkCfgR; simpl; rewrite (w8_D4 tm hc); reflexivity. }
        assert (Hrevv : W8Word (rev v)) by (apply Forall_rev; exact Hv).
        pose proof (w8_dec_left 3 (w8_D5 tm hc) (w8_D6 tm hc) (rev v) (rep m' 7 []) 7 (4 :: rev u' ++ 2 :: v ++ 4 :: R) Hrevv) as H4.
        rewrite rev_involutive in H4.
        assert (H5 : Reaches tm (mkCfgR (Some 3) (rep m' 7 []) (7 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R))
                                (match m' with
                                 | 0 => mkCfgR (Some 1) [] (0 :: 3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                                 | S m'' => mkCfgR (Some 1) (rep m'' 7 []) (7 :: 3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                                 end) 1).
        { apply steps_one. destruct m'; unfold step, mkCfgR; simpl; rewrite (w8_D7 tm hc); reflexivity. }
        assert (H6 : exists t6, Reaches tm (match m' with
                                            | 0 => mkCfgR (Some 1) [] (0 :: 3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                                            | S m'' => mkCfgR (Some 1) (rep m'' 7 []) (7 :: 3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)
                                            end)
                                           (mkCfgR (Some 0) (rep (S m') 7 []) (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)) t6).
        { destruct m' as [| m''].
          - exists 1. apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B0 tm hc); reflexivity.
          - pose proof (w8_B7_left m'' (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)) as Hb.
            assert (Hb0 : Reaches tm (mkCfgR (Some 1) [] (0 :: rep (S m'') 7 (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)))
                                     (mkCfgR (Some 0) [7] (rep (S m'') 7 (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R))) 1)
              by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B0 tm hc); reflexivity).
            pose proof (w8_A7_right (S m'') [7] (3 :: v ++ 4 :: rev u' ++ 2 :: v ++ 4 :: R)) as Ha.
            rewrite rep_r8 in Ha.
            exists (S m'' + 1 + S m''). eapply reaches_trans; [eapply reaches_trans; [exact Hb | exact Hb0] | exact Ha]. }
        destruct H6 as [t6 H6].
        pose proof (w8_A_enc_right (3 :: v) (rep (S m') 7 []) (4 :: rev u' ++ 2 :: v ++ 4 :: R) Huv) as H7.
        assert (H8 : Reaches tm (mkCfgR (Some 0) (rev (enc_word (3 :: v)) ++ rep (S m') 7 []) (4 :: rev u' ++ 2 :: v ++ 4 :: R))
                                (mkCfgR (Some 5) (4 :: rev (enc_word (3 :: v)) ++ rep (S m') 7 []) (rev u' ++ 2 :: v ++ 4 :: R)) 1)
          by (apply (w8_step_R 0 4 3 (Some 5) _ _ (w8_A4 tm hc))).
        assert (Hrevu : W8Word (rev u')) by (apply Forall_rev; exact Hu').
        pose proof (w8_F_enc_right (rev u') (4 :: rev (enc_word (3 :: v)) ++ rep (S m') 7 []) (2 :: v ++ 4 :: R) Hrevu) as H9.
        assert (H10 : Reaches tm (mkCfgR (Some 5) (rev (enc_word (rev u')) ++ 4 :: rev (enc_word (3 :: v)) ++ rep (S m') 7 []) (2 :: v ++ 4 :: R))
                                 (match enc_word u' with
                                  | [] => mkCfgR (Some 1) (rev (enc_word (3 :: v)) ++ rep (S m') 7 []) (4 :: (3 :: v) ++ 4 :: R)
                                  | h' :: t' => mkCfgR (Some 1) (t' ++ 4 :: rev (enc_word (3 :: v)) ++ rep (S m') 7 []) (h' :: (3 :: v) ++ 4 :: R)
                                  end) 1).
        { rewrite rev_enc_word, rev_involutive. apply steps_one.
          destruct (enc_word u'); unfold step, mkCfgR; simpl; rewrite (w8_F2 tm hc); reflexivity. }
        destruct (IH (3 :: v) R ltac:(lia) Hu' Huv) as [t11 H11].
        exists (1 + length u' + 1 + length (rev v) + 1 + t6 + length (3 :: v) + 1 + length (rev u') + 1 + t11).
        simpl rev. rewrite <- app_assoc.
        eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | exact H10] | exact H11].
  Qed.

  (* Repeat loop: 7^{S m} E> 3 w 4 R -> 3^1 2^1 H> (w 4)^{S (S m)} R *)
  Lemma w8_repeat_E : forall m w R, W8Word w ->
    exists t, Reaches tm (mkCfgR (Some 4) (rep (S m) 7 []) (3 :: w ++ 4 :: R))
                         (H8cfg 1 1 (rep_app (S (S m)) (w ++ [4]) R)) t /\ 1 <= t.
  Proof.
    induction m as [| m' IH]; intros w R Hw.
    - (* m = 0: 7^1 E> 3 w 4 R -> 7^1 4 F> w 4 R -> copy -> 7^1 enc(w) B> 4 w 4 R -> B4=4LF -> F decodes -> F7=3LE -> E0=3RB -> B3=2RH *)
      assert (H1 : Reaches tm (mkCfgR (Some 4) [7] (3 :: w ++ 4 :: R)) (mkCfgR (Some 5) [4; 7] (w ++ 4 :: R)) 1)
        by (apply (w8_step_R 4 3 3 (Some 5) _ _ (w8_E3 tm hc))).
      pose proof (w8_F_enc_right w [4; 7] (4 :: R) Hw) as H2.
      assert (H3 : Reaches tm (mkCfgR (Some 5) (rev (enc_word w) ++ [4; 7]) (4 :: R))
                              (match enc_word (rev w) with
                               | [] => mkCfgR (Some 1) [7] (4 :: 4 :: R)
                               | h :: t0 => mkCfgR (Some 1) (t0 ++ 4 :: [7]) (h :: 4 :: R)
                               end) 1).
      { rewrite rev_enc_word. apply steps_one.
        destruct (enc_word (rev w)); unfold step, mkCfgR; simpl; rewrite (w8_F4 tm hc); reflexivity. }
      assert (Hrevw : W8Word (rev w)) by (apply Forall_rev; exact Hw).
      destruct (w8_copy_step 1 (rev w) [] R ltac:(lia) Hrevw (Forall_nil _)) as [t4 H4].
      rewrite rev_involutive, app_nil_r in H4.
      assert (H5 : Reaches tm (mkCfgR (Some 1) (rev (enc_word w) ++ [7]) (4 :: w ++ 4 :: R))
                              (match enc_word (rev w) with
                               | [] => mkCfgR (Some 5) [] (7 :: 4 :: w ++ 4 :: R)
                               | h :: t0 => mkCfgR (Some 5) (t0 ++ [7]) (h :: 4 :: w ++ 4 :: R)
                               end) 1).
      { rewrite rev_enc_word. apply steps_one.
        destruct (enc_word (rev w)); unfold step, mkCfgR; simpl; rewrite (w8_B4 tm hc); reflexivity. }
      pose proof (w8_dec_left 5 (w8_F5 tm hc) (w8_F6 tm hc) (rev w) [] 7 (4 :: w ++ 4 :: R) Hrevw) as H6.
      rewrite rev_involutive in H6.
      assert (H7 : Reaches tm (mkCfgR (Some 5) [] (7 :: w ++ 4 :: w ++ 4 :: R))
                              (mkCfgR (Some 4) [] (0 :: 3 :: w ++ 4 :: w ++ 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_F7 tm hc); reflexivity).
      assert (H8 : Reaches tm (mkCfgR (Some 4) [] (0 :: 3 :: w ++ 4 :: w ++ 4 :: R))
                              (mkCfgR (Some 1) [3] (3 :: w ++ 4 :: w ++ 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_E0 tm hc); reflexivity).
      assert (H9 : Reaches tm (mkCfgR (Some 1) [3] (3 :: w ++ 4 :: w ++ 4 :: R))
                              (H8cfg 1 1 (rep_app 2 (w ++ [4]) R)) 1).
      { unfold H8cfg; simpl rep_app; rewrite <- !app_assoc; simpl.
        apply (w8_step_R 1 3 1 (Some 7) _ _ (w8_B3 tm hc)). }
      exists (1 + length w + 1 + t4 + 1 + length (rev w) + 1 + 1 + 1).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | lia].
    - (* m = S m': one copy + F7=3LE -> E7=7RE -> IH m' on (w ++ 4 :: R) *)
      assert (H1 : Reaches tm (mkCfgR (Some 4) (rep (S (S m')) 7 []) (3 :: w ++ 4 :: R))
                              (mkCfgR (Some 5) (4 :: rep (S (S m')) 7 []) (w ++ 4 :: R)) 1)
        by (apply (w8_step_R 4 3 3 (Some 5) _ _ (w8_E3 tm hc))).
      pose proof (w8_F_enc_right w (4 :: rep (S (S m')) 7 []) (4 :: R) Hw) as H2.
      assert (H3 : Reaches tm (mkCfgR (Some 5) (rev (enc_word w) ++ 4 :: rep (S (S m')) 7 []) (4 :: R))
                              (match enc_word (rev w) with
                               | [] => mkCfgR (Some 1) (rep (S (S m')) 7 []) (4 :: 4 :: R)
                               | h :: t0 => mkCfgR (Some 1) (t0 ++ 4 :: rep (S (S m')) 7 []) (h :: 4 :: R)
                               end) 1).
      { rewrite rev_enc_word. apply steps_one.
        destruct (enc_word (rev w)); unfold step, mkCfgR; simpl; rewrite (w8_F4 tm hc); reflexivity. }
      assert (Hrevw : W8Word (rev w)) by (apply Forall_rev; exact Hw).
      destruct (w8_copy_step (S (S m')) (rev w) [] R ltac:(lia) Hrevw (Forall_nil _)) as [t4 H4].
      rewrite rev_involutive, app_nil_r in H4.
      assert (H5 : Reaches tm (mkCfgR (Some 1) (rev (enc_word w) ++ rep (S (S m')) 7 []) (4 :: w ++ 4 :: R))
                              (match enc_word (rev w) with
                               | [] => mkCfgR (Some 5) (rep (S m') 7 []) (7 :: 4 :: w ++ 4 :: R)
                               | h :: t0 => mkCfgR (Some 5) (t0 ++ 7 :: rep (S m') 7 []) (h :: 4 :: w ++ 4 :: R)
                               end) 1).
      { rewrite rev_enc_word. apply steps_one.
        destruct (enc_word (rev w)); unfold step, mkCfgR; simpl; rewrite (w8_B4 tm hc); reflexivity. }
      pose proof (w8_dec_left 5 (w8_F5 tm hc) (w8_F6 tm hc) (rev w) (rep (S m') 7 []) 7 (4 :: w ++ 4 :: R) Hrevw) as H6.
      rewrite rev_involutive in H6.
      assert (H7 : Reaches tm (mkCfgR (Some 5) (rep (S m') 7 []) (7 :: w ++ 4 :: w ++ 4 :: R))
                              (mkCfgR (Some 4) (rep m' 7 []) (7 :: 3 :: w ++ 4 :: w ++ 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_F7 tm hc); reflexivity).
      assert (H8 : Reaches tm (mkCfgR (Some 4) (rep m' 7 []) (7 :: 3 :: w ++ 4 :: w ++ 4 :: R))
                              (mkCfgR (Some 4) (rep (S m') 7 []) (3 :: w ++ 4 :: w ++ 4 :: R)) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_E7 tm hc); reflexivity).
      destruct (IH w (w ++ 4 :: R) Hw) as [t9 [H9 _]].
      assert (Hra : rep_app (S (S m')) (w ++ [4]) (w ++ 4 :: R) = rep_app (S (S (S m'))) (w ++ [4]) R).
      { assert (Haux : forall k A B, rep_app k A (A ++ B) = rep_app (S k) A B).
        { induction k as [| k' IHk]; intros A B; [reflexivity | simpl; rewrite IHk; reflexivity]. }
        replace (w ++ 4 :: R) with ((w ++ [4]) ++ R) by (rewrite <- app_assoc; reflexivity).
        apply Haux. }
      rewrite Hra in H9.
      exists (1 + length w + 1 + t4 + 1 + length (rev w) + 1 + 1 + t9).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | lia].
  Qed.

  (* Rule 4: 3^n 2^1 H> 1 w 4 R -> 3^1 2^1 H> (w 4)^{n+3} R *)
  Lemma w8_rule_1_low : forall n w R, W8Word w ->
    exists t, Reaches tm (H8cfg n 1 (1 :: w ++ 4 :: R))
                         (H8cfg 1 1 (rep_app (n + 3) (w ++ [4]) R)) t /\ 1 <= t.
  Proof.
    intros n w R Hw.
    assert (H1 : Reaches tm (H8cfg n 1 (1 :: w ++ 4 :: R))
                            (mkCfgR (Some 1) (rep n 3 []) (2 :: 3 :: w ++ 4 :: R)) 1)
      by (unfold H8cfg; apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_H1 tm hc); reflexivity).
    assert (Hloop : forall a m,
      Reaches tm (mkCfgR (Some 1) (rep a 3 []) (2 :: rep m 1 (3 :: w ++ 4 :: R)))
                 (mkCfgR (Some 1) [] (2 :: rep (a + m) 1 (3 :: w ++ 4 :: R))) (3 * a)).
    { induction a as [| a' IHa]; intros m; [apply reaches_zero |].
      replace (3 * S a') with (1 + 1 + 1 + 3 * a') by lia.
      assert (Hs1 : Reaches tm (mkCfgR (Some 1) (3 :: rep a' 3 []) (2 :: rep m 1 (3 :: w ++ 4 :: R)))
                               (mkCfgR (Some 3) (rep a' 3 []) (3 :: 1 :: rep m 1 (3 :: w ++ 4 :: R))) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B2 tm hc); reflexivity).
      assert (Hs2 : Reaches tm (mkCfgR (Some 3) (rep a' 3 []) (3 :: 1 :: rep m 1 (3 :: w ++ 4 :: R)))
                               (mkCfgR (Some 2) (2 :: rep a' 3 []) (1 :: rep m 1 (3 :: w ++ 4 :: R))) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_D3 tm hc); reflexivity).
      assert (Hs3 : Reaches tm (mkCfgR (Some 2) (2 :: rep a' 3 []) (1 :: rep m 1 (3 :: w ++ 4 :: R)))
                               (mkCfgR (Some 1) (rep a' 3 []) (2 :: 1 :: rep m 1 (3 :: w ++ 4 :: R))) 1)
        by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_C1 tm hc); reflexivity).
      specialize (IHa (S m)). replace (a' + S m) with (S a' + m) in IHa by lia.
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact IHa]. }
    pose proof (Hloop n 0) as H2. rewrite Nat.add_0_r in H2.
    assert (H3 : Reaches tm (mkCfgR (Some 1) [] (2 :: rep n 1 (3 :: w ++ 4 :: R)))
                            (mkCfgR (Some 3) [] (0 :: 1 :: rep n 1 (3 :: w ++ 4 :: R))) 1)
      by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_B2 tm hc); reflexivity).
    assert (H4 : Reaches tm (mkCfgR (Some 3) [] (0 :: 1 :: rep n 1 (3 :: w ++ 4 :: R)))
                            (mkCfgR (Some 4) [7] (rep (S n) 1 (3 :: w ++ 4 :: R))) 1)
      by (apply steps_one; unfold step, mkCfgR; simpl; rewrite (w8_D0 tm hc); reflexivity).
    pose proof (w8_E1_right (S n) [7] (3 :: w ++ 4 :: R)) as H5.
    rewrite rep_r8 in H5.
    destruct (w8_repeat_E (S n) w R Hw) as [t6 [H6 _]].
    replace (S (S (S n))) with (n + 3) in H6 by lia.
    exists (1 + 3 * n + 1 + 1 + S n + t6).
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | lia].
  Qed.

  (* Pure machine recurrence F8_step matching Rules 3 & 4 *)
  Fixpoint F8_step (k : nat) (f : nat -> nat) : nat -> nat :=
    match k with
    | 0 => fun m => iter f (m + 3) 1
    | S k' => fun m => iterF (F8_step k') (S m) f 1
    end.

  Lemma rep_app_add : forall a b w R, rep_app (a + b) w R = rep_app a w (rep_app b w R).
  Proof. induction a as [| a' IH]; intros; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

  (* Semantic evaluation predicate RunW k w f *)
  Definition RunW (k : nat) (w : list nat) (f : nat -> nat) : Prop :=
    forall m R, 1 <= m ->
      exists n' t, Reaches tm (H8cfg m k (w ++ 4 :: R)) (H8cfg n' 1 R) t /\
                   f m <= n' /\ n' <= t.

  Lemma runW_nil : forall k, 1 <= k -> RunW k [] (fun m => m + 2).
  Proof.
    intros k Hk m R Hm.
    destruct (w8_rule_4 m k R Hk) as [t [H1 Ht]].
    exists (m + k + 1), t. split; [exact H1 | lia].
  Qed.

  Lemma runW_3 : forall k w f, RunW (S k) w f -> RunW k (3 :: w) f.
  Proof.
    intros k w f Hw m R Hm.
    pose proof (w8_rule_3 m k (w ++ 4 :: R)) as H1.
    destruct (Hw m R Hm) as [n' [t2 [H2 [Hf Ht2]]]].
    exists n', (1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | lia].
  Qed.

  Lemma runW_rep_app : forall f w,
    (forall x y, x <= y -> f x <= f y) -> (forall x, x <= f x) -> RunW 1 w f ->
    forall c m R, 1 <= m ->
      exists n' t, Reaches tm (H8cfg m 1 (rep_app c (w ++ [4]) R)) (H8cfg n' 1 R) t /\
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
        exists n2, (t1 + t2).
        split; [eapply reaches_trans; [exact H1 | exact H2] |].
        split.
        * assert (Hsh : f (iter f (S c'') m) = iter f (S c'') (f m)).
          { change (iter f (S (S c'')) m = iter f (S c'') (f m)).
            replace (S (S c'')) with (S c'' + 1) by lia. rewrite iter_add. reflexivity. }
          rewrite Hsh.
          eapply Nat.le_trans; [apply iter_mono_arg; [exact Hmono | exact Hf1] | exact Hf2].
        * intros _. specialize (Ht2 ltac:(lia)). lia.
  Qed.

  Lemma F8_step_props : forall k f,
    (forall x y, x <= y -> f x <= f y) -> (forall x, x + 2 <= f x) ->
    (forall x y, x <= y -> F8_step k f x <= F8_step k f y) /\
    (forall x, x + 2 <= F8_step k f x) /\
    (forall x, 1 <= x -> f x + 2 <= F8_step k f x) /\
    f (f 1) + 2 <= F8_step k f 1.
  Proof.
    induction k as [| k' IH]; intros f Hmono Hinc.
    - simpl.
      assert (Hge : forall c z, z + 2 * c <= iter f c z).
      { induction c as [| c' IHc]; intro z; [simpl; lia |].
        rewrite iter_succ. pose proof (Hinc (iter f c' z)). specialize (IHc z). lia. }
      repeat split.
      + intros x y Hxy. apply iter_mono_steps; [intro z; pose proof (Hinc z); lia | lia].
      + intro x. pose proof (Hge (x + 3) 1). lia.
      + intros x Hx. replace (x + 3) with (1 + (1 + (x + 1))) by lia.
        rewrite iter_add, iter_add, !iter_succ, !iter_zero.
        pose proof (Hinc (f (iter f (x + 1) 1))).
        assert (Harg : x <= iter f (x + 1) 1) by (pose proof (Hge (x + 1) 1); lia).
        pose proof (Hmono _ _ Harg). lia.
      + pose proof (Hinc (f (f (f 1)))). pose proof (Hinc (f (f 1))). lia.
    - assert (Hiter : forall c,
        (forall x y, x <= y -> iterF (F8_step k') c f x <= iterF (F8_step k') c f y) /\
        (forall x, x + 2 <= iterF (F8_step k') c f x) /\
        (forall x, 1 <= x -> f x <= iterF (F8_step k') c f x)).
      { induction c as [| c' [IHm [IHi IHf]]].
        - repeat split; [exact Hmono | exact Hinc | intros; simpl; lia].
        - simpl. destruct (IH _ IHm IHi) as [A [B [C _]]].
          repeat split; [exact A | exact B | intros x Hx; pose proof (C x Hx); pose proof (IHf x Hx); lia]. }
      assert (Hstep_le : forall c x, 1 <= x -> iterF (F8_step k') c f x + 2 <= iterF (F8_step k') (S c) f x).
      { intros c x Hx. simpl. destruct (Hiter c) as [Hm [Hi _]].
        destruct (IH _ Hm Hi) as [_ [_ [C _]]]. apply C; exact Hx. }
      assert (Hgrow : forall c, 1 + 2 * c <= iterF (F8_step k') c f 1).
      { induction c as [| c' IHc]; [simpl; pose proof (Hinc 1); lia |].
        pose proof (Hstep_le c' 1 ltac:(lia)). lia. }
      repeat split.
      + intros x y Hxy. simpl.
        assert (Hmono_c : forall c1 c2, c1 <= c2 -> iterF (F8_step k') c1 f 1 <= iterF (F8_step k') c2 f 1).
        { intros c1 c2 Hc. induction Hc as [| c2' Hle IHc]; [lia |].
          eapply Nat.le_trans; [exact IHc | pose proof (Hstep_le c2' 1 ltac:(lia)); lia]. }
        apply (Hmono_c (S x) (S y)); lia.
      + intro x. change (x + 2 <= iterF (F8_step k') (S x) f 1). pose proof (Hgrow (S x)). lia.
      + intros x Hx. simpl.
        destruct (Hiter x) as [Hm [Hi Hf]].
        destruct (IH _ Hm Hi) as [_ [_ [_ D]]].
        pose proof (Hgrow x) as Hgx.
        pose proof (Hm x (iterF (F8_step k') x f 1) ltac:(lia)).
        pose proof (Hf x Hx). lia.
      + simpl.
        destruct (Hiter 1) as [Hm [Hi Hf]]. simpl in Hm, Hi, Hf.
        destruct (IH _ Hm Hi) as [_ [_ [_ D]]].
        pose proof (Hf 1 ltac:(lia)) as Hf1.
        pose proof (Hm (f 1) (F8_step k' f 1) Hf1).
        pose proof (Hf (f 1) ltac:(pose proof (Hinc 1); lia)). lia.
  Qed.

  Theorem w8_run_F8 : forall k w f,
    W8Word w -> (forall x y, x <= y -> f x <= f y) -> (forall x, x + 2 <= f x) ->
    RunW (S k) w f ->
    RunW (S k) (1 :: w) (F8_step k f).
  Proof.
    induction k as [| k' IH]; intros w f Hw Hmono Hinc Hrun.
    - intros m R Hm.
      destruct (w8_rule_1_low m w R Hw) as [t1 [H1 _]].
      destruct (runW_rep_app f w Hmono (fun x => ltac:(pose proof (Hinc x); lia)) Hrun (m + 3) 1 R ltac:(lia))
        as [n' [t2 [H2 [Hf2 Ht2]]]].
      exists n', (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] |].
      split; [exact Hf2 | specialize (Ht2 ltac:(lia)); lia].
    - intros m R Hm.
      destruct (w8_rule_1_high m (S k') (w ++ 4 :: R) ltac:(lia)) as [t1 [H1 _]].
      assert (Hrep1 : forall c,
        RunW (S k') (rep c 1 (3 :: w)) (iterF (F8_step k') c f) /\
        (forall x y, x <= y -> iterF (F8_step k') c f x <= iterF (F8_step k') c f y) /\
        (forall x, x + 2 <= iterF (F8_step k') c f x)).
      { induction c as [| c' [IHr [IHm IHi]]].
        - repeat split; [apply runW_3; exact Hrun | exact Hmono | exact Hinc].
        - simpl. destruct (F8_step_props k' _ IHm IHi) as [A [B _]].
          repeat split; [| exact A | exact B].
          apply IH; [| exact IHm | exact IHi | exact IHr].
          assert (Hwr : forall j u, W8Word u -> W8Word (rep j 1 u))
            by (induction j; intros; [exact H | constructor; [left; reflexivity | apply IHj; exact H]]).
          apply Hwr; constructor; [right; reflexivity | exact Hw]. }
      assert (Hrep_app : rep (S m) 1 (3 :: w ++ 4 :: R) = rep (S m) 1 (3 :: w) ++ 4 :: R).
      { clear. induction (S m) as [| j IHj]; simpl; [reflexivity | f_equal; exact IHj]. }
      rewrite Hrep_app in H1.
      destruct (proj1 (Hrep1 (S m)) 1 R ltac:(lia)) as [n' [t2 [H2 [Hf2 Ht2]]]].
      exists n', (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] | split; [exact Hf2 | lia]].
  Qed.

  (* Pure FGH lower bound: F8_step k g (2 * n) >= 2 * fOmegaPowStep k f n *)
  Lemma F8_step_ge_fOmegaPowStep : forall k f g,
    FGHProps f ->
    (forall x y, x <= y -> g x <= g y) ->
    (forall x, x + 2 <= g x) ->
    (forall x, 1 <= x -> 2 * f x <= g (2 * x)) ->
    forall n, 1 <= n -> 2 * fOmegaPowStep k f n <= F8_step k g (2 * n).
  Proof.
    induction k as [| k' IH]; intros f g Hf Hgm Hgi Hfg n Hn.
    - simpl.
      assert (Hiter : forall c x, 1 <= x -> 2 * iter f c x <= iter g c (2 * x)).
      { induction c as [| c' IHc]; intros x Hx; [simpl; lia |].
        rewrite !iter_succ.
        eapply Nat.le_trans; [apply Hfg; pose proof (iter_ge_self _ (fgh_ge_self _ Hf) c' x); lia |].
        apply Hgm; apply IHc; exact Hx. }
      assert (Hge : forall c z, z + 2 * c <= iter g c z).
      { induction c as [| c' IHc]; intro z; [simpl; lia |].
        rewrite iter_succ. pose proof (Hgi (iter g c' z)). specialize (IHc z). lia. }
      change (2 * iter f n n <= iter g (2 * n + 3) 1).
      replace (2 * n + 3) with (n + (n + 3)) by lia. rewrite iter_add.
      eapply Nat.le_trans; [apply (Hiter n n Hn) |].
      apply iter_mono_arg; [exact Hgm | pose proof (Hge (n + 3) 1); lia].
    - simpl.
      assert (Hiter_props : forall c,
        FGHProps (iterF (fOmegaPowStep k') c f) /\
        (forall x y, x <= y -> iterF (F8_step k') c g x <= iterF (F8_step k') c g y) /\
        (forall x, x + 2 <= iterF (F8_step k') c g x) /\
        (forall x, 1 <= x -> 2 * iterF (fOmegaPowStep k') c f x <= iterF (F8_step k') c g (2 * x))).
      { induction c as [| c' [Hcf [Hcm [Hci Hcfg]]]].
        - split; [exact Hf | split; [exact Hgm | split; [exact Hgi | exact Hfg]]].
        - simpl. destruct (F8_step_props k' _ Hcm Hci) as [A [B _]].
          split; [apply fOmegaPowStep_props; exact Hcf | split; [exact A | split; [exact B |]]].
          intros x Hx. apply IH; assumption. }
      (* iterF (F8_step k') (S (2*n)) g 1 = iterF (F8_step k') (n + 1) (iterF (F8_step k') n g) 1 *)
      (* Wait: iterF (F8_step k') (S (2*n)) g 1 = F8_step k' (iterF (F8_step k') (2*n) g) 1
         >= (iterF (F8_step k') (2*n) g) ((iterF (F8_step k') (2*n) g) 1)
         and (iterF (F8_step k') (2*n) g) 1 >= 1 + 2*(2*n) >= 2*n!
         And (iterF (F8_step k') (2*n) g) (2*n) >= (iterF (F8_step k') n g) (2*n) >= 2 * iterF (fOmegaPowStep k') n f n! *)
      assert (Hgrow : forall c, 1 + 2 * c <= iterF (F8_step k') c g 1).
      { induction c as [| c' IHc]; [simpl; pose proof (Hgi 1); lia |].
        simpl. destruct (Hiter_props c') as [_ [Hm [Hi _]]].
        destruct (F8_step_props k' _ Hm Hi) as [_ [_ [C _]]].
        pose proof (C 1 ltac:(lia)). lia. }
      assert (Hmono_c : forall c1 c2 x, 1 <= x -> c1 <= c2 -> iterF (F8_step k') c1 g x <= iterF (F8_step k') c2 g x).
      { intros c1 c2 x Hx Hc. induction Hc as [| c2' Hle IHc]; [lia |].
        eapply Nat.le_trans; [exact IHc |].
        simpl. destruct (Hiter_props c2') as [_ [Hm [Hi _]]].
        destruct (F8_step_props k' _ Hm Hi) as [_ [_ [C _]]].
        pose proof (C x Hx). lia. }
      destruct (Hiter_props (2 * n)) as [_ [H2m [H2i _]]].
      destruct (F8_step_props k' _ H2m H2i) as [_ [_ [_ D]]].
      destruct (Hiter_props n) as [_ [_ [_ Hnfg]]].
      pose proof (Hgrow (2 * n)) as Hg2n.
      pose proof (H2m (2 * n) (iterF (F8_step k') (2 * n) g 1) ltac:(lia)) as Hstep1.
      pose proof (Hmono_c n (2 * n) (2 * n) ltac:(lia) ltac:(lia)) as Hstep2.
      pose proof (Hnfg n Hn) as Hstep3.
      change (2 * iterF (fOmegaPowStep k') n f n <= F8_step k' (iterF (F8_step k') (2 * n) g) 1).
      lia.
  Qed.

  (* Parity preservation: if w++[4] preserves Odd, then (1::w)++[4] preserves Odd! *)
  Definition PresOdd (k : nat) (w : list nat) : Prop :=
    forall m R, 1 <= m -> Nat.Odd m ->
      exists n' t, Reaches tm (H8cfg m k (w ++ 4 :: R)) (H8cfg n' 1 R) t /\ Nat.Odd n'.

  Lemma presOdd_rep_app : forall w, PresOdd 1 w ->
    forall c m R, 1 <= m -> Nat.Odd m ->
      exists n' t, Reaches tm (H8cfg m 1 (rep_app c (w ++ [4]) R)) (H8cfg n' 1 R) t /\ Nat.Odd n'.
  Proof.
    intros w Hw. induction c as [| c' IH]; intros m R Hm Hodd.
    - exists m, 0. split; [apply reaches_zero | exact Hodd].
    - simpl rep_app. rewrite <- app_assoc. simpl.
      destruct (Hw m (rep_app c' (w ++ [4]) R) Hm Hodd) as [n1 [t1 [H1 Hodd1]]].
      assert (Hn1 : 1 <= n1) by (destruct Hodd1 as [q ->]; lia).
      destruct (IH n1 R Hn1 Hodd1) as [n2 [t2 [H2 Hodd2]]].
      exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | exact Hodd2].
  Qed.

  Lemma presOdd_13_level1 : PresOdd 1 [1; 3].
  Proof.
    intros m R Hm [q Hq].
    destruct (w8_rule_1_low m [3] R ltac:(constructor; [right; reflexivity | constructor])) as [t1 [H1 _]].
    (* m + 3 = 2 * (q + 2) copies of [3; 4], each adding 3 -> 1 + 3 * 2 * (q + 2) is Odd! *)
    assert (Hpairs : forall p a R0, 1 <= a ->
      exists t, Reaches tm (H8cfg a 1 (rep_app (2 * p) [3; 4] R0)) (H8cfg (a + 6 * p) 1 R0) t).
    { induction p as [| p' IHp]; intros a R0 Ha.
      - exists 0. replace (a + 6 * 0) with a by lia. apply reaches_zero.
      - replace (2 * S p') with (2 + 2 * p') by lia. rewrite rep_app_add. simpl rep_app.
        pose proof (w8_rule_3 a 1 (4 :: 3 :: 4 :: rep_app (2 * p') [3; 4] R0)) as Hs1.
        destruct (w8_rule_4 a 2 (3 :: 4 :: rep_app (2 * p') [3; 4] R0) ltac:(lia)) as [t2 [Hs2 _]].
        pose proof (w8_rule_3 (a + 2 + 1) 1 (4 :: rep_app (2 * p') [3; 4] R0)) as Hs3.
        destruct (w8_rule_4 (a + 2 + 1) 2 (rep_app (2 * p') [3; 4] R0) ltac:(lia)) as [t4 [Hs4 _]].
        destruct (IHp (a + 2 + 1 + 2 + 1) R0 ltac:(lia)) as [t5 Hs5].
        replace (a + 2 + 1 + 2 + 1 + 6 * p') with (a + 6 * S p') in Hs5 by lia.
        exists (1 + t2 + 1 + t4 + t5).
        eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Hs3] | exact Hs4] | exact Hs5]. }
    replace (m + 3) with (2 * (q + 2)) in H1 by lia.
    destruct (Hpairs (q + 2) 1 R ltac:(lia)) as [t2 H2].
    exists (1 + 6 * (q + 2)), (t1 + t2).
    split; [eapply reaches_trans; [exact H1 | exact H2] | exists (3 * (q + 2)); lia].
  Qed.

  Lemma presOdd_step : forall k w, W8Word w -> PresOdd (S k) w -> PresOdd (S k) (1 :: w).
  Proof.
    induction k as [| k' IH]; intros w Hw Hodd m R Hm Hmo.
    - destruct (w8_rule_1_low m w R Hw) as [t1 [H1 _]].
      destruct (presOdd_rep_app w Hodd (m + 3) 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 Hodd']]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | exact Hodd'].
    - destruct (w8_rule_1_high m (S k') (w ++ 4 :: R) ltac:(lia)) as [t1 [H1 _]].
      assert (Hrep1 : forall c, PresOdd (S k') (rep c 1 (3 :: w))).
      { induction c as [| c' IHc].
        - intros a R0 Ha Hao. pose proof (w8_rule_3 a (S k') (w ++ 4 :: R0)) as Hs1.
          destruct (Hodd a R0 Ha Hao) as [n' [t2 [Hs2 Ho']]].
          exists n', (1 + t2). split; [eapply reaches_trans; [exact Hs1 | exact Hs2] | exact Ho'].
        - apply IH; [| exact IHc].
          assert (Hwr : forall j u, W8Word u -> W8Word (rep j 1 u))
            by (induction j; intros; [exact H | constructor; [left; reflexivity | apply IHj; exact H]]).
          apply Hwr; constructor; [right; reflexivity | exact Hw]. }
      assert (Hra : rep (S m) 1 (3 :: w ++ 4 :: R) = rep (S m) 1 (3 :: w) ++ 4 :: R)
        by (clear; induction (S m); simpl; [reflexivity | f_equal; exact IHn]).
      rewrite Hra in H1.
      destruct (Hrep1 (S m) 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 Hodd']]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | exact Hodd'].
  Qed.

  (* Combined FGH + Odd preservation: RunWOdd k w f *)
  Definition RunWOdd (k : nat) (w : list nat) (f : nat -> nat) : Prop :=
    forall m R, 1 <= m -> Nat.Odd m ->
      exists n' t, Reaches tm (H8cfg m k (w ++ 4 :: R)) (H8cfg n' 1 R) t /\
                   f m <= n' /\ n' <= t /\ Nat.Odd n'.

  Lemma runWOdd_rep_app : forall f w,
    (forall x y, x <= y -> f x <= f y) -> (forall x, x <= f x) -> RunWOdd 1 w f ->
    forall c m R, 1 <= m -> Nat.Odd m ->
      exists n' t, Reaches tm (H8cfg m 1 (rep_app c (w ++ [4]) R)) (H8cfg n' 1 R) t /\
                   iter f c m <= n' /\ (1 <= c -> n' <= t) /\ Nat.Odd n'.
  Proof.
    intros f w Hmono Hself Hw. induction c as [| c' IH]; intros m R Hm Ho.
    - exists m, 0. split; [apply reaches_zero | simpl; repeat split; [lia | lia | exact Ho]].
    - simpl rep_app. rewrite <- app_assoc. simpl.
      destruct (Hw m (rep_app c' (w ++ [4]) R) Hm Ho) as [n1 [t1 [H1 [Hf1 [Ht1 Ho1]]]]].
      destruct c' as [| c''].
      + exists n1, t1. simpl in *. split; [exact H1 | repeat split; [lia | lia | exact Ho1]].
      + assert (Hn1 : 1 <= n1) by (pose proof (Hself m); lia).
        destruct (IH n1 R Hn1 Ho1) as [n2 [t2 [H2 [Hf2 [Ht2 Ho2]]]]].
        exists n2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
        repeat split; [| intros _; specialize (Ht2 ltac:(lia)); lia | exact Ho2].
        assert (Hsh : f (iter f (S c'') m) = iter f (S c'') (f m)).
        { change (iter f (S (S c'')) m = iter f (S c'') (f m)).
          replace (S (S c'')) with (S c'' + 1) by lia. rewrite iter_add. reflexivity. }
        rewrite Hsh.
        eapply Nat.le_trans; [apply iter_mono_arg; [exact Hmono | exact Hf1] | exact Hf2].
  Qed.

  Lemma w8_run_F8_odd : forall k w f,
    W8Word w -> (forall x y, x <= y -> f x <= f y) -> (forall x, x + 2 <= f x) ->
    RunWOdd (S k) w f ->
    RunWOdd (S k) (1 :: w) (F8_step k f).
  Proof.
    induction k as [| k' IH]; intros w f Hw Hmono Hinc Hrun m R Hm Ho.
    - destruct (w8_rule_1_low m w R Hw) as [t1 [H1 _]].
      destruct (runWOdd_rep_app f w Hmono (fun x => ltac:(pose proof (Hinc x); lia)) Hrun (m + 3) 1 R ltac:(lia) (ex_intro _ 0 eq_refl))
        as [n' [t2 [H2 [Hf2 [Ht2 Ho']]]]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | repeat split; [exact Hf2 | specialize (Ht2 ltac:(lia)); lia | exact Ho']].
    - destruct (w8_rule_1_high m (S k') (w ++ 4 :: R) ltac:(lia)) as [t1 [H1 _]].
      assert (Hrep1 : forall c,
        RunWOdd (S k') (rep c 1 (3 :: w)) (iterF (F8_step k') c f) /\
        (forall x y, x <= y -> iterF (F8_step k') c f x <= iterF (F8_step k') c f y) /\
        (forall x, x + 2 <= iterF (F8_step k') c f x)).
      { induction c as [| c' [IHr [IHm IHi]]].
        - repeat split; [| exact Hmono | exact Hinc].
          intros a R0 Ha Hao. pose proof (w8_rule_3 a (S k') (w ++ 4 :: R0)) as Hs1.
          destruct (Hrun a R0 Ha Hao) as [n' [t2 [Hs2 [Hf2 [Ht2 Ho']]]]].
          exists n', (1 + t2). split; [eapply reaches_trans; [exact Hs1 | exact Hs2] | repeat split; [exact Hf2 | lia | exact Ho']].
        - simpl. destruct (F8_step_props k' _ IHm IHi) as [A [B _]].
          repeat split; [| exact A | exact B].
          apply IH; [| exact IHm | exact IHi | exact IHr].
          assert (Hwr : forall j u, W8Word u -> W8Word (rep j 1 u))
            by (induction j; intros; [exact H | constructor; [left; reflexivity | apply IHj; exact H]]).
          apply Hwr; constructor; [right; reflexivity | exact Hw]. }
      assert (Hra : rep (S m) 1 (3 :: w ++ 4 :: R) = rep (S m) 1 (3 :: w) ++ 4 :: R)
        by (clear; induction (S m); simpl; [reflexivity | f_equal; exact IHn]).
      rewrite Hra in H1.
      destruct (proj1 (Hrep1 (S m)) 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 [Hf2 [Ht2 Ho']]]]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | repeat split; [exact Hf2 | lia | exact Ho']].
  Qed.

  (* Base case for RunWOdd: 1 :: rep j 3 [] at level S k! *)
  Lemma w8_run_1_rep3_odd : forall k j,
    RunWOdd (S k) (1 :: rep j 3 []) (F8_step k (fun m => m + 2)).
  Proof.
    induction k as [| k' IH]; intros j m R Hm [q Hq].
    - destruct (w8_rule_1_low m (rep j 3 []) R) as [t1 [H1 _]].
      { clear. induction j; [constructor | constructor; [right; reflexivity | exact IHj]]. }
      assert (Hone : forall a R0, 1 <= a ->
        exists t, Reaches tm (H8cfg a 1 (rep j 3 [] ++ 4 :: R0)) (H8cfg (a + j + 2) 1 R0) t /\ a + j + 2 <= t).
      { intros a R0 Ha.
        assert (Hra : rep j 3 [] ++ 4 :: R0 = rep j 3 (4 :: R0)) by (clear; induction j; simpl; [reflexivity | f_equal; exact IHj]).
        rewrite Hra.
        pose proof (w8_rule_3_rep j a 1 (4 :: R0)) as Hs1.
        destruct (w8_rule_4 a (j + 1) R0 ltac:(lia)) as [t2 [Hs2 Ht2]].
        replace (a + (j + 1) + 1) with (a + j + 2) in Hs2, Ht2 by lia.
        exists (j + t2). split; [eapply reaches_trans; [exact Hs1 | exact Hs2] | lia]. }
      assert (Hrep : forall c a R0, 1 <= a ->
        exists t, Reaches tm (H8cfg a 1 (rep_app c (rep j 3 [] ++ [4]) R0)) (H8cfg (a + c * (j + 2)) 1 R0) t /\ (1 <= c -> a + c * (j + 2) <= t)).
      { induction c as [| c' IHc]; intros a R0 Ha.
        - exists 0. replace (a + 0 * (j + 2)) with a by lia. split; [apply reaches_zero | lia].
        - simpl rep_app. rewrite <- app_assoc. simpl.
          destruct (Hone a (rep_app c' (rep j 3 [] ++ [4]) R0) Ha) as [t2 [Hs2 Ht2]].
          destruct c' as [| c''].
          + exists t2. simpl in *. replace (a + (j + 2 + 0)) with (a + j + 2) by lia. split; [exact Hs2 | lia].
          + destruct (IHc (a + j + 2) R0 ltac:(lia)) as [t3 [Hs3 Ht3]].
            replace (a + j + 2 + S c'' * (j + 2)) with (a + S (S c'') * (j + 2)) in Hs3, Ht3 by lia.
            exists (t2 + t3). split; [eapply reaches_trans; [exact Hs2 | exact Hs3] | intros _; specialize (Ht3 ltac:(lia)); lia]. }
      destruct (Hrep (m + 3) 1 R ltac:(lia)) as [t2 [H2 Ht2]].
      assert (Hiter : forall c z, iter (fun x => x + 2) c z = z + 2 * c)
        by (induction c; intro z; [simpl; lia | rewrite iter_succ, IHc; lia]).
      exists (1 + (m + 3) * (j + 2)), (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] |].
      repeat split.
      + simpl. rewrite Hiter. nia.
      + specialize (Ht2 ltac:(lia)). lia.
      + exists ((q + 2) * (j + 2)). nia.
    - destruct (w8_rule_1_high m (S k') (rep j 3 [] ++ 4 :: R) ltac:(lia)) as [t1 [H1 _]].
      assert (Hbase : RunWOdd (S k') (1 :: rep (S j) 3 []) (F8_step k' (fun x => x + 2))) by apply IH.
      assert (Hrep1 : forall c,
        RunWOdd (S k') (rep (S c) 1 (rep (S j) 3 [])) (iterF (F8_step k') (S c) (fun x => x + 2)) /\
        (forall x y, x <= y -> iterF (F8_step k') (S c) (fun x => x + 2) x <= iterF (F8_step k') (S c) (fun x => x + 2) y) /\
        (forall x, x + 2 <= iterF (F8_step k') (S c) (fun x => x + 2) x)).
      { induction c as [| c' [IHr [IHm IHi]]].
        - destruct (F8_step_props k' (fun x => x + 2) (fun x y H => proj1 (Nat.add_le_mono_r x y 2) H) (fun x => Nat.le_refl (x + 2))) as [A [B _]].
          simpl. repeat split; [exact Hbase | exact A | exact B].
        - simpl. destruct (F8_step_props k' _ IHm IHi) as [A [B _]].
          repeat split; [| exact A | exact B].
          apply w8_run_F8_odd; [| exact IHm | exact IHi | exact IHr].
          assert (Hwr : forall u0 u, W8Word u -> W8Word (rep u0 1 u))
            by (induction u0; intros; [exact H | constructor; [left; reflexivity | apply IHu0; exact H]]).
          apply (Hwr (S c')). clear. constructor; [right; reflexivity |]. induction j; [constructor | constructor; [right; reflexivity | exact IHj]]. }
      assert (Hra : rep (S m) 1 (3 :: rep j 3 [] ++ 4 :: R) = rep (S m) 1 (rep (S j) 3 []) ++ 4 :: R)
        by (clear; induction (S m); simpl; [reflexivity | f_equal; exact IHn]).
      rewrite Hra in H1.
      destruct (proj1 (Hrep1 m) 1 R ltac:(lia) (ex_intro _ 0 eq_refl)) as [n' [t2 [H2 [Hf2 [Ht2 Ho']]]]].
      exists n', (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | repeat split; [exact Hf2 | lia | exact Ho']].
  Qed.

End Fwpw_8_Lemmas.

