(*
  rocq/Fwp2_4_Ladder.v
  Reusable Rocq 9.1 peeker-counter ladder on top of Fwp2_4Core.
  Provides f_{ω^2+1}, f_{ω^2+2}, f_{ω^2+3}, f_{ω^2+4} macro-transitions for
  BB(12,4), BB(13,4), BB(14,4), BB(15,4), BB(16,4), BB(17,4), BB(18,4).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2_4.
Import ListNotations.

Lemma rep_r : forall n v R, rep n v (v :: R) = rep (S n) v R.
Proof. induction n as [| n' IH]; intros; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma length_rep : forall n v L, length (rep n v L) = n + length L.
Proof. induction n as [| n' IH]; intros; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma forall_rep : forall n v (P : nat -> Prop) L,
  P v -> Forall P L -> Forall P (rep n v L).
Proof.
  induction n as [| n' IH]; intros v P L Hv HL; [exact HL | constructor; [exact Hv | apply IH; assumption]].
Qed.

Lemma f_omega2_props : FGHProps f_omega2.
Proof.
  constructor; unfold f_omega2.
  - intro n. apply (fgh_ge_self _ (fOmegaMul_props n 0) n).
  - intros n Hn. apply (fgh_gt_pos _ (fOmegaMul_props n 0) n Hn).
  - intros x y Hxy.
    eapply Nat.le_trans; [apply (fgh_mono _ (fOmegaMul_props x 0) x y Hxy) |].
    assert (Hma : forall a1 a2 n, a1 <= a2 -> fOmegaMul a1 0 n <= fOmegaMul a2 0 n).
    { intros a1 a2 n Ha. induction Ha as [| a2' Hle IH]; [lia |].
      eapply Nat.le_trans; [exact IH |].
      destruct n as [| n']; [change (fOmegaMul a2' 0 0 <= fOmegaMul a2' 0 0); lia |].
      change (fOmegaMul a2' 0 (S n') <= fOmegaMul a2' (S n') (S n')).
      apply fPlus_mono_idx; [apply (fOmegaMul_props a2' 0) | lia | lia]. }
    apply Hma; exact Hxy.
Qed.

Definition nz (s : nat) : Prop := s = 1 \/ s = 2 \/ s = 3.

(* Generic left-sweeper lemma: state st writes w on {1,2,3} and moves L *)
Lemma sweep_left_nz : forall tm st w L s R,
  tm st 1 = Some (mkAction w DL (Some st)) ->
  tm st 2 = Some (mkAction w DL (Some st)) ->
  tm st 3 = Some (mkAction w DL (Some st)) ->
  nz s -> Forall nz L -> R <> [] ->
  Reaches tm (mkCfgR (Some st) L (s :: R))
             (mkCfgR (Some st) [] (0 :: rep (S (length L)) w R)) (S (length L)).
Proof.
  intros tm st w L.
  induction L as [| x L' IH]; intros s R H1 H2 H3 Hs Hfa HR.
  - simpl length. apply steps_one.
    destruct R as [| r R']; [contradiction |].
    unfold step, mkCfgR; simpl.
    destruct Hs as [-> | [-> | ->]]; [rewrite H1 | rewrite H2 | rewrite H3]; simpl; destruct w; reflexivity.
  - inversion Hfa as [| ? ? Hx Hfa']; subst.
    assert (Hs1 : Reaches tm (mkCfgR (Some st) (x :: L') (s :: R))
                             (mkCfgR (Some st) L' (x :: w :: R)) 1).
    { apply steps_one.
      destruct R as [| r R']; [contradiction |].
      unfold step, mkCfgR; simpl.
      destruct Hs as [-> | [-> | ->]]; [rewrite H1 | rewrite H2 | rewrite H3]; simpl; destruct w; reflexivity. }
    pose proof (IH x (w :: R) H1 H2 H3 Hx Hfa' ltac:(discriminate)) as Hrest.
    simpl length.
    replace (S (S (length L'))) with (1 + S (length L')) by lia.
    eapply reaches_trans; [exact Hs1 |].
    rewrite rep_r in Hrest. exact Hrest.
Qed.

(* Level 1 & 2: I, J, K core *)
Record Fwp2_4_IJKCore (tm : TM) : Prop := mkFwp2_4_IJKCore {
  ijk_core : Fwp2_4Core tm;
  ijk_F0 : tm 5 0 = Some (mkAction 1 DR (Some 8));
  ijk_I0 : tm 8 0 = Some (mkAction 0 DL (Some 9));
  ijk_I1 : tm 8 1 = Some (mkAction 0 DL (Some 10));
  ijk_J0 : tm 9 0 = Some (mkAction 3 DR (Some 2));
  ijk_J1 : tm 9 1 = Some (mkAction 3 DL (Some 9));
  ijk_J2 : tm 9 2 = Some (mkAction 3 DL (Some 9));
  ijk_J3 : tm 9 3 = Some (mkAction 3 DL (Some 9));
  ijk_K0 : tm 10 0 = Some (mkAction 0 DL (Some 5));
  ijk_K1 : tm 10 1 = Some (mkAction 0 DL (Some 10));
  ijk_K2 : tm 10 2 = Some (mkAction 0 DL (Some 10));
  ijk_K3 : tm 10 3 = Some (mkAction 0 DL (Some 10))
}.

Section IJK_Lemmas.
  Variable tm : TM.
  Hypothesis hc : Fwp2_4_IJKCore tm.

  Lemma ijk_J_finish : forall R,
    Reaches tm (mkCfgR (Some 9) [] (0 :: 3 :: R)) (mkCfgR (Some 6) [] (3 :: 3 :: R)) 2.
  Proof.
    intro R.
    replace 2 with (1 + 1) by lia.
    eapply reaches_trans.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_J0 tm hc); reflexivity.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (f4_C3 tm (ijk_core tm hc)); reflexivity.
  Qed.

  (* One 0-cycle: G> 3^m (0 :: 0 :: R) -> G> 3^m' (0 :: R) *)
  Lemma ijk_zero_step : forall m R, 2 <= m -> R <> [] ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: 0 :: R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: R))) t /\
                 (3 <= m -> f_omega2 (m - 1) < m') /\
                 3 <= m' /\ m' <= t + 3.
  Proof.
    intros m R Hm HR.
    destruct (f4_rule_G3_rep tm (ijk_core tm hc) m (0 :: 0 :: R) ltac:(lia))
      as [a [b [t1 [H1 [Ha [Hge1 Hle1]]]]]].
    assert (H2 : Reaches tm (F4cfg (m - 1) a b (0 :: 0 :: R))
                            (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (0 :: R)) 1).
    { unfold F4cfg. apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_F0 tm hc); reflexivity. }
    assert (H3 : Reaches tm (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (0 :: R))
                            (mkCfgR (Some 9) (rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (1 :: 0 :: R)) 1).
    { apply steps_one. destruct R; [contradiction |].
      unfold step, mkCfgR; simpl; rewrite (ijk_I0 tm hc); reflexivity. }
    assert (Hfa : Forall nz (rep (S b) 2 (rep a 1 (rep (m - 1) 3 [])))).
    { apply forall_rep; [right; left; reflexivity |].
      apply forall_rep; [left; reflexivity |].
      apply forall_rep; [right; right; reflexivity | constructor]. }
    pose proof (sweep_left_nz tm 9 3 _ 1 (0 :: R)
                  (ijk_J1 tm hc) (ijk_J2 tm hc) (ijk_J3 tm hc) (or_introl eq_refl) Hfa ltac:(discriminate)) as H4.
    pose proof (ijk_J_finish (rep (length (rep (S b) 2 (rep a 1 (rep (m - 1) 3 [])))) 3 (0 :: R))) as H5.
    exists (S (S (length (rep (S b) 2 (rep a 1 (rep (m - 1) 3 [])))))),
           (t1 + 1 + 1 + S (length (rep (S b) 2 (rep a 1 (rep (m - 1) 3 [])))) + 2).
    split.
    - eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5].
    - rewrite !length_rep, length_nil.
      specialize (Hge1 ltac:(lia)).
      split; [intro Hm3; pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)); lia |].
      split; [lia | lia].
  Qed.

  (* Iterated 0-cycles: G> 3^m (rep k 0 (0 :: R)) -> G> 3^m' (0 :: R) *)
  Lemma ijk_zero_rep : forall k m R, 3 <= m -> R <> [] ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (rep k 0 (0 :: R))))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: R))) t /\
                 iter f_omega2 k (m - 1) <= m' - 1 /\ 3 <= m' /\ m' <= t + 3 + m.
  Proof.
    induction k as [| k' IH]; intros m R Hm HR.
    - exists m, 0. split; [apply reaches_zero | simpl; lia].
    - destruct (ijk_zero_step m (rep k' 0 R) ltac:(lia) ltac:(destruct k'; [exact HR | discriminate]))
        as [m1 [t1 [H1 [Hm1 [Hge1 Hle1]]]]].
      destruct (IH m1 R Hge1 HR) as [m2 [t2 [H2 [Hm2 [Hge2 Hle2]]]]].
      exists m2, (t1 + t2).
      split; [simpl rep; rewrite rep_r; eapply reaches_trans; [exact H1 | rewrite rep_r in H2; exact H2] |].
      split; [| lia].
      replace (iter f_omega2 (S k') (m - 1)) with (iter f_omega2 k' (f_omega2 (m - 1)))
        by (replace (S k') with (k' + 1) by lia; rewrite iter_add; reflexivity).
      eapply Nat.le_trans; [| exact Hm2].
      apply iter_mono_arg; [apply fgh_mono, f_omega2_props |].
      specialize (Hm1 Hm). lia.
  Qed.

  (* K0 = 0LF -> F0 = 1RI -> I0 = 0LJ -> J1 = 3LJ -> J0 = 3RC -> C3 = 3LG
     From mkCfgR (Some 10) [] (0 :: 0 :: R) with R <> [] -> mkCfgR (Some 6) [] (3 :: 3 :: 0 :: 0 :: R) *)
  Lemma ijk_K_finish : forall R, R <> [] ->
    Reaches tm (mkCfgR (Some 10) [] (0 :: R)) (mkCfgR (Some 6) [] (3 :: 3 :: 0 :: R)) 6.
  Proof.
    intros R HR.
    replace 6 with (1 + 1 + 1 + 1 + 2) by lia.
    destruct R as [| r R']; [contradiction |].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans | ] | ] | ].
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_K0 tm hc); reflexivity.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_F0 tm hc); reflexivity.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_I0 tm hc); reflexivity.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_J1 tm hc); reflexivity.
    - apply ijk_J_finish.
  Qed.

  (* One 1-cycle: G> 3^m (0 :: 1 :: R) -> G> 3^m' (0 :: R) with fPlus f_omega2 1 (m - 1) < m' *)
  Lemma ijk_one_step : forall m R, 3 <= m -> R <> [] ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: 1 :: R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: R))) t /\
                 fPlus f_omega2 1 (m - 1) < m' /\ 3 <= m'.
  Proof.
    intros m R Hm HR.
    destruct (f4_rule_G3_rep tm (ijk_core tm hc) m (0 :: 1 :: R) ltac:(lia))
      as [a [b [t1 [H1 [Ha [Hge1 _]]]]]].
    assert (H2 : Reaches tm (F4cfg (m - 1) a b (0 :: 1 :: R))
                            (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (1 :: R)) 1).
    { unfold F4cfg. apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_F0 tm hc); reflexivity. }
    assert (H3 : Reaches tm (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (1 :: R))
                            (mkCfgR (Some 10) (rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (1 :: 0 :: R)) 1).
    { apply steps_one. destruct R; [contradiction |].
      unfold step, mkCfgR; simpl; rewrite (ijk_I1 tm hc); reflexivity. }
    assert (Hfa : Forall nz (rep (S b) 2 (rep a 1 (rep (m - 1) 3 [])))).
    { apply forall_rep; [right; left; reflexivity |].
      apply forall_rep; [left; reflexivity |].
      apply forall_rep; [right; right; reflexivity | constructor]. }
    set (L0 := rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))).
    pose proof (sweep_left_nz tm 10 0 L0 1 (0 :: R)
                  (ijk_K1 tm hc) (ijk_K2 tm hc) (ijk_K3 tm hc) (or_introl eq_refl) Hfa ltac:(discriminate)) as H4.
    pose proof (ijk_K_finish (rep (S (length L0)) 0 (0 :: R)) ltac:(discriminate)) as H5.
    (* Now at mkCfgR (Some 6) [] (3 :: 3 :: 0 :: rep (S (length L0)) 0 (0 :: R))
       First 0-step takes m=2 to m1 >= 3; then remaining (length L0) 0-steps run iter f_omega2 (length L0) (m1 - 1) *)
    destruct (ijk_zero_step 2 (rep (length L0) 0 (0 :: R)) ltac:(lia) ltac:(destruct (length L0); discriminate))
      as [m1 [t6 [H6 [_ [Hge6 _]]]]].
    destruct (ijk_zero_rep (S (length L0)) m1 R Hge6 HR) as [m2 [t7 [H7 [Hm2 [Hge7 _]]]]].
    exists m2, (t1 + 1 + 1 + S (length L0) + 6 + t6 + t7).
    split.
    - eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7].
    - split; [| exact Hge7].
      assert (HL0 : m - 1 <= length L0).
      { unfold L0. rewrite !length_rep, length_nil. lia. }
      change (iter f_omega2 (m - 1) (m - 1) < m2).
      assert (Hcmp : iter f_omega2 (m - 1) (m - 1) <= iter f_omega2 (S (length L0)) (m1 - 1)).
      { specialize (Hge1 ltac:(lia)).
        pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)) as Hgt.
        pose proof (fgh_ge_self _ f_omega2_props (m - 1)) as Hself.
        assert (Hlen : m - 1 + (m - 1) <= S (length L0)).
        { unfold L0. rewrite !length_rep, length_nil. lia. }
        eapply Nat.le_trans; [| apply iter_mono_steps; [apply fgh_ge_self, f_omega2_props | exact Hlen]].
        rewrite iter_add.
        apply iter_mono_arg; [apply fgh_mono, f_omega2_props |].
        pose proof (iter_ge_add_pos f_omega2 (fgh_gt_pos _ f_omega2_props) (m - 1) (m1 - 1) ltac:(lia)).
        lia. }
      lia.
  Qed.

  (* Iterated 1-cycles: G> 3^m (0 :: rep n 1 R) -> G> 3^m' (0 :: R) *)
  Lemma ijk_one_rep : forall n m R, 3 <= m -> R <> [] ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: rep n 1 R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: R))) t /\
                 iter (fPlus f_omega2 1) n (m - 1) <= m' - 1 /\ 3 <= m'.
  Proof.
    induction n as [| n' IH]; intros m R Hm HR.
    - exists m, 0. split; [apply reaches_zero | simpl; lia].
    - destruct (ijk_one_step m (rep n' 1 R) Hm ltac:(destruct n'; [exact HR | discriminate]))
        as [m1 [t1 [H1 [Hm1 Hge1]]]].
      destruct (IH m1 R Hge1 HR) as [m2 [t2 [H2 [Hm2 Hge2]]]].
      exists m2, (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] |].
      split; [| exact Hge2].
      replace (iter (fPlus f_omega2 1) (S n') (m - 1))
        with (iter (fPlus f_omega2 1) n' (fPlus f_omega2 1 (m - 1)))
        by (replace (S n') with (n' + 1) by lia; rewrite iter_add; reflexivity).
      eapply Nat.le_trans; [| exact Hm2].
      apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props | lia].
  Qed.

End IJK_Lemmas.

(* Level 3: L core (adds I2 = 1LL, L0 = 0LK, L1=L2=L3 = 1LL) *)
Record Fwp2_4_LCore (tm : TM) : Prop := mkFwp2_4_LCore {
  l_ijk : Fwp2_4_IJKCore tm;
  l_I2 : tm 8 2 = Some (mkAction 1 DL (Some 11));
  l_L0 : tm 11 0 = Some (mkAction 0 DL (Some 10));
  l_L1 : tm 11 1 = Some (mkAction 1 DL (Some 11));
  l_L2 : tm 11 2 = Some (mkAction 1 DL (Some 11));
  l_L3 : tm 11 3 = Some (mkAction 1 DL (Some 11))
}.

Section L_Lemmas.
  Variable tm : TM.
  Hypothesis hc : Fwp2_4_LCore tm.

  Lemma l_L_finish : forall R, R <> [] ->
    Reaches tm (mkCfgR (Some 11) [] (0 :: R)) (mkCfgR (Some 6) [] (3 :: 3 :: 0 :: 0 :: R)) 7.
  Proof.
    intros R HR.
    replace 7 with (1 + 6) by lia.
    destruct R as [| r R']; [contradiction |].
    eapply reaches_trans.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (l_L0 tm hc); reflexivity.
    - apply (ijk_K_finish tm (l_ijk tm hc) (0 :: r :: R') ltac:(discriminate)).
  Qed.

  (* One 2-cycle: G> 3^m (0 :: 2 :: R) -> G> 3^m' (0 :: R) with fPlus f_omega2 2 (m - 1) < m' *)
  Lemma l_two_step : forall m R, 3 <= m -> R <> [] ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: 2 :: R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: R))) t /\
                 fPlus f_omega2 2 (m - 1) < m' /\ 3 <= m'.
  Proof.
    intros m R Hm HR.
    destruct (f4_rule_G3_rep tm (ijk_core tm (l_ijk tm hc)) m (0 :: 2 :: R) ltac:(lia))
      as [a [b [t1 [H1 [Ha [Hge1 _]]]]]].
    assert (H2 : Reaches tm (F4cfg (m - 1) a b (0 :: 2 :: R))
                            (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (2 :: R)) 1).
    { unfold F4cfg. apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_F0 tm (l_ijk tm hc)); reflexivity. }
    assert (H3 : Reaches tm (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (2 :: R))
                            (mkCfgR (Some 11) (rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (1 :: 1 :: R)) 1).
    { apply steps_one. destruct R; [contradiction |].
      unfold step, mkCfgR; simpl; rewrite (l_I2 tm hc); reflexivity. }
    assert (Hfa : Forall nz (rep (S b) 2 (rep a 1 (rep (m - 1) 3 [])))).
    { apply forall_rep; [right; left; reflexivity |].
      apply forall_rep; [left; reflexivity |].
      apply forall_rep; [right; right; reflexivity | constructor]. }
    set (L0 := rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))).
    pose proof (sweep_left_nz tm 11 1 L0 1 (1 :: R)
                  (l_L1 tm hc) (l_L2 tm hc) (l_L3 tm hc) (or_introl eq_refl) Hfa ltac:(discriminate)) as H4.
    pose proof (l_L_finish (rep (S (length L0)) 1 (1 :: R)) ltac:(discriminate)) as H5.
    destruct (ijk_zero_step tm (l_ijk tm hc) 2 (rep (S (length L0)) 1 (1 :: R)) ltac:(lia) ltac:(discriminate))
      as [m1 [t6 [H6 [_ [Hge6 _]]]]].
    destruct (ijk_one_rep tm (l_ijk tm hc) (S (S (length L0))) m1 R Hge6 HR)
      as [m2 [t7 [H7 [Hm2 Hge7]]]].
    exists m2, (t1 + 1 + 1 + S (length L0) + 7 + t6 + t7).
    split.
    - eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] |].
      rewrite <- rep_r in H7. exact H7.
    - split; [| exact Hge7].
      assert (Hlen : m - 1 + (m - 1) <= S (S (length L0))).
      { specialize (Hge1 ltac:(lia)).
        pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)) as Hgt.
        pose proof (fgh_ge_self _ f_omega2_props (m - 1)) as Hself.
        unfold L0. rewrite !length_rep, length_nil. lia. }
      assert (HfP : FGHProps (fPlus f_omega2 1)) by (apply fPlus_props, f_omega2_props).
      assert (Hcmp : iter (fPlus f_omega2 1) (m - 1) (m - 1) <= iter (fPlus f_omega2 1) (S (S (length L0))) (m1 - 1)).
      { eapply Nat.le_trans; [| apply iter_mono_steps; [apply fgh_ge_self, HfP | exact Hlen]].
        rewrite iter_add.
        apply iter_mono_arg; [apply fgh_mono, HfP |].
        pose proof (iter_ge_add_pos _ (fgh_gt_pos _ HfP) (m - 1) (m1 - 1) ltac:(lia)). lia. }
      assert (Heq : forall n, fPlus f_omega2 2 n = iter (fPlus f_omega2 1) n n) by reflexivity.
      rewrite Heq. lia.
  Qed.

  (* Iterated 2-cycles: G> 3^m (0 :: rep n 2 R) -> G> 3^m' (0 :: R) *)
  Lemma l_two_rep : forall n m R, 3 <= m -> R <> [] ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: rep n 2 R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: R))) t /\
                 iter (fPlus f_omega2 2) n (m - 1) <= m' - 1 /\ 3 <= m'.
  Proof.
    induction n as [| n' IH]; intros m R Hm HR.
    - exists m, 0. split; [apply reaches_zero | simpl; lia].
    - destruct (l_two_step m (rep n' 2 R) Hm ltac:(destruct n'; [exact HR | discriminate]))
        as [m1 [t1 [H1 [Hm1 Hge1]]]].
      destruct (IH m1 R Hge1 HR) as [m2 [t2 [H2 [Hm2 Hge2]]]].
      exists m2, (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] |].
      split; [| exact Hge2].
      replace (iter (fPlus f_omega2 2) (S n') (m - 1))
        with (iter (fPlus f_omega2 2) n' (fPlus f_omega2 2 (m - 1)))
        by (replace (S n') with (n' + 1) by lia; rewrite iter_add; reflexivity).
      eapply Nat.le_trans; [| exact Hm2].
      apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props | lia].
  Qed.

End L_Lemmas.

(* Level 4: M, N core (adds I3 = 3RM, M3 = 3LN, N0 = 0LL, N1=N2=N3 = 2LN) *)
Record Fwp2_4_MNCore (tm : TM) : Prop := mkFwp2_4_MNCore {
  mn_l : Fwp2_4_LCore tm;
  mn_I3 : tm 8 3 = Some (mkAction 3 DR (Some 12));
  mn_M3 : tm 12 3 = Some (mkAction 3 DL (Some 13));
  mn_N0 : tm 13 0 = Some (mkAction 0 DL (Some 11));
  mn_N1 : tm 13 1 = Some (mkAction 2 DL (Some 13));
  mn_N2 : tm 13 2 = Some (mkAction 2 DL (Some 13));
  mn_N3 : tm 13 3 = Some (mkAction 2 DL (Some 13))
}.

Section MN_Lemmas.
  Variable tm : TM.
  Hypothesis hc : Fwp2_4_MNCore tm.

  Lemma mn_N_finish : forall R, R <> [] ->
    Reaches tm (mkCfgR (Some 13) [] (0 :: R)) (mkCfgR (Some 6) [] (3 :: 3 :: 0 :: 0 :: 0 :: R)) 8.
  Proof.
    intros R HR.
    replace 8 with (1 + 7) by lia.
    destruct R as [| r R']; [contradiction |].
    eapply reaches_trans.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (mn_N0 tm hc); reflexivity.
    - apply (l_L_finish tm (mn_l tm hc) (0 :: r :: R') ltac:(discriminate)).
  Qed.

  (* One 3-cycle: G> 3^m (0 :: 3 :: 3 :: R) -> G> 3^m' (0 :: 3 :: R) with fPlus f_omega2 3 (m - 1) < m' *)
  Lemma mn_three_step : forall m R, 3 <= m ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: 3 :: 3 :: R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: 3 :: R))) t /\
                 fPlus f_omega2 3 (m - 1) < m' /\ 3 <= m'.
  Proof.
    intros m R Hm.
    destruct (f4_rule_G3_rep tm (ijk_core tm (l_ijk tm (mn_l tm hc))) m (0 :: 3 :: 3 :: R) ltac:(lia))
      as [a [b [t1 [H1 [Ha [Hge1 _]]]]]].
    set (L0 := rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))).
    assert (H2 : Reaches tm (F4cfg (m - 1) a b (0 :: 3 :: 3 :: R))
                            (mkCfgR (Some 8) (1 :: L0) (3 :: 3 :: R)) 1).
    { unfold F4cfg, L0. apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_F0 tm (l_ijk tm (mn_l tm hc))); reflexivity. }
    assert (H3 : Reaches tm (mkCfgR (Some 8) (1 :: L0) (3 :: 3 :: R))
                            (mkCfgR (Some 12) (3 :: 1 :: L0) (3 :: R)) 1).
    { apply steps_one. unfold step, mkCfgR; simpl; rewrite (mn_I3 tm hc); reflexivity. }
    assert (H4 : Reaches tm (mkCfgR (Some 12) (3 :: 1 :: L0) (3 :: R))
                            (mkCfgR (Some 13) (1 :: L0) (3 :: 3 :: R)) 1).
    { apply steps_one. unfold step, mkCfgR; simpl; rewrite (mn_M3 tm hc); reflexivity. }
    assert (Hfa : Forall nz (1 :: L0)).
    { constructor; [left; reflexivity |].
      unfold L0. apply forall_rep; [right; left; reflexivity |].
      apply forall_rep; [left; reflexivity |].
      apply forall_rep; [right; right; reflexivity | constructor]. }
    pose proof (sweep_left_nz tm 13 2 (1 :: L0) 3 (3 :: R)
                  (mn_N1 tm hc) (mn_N2 tm hc) (mn_N3 tm hc) (or_intror (or_intror eq_refl)) Hfa ltac:(discriminate)) as H5.
    pose proof (mn_N_finish (rep (S (length (1 :: L0))) 2 (3 :: R)) ltac:(discriminate)) as H6.
    destruct (ijk_zero_step tm (l_ijk tm (mn_l tm hc)) 2 (0 :: rep (S (length (1 :: L0))) 2 (3 :: R)) ltac:(lia) ltac:(discriminate))
      as [m0 [t7 [H7 [_ [Hge7 _]]]]].
    destruct (ijk_zero_step tm (l_ijk tm (mn_l tm hc)) m0 (rep (S (length (1 :: L0))) 2 (3 :: R)) ltac:(lia) ltac:(discriminate))
      as [m1 [t8 [H8 [_ [Hge8 _]]]]].
    destruct (l_two_rep tm (mn_l tm hc) (S (length (1 :: L0))) m1 (3 :: R) Hge8 ltac:(discriminate))
      as [m2 [t9 [H9 [Hm2 Hge9]]]].
    exists m2, (t1 + 1 + 1 + 1 + S (length (1 :: L0)) + 8 + t7 + t8 + t9).
    split.
    - eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9].
    - split; [| exact Hge9].
      assert (Hlen : m - 1 + (m - 1) <= S (length (1 :: L0))).
      { specialize (Hge1 ltac:(lia)).
        pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)) as Hgt.
        pose proof (fgh_ge_self _ f_omega2_props (m - 1)) as Hself.
        simpl length. unfold L0. rewrite !length_rep, length_nil. lia. }
      assert (HfP : FGHProps (fPlus f_omega2 2)) by (apply fPlus_props, f_omega2_props).
      assert (Hcmp : iter (fPlus f_omega2 2) (m - 1) (m - 1) <= iter (fPlus f_omega2 2) (S (length (1 :: L0))) (m1 - 1)).
      { eapply Nat.le_trans; [| apply iter_mono_steps; [apply fgh_ge_self, HfP | exact Hlen]].
        rewrite iter_add.
        apply iter_mono_arg; [apply fgh_mono, HfP |].
        pose proof (iter_ge_add_pos _ (fgh_gt_pos _ HfP) (m - 1) (m1 - 1) ltac:(lia)). lia. }
      assert (Heq : forall n, fPlus f_omega2 3 n = iter (fPlus f_omega2 2) n n) by reflexivity.
      rewrite Heq. lia.
  Qed.

  (* Iterated 3-cycles: G> 3^m (0 :: rep n 3 (3 :: R)) -> G> 3^m' (0 :: 3 :: R) *)
  Lemma mn_three_rep : forall n m R, 3 <= m ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: rep n 3 (3 :: R))))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: 3 :: R))) t /\
                 iter (fPlus f_omega2 3) n (m - 1) <= m' - 1 /\ 3 <= m'.
  Proof.
    induction n as [| n' IH]; intros m R Hm.
    - exists m, 0. split; [apply reaches_zero | simpl; lia].
    - destruct (mn_three_step m (rep n' 3 R) Hm) as [m1 [t1 [H1 [Hm1 Hge1]]]].
      destruct (IH m1 R Hge1) as [m2 [t2 [H2 [Hm2 Hge2]]]].
      exists m2, (t1 + t2).
      split; [simpl rep; rewrite rep_r; eapply reaches_trans; [exact H1 | rewrite rep_r in H2; exact H2] |].
      split; [| exact Hge2].
      replace (iter (fPlus f_omega2 3) (S n') (m - 1))
        with (iter (fPlus f_omega2 3) n' (fPlus f_omega2 3 (m - 1)))
        by (replace (S n') with (n' + 1) by lia; rewrite iter_add; reflexivity).
      eapply Nat.le_trans; [| exact Hm2].
      apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props | lia].
  Qed.

End MN_Lemmas.

(* Level 5: O core (adds M2 = 3LO, O0 = 0LN, O1=O2=O3 = 3LO) *)
Record Fwp2_4_OCore (tm : TM) : Prop := mkFwp2_4_OCore {
  o_mn : Fwp2_4_MNCore tm;
  o_M2 : tm 12 2 = Some (mkAction 3 DL (Some 14));
  o_O0 : tm 14 0 = Some (mkAction 0 DL (Some 13));
  o_O1 : tm 14 1 = Some (mkAction 3 DL (Some 14));
  o_O2 : tm 14 2 = Some (mkAction 3 DL (Some 14));
  o_O3 : tm 14 3 = Some (mkAction 3 DL (Some 14))
}.

Section O_Lemmas.
  Variable tm : TM.
  Hypothesis hc : Fwp2_4_OCore tm.

  Lemma o_O_finish : forall R, R <> [] ->
    Reaches tm (mkCfgR (Some 14) [] (0 :: R)) (mkCfgR (Some 6) [] (3 :: 3 :: 0 :: 0 :: 0 :: 0 :: R)) 9.
  Proof.
    intros R HR.
    replace 9 with (1 + 8) by lia.
    destruct R as [| r R']; [contradiction |].
    eapply reaches_trans.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (o_O0 tm hc); reflexivity.
    - apply (mn_N_finish tm (o_mn tm hc) (0 :: r :: R') ltac:(discriminate)).
  Qed.

  (* One 2-after-3 cycle: G> 3^m (0 :: 3 :: 2 :: R) -> G> 3^m' (0 :: 3 :: R) with fPlus f_omega2 4 (m - 1) < m' *)
  Lemma o_four_step : forall m R, 3 <= m ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: 3 :: 2 :: R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: 3 :: R))) t /\
                 fPlus f_omega2 4 (m - 1) < m' /\ 3 <= m'.
  Proof.
    intros m R Hm.
    destruct (f4_rule_G3_rep tm (ijk_core tm (l_ijk tm (mn_l tm (o_mn tm hc)))) m (0 :: 3 :: 2 :: R) ltac:(lia))
      as [a [b [t1 [H1 [Ha [Hge1 _]]]]]].
    set (L0 := rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))).
    assert (H2 : Reaches tm (F4cfg (m - 1) a b (0 :: 3 :: 2 :: R))
                            (mkCfgR (Some 8) (1 :: L0) (3 :: 2 :: R)) 1).
    { unfold F4cfg, L0. apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_F0 tm (l_ijk tm (mn_l tm (o_mn tm hc)))); reflexivity. }
    assert (H3 : Reaches tm (mkCfgR (Some 8) (1 :: L0) (3 :: 2 :: R))
                            (mkCfgR (Some 12) (3 :: 1 :: L0) (2 :: R)) 1).
    { apply steps_one. unfold step, mkCfgR; simpl; rewrite (mn_I3 tm (o_mn tm hc)); reflexivity. }
    assert (H4 : Reaches tm (mkCfgR (Some 12) (3 :: 1 :: L0) (2 :: R))
                            (mkCfgR (Some 14) (1 :: L0) (3 :: 3 :: R)) 1).
    { apply steps_one. unfold step, mkCfgR; simpl; rewrite (o_M2 tm hc); reflexivity. }
    assert (Hfa : Forall nz (1 :: L0)).
    { constructor; [left; reflexivity |].
      unfold L0. apply forall_rep; [right; left; reflexivity |].
      apply forall_rep; [left; reflexivity |].
      apply forall_rep; [right; right; reflexivity | constructor]. }
    pose proof (sweep_left_nz tm 14 3 (1 :: L0) 3 (3 :: R)
                  (o_O1 tm hc) (o_O2 tm hc) (o_O3 tm hc) (or_intror (or_intror eq_refl)) Hfa ltac:(discriminate)) as H5.
    pose proof (o_O_finish (rep (S (length (1 :: L0))) 3 (3 :: R)) ltac:(discriminate)) as H6.
    destruct (ijk_zero_step tm (l_ijk tm (mn_l tm (o_mn tm hc))) 2 (0 :: 0 :: rep (S (length (1 :: L0))) 3 (3 :: R)) ltac:(lia) ltac:(discriminate))
      as [m0 [t7 [H7 [_ [Hge7 _]]]]].
    destruct (ijk_zero_step tm (l_ijk tm (mn_l tm (o_mn tm hc))) m0 (0 :: rep (S (length (1 :: L0))) 3 (3 :: R)) ltac:(lia) ltac:(discriminate))
      as [m0' [t8 [H8 [_ [Hge8 _]]]]].
    destruct (ijk_zero_step tm (l_ijk tm (mn_l tm (o_mn tm hc))) m0' (rep (S (length (1 :: L0))) 3 (3 :: R)) ltac:(lia) ltac:(discriminate))
      as [m1 [t9 [H9 [_ [Hge9 _]]]]].
    destruct (mn_three_rep tm (o_mn tm hc) (S (length (1 :: L0))) m1 R Hge9)
      as [m2 [t10 [H10 [Hm2 Hge10]]]].
    exists m2, (t1 + 1 + 1 + 1 + S (length (1 :: L0)) + 9 + t7 + t8 + t9 + t10).
    split.
    - eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | exact H10].
    - split; [| exact Hge10].
      assert (Hlen : m - 1 + (m - 1) <= S (length (1 :: L0))).
      { specialize (Hge1 ltac:(lia)).
        pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)) as Hgt.
        pose proof (fgh_ge_self _ f_omega2_props (m - 1)) as Hself.
        simpl length. unfold L0. rewrite !length_rep, length_nil. lia. }
      assert (HfP : FGHProps (fPlus f_omega2 3)) by (apply fPlus_props, f_omega2_props).
      assert (Hcmp : iter (fPlus f_omega2 3) (m - 1) (m - 1) <= iter (fPlus f_omega2 3) (S (length (1 :: L0))) (m1 - 1)).
      { eapply Nat.le_trans; [| apply iter_mono_steps; [apply fgh_ge_self, HfP | exact Hlen]].
        rewrite iter_add.
        apply iter_mono_arg; [apply fgh_mono, HfP |].
        pose proof (iter_ge_add_pos _ (fgh_gt_pos _ HfP) (m - 1) (m1 - 1) ltac:(lia)). lia. }
      assert (Heq : forall n, fPlus f_omega2 4 n = iter (fPlus f_omega2 3) n n) by reflexivity.
      rewrite Heq. lia.
  Qed.

  (* Iterated 4-cycles: G> 3^m (0 :: 3 :: rep n 2 R) -> G> 3^m' (0 :: 3 :: R) *)
  Lemma o_four_rep : forall n m R, 3 <= m ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: 3 :: rep n 2 R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: 3 :: R))) t /\
                 iter (fPlus f_omega2 4) n (m - 1) <= m' - 1 /\ 3 <= m'.
  Proof.
    induction n as [| n' IH]; intros m R Hm.
    - exists m, 0. split; [apply reaches_zero | simpl; lia].
    - destruct (o_four_step m (rep n' 2 R) Hm) as [m1 [t1 [H1 [Hm1 Hge1]]]].
      destruct (IH m1 R Hge1) as [m2 [t2 [H2 [Hm2 Hge2]]]].
      exists m2, (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] |].
      split; [| exact Hge2].
      replace (iter (fPlus f_omega2 4) (S n') (m - 1))
        with (iter (fPlus f_omega2 4) n' (fPlus f_omega2 4 (m - 1)))
        by (replace (S n') with (n' + 1) by lia; rewrite iter_add; reflexivity).
      eapply Nat.le_trans; [| exact Hm2].
      apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props | lia].
  Qed.

End O_Lemmas.

(* Level 6: P core (adds M1 = 2LP, P0 = 3LO, P1=P2=P3 = 2LP) *)
Record Fwp2_4_PCore (tm : TM) : Prop := mkFwp2_4_PCore {
  p_o : Fwp2_4_OCore tm;
  p_M1 : tm 12 1 = Some (mkAction 2 DL (Some 15));
  p_P0 : tm 15 0 = Some (mkAction 3 DL (Some 14));
  p_P1 : tm 15 1 = Some (mkAction 2 DL (Some 15));
  p_P2 : tm 15 2 = Some (mkAction 2 DL (Some 15));
  p_P3 : tm 15 3 = Some (mkAction 2 DL (Some 15))
}.

Section P_Lemmas.
  Variable tm : TM.
  Hypothesis hc : Fwp2_4_PCore tm.

  Lemma p_P_finish : forall R, R <> [] ->
    Reaches tm (mkCfgR (Some 15) [] (0 :: R)) (mkCfgR (Some 6) [] (3 :: 3 :: 0 :: 0 :: 0 :: 0 :: 3 :: R)) 10.
  Proof.
    intros R HR.
    replace 10 with (1 + 9) by lia.
    destruct R as [| r R']; [contradiction |].
    eapply reaches_trans.
    - apply steps_one. unfold step, mkCfgR; simpl; rewrite (p_P0 tm hc); reflexivity.
    - apply (o_O_finish tm (p_o tm hc) (3 :: r :: R') ltac:(discriminate)).
  Qed.

  (* One 1-after-3 cycle: G> 3^m (0 :: 3 :: 1 :: R) -> G> 3^m' (0 :: 3 :: R) with fPlus f_omega2 5 (m - 1) < m' *)
  Lemma p_five_step : forall m R, 3 <= m ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: 3 :: 1 :: R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: 3 :: R))) t /\
                 fPlus f_omega2 5 (m - 1) < m' /\ 3 <= m'.
  Proof.
    intros m R Hm.
    destruct (f4_rule_G3_rep tm (ijk_core tm (l_ijk tm (mn_l tm (o_mn tm (p_o tm hc))))) m (0 :: 3 :: 1 :: R) ltac:(lia))
      as [a [b [t1 [H1 [Ha [Hge1 _]]]]]].
    set (L0 := rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))).
    assert (H2 : Reaches tm (F4cfg (m - 1) a b (0 :: 3 :: 1 :: R))
                            (mkCfgR (Some 8) (1 :: L0) (3 :: 1 :: R)) 1).
    { unfold F4cfg, L0. apply steps_one. unfold step, mkCfgR; simpl; rewrite (ijk_F0 tm (l_ijk tm (mn_l tm (o_mn tm (p_o tm hc))))); reflexivity. }
    assert (H3 : Reaches tm (mkCfgR (Some 8) (1 :: L0) (3 :: 1 :: R))
                            (mkCfgR (Some 12) (3 :: 1 :: L0) (1 :: R)) 1).
    { apply steps_one. unfold step, mkCfgR; simpl; rewrite (mn_I3 tm (o_mn tm (p_o tm hc))); reflexivity. }
    assert (H4 : Reaches tm (mkCfgR (Some 12) (3 :: 1 :: L0) (1 :: R))
                            (mkCfgR (Some 15) (1 :: L0) (3 :: 2 :: R)) 1).
    { apply steps_one. unfold step, mkCfgR; simpl; rewrite (p_M1 tm hc); reflexivity. }
    assert (Hfa : Forall nz (1 :: L0)).
    { constructor; [left; reflexivity |].
      unfold L0. apply forall_rep; [right; left; reflexivity |].
      apply forall_rep; [left; reflexivity |].
      apply forall_rep; [right; right; reflexivity | constructor]. }
    pose proof (sweep_left_nz tm 15 2 (1 :: L0) 3 (2 :: R)
                  (p_P1 tm hc) (p_P2 tm hc) (p_P3 tm hc) (or_intror (or_intror eq_refl)) Hfa ltac:(discriminate)) as H5.
    pose proof (p_P_finish (rep (S (length (1 :: L0))) 2 (2 :: R)) ltac:(discriminate)) as H6.
    destruct (ijk_zero_step tm (l_ijk tm (mn_l tm (o_mn tm (p_o tm hc)))) 2 (0 :: 0 :: 3 :: rep (S (length (1 :: L0))) 2 (2 :: R)) ltac:(lia) ltac:(discriminate))
      as [m0 [t7 [H7 [_ [Hge7 _]]]]].
    destruct (ijk_zero_step tm (l_ijk tm (mn_l tm (o_mn tm (p_o tm hc)))) m0 (0 :: 3 :: rep (S (length (1 :: L0))) 2 (2 :: R)) ltac:(lia) ltac:(discriminate))
      as [m0' [t8 [H8 [_ [Hge8 _]]]]].
    destruct (ijk_zero_step tm (l_ijk tm (mn_l tm (o_mn tm (p_o tm hc)))) m0' (3 :: rep (S (length (1 :: L0))) 2 (2 :: R)) ltac:(lia) ltac:(discriminate))
      as [m1 [t9 [H9 [_ [Hge9 _]]]]].
    destruct (o_four_rep tm (p_o tm hc) (S (S (length (1 :: L0)))) m1 R Hge9)
      as [m2 [t10 [H10 [Hm2 Hge10]]]].
    exists m2, (t1 + 1 + 1 + 1 + S (length (1 :: L0)) + 10 + t7 + t8 + t9 + t10).
    split.
    - eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] |].
      rewrite <- rep_r in H10. exact H10.
    - split; [| exact Hge10].
      assert (Hlen : m - 1 + (m - 1) <= S (S (length (1 :: L0)))).
      { specialize (Hge1 ltac:(lia)).
        pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)) as Hgt.
        pose proof (fgh_ge_self _ f_omega2_props (m - 1)) as Hself.
        simpl length. unfold L0. rewrite !length_rep, length_nil. lia. }
      assert (HfP : FGHProps (fPlus f_omega2 4)) by (apply fPlus_props, f_omega2_props).
      assert (Hcmp : iter (fPlus f_omega2 4) (m - 1) (m - 1) <= iter (fPlus f_omega2 4) (S (S (length (1 :: L0)))) (m1 - 1)).
      { eapply Nat.le_trans; [| apply iter_mono_steps; [apply fgh_ge_self, HfP | exact Hlen]].
        rewrite iter_add.
        apply iter_mono_arg; [apply fgh_mono, HfP |].
        pose proof (iter_ge_add_pos _ (fgh_gt_pos _ HfP) (m - 1) (m1 - 1) ltac:(lia)). lia. }
      assert (Heq : forall n, fPlus f_omega2 5 n = iter (fPlus f_omega2 4) n n) by reflexivity.
      rewrite Heq. lia.
  Qed.

  (* Iterated 5-cycles: G> 3^m (0 :: 3 :: rep n 1 R) -> G> 3^m' (0 :: 3 :: R) *)
  Lemma p_five_rep : forall n m R, 3 <= m ->
    exists m' t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 (0 :: 3 :: rep n 1 R)))
                            (mkCfgR (Some 6) [] (rep m' 3 (0 :: 3 :: R))) t /\
                 iter (fPlus f_omega2 5) n (m - 1) <= m' - 1 /\ 3 <= m'.
  Proof.
    induction n as [| n' IH]; intros m R Hm.
    - exists m, 0. split; [apply reaches_zero | simpl; lia].
    - destruct (p_five_step m (rep n' 1 R) Hm) as [m1 [t1 [H1 [Hm1 Hge1]]]].
      destruct (IH m1 R Hge1) as [m2 [t2 [H2 [Hm2 Hge2]]]].
      exists m2, (t1 + t2).
      split; [eapply reaches_trans; [exact H1 | exact H2] |].
      split; [| exact Hge2].
      replace (iter (fPlus f_omega2 5) (S n') (m - 1))
        with (iter (fPlus f_omega2 5) n' (fPlus f_omega2 5 (m - 1)))
        by (replace (S n') with (n' + 1) by lia; rewrite iter_add; reflexivity).
      eapply Nat.le_trans; [| exact Hm2].
      apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props | lia].
  Qed.

End P_Lemmas.
