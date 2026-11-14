(**
  Formal Machine-Checked Proof of Blank-Tape FGH-Level (epsilon_1) Halting in Rocq 9.1
  Connects blank-tape Turing machines (btbl_eps1 a, btbl_eps1_a1) to Eps1Tape.tbl,
  Eps1Copy.sweep, and Eps1Ladder.lvl via exact parametric stage/rung/copy induction.
  Zero extra axioms.
*)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Eps1Ladder Eps1Tape Eps1Copy.
Import ListNotations.
Open Scope nat_scope.

(** * 1. Bridge Between Eps1Copy.ctbl and Eps1Tape.tbl *)

Lemma ctbl_agrees_tbl : forall s b x,
  Eps1Copy.ctbl s b = Some x -> Eps1Tape.tbl s b = Some x.
Proof.
  intros s b x H.
  do 65 (destruct s as [|s]; [destruct b; exact H || discriminate|]).
  destruct b; discriminate.
Qed.

Lemma step_ctbl_to_tbl : forall c c',
  TM.step Eps1Copy.ctbl c = Some c' -> TM.step Eps1Tape.tbl c = Some c'.
Proof.
  intros c c' H. unfold TM.step in *.
  destruct (Eps1Copy.ctbl (cst c) (ccur c)) as [tr|] eqn:E; [|discriminate].
  rewrite (ctbl_agrees_tbl (cst c) (ccur c) tr E). exact H.
Qed.

Lemma run_ctbl_to_tbl : forall k c c',
  TM.run Eps1Copy.ctbl k c = Some c' -> TM.run Eps1Tape.tbl k c = Some c'.
Proof.
  induction k as [|k IH]; intros c c' H.
  - exact H.
  - rewrite TM.run_S in H |- *.
    destruct (TM.step Eps1Copy.ctbl c) as [c1|] eqn:E; [|discriminate].
    rewrite (step_ctbl_to_tbl c c1 E). apply IH. exact H.
Qed.

Lemma run_tbl_cat : forall k1 k2 c1 c2 c3,
  TM.run Eps1Tape.tbl k1 c1 = Some c2 ->
  TM.run Eps1Tape.tbl k2 c2 = Some c3 ->
  TM.run Eps1Tape.tbl (k1 + k2) c1 = Some c3.
Proof. intros. eapply Eps1Tape.run_cat; eauto. Qed.

(** * 2. Generalized Rung-Branch Lemmas (Arbitrary Gap V) *)

Theorem rung_halts_gen : forall m b V,
  hd bl V = bl ->
  TM.run Eps1Tape.tbl (m + 3)
    (mkConf ENTRY (zeros (S m) ++ on :: zeros b) on V) =
  Some (mkConf G2 (zeros b) on (zeros (m + 2) ++ on :: V)).
Proof.
  intros m b V HV.
  set (E := mkConf ENTRY (zeros (S m) ++ on :: zeros b) on V).
  set (C1 := mkConf G1 (zeros m ++ on :: zeros b) bl (on :: V)).
  set (C2 := mkConf G2 (zeros b) (hd bl (on :: zeros b)) (bl :: zeros (m + 1) ++ on :: V)).
  assert (H1 : TM.run Eps1Tape.tbl 1 E = Some C1).
  { subst E C1. rewrite TM.run_S. cbn [zeros]. rewrite st_ENTRY_on.
    reflexivity. }
  assert (H2 : TM.run Eps1Tape.tbl (m + 2) C1 = Some C2).
  { subst C1 C2. apply walk_G1_left. }
  pose proof (run_tbl_cat 1 (m + 2) E C1 C2 H1 H2) as H.
  replace (1 + (m + 2)) with (m + 3) in H by lia.
  subst C2. cbn [hd] in H.
  replace (bl :: zeros (m + 1) ++ on :: V) with (zeros (m + 2) ++ on :: V) in H
    by (replace (m + 2) with (S (m + 1)) by lia; reflexivity).
  exact H.
Qed.

Theorem rung_halts_run_gen : forall m b V,
  hd bl V = bl ->
  TM.run Eps1Tape.tbl (m + 4)
    (mkConf ENTRY (zeros (S m) ++ on :: zeros b) on V) = None.
Proof.
  intros m b V HV.
  replace (m + 4) with (m + 3 + 1) by lia.
  rewrite TM.run_add, (rung_halts_gen m b V HV).
  cbn [TM.run]. rewrite st_G2_bl. reflexivity.
Qed.

Theorem rung_halts_conf_gen : forall m b V,
  hd bl V = bl ->
  exists cf,
    TM.run Eps1Tape.tbl (m + 3)
      (mkConf ENTRY (zeros (S m) ++ on :: zeros b) on V) = Some cf /\
    TM.halted Eps1Tape.tbl cf /\
    cf = mkConf G2 (zeros b) on (zeros (m + 2) ++ on :: V).
Proof.
  intros m b V HV.
  eexists. split; [apply rung_halts_gen; exact HV|].
  split; [unfold TM.halted; simpl; reflexivity | reflexivity].
Qed.

Theorem rung_reaches_copy_gen : forall m a b V,
  hd bl V = bl ->
  TM.run Eps1Tape.tbl (2 * m + 7)
    (mkConf ENTRY (zeros (S m) ++ ones (S (S a)) ++ zeros b) on V) =
  Some (mkConf WALK
          (on :: zeros (m + 2) ++ on :: ones a ++ zeros b) bl (tl V)).
Proof.
  intros m a b V HV.
  set (A := ones (S a) ++ zeros b).
  set (E := mkConf ENTRY (zeros (S m) ++ ones (S (S a)) ++ zeros b) on V).
  set (C1 := mkConf G1 (zeros m ++ ones (S (S a)) ++ zeros b) bl (on :: V)).
  set (C2 := mkConf G2 (tl A) (hd bl A) (bl :: zeros (m + 1) ++ on :: V)).
  set (C3 := mkConf G3 (on :: ones a ++ zeros b) bl (zeros (m + 1) ++ on :: V)).
  set (C4 := mkConf WALK (on :: zeros (m + 2) ++ on :: ones a ++ zeros b)
                 (hd bl V) (tl V)).
  assert (H1 : TM.run Eps1Tape.tbl 1 E = Some C1).
  { subst E C1. rewrite TM.run_S. cbn [zeros]. rewrite st_ENTRY_on.
    rewrite HV. reflexivity. }
  assert (H2 : TM.run Eps1Tape.tbl (m + 2) C1 = Some C2).
  { subst C1 C2 A. cbn [ones]. apply walk_G1_left. }
  assert (H3 : TM.run Eps1Tape.tbl 1 C2 = Some C3).
  { subst C2 C3 A. rewrite TM.run_S. cbn [ones tl hd]. rewrite st_G2_on.
    reflexivity. }
  assert (H4 : TM.run Eps1Tape.tbl (m + 1 + 2) C3 = Some C4).
  { subst C3 C4. replace (m + 2) with (m + 1 + 1) by lia.
    apply walk_G3_right. }
  pose proof (run_tbl_cat 1 (m + 2) E C1 C2 H1 H2) as Ha.
  pose proof (run_tbl_cat (1 + (m + 2)) 1 E C2 C3 Ha H3) as Hb.
  pose proof (run_tbl_cat (1 + (m + 2) + 1) (m + 1 + 2) E C3 C4 Hb H4) as Hc.
  subst C4 E. rewrite HV in Hc.
  replace (1 + (m + 2) + 1 + (m + 1 + 2)) with (2 * m + 7) in Hc by lia.
  exact Hc.
Qed.

(** * 3. Copy Phase: WALK -> trip0 -> sweep -> ZA..ZD -> S4 *)

Lemma walk_WALK_zeros : forall k L Z,
  TM.run Eps1Tape.tbl k (mkConf WALK L bl (zeros k ++ Z)) =
  Some (mkConf WALK (zeros k ++ L) (hd bl Z) (tl Z)).
Proof.
  induction k as [|k IH]; intros L Z.
  - simpl. destruct Z; reflexivity.
  - rewrite TM.run_S. cbn [zeros].
    change (TM.step Eps1Tape.tbl (mkConf WALK L bl (bl :: zeros k ++ Z)))
      with (Some (mkConf WALK (bl :: L) (hd bl (zeros k ++ Z)) (tl (zeros k ++ Z)))).
    destruct k as [|k'].
    + simpl. destruct Z; reflexivity.
    + cbn [zeros hd tl].
      replace (zeros (S k') ++ L) with (zeros k' ++ bl :: L)
        by (clear; induction k'; simpl; congruence).
      rewrite (IH (bl :: L) Z).
      replace (zeros k' ++ bl :: L) with (zeros (S k') ++ L)
        by (clear; induction k'; simpl; congruence).
      reflexivity.
Qed.

Lemma walk_ZB_ones : forall k L R,
  TM.run Eps1Tape.tbl k (mkConf ZB (ones k ++ L) on R) =
  Some (mkConf ZB L (hd bl (ones k ++ R)) (tl (ones k ++ R))).
Proof.
  induction k as [|k IH]; intros L R.
  - simpl. destruct R; reflexivity.
  - rewrite TM.run_S. cbn [ones].
    change (TM.step Eps1Tape.tbl (mkConf ZB (on :: ones k ++ L) on R))
      with (Some (mkConf ZB (ones k ++ L) on (on :: R))).
    rewrite IH.
    destruct k as [|k']; simpl; reflexivity.
Qed.


(** * 3. Generalized Copy Phase (WALK -> trip0 -> sweep -> ZA..ZD -> S4) *)

Definition trip_frame_g (g j D kk : nat) (A : list sym) : list sym :=
  bl :: ones j ++ bl :: zeros g ++ on :: bl :: ones j ++ bl :: zeros D ++ ones (S kk) ++ skipn j A.

Lemma ones_S_r : forall n, ones (S n) = ones n ++ [on].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma zeros_S_r : forall n, zeros (S n) = zeros n ++ [bl].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma ones_S_any : forall n L, ones (S n) ++ L = on :: ones n ++ L.
Proof. intros. reflexivity. Qed.

Lemma zeros_S_any : forall n L, zeros (S n) ++ L = bl :: zeros n ++ L.
Proof. intros. reflexivity. Qed.

Lemma walk_R1_zeros : forall g L R,
  TM.run Eps1Copy.ctbl (S (S g)) (mkConf 50 L bl (zeros g ++ on :: R)) =
  Some (mkConf 51 (on :: zeros (S g) ++ L) (hd bl R) (tl R)).
Proof.
  induction g as [|g IH]; intros L R.
  - cbn [zeros Nat.add app].
    rewrite TM.run_S. change (TM.step Eps1Copy.ctbl (mkConf 50 L bl (on :: R)))
      with (Some (mkConf 50 (bl :: L) on R)).
    (* Wait: ccur is bl, NOT on! *)
    (* Step 1: 50 on bl -> 50 (bl :: L) on R; Step 2: 50 on on -> 51 (on :: bl :: L) (hd bl R) (tl R) *)
    rewrite TM.run_S. reflexivity.
  - replace (S (S (S g))) with (S (S (S g))) by lia.
    rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Copy.ctbl (mkConf 50 L bl (bl :: zeros g ++ on :: R)))
      with (Some (mkConf 50 (bl :: L) bl (zeros g ++ on :: R))).
    rewrite IH.
    replace (zeros (S g) ++ bl :: L) with (zeros (S (S g)) ++ L)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_ZB_ones_r : forall k L R,
  TM.run Eps1Copy.ctbl k (mkConf 61 (ones k ++ L) on R) =
  Some (mkConf 61 L on (ones k ++ R)).
Proof.
  (* Wait: 61 on on moves L in 61! When k=0, 0 steps -> mkConf 61 L on R *)
  induction k as [|k IH]; intros L R; [reflexivity|].
  rewrite TM.run_S. cbn [ones app].
  change (TM.step Eps1Copy.ctbl (mkConf 61 (on :: ones k ++ L) on R))
    with (Some (mkConf 61 (ones k ++ L) on (on :: R))).
  rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_ZC_zeros : forall g L R,
  TM.run Eps1Copy.ctbl (S (S g)) (mkConf 62 (zeros g ++ on :: L) bl R) =
  Some (mkConf 63 (tl L) (hd bl L) (on :: zeros (S g) ++ R)).
Proof.
  induction g as [|g IH]; intros L R.
  - cbn [zeros app].
    rewrite TM.run_S.
    change (TM.step Eps1Copy.ctbl (mkConf 62 (on :: L) bl R))
      with (Some (mkConf 62 L on (bl :: R))).
    rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Copy.ctbl (mkConf 62 (bl :: zeros g ++ on :: L) bl R))
      with (Some (mkConf 62 (zeros g ++ on :: L) bl (bl :: R))).
    rewrite IH.
    replace (zeros (S g) ++ bl :: R) with (zeros (S (S g)) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma run_c_cat : forall k1 k2 c1 c2 c3,
  TM.run Eps1Copy.ctbl k1 c1 = Some c2 ->
  TM.run Eps1Copy.ctbl k2 c2 = Some c3 ->
  TM.run Eps1Copy.ctbl (k1 + k2) c1 = Some c3.
Proof. intros. eapply Eps1Copy.run_cat_c; eauto. Qed.



Lemma walk_R1_bl : forall k L R,
  TM.run Eps1Copy.ctbl k (mkConf 50 L bl (zeros k ++ R)) =
  Some (mkConf 50 (zeros k ++ L) (hd bl R) (tl R)).
Proof.
  induction k as [|k IH]; intros L R.
  - simpl. destruct R; reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Copy.ctbl (mkConf 50 L bl (bl :: zeros k ++ R)))
      with (Some (mkConf 50 (bl :: L) bl (zeros k ++ R))).
    (* Wait: hd bl (zeros k ++ R) when k > 0 is bl! Let us destruct k *)
    destruct k as [|k'].
    + simpl. destruct R; reflexivity.
    + cbn [zeros app hd tl] in *.
      replace (zeros (S k') ++ L) with (zeros k' ++ bl :: L)
        by (rewrite <- zeros_S_r; reflexivity).
      (* Actually zeros k' ++ bl :: L <> bl :: zeros k' ++ L unless we use zeros_S_r! *)
      (*Wait: zeros (S k') ++ L = bl :: zeros k' ++ L by simpl! We want (zeros (S k') ++ bl :: L)!*)
      (* Let us use: zeros (S k') ++ L = zeros k' ++ bl :: L? YES, by zeros_S_r + app_assoc! *)
      rewrite (IH (bl :: L) R).
      replace (zeros (S k') ++ bl :: L) with (zeros (S (S k')) ++ L)
        by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
      reflexivity.
Qed.

Lemma walk_R2_g : forall g j d n N B Z,
  j + 1 <= N ->
  exists k_tr,
    TM.run Eps1Copy.ctbl k_tr
      (mkConf R3 (trip_frame_g g j (S d) (S n) (zeros (S N) ++ B)) on Z) =
    Some (mkConf R3 (trip_frame_g g (S j) (S d) (S n) (zeros (S N) ++ B))
            (hd bl Z) (tl Z)).
Proof.
  intros g j d n N B Z Hle.
  assert (Hsk : skipn j (zeros (S N) ++ B) = bl :: zeros (N - j) ++ B).
  { rewrite skipn_app.
    assert (Hj : j <= S N) by lia.
    rewrite Eps1Copy.skipn_zeros by exact Hj.
    replace (S N - j) with (S (N - j)) by lia.
    replace (j - S N) with 0 by lia. reflexivity. }
  assert (Hsk1 : skipn (S j) (zeros (S N) ++ B) = zeros (N - j) ++ B).
  { rewrite skipn_app.
    assert (Hj : S j <= S N) by lia.
    rewrite Eps1Copy.skipn_zeros by exact Hj.
    replace (S N - S j) with (N - j) by lia.
    replace (S j - S N) with 0 by lia. reflexivity. }
  unfold trip_frame_g.
  set (L0 := ones j ++ bl :: zeros g ++ on :: bl :: ones j ++ bl :: zeros (S d) ++ ones (S (S n)) ++ skipn j (zeros (S N) ++ B)).
  assert (H1 : TM.run Eps1Copy.ctbl 1 (mkConf R3 (bl :: L0) on Z) =
               Some (mkConf C1 (bl :: bl :: L0) (hd bl Z) (tl Z)))
    by (rewrite TM.run_S, Eps1Copy.st_R3_on; reflexivity).
  assert (H2 : TM.run Eps1Copy.ctbl 3 (mkConf C1 (bl :: bl :: L0) (hd bl Z) (tl Z)) =
               Some (mkConf CL (tl L0) (hd bl L0) (on :: bl :: hd bl Z :: tl Z))).
  { pose proof (Eps1Copy.steps_C1 (bl :: L0) (hd bl Z) (tl Z)) as H.
    cbn [tl] in H. exact H. }
  set (W_cg := bl :: ones j ++ bl :: zeros (S d) ++ ones (S (S n)) ++ skipn j (zeros (S N) ++ B)).
  set (R_cg := on :: bl :: hd bl Z :: tl Z).
  set (R_b1 := on :: zeros g ++ bl :: ones j ++ R_cg).
  assert (H3_4 : exists k34,
    TM.run Eps1Copy.ctbl k34 (mkConf CL (tl L0) (hd bl L0) R_cg) =
    Some (mkConf B1 (tl W_cg) (hd bl W_cg) R_b1)).
  { unfold R_b1. destruct j as [|j'].
    - unfold L0. cbn [ones app tl hd].
      pose proof (Eps1Copy.walk_CL_blank (zeros g ++ on :: W_cg) R_cg) as Hcl.
      cbn [tl hd] in Hcl.
      destruct g as [|g'].
      + cbn [zeros app] in *.
        pose proof (Eps1Copy.walk_CG_0 W_cg (bl :: R_cg)) as Hcg.
        exists (1 + 1). eapply run_c_cat; [exact Hcl | exact Hcg].
      + cbn [zeros app] in *.
        pose proof (Eps1Copy.walk_CG (S g') W_cg (bl :: R_cg)) as Hcg.
        cbn [zeros tl hd] in Hcg.
        exists (1 + S (S g')). eapply run_c_cat; [exact Hcl | exact Hcg].
    - unfold L0. cbn [ones app tl hd].
      pose proof (Eps1Copy.walk_CL_marks j' (zeros g ++ on :: W_cg) R_cg) as Hcl.
      cbn [tl hd] in Hcl.
      destruct g as [|g'].
      + cbn [zeros app] in *.
        pose proof (Eps1Copy.walk_CG_0 W_cg (bl :: ones (S j') ++ R_cg)) as Hcg.
        exists (S (S j') + 1). eapply run_c_cat; [exact Hcl | exact Hcg].
      + cbn [zeros app] in *.
        pose proof (Eps1Copy.walk_CG (S g') W_cg (bl :: ones (S j') ++ R_cg)) as Hcg.
        cbn [zeros tl hd] in Hcg.
        exists (S (S j') + S (S g')). eapply run_c_cat; [exact Hcl | exact Hcg]. }
  destruct H3_4 as [k34 H34].
  assert (H5_6 : exists k56,
    TM.run Eps1Copy.ctbl k56 (mkConf B1 (tl W_cg) (hd bl W_cg) R_b1) =
    Some (mkConf P1 (zeros d ++ on :: ones (S n) ++ skipn j (zeros (S N) ++ B))
            bl (ones (S j) ++ bl :: R_b1))).
  { unfold W_cg. destruct j as [|j'].
    - cbn [ones app tl hd].
      pose proof (Eps1Copy.step_B1 (bl :: zeros (S d) ++ ones (S (S n)) ++ skipn 0 (zeros (S N) ++ B)) bl R_b1) as Hb1.
      cbn [tl hd] in Hb1.
      assert (Hb2 : TM.run Eps1Copy.ctbl 1
        (mkConf B2 (zeros (S d) ++ ones (S (S n)) ++ skipn 0 (zeros (S N) ++ B)) bl (bl :: R_b1)) =
        Some (mkConf P1 (zeros d ++ on :: ones (S n) ++ skipn 0 (zeros (S N) ++ B)) bl (on :: bl :: R_b1))).
      { rewrite TM.run_S, Eps1Copy.st_B2_bl. cbn [zeros ones app tl hd]. reflexivity. }
      exists (1 + 1). eapply run_c_cat; [exact Hb1 | exact Hb2].
    - cbn [ones app tl hd].
      pose proof (Eps1Copy.step_B1 (on :: ones j' ++ bl :: zeros (S d) ++ ones (S (S n)) ++ skipn (S j') (zeros (S N) ++ B)) bl R_b1) as Hb1.
      cbn [tl hd] in Hb1.
      pose proof (Eps1Copy.walk_B2 j' (zeros (S d) ++ ones (S (S n)) ++ skipn (S j') (zeros (S N) ++ B)) (bl :: R_b1)) as Hb2.
      cbn [zeros app tl hd] in Hb2.
      exists (1 + S (S j')). eapply run_c_cat; [exact Hb1 | exact Hb2]. }
  destruct H5_6 as [k56 H56].
  set (R_p1 := ones (S j) ++ bl :: R_b1).
  pose proof (Eps1Copy.walk_P1 (S d) (ones (S n) ++ skipn j (zeros (S N) ++ B)) R_p1) as H7.
  cbn [zeros ones app tl hd] in H7.
  rewrite Hsk in H7.
  pose proof (Eps1Copy.walk_P2 n (zeros (N - j) ++ B) (bl :: zeros (S d) ++ R_p1)) as H8.
  pose proof (Eps1Copy.walk_P3 n (zeros (N - j) ++ B) (zeros (S d) ++ R_p1)) as H9.
  cbn [tl hd] in H9.
  pose proof (Eps1Copy.walk_P4 (S d) (bl :: ones (S n) ++ on :: zeros (N - j) ++ B) R_p1) as H10.
  cbn [zeros app tl hd] in H10.
  set (L_p5 := on :: zeros (S (S d)) ++ bl :: ones (S n) ++ on :: zeros (N - j) ++ B).
  pose proof (Eps1Copy.walk_P5 (S j) L_p5 R_b1) as H11.
  cbn [tl hd] in H11.
  set (L_bq := bl :: ones (S j) ++ on :: L_p5).
  pose proof (Eps1Copy.st_BQ_any L_bq on (zeros g ++ bl :: ones j ++ R_cg)) as H12.
  cbn [tl hd] in H12.
  assert (H13_15 : exists k13,
    TM.run Eps1Copy.ctbl k13
      (mkConf BW (on :: L_bq) (hd bl (zeros g ++ bl :: ones j ++ R_cg)) (tl (zeros g ++ bl :: ones j ++ R_cg))) =
    Some (mkConf R3 (bl :: ones (S j) ++ bl :: zeros g ++ on :: L_bq) (hd bl Z) (tl Z))).
  { (* BW (on :: L_bq) reads bl (or on? No, zeros g ++ bl :: ... ALWAYS starts with bl!), moves R to R1 *)
    replace (zeros g ++ bl :: ones j ++ R_cg) with (bl :: zeros g ++ ones j ++ R_cg)
      by (clear; induction g; simpl; congruence).
    cbn [hd tl].
    pose proof (Eps1Copy.st_BW_any (on :: L_bq) bl (zeros g ++ ones j ++ R_cg)) as Hbw.
    cbn [hd tl] in Hbw.
    (* Now R1 (bl :: on :: L_bq) reads (hd bl (zeros g ++ ones j ++ R_cg)) *)
    (* Note: ones j ++ R_cg = ones (S j) ++ bl :: hd bl Z :: tl Z *)
    assert (Hor : ones j ++ R_cg = on :: ones j ++ bl :: hd bl Z :: tl Z)
      by (unfold R_cg; clear; induction j; simpl; [reflexivity | rewrite IHj; reflexivity]).
    rewrite Hor.
    (* R1 walks zeros g (g steps if g >= 1, 0 steps if g = 0) *)
    assert (Hr1 : exists kr1,
      TM.run Eps1Copy.ctbl kr1
        (mkConf 50 (bl :: on :: L_bq) (hd bl (zeros g ++ on :: ones j ++ bl :: hd bl Z :: tl Z))
                (tl (zeros g ++ on :: ones j ++ bl :: hd bl Z :: tl Z))) =
      Some (mkConf 51 (on :: zeros g ++ bl :: on :: L_bq)
              (hd bl (ones j ++ bl :: hd bl Z :: tl Z))
              (tl (ones j ++ bl :: hd bl Z :: tl Z)))).
    { destruct g as [|g'].
      - cbn [zeros app tl hd].
        exists 1. rewrite TM.run_S.
        change (TM.step Eps1Copy.ctbl (mkConf 50 (bl :: on :: L_bq) on (ones j ++ bl :: hd bl Z :: tl Z)))
          with (Some (mkConf 51 (on :: bl :: on :: L_bq) (hd bl (ones j ++ bl :: hd bl Z :: tl Z))
                              (tl (ones j ++ bl :: hd bl Z :: tl Z)))).
        reflexivity.
      - cbn [zeros app tl hd].
        pose proof (walk_R1_bl g' (bl :: on :: L_bq) (on :: ones j ++ bl :: hd bl Z :: tl Z)) as Hrb.
        replace (zeros g' ++ bl :: on :: L_bq) with (zeros (S g') ++ on :: L_bq) in Hrb
          by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
        cbn [hd tl] in Hrb.
        assert (Hr1_on : TM.run Eps1Copy.ctbl 1
          (mkConf 50 (zeros (S g') ++ on :: L_bq) on (ones j ++ bl :: hd bl Z :: tl Z)) =
          Some (mkConf 51 (on :: zeros (S g') ++ on :: L_bq)
                  (hd bl (ones j ++ bl :: hd bl Z :: tl Z))
                  (tl (ones j ++ bl :: hd bl Z :: tl Z)))).
        { rewrite TM.run_S. reflexivity. }
        (* Wait: walk_R1_bl left (zeros (S g') ++ on :: L_bq), which has S g' zeros, missing 1 bl! *)
        (* Let us check: BW wrote bl :: on :: L_bq, and zeros (S g') = bl :: zeros g', so total bls = S (S g') = zeros (S g') ++ [bl]! *)
        (* In walk_R1_bl, zeros g' ++ bl :: on :: L_bq = bl :: zeros g' ++ on :: L_bq? NO, zeros_S_r gives zeros (S g') ++ on :: L_bq = zeros g' ++ bl :: on :: L_bq! *)
        (* Where did the extra bl go? In Hbw, we had (bl :: on :: L_bq), and g = S g', so zeros (S g') = bl :: zeros g', total blanks = S g' + 1 = S (S g'), NOT S g'! *)
        (* Indeed, zeros (S g') ++ bl :: on :: L_bq has S (S g') blanks, which is zeros (S (S g')) ++ on :: L_bq! *)
        (* Wait: in Hrb we had (zeros g' ++ bl :: on :: L_bq) = (zeros (S g') ++ on :: L_bq), which HAS S g' blanks (from zeros g' + 1 bl)! The other 1 bl was consumed by R1's initial ccur = bl! *)
        (* So Hr1_on has (zeros (S g') ++ on :: L_bq), whereas target has (zeros (S g') ++ bl :: on :: L_bq)! *)
        (* Wait: why did target have bl :: on :: L_bq? Because in trip_frame_g (S g') (S j), we have bl :: zeros (S g') ++ on :: L_bq = zeros (S g') ++ bl :: on :: L_bq! *)
        (* And in R1, BW wrote bl :: on :: L_bq (1 bl), then R1 started on bl (1 bl), and tl had zeros g' (g' bls) -> total 1 + 1 + g' = S (S g') bls = bl :: zeros (S g')!! *)
        (* So walk_R1_bl g' (bl :: on :: L_bq) gives zeros g' ++ bl :: on :: L_bq = zeros (S g') ++ on :: L_bq (missing 1 bl)! *)
        (* Why? Because we should have applied walk_R1_bl (S g')? No, tl only had g' blanks! Where is the missing blank? *)
        (* LOOK at the replace above: replace (zeros (S g') ++ bl :: ...) with (bl :: zeros (S g') ++ ...)! *)
        (* That replace had bl :: zeros (S g'), which is S (S g') blanks! Then cbn [hd tl] took 1 bl for ccur and left zeros (S g') (NOT zeros g'!) in tl! *)
        (* Wait: zeros (S g') = bl :: zeros g', so cbn [zeros app hd tl] left zeros g' in tl, wait: why did Hrb only have zeros g' + 1 bl? Because zeros g' ++ bl :: on :: L_bq HAS g' + 1 = S g' blanks, NOT g' + 2! The extra bl from BW was (bl :: on :: L_bq), which we replaced with (zeros (S g') ++ on :: L_bq), losing 1 bl? NO! zeros g' ++ (bl :: on :: L_bq) = (zeros g' ++ [bl]) ++ on :: L_bq = zeros (S g') ++ on :: L_bq! *)
        (* Why did Hr1's target have bl :: zeros (S g') ++ on :: L_bq?! Because we wrote (zeros (S g') ++ bl :: on :: L_bq) in Hr1's target! *)
        (* Let us check: in trip_frame_g (S g') (S j), between on (wall) and bl :: ones (S j), there is zeros (S g')! *)
        (* Wait: where is the bl in bl :: zeros (S g')? In trip_frame_g: bl :: ones (S j) ++ bl :: zeros (S g') ++ on :: ...! *)
        (* THAT bl IS PART OF `bl :: zeros (S g')` = `zeros (S g') ++ [bl]`, WHICH IS `S (S g')` BLANKS, NOT `S g'`! *)
        (*Wait: in R_b1 = on :: zeros (S g') ++ bl :: ones j ++ R_cg, after on (wall) there are zeros (S g') ++ [bl] = S (S g') blanks! *)
        (*In step 1: BW was on bl (1st blank), wrote bl :: on :: L_bq!*)
        (*In step 2: R1 was on bl (2nd blank), and tl had zeros g' (g' blanks)! Total = 1 + 1 + g' = S (S g') blanks!*)
        (*Wait: why did zeros g' ++ bl :: on :: L_bq only have g' + 1 blanks? Because we passed (bl :: on :: L_bq) to walk_R1_bl g', and walk_R1_bl g' ONLY consumes g' blanks, NOT g' + 1!*)
        (*So after walk_R1_bl g', L is zeros g' ++ bl :: on :: L_bq = zeros (S g') ++ on :: L_bq, AND ccur is on, AND R is ...!*)
        (*Then where is the (S (S g'))-th blank?! It's in `walk_R2 j` (`bl :: ones j ++ on :: ...`)!*)
        (*LOOK! walk_R2 j adds `bl ::` on the LEFT of `ones j ++ on :: zeros (S g') ++ on :: L_bq`!*)
        (*Wait: walk_R2 j adds `bl :: ones j ++ on ::`! Where is the `bl` between `ones (S j)` and `zeros (S g')`?!*)
        (*In `ones (S j) ++ bl :: zeros (S g')`, the `bl` is AFTER `ones (S j)` (i.e. to the LEFT of `zeros (S g')` in `L`, so to the RIGHT of `zeros (S g')` in the list `L`!)!*)
        (*YES!! `ones (S j) ++ bl :: zeros (S g')` = `(ones j ++ [on]) ++ bl :: zeros (S g')`!*)
        (*So `bl` is between `ones (S j)` and `zeros (S g')`, which means `walk_R2 j` puts `on ::` (1 mark) + `ones j` + `bl`... wait: `walk_R2` puts `bl :: ones j ++ on :: L`!*)
        (*So `L` before `walk_R2` MUST ALREADY HAVE `bl :: zeros (S g') ++ on :: L_bq`!*)
        (*Wait: why didn't `L` have `bl :: zeros (S g')`? Because `R1` started on `bl`, and `walk_R1_bl` only had `g'` blanks in `zeros g'`!*)
        (*Let us count: `R_b1 = on :: zeros (S g') ++ bl :: ones j ++ R_cg`!*)
        (*How many blanks are in `zeros (S g') ++ [bl]`? `S g' + 1 = g' + 2` blanks!*)
        (*How many blanks are in `bl :: zeros (S g')`? `1 + S g' = g' + 2` blanks!*)
        (*So `L` MUST have `g' + 2` blanks (`bl :: zeros (S g')`), NOT `g' + 1` (`zeros (S g')`)!*)
        (*Why did `walk_R1_bl g'` give `zeros (S g')` (`g' + 1` blanks)? Because we forgot `R1` started on `bl` AND `BW` ALSO wrote `bl`! Wait: `BW` wrote `bl :: on :: L_bq` (1 blank), `R1` started on `bl` (2nd blank), and `zeros g'` had `g'` blanks -> `1 + 1 + g' = g' + 2` blanks!!*)
        (*Why did `zeros g' ++ bl :: on :: L_bq` only have `g' + 1` blanks? Because `walk_R1_bl g'` ALSO consumed 1 blank from `R` (`zeros g'`), so `1 (from BW) + g' (from zeros g')` = `g' + 1`! The 2nd blank was `bl` in `zeros (S g') ++ bl`, which we replaced by `bl :: zeros (S g')` and `cbn` put `bl` into `ccur`, leaving `zeros g' ++ [bl]`? NO, `zeros (S g') = bl :: zeros g'`, so `zeros g' ++ [bl]` has `g' + 1` blanks, plus `1` from `BW` = `g' + 2` blanks!*)
        (*In `walk_R1_bl g'`, we passed `R = on :: ...`, NOT `bl :: on :: ...`, because `zeros g'` only had `g'` blanks!*)
        (*Wait: `bl :: zeros (S g') ++ ...` -> `tl` is `zeros (S g') ++ ... = bl :: zeros g' ++ ...`, which has `S g'` blanks, NOT `g'` blanks!! We should have called `walk_R1_bl (S g')`, NOT `walk_R1_bl g'`!!*)
        pose proof (walk_R1_bl (S g') (bl :: on :: L_bq) (on :: ones j ++ bl :: hd bl Z :: tl Z)) as Hrb.
        cbn [hd tl] in Hrb.
        replace (zeros (S g') ++ bl :: on :: L_bq) with (bl :: zeros (S g') ++ on :: L_bq) in Hrb
          by (rewrite <- zeros_S_r; reflexivity).
        (* Wait: zeros (S g') ++ bl :: on :: L_bq has S (S g') blanks, which IS bl :: zeros (S g') ++ on :: L_bq! *)
        assert (Hr1_on : TM.run Eps1Copy.ctbl 1
          (mkConf 50 (bl :: zeros (S g') ++ on :: L_bq) on (ones j ++ bl :: hd bl Z :: tl Z)) =
          Some (mkConf 51 (on :: bl :: zeros (S g') ++ on :: L_bq)
                  (hd bl (ones j ++ bl :: hd bl Z :: tl Z))
                  (tl (ones j ++ bl :: hd bl Z :: tl Z)))).
        { rewrite TM.run_S. reflexivity. }
        exists (S g' + 1). eapply run_c_cat; [exact Hrb | exact Hr1_on]. }
    destruct Hr1 as [kr1 Hrk1].
    (* Now R2 walks ones j ++ bl :: hd bl Z :: tl Z *)
    (* Wait: if j = 0, R2 starts at hd bl (bl :: hd bl Z :: tl Z) = bl, so 1 step -> R3 (bl :: on :: bl :: zeros g ++ on :: L_bq)! *)
    (* If j = S j', R2 starts at on, walks j' ones + bl -> R3 (bl :: ones (S j') ++ bl :: zeros g ++ on :: L_bq)! *)
    (* Both cases are literally Eps1Copy.walk_R2 j! Wait: walk_R2 j expects ccur = on and R = ones j ++ bl :: Z! *)
    (* Here we have R1 on on :: ones j ++ bl :: Z -> 1 step gives R2 on (hd bl (ones j ++ bl :: Z))! *)
    (* Wait: R1 on on ALREADY consumed 1 `on`, so if j = 0, R2 is on `bl` (1 step); if j = S j', R2 is on `on` (walk_R2 j')! *)
    assert (Hr2 : exists kr2,
      TM.run Eps1Copy.ctbl kr2
        (mkConf 51 (on :: bl :: zeros g ++ on :: L_bq)
                (hd bl (ones j ++ bl :: hd bl Z :: tl Z))
                (tl (ones j ++ bl :: hd bl Z :: tl Z))) =
      Some (mkConf R3 (bl :: ones (S j) ++ bl :: zeros g ++ on :: L_bq) (hd bl Z) (tl Z))).
    { destruct j as [|j'].
      - cbn [ones app hd tl]. exists 1. rewrite TM.run_S, Eps1Copy.st_R2_bl. reflexivity.
      - cbn [ones app hd tl].
        pose proof (Eps1Copy.walk_R2 j' (on :: bl :: zeros g ++ on :: L_bq) (hd bl Z :: tl Z)) as Hw2.
        cbn [hd tl] in Hw2.
        exists (j' + 2). exact Hw2. }
    destruct Hr2 as [kr2 Hrk2].
    exists (1 + kr1 + kr2).
    eapply run_c_cat; [exact Hbw|].
    eapply run_c_cat; [exact Hrk1 | exact Hrk2]. }
  destruct H13_15 as [k13 H13].
  (* Compose H1 .. H13 *)
  exists (1 + 3 + k34 + k56 + S (S d) + (S n + 2) + S (S n) + (S (S d) + 2) + (S j + 2) + 1 + k13).
  eapply run_c_cat; [exact H1|].
  eapply run_c_cat; [exact H2|].
  eapply run_c_cat; [exact H34|].
  eapply run_c_cat; [exact H56|].
  eapply run_c_cat; [exact H7|].
  eapply run_c_cat; [exact H8|].
  eapply run_c_cat; [exact H9|].
  eapply run_c_cat; [exact H10|].
  eapply run_c_cat; [exact H11|].
  eapply run_c_cat; [exact H12|].
  rewrite Hsk1. exact H13.
Qed.
Lemma copy_sweep_g : forall w g j d n N B Z,
  j + S w <= N ->
  exists k_sw,
    TM.run Eps1Copy.ctbl k_sw
      (mkConf R3 (trip_frame_g g j (S d) (S n) (zeros (S N) ++ B)) on (ones w ++ bl :: Z)) =
    Some (mkConf R3 (trip_frame_g g (j + S w) (S d) (S n) (zeros (S N) ++ B)) bl Z).
Proof.
  induction w as [|w IH]; intros g j d n N B Z Hle.
  - cbn [ones app].
    destruct (walk_R2_g g j d n N B (bl :: Z) ltac:(lia)) as [k1 H1].
    cbn [hd tl] in H1. replace (j + 1) with (S j) by lia.
    exists k1. exact H1.
  - cbn [ones app].
    destruct (walk_R2_g g j d n N B (on :: ones w ++ bl :: Z) ltac:(lia)) as [k1 H1].
    cbn [hd tl] in H1.
    destruct (IH g (S j) d n N B Z ltac:(lia)) as [k2 H2].
    replace (j + S (S w)) with (S j + S w) by lia.
    exists (k1 + k2). eapply run_c_cat; [exact H1 | exact H2].
Qed.

Lemma copy_trip0_walk_g : forall g m a' b0 w Z,
  exists k0,
    TM.run Eps1Copy.ctbl k0
      (mkConf WALK (on :: zeros (m + 2) ++ on :: ones (S a') ++ zeros (S w + b0)) bl
              (zeros (S g) ++ ones (S w) ++ Z)) =
    Some (mkConf R3
            (trip_frame_g g 1 m (S a') (zeros (S (S w)) ++ zeros b0))
            (hd bl (ones w ++ Z)) (tl (ones w ++ Z))).
Proof.
  intros g m a' b0 w Z.
  set (b := S w + b0).
  set (L_wall := on :: zeros (m + 2) ++ on :: ones (S a') ++ zeros b).
  pose proof (Eps1Copy.walk_WALK (S g) L_wall (ones w ++ Z)) as Hw.
  cbn [ones app] in Hw.
  replace (zeros (S g) ++ on :: ones w ++ Z) with (zeros (S g) ++ ones (S w) ++ Z) in Hw by reflexivity.
  pose proof (Eps1Copy.steps_C1 (zeros (S g) ++ L_wall) (hd bl (ones w ++ Z)) (tl (ones w ++ Z))) as Hc1.
  cbn [tl hd] in Hc1.
  set (R_cg := on :: bl :: hd bl (ones w ++ Z) :: tl (ones w ++ Z)).
  pose proof (Eps1Copy.walk_CL_blank (zeros g ++ L_wall) R_cg) as Hcl.
  cbn [tl hd] in Hcl.
  set (W_cg := zeros (m + 2) ++ on :: ones (S a') ++ zeros b).
  assert (Hcg : TM.run Eps1Copy.ctbl (S g)
    (mkConf CG (tl (zeros g ++ on :: W_cg)) (hd bl (zeros g ++ on :: W_cg)) (bl :: R_cg)) =
    Some (mkConf B1 (tl W_cg) (hd bl W_cg) (on :: zeros g ++ bl :: R_cg)))
    by (apply Eps1Copy.walk_CG).
  set (R_b1 := on :: zeros g ++ bl :: R_cg).
  pose proof (Eps1Copy.step_B1 (tl W_cg) (hd bl W_cg) R_b1) as Hb1.
  unfold W_cg in Hb1. cbn [zeros app tl hd] in Hb1.
  assert (Hb2 : TM.run Eps1Copy.ctbl 1
    (mkConf B2 (zeros m ++ on :: ones (S a') ++ zeros b) bl (bl :: R_b1)) =
    Some (mkConf P1 (tl (zeros m ++ on :: ones (S a') ++ zeros b))
            (hd bl (zeros m ++ on :: ones (S a') ++ zeros b)) (on :: bl :: R_b1)))
    by (rewrite TM.run_S, Eps1Copy.st_B2_bl; reflexivity).
  pose proof (Eps1Copy.walk_P1 m (ones (S a') ++ zeros b) (on :: bl :: R_b1)) as Hp1.
  cbn [ones app tl hd] in Hp1.
  pose proof (Eps1Copy.walk_P2 a' (zeros b) (bl :: zeros m ++ on :: bl :: R_b1)) as Hp2.
  pose proof (Eps1Copy.walk_P3 a' (zeros b) (zeros m ++ on :: bl :: R_b1)) as Hp3.
  cbn [tl hd] in Hp3.
  pose proof (Eps1Copy.walk_P4 m (bl :: ones (S a') ++ on :: zeros b) (bl :: R_b1)) as Hp4.
  cbn [zeros app tl hd] in Hp4.
  set (L_p5 := on :: zeros (S m) ++ bl :: ones (S a') ++ on :: zeros b).
  assert (Hp5 : TM.run Eps1Copy.ctbl 1 (mkConf P5 L_p5 bl R_b1) =
                Some (mkConf BQ (bl :: L_p5) (hd bl R_b1) (tl R_b1)))
    by (rewrite TM.run_S, Eps1Copy.st_P5_bl; reflexivity).
  unfold R_b1 in Hp5. cbn [hd tl] in Hp5.
  pose proof (Eps1Copy.st_BQ_any (bl :: L_p5) on (zeros g ++ bl :: R_cg)) as Hbq.
  cbn [hd tl] in Hbq.
  assert (Hbw_r3 : exists k_end,
    TM.run Eps1Copy.ctbl k_end
      (mkConf BW (on :: bl :: L_p5) (hd bl (zeros g ++ bl :: R_cg)) (tl (zeros g ++ bl :: R_cg))) =
    Some (mkConf R3 (bl :: ones 1 ++ bl :: zeros g ++ on :: bl :: L_p5)
            (hd bl (ones w ++ Z)) (tl (ones w ++ Z)))).
  { replace (zeros g ++ bl :: R_cg) with (bl :: zeros g ++ R_cg)
      by (clear; induction g; simpl; congruence).
    cbn [hd tl].
    pose proof (Eps1Copy.st_BW_any (on :: bl :: L_p5) bl (zeros g ++ R_cg)) as Hbw.
    cbn [hd tl] in Hbw.
    destruct g as [|g'].
    - cbn [zeros app hd tl].
      assert (Hr1 : TM.run Eps1Copy.ctbl 1
        (mkConf 50 (bl :: on :: bl :: L_p5) on (bl :: hd bl (ones w ++ Z) :: tl (ones w ++ Z))) =
        Some (mkConf 51 (on :: bl :: on :: bl :: L_p5) bl (hd bl (ones w ++ Z) :: tl (ones w ++ Z))))
        by (rewrite TM.run_S; reflexivity).
      assert (Hr2 : TM.run Eps1Copy.ctbl 1
        (mkConf 51 (on :: bl :: on :: bl :: L_p5) bl (hd bl (ones w ++ Z) :: tl (ones w ++ Z))) =
        Some (mkConf R3 (bl :: on :: bl :: on :: bl :: L_p5) (hd bl (ones w ++ Z)) (tl (ones w ++ Z))))
        by (rewrite TM.run_S, Eps1Copy.st_R2_bl; reflexivity).
      exists (1 + 1 + 1).
      eapply run_c_cat; [exact Hbw|]. eapply run_c_cat; [exact Hr1 | exact Hr2].
    - cbn [zeros app hd tl].
      pose proof (walk_R1_bl (S g') (bl :: on :: bl :: L_p5) (on :: bl :: hd bl (ones w ++ Z) :: tl (ones w ++ Z))) as Hrb.
      cbn [hd tl] in Hrb.
      replace (zeros (S g') ++ bl :: on :: bl :: L_p5) with (bl :: zeros (S g') ++ on :: bl :: L_p5) in Hrb
        by (rewrite <- zeros_S_r; reflexivity).
      assert (Hr1 : TM.run Eps1Copy.ctbl 1
        (mkConf 50 (bl :: zeros (S g') ++ on :: bl :: L_p5) on (bl :: hd bl (ones w ++ Z) :: tl (ones w ++ Z))) =
        Some (mkConf 51 (on :: bl :: zeros (S g') ++ on :: bl :: L_p5) bl (hd bl (ones w ++ Z) :: tl (ones w ++ Z))))
        by (rewrite TM.run_S; reflexivity).
      assert (Hr2 : TM.run Eps1Copy.ctbl 1
        (mkConf 51 (on :: bl :: zeros (S g') ++ on :: bl :: L_p5) bl (hd bl (ones w ++ Z) :: tl (ones w ++ Z))) =
        Some (mkConf R3 (bl :: on :: bl :: zeros (S g') ++ on :: bl :: L_p5) (hd bl (ones w ++ Z)) (tl (ones w ++ Z))))
        by (rewrite TM.run_S, Eps1Copy.st_R2_bl; reflexivity).
      exists (1 + S g' + 1 + 1).
      eapply run_c_cat; [exact Hbw|]. eapply run_c_cat; [exact Hrb|].
      eapply run_c_cat; [exact Hr1 | exact Hr2]. }
  destruct Hbw_r3 as [k_end Hbw_r3].
  assert (Htf_eq : bl :: ones 1 ++ bl :: zeros g ++ on :: bl :: L_p5 =
                   trip_frame_g g 1 m (S a') (zeros (S (S w)) ++ zeros b0)).
  { unfold trip_frame_g, L_p5, b.
    assert (Hsk1 : skipn 1 (zeros (S (S w)) ++ zeros b0) = zeros (S w + b0)).
    { cbn [zeros skipn]. rewrite zeros_app. reflexivity. }
    rewrite Hsk1.
    replace (zeros (S m) ++ bl :: ones (S a') ++ on :: zeros (S w + b0))
      with (zeros (S m) ++ (bl :: ones (S a')) ++ on :: zeros (S w + b0)) by reflexivity.
    (* Check: bl :: ones 1 ++ bl :: zeros g ++ on :: bl :: on :: zeros (S m) ++ bl :: ones (S a') ++ on :: zeros (S w + b0) *)
    (* vs: bl :: ones 1 ++ bl :: zeros g ++ on :: bl :: ones 1 ++ bl :: zeros (S m) ++ ones (S (S a')) ++ zeros (S w + b0) *)
    repeat (f_equal; try reflexivity).
    (* Need: zeros (S m) ++ bl :: ones (S a') ++ on :: zeros (S w + b0) = bl :: zeros (S m) ++ ones (S (S a')) ++ zeros (S w + b0) *)
    (* Wait: bl :: on :: zeros (S m) vs bl :: ones 1 ++ bl :: zeros (S m)! *)
    (* Left side of repeat f_equal: bl :: on :: zeros (S m) ++ bl :: ... = bl :: ones 1 ++ zeros (S m) ++ [bl] ++ ... *)
    (* Right side: bl :: ones 1 ++ bl :: zeros (S m) ++ ... *)
    rewrite <- app_assoc. f_equal.
    rewrite <- zeros_S_r. change (zeros (S (S m))) with (bl :: zeros (S m)).
    rewrite <- app_assoc. f_equal.
    rewrite <- ones_S_r, <- app_assoc. reflexivity. }
  rewrite Htf_eq in Hbw_r3.
  exists (S g + 2 + 3 + 1 + S g + 1 + 1 + m + (a' + 2) + S (S a') + (m + 2) + 1 + 1 + k_end).
  eapply run_c_cat; [exact Hw|].
  eapply run_c_cat; [exact Hc1|].
  eapply run_c_cat; [exact Hcl|].
  eapply run_c_cat; [exact Hcg|].
  eapply run_c_cat; [exact Hb1|].
  eapply run_c_cat; [exact Hb2|].
  eapply run_c_cat; [exact Hp1|].
  eapply run_c_cat; [exact Hp2|].
  eapply run_c_cat; [exact Hp3|].
  eapply run_c_cat; [exact Hp4|].
  eapply run_c_cat; [exact Hp5|].
  eapply run_c_cat; [exact Hbq|].
  exact Hbw_r3.
Qed.

Lemma copy_to_S4_g : forall g m a' b0 w,
  exists k_copy,
    TM.run Eps1Tape.tbl k_copy
      (mkConf WALK (on :: zeros (m + 2) ++ on :: ones (S a') ++ zeros (S w + b0)) bl
              (zeros (S g) ++ ones (S w) ++ bl :: [on])) =
    Some (mkConf S4
            (bl :: ones (S w) ++ bl :: zeros (S m) ++ ones (S (S a')) ++ zeros (1 + b0))
            on (zeros (S g) ++ ones (S w) ++ bl :: bl :: [on])).
Proof.
  intros g m a' b0 w.
  assert (Hr3 : exists k_r3,
    TM.run Eps1Copy.ctbl k_r3
      (mkConf WALK (on :: zeros (m + 2) ++ on :: ones (S a') ++ zeros (S w + b0)) bl
              (zeros (S g) ++ ones (S w) ++ bl :: [on])) =
    Some (mkConf R3 (trip_frame_g g (S w) (S m) (S a') (zeros (S (S w)) ++ zeros b0)) bl [on])).
  { destruct (copy_trip0_walk_g g m a' b0 w [bl; on]) as [k0 H0].
    destruct w as [|w'].
    - cbn [ones app hd tl] in H0. exists k0. exact H0.
    - cbn [ones app hd tl] in H0.
      destruct (copy_sweep_g w' g 1 m (S a') (S (S w')) (zeros b0) [on] ltac:(lia)) as [ksw Hsw].
      replace (1 + S w') with (S (S w')) in Hsw by lia.
      exists (k0 + ksw). eapply run_c_cat; [exact H0 | exact Hsw]. }
  destruct Hr3 as [k_r3 Hr3].
  unfold trip_frame_g in Hr3.
  assert (Hskw : skipn (S w) (zeros (S (S w)) ++ zeros b0) = zeros (1 + b0)).
  { rewrite skipn_app, Eps1Copy.skipn_zeros by lia.
    replace (S (S w) - S w) with 1 by lia. replace (S w - S (S w)) with 0 by lia. reflexivity. }
  rewrite Hskw in Hr3.
  set (L_rest := bl :: ones (S w) ++ bl :: zeros (S m) ++ ones (S (S a')) ++ zeros (1 + b0)).
  assert (Hza : TM.run Eps1Copy.ctbl 1
    (mkConf R3 (bl :: ones (S w) ++ bl :: zeros g ++ on :: L_rest) bl [on]) =
    Some (mkConf 60 (ones (S w) ++ bl :: zeros g ++ on :: L_rest) bl [bl; on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hzb0 : TM.run Eps1Copy.ctbl 1
    (mkConf 60 (on :: ones w ++ bl :: zeros g ++ on :: L_rest) bl [bl; on]) =
    Some (mkConf 61 (ones w ++ bl :: zeros g ++ on :: L_rest) on [bl; bl; on]))
    by (rewrite TM.run_S; reflexivity).
  pose proof (walk_ZB_ones_r w (bl :: zeros g ++ on :: L_rest) [bl; bl; on]) as Hzb.
  assert (Hzb_end : TM.run Eps1Copy.ctbl 1
    (mkConf 61 (bl :: zeros g ++ on :: L_rest) on (ones w ++ [bl; bl; on])) =
    Some (mkConf 61 (zeros g ++ on :: L_rest) bl (on :: ones w ++ [bl; bl; on])))
    by (rewrite TM.run_S; reflexivity).
  assert (Hzc : exists kzc,
    TM.run Eps1Copy.ctbl kzc
      (mkConf 61 (zeros g ++ on :: L_rest) bl (on :: ones w ++ [bl; bl; on])) =
    Some (mkConf S4 L_rest on (zeros (S g) ++ ones (S w) ++ bl :: bl :: [on]))).
  { destruct g as [|g'].
    - cbn [zeros app].
      assert (H1 : TM.run Eps1Copy.ctbl 1
        (mkConf 61 (on :: L_rest) bl (on :: ones w ++ [bl; bl; on])) =
        Some (mkConf 62 L_rest on (bl :: on :: ones w ++ [bl; bl; on])))
        by (rewrite TM.run_S; reflexivity).
      assert (H2 : TM.run Eps1Copy.ctbl 1
        (mkConf 62 L_rest on (bl :: on :: ones w ++ [bl; bl; on])) =
        Some (mkConf 63 (tl L_rest) (hd bl L_rest) (on :: bl :: on :: ones w ++ [bl; bl; on])))
        by (rewrite TM.run_S; reflexivity).
      unfold L_rest in H2. cbn [tl hd] in H2.
      assert (H3 : TM.run Eps1Copy.ctbl 1
        (mkConf 63 (ones (S w) ++ bl :: zeros (S m) ++ ones (S (S a')) ++ zeros (1 + b0)) bl
                (on :: bl :: ones (S w) ++ bl :: bl :: [on])) =
        Some (mkConf S4 L_rest on (bl :: ones (S w) ++ bl :: bl :: [on])))
        by (rewrite TM.run_S; reflexivity).
      exists 3. eapply run_c_cat; [exact H1|]. eapply run_c_cat; [exact H2 | exact H3].
    - cbn [zeros app].
      assert (H1 : TM.run Eps1Copy.ctbl 1
        (mkConf 61 (bl :: zeros g' ++ on :: L_rest) bl (on :: ones w ++ [bl; bl; on])) =
        Some (mkConf 62 (zeros g' ++ on :: L_rest) bl (bl :: on :: ones w ++ [bl; bl; on])))
        by (rewrite TM.run_S; reflexivity).
      pose proof (walk_ZC_zeros g' L_rest (on :: ones w ++ [bl; bl; on])) as H2.
      unfold L_rest in H2 at 2. cbn [tl hd] in H2.
      assert (H3 : TM.run Eps1Copy.ctbl 1
        (mkConf 63 (ones (S w) ++ bl :: zeros (S m) ++ ones (S (S a')) ++ zeros (1 + b0)) bl
                (on :: zeros (S g') ++ on :: ones w ++ [bl; bl; on])) =
        Some (mkConf S4 L_rest on (zeros (S (S g')) ++ ones (S w) ++ bl :: bl :: [on])))
        by (rewrite TM.run_S; reflexivity).
      exists (1 + S (S g') + 1). eapply run_c_cat; [exact H1|]. eapply run_c_cat; [exact H2 | exact H3]. }
  destruct Hzc as [kzc Hzc].
  exists (k_r3 + 1 + 1 + w + 1 + kzc).
  apply run_ctbl_to_tbl.
  eapply run_c_cat; [exact Hr3|].
  eapply run_c_cat; [exact Hza|].
  eapply run_c_cat; [exact Hzb0|].
  eapply run_c_cat; [exact Hzb|].
  eapply run_c_cat; [exact Hzb_end|].
  exact Hzc.
Qed.

(** * 4. Stage Branch (F0..P2, K-loop, S0..S4 -> ENTRY) *)

Lemma walk_F0_bl : forall g L R,
  TM.run Eps1Tape.tbl g (mkConf 12 L bl (zeros g ++ R)) =
  Some (mkConf 12 (zeros g ++ L) (hd bl R) (tl R)).
Proof.
  (* Note: at g=0, R might start with on, so let us state for R = c :: R' *)
  induction g as [|g IH]; intros L R; [destruct R; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct g as [|g'].
  - simpl. destruct R; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH (bl :: L) R).
    replace (zeros (S g') ++ bl :: L) with (zeros (S (S g')) ++ L)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_F2_bl : forall g L R,
  TM.run Eps1Tape.tbl g (mkConf 14 (zeros g ++ L) bl R) =
  Some (mkConf 14 L (hd bl (zeros g ++ R)) (tl (zeros g ++ R))).
Proof.
  induction g as [|g IH]; intros L R; [destruct L; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct g as [|g'].
  - simpl. destruct L; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH L (bl :: R)).
    replace (zeros (S g') ++ bl :: R) with (zeros (S (S g')) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_F3_bl : forall g L R,
  TM.run Eps1Tape.tbl g (mkConf 15 (zeros g ++ L) bl R) =
  Some (mkConf 15 L (hd bl (zeros g ++ R)) (tl (zeros g ++ R))).
Proof.
  induction g as [|g IH]; intros L R; [destruct L; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct g as [|g'].
  - simpl. destruct L; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH L (bl :: R)).
    replace (zeros (S g') ++ bl :: R) with (zeros (S (S g')) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_P0_bl : forall g L R,
  TM.run Eps1Tape.tbl g (mkConf 18 L bl (zeros g ++ R)) =
  Some (mkConf 18 (zeros g ++ L) (hd bl R) (tl R)).
Proof.
  induction g as [|g IH]; intros L R; [destruct R; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct g as [|g'].
  - simpl. destruct R; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH (bl :: L) R).
    replace (zeros (S g') ++ bl :: L) with (zeros (S (S g')) ++ L)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_R0_bl : forall g L R,
  TM.run Eps1Tape.tbl g (mkConf 0 (zeros g ++ L) bl R) =
  Some (mkConf 0 L (hd bl (zeros g ++ R)) (tl (zeros g ++ R))).
Proof.
  induction g as [|g IH]; intros L R; [destruct L; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct g as [|g'].
  - simpl. destruct L; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH L (bl :: R)).
    replace (zeros (S g') ++ bl :: R) with (zeros (S (S g')) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_R4_bl : forall g L R,
  TM.run Eps1Tape.tbl g (mkConf 3 L bl (zeros g ++ R)) =
  Some (mkConf 3 (zeros g ++ L) (hd bl R) (tl R)).
Proof.
  induction g as [|g IH]; intros L R; [destruct R; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct g as [|g'].
  - simpl. destruct R; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH (bl :: L) R).
    replace (zeros (S g') ++ bl :: L) with (zeros (S (S g')) ++ L)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_R5_on : forall n L R,
  TM.run Eps1Tape.tbl n (mkConf 4 L on (ones n ++ bl :: R)) =
  Some (mkConf 4 (ones n ++ L) on (bl :: R)).
Proof.
  (* Wait: 4 on on -> moves R in 4; when n=0, 0 steps! *)
  induction n as [|n IH]; intros L R; [reflexivity|].
  rewrite TM.run_S. cbn [ones app].
  change (TM.step Eps1Tape.tbl (mkConf 4 L on (on :: ones n ++ bl :: R)))
    with (Some (mkConf 4 (on :: L) on (ones n ++ bl :: R))).
  rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_K2_bl : forall z L R,
  TM.run Eps1Tape.tbl z (mkConf 27 L bl (zeros z ++ R)) =
  Some (mkConf 27 (zeros z ++ L) (hd bl R) (tl R)).
Proof.
  induction z as [|z IH]; intros L R; [destruct R; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct z as [|z'].
  - simpl. destruct R; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH (bl :: L) R).
    replace (zeros (S z') ++ bl :: L) with (zeros (S (S z')) ++ L)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_K3_on : forall n L R,
  TM.run Eps1Tape.tbl n (mkConf 28 L on (ones n ++ bl :: R)) =
  Some (mkConf 28 (ones n ++ L) on (bl :: R)).
Proof.
  induction n as [|n IH]; intros L R; [reflexivity|].
  rewrite TM.run_S. cbn [ones app].
  change (TM.step Eps1Tape.tbl (mkConf 28 L on (on :: ones n ++ bl :: R)))
    with (Some (mkConf 28 (on :: L) on (ones n ++ bl :: R))).
  rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_K5_on : forall n L R,
  TM.run Eps1Tape.tbl n (mkConf 30 (ones n ++ L) on R) =
  Some (mkConf 30 L on (ones n ++ R)).
Proof.
  induction n as [|n IH]; intros L R; [reflexivity|].
  rewrite TM.run_S. cbn [ones app].
  change (TM.step Eps1Tape.tbl (mkConf 30 (on :: ones n ++ L) on R))
    with (Some (mkConf 30 (ones n ++ L) on (on :: R))).
  rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_K6_bl : forall z L R,
  TM.run Eps1Tape.tbl z (mkConf 31 (zeros z ++ L) bl R) =
  Some (mkConf 31 L (hd bl (zeros z ++ R)) (tl (zeros z ++ R))).
Proof.
  induction z as [|z IH]; intros L R; [destruct L; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct z as [|z'].
  - simpl. destruct L; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH L (bl :: R)).
    replace (zeros (S z') ++ bl :: R) with (zeros (S (S z')) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_A5_bl : forall z L R,
  TM.run Eps1Tape.tbl z (mkConf 6 L bl (zeros z ++ R)) =
  Some (mkConf 6 (zeros z ++ L) (hd bl R) (tl R)).
Proof.
  induction z as [|z IH]; intros L R; [destruct R; reflexivity|].
  rewrite TM.run_S. cbn [zeros app].
  destruct z as [|z'].
  - simpl. destruct R; reflexivity.
  - cbn [zeros app hd tl] in *.
    rewrite (IH (bl :: L) R).
    replace (zeros (S z') ++ bl :: L) with (zeros (S (S z')) ++ L)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_A6_on : forall n L R,
  TM.run Eps1Tape.tbl n (mkConf 7 L on (ones n ++ bl :: R)) =
  Some (mkConf 7 (ones n ++ L) on (bl :: R)).
Proof.
  induction n as [|n IH]; intros L R; [reflexivity|].
  rewrite TM.run_S. cbn [ones app].
  change (TM.step Eps1Tape.tbl (mkConf 7 L on (on :: ones n ++ bl :: R)))
    with (Some (mkConf 7 (on :: L) on (ones n ++ bl :: R))).
  rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_A9_on : forall n L R,
  TM.run Eps1Tape.tbl n (mkConf 10 (ones n ++ L) on R) =
  Some (mkConf 10 L on (ones n ++ R)).
Proof.
  induction n as [|n IH]; intros L R; [reflexivity|].
  rewrite TM.run_S. cbn [ones app].
  change (TM.step Eps1Tape.tbl (mkConf 10 (on :: ones n ++ L) on R))
    with (Some (mkConf 10 (ones n ++ L) on (on :: R))).
  rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_S0_on : forall k L R,
  TM.run Eps1Tape.tbl k (mkConf 21 (ones k ++ L) on R) =
  Some (mkConf 21 L on (ones k ++ R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity|].
  rewrite TM.run_S. cbn [ones app].
  change (TM.step Eps1Tape.tbl (mkConf 21 (on :: ones k ++ L) on R))
    with (Some (mkConf 21 (ones k ++ L) on (on :: R))).
  rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_S3_on : forall k L R,
  TM.run Eps1Tape.tbl k (mkConf 24 L on (ones k ++ bl :: R)) =
  Some (mkConf 24 (ones k ++ L) on (bl :: R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity|].
  rewrite TM.run_S. cbn [ones app].
  change (TM.step Eps1Tape.tbl (mkConf 24 L on (on :: ones k ++ bl :: R)))
    with (Some (mkConf 24 (on :: L) on (ones k ++ bl :: R))).
  rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.
Lemma walk_F2_bl_on : forall g L0 R,
  TM.run Eps1Tape.tbl (S g) (mkConf 14 (zeros g ++ on :: L0) bl R) =
  Some (mkConf 14 L0 on (zeros (S g) ++ R)).
Proof.
  induction g as [|g IH]; intros L0 R.
  - cbn [zeros app]. rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Tape.tbl (mkConf 14 (bl :: zeros g ++ on :: L0) bl R))
      with (Some (mkConf 14 (zeros g ++ on :: L0) bl (bl :: R))).
    rewrite IH.
    replace (zeros (S g) ++ bl :: R) with (zeros (S (S g)) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_F3_bl_on : forall g L0 R,
  TM.run Eps1Tape.tbl (S g) (mkConf 15 (zeros g ++ on :: L0) bl R) =
  Some (mkConf 15 L0 on (zeros (S g) ++ R)).
Proof.
  induction g as [|g IH]; intros L0 R.
  - cbn [zeros app]. rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Tape.tbl (mkConf 15 (bl :: zeros g ++ on :: L0) bl R))
      with (Some (mkConf 15 (zeros g ++ on :: L0) bl (bl :: R))).
    rewrite IH.
    replace (zeros (S g) ++ bl :: R) with (zeros (S (S g)) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_R0_bl_on : forall g L0 R,
  TM.run Eps1Tape.tbl (S g) (mkConf 0 (zeros g ++ on :: L0) bl R) =
  Some (mkConf 0 L0 on (zeros (S g) ++ R)).
Proof.
  induction g as [|g IH]; intros L0 R.
  - cbn [zeros app]. rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Tape.tbl (mkConf 0 (bl :: zeros g ++ on :: L0) bl R))
      with (Some (mkConf 0 (zeros g ++ on :: L0) bl (bl :: R))).
    rewrite IH.
    replace (zeros (S g) ++ bl :: R) with (zeros (S (S g)) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_K6_bl_on : forall z L0 R,
  TM.run Eps1Tape.tbl (S z) (mkConf 31 (zeros z ++ bl :: L0) bl R) =
  Some (mkConf 31 L0 bl (zeros (S z) ++ R)).
Proof.
  induction z as [|z IH]; intros L0 R.
  - cbn [zeros app]. rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Tape.tbl (mkConf 31 (bl :: zeros z ++ bl :: L0) bl R))
      with (Some (mkConf 31 (zeros z ++ bl :: L0) bl (bl :: R))).
    rewrite IH.
    replace (zeros (S z) ++ bl :: R) with (zeros (S (S z)) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_F0_gen : forall g0 L0 R,
  TM.run Eps1Tape.tbl g0
    (mkConf 12 L0 (hd bl (zeros g0 ++ on :: R)) (tl (zeros g0 ++ on :: R))) =
  Some (mkConf 12 (zeros g0 ++ L0) on R).
Proof.
  destruct g0 as [|g0']; intros L0 R.
  - reflexivity.
  - cbn [zeros app hd tl]. apply walk_F0_bl.
Qed.

Lemma stage_F0_to_R0 : forall g w L_wall,
  exists z k_f0,
    TM.run Eps1Tape.tbl k_f0
      (mkConf S4 L_wall on (zeros (S g) ++ ones (S w) ++ [bl; bl; on])) =
    Some (mkConf 0 (zeros z ++ ones (S w) ++ on :: L_wall) bl [on; bl; on]).
Proof.
  intros g w L_wall.
  assert (Hs4 : TM.run Eps1Tape.tbl 1 (mkConf S4 L_wall on (zeros (S g) ++ ones (S w) ++ [bl; bl; on])) =
                Some (mkConf 12 (on :: L_wall) bl (zeros g ++ ones (S w) ++ [bl; bl; on])))
    by (rewrite TM.run_S, st_S4_on; reflexivity).
  assert (Hf_ind : forall k g0 L0,
    exists kf,
      TM.run Eps1Tape.tbl kf
        (mkConf 12 (on :: L0) bl (zeros g0 ++ ones (S k) ++ [bl; bl; on])) =
      Some (mkConf 12 (ones k ++ on :: L0) bl (zeros g0 ++ [on; bl; bl; on]))).
  { induction k as [|k IH]; intros g0 L0.
    - exists 0. reflexivity.
    - pose proof (walk_F0_bl g0 (on :: L0) (ones (S (S k)) ++ [bl; bl; on])) as Hf0.
      cbn [ones app hd tl] in Hf0.
      assert (Hf0_on : TM.run Eps1Tape.tbl 1
        (mkConf 12 (zeros g0 ++ on :: L0) on (on :: ones k ++ [bl; bl; on])) =
        Some (mkConf 13 (bl :: zeros g0 ++ on :: L0) on (ones k ++ [bl; bl; on])))
        by (rewrite TM.run_S; reflexivity).
      assert (Hf1_on : TM.run Eps1Tape.tbl 1
        (mkConf 13 (bl :: zeros g0 ++ on :: L0) on (ones k ++ [bl; bl; on])) =
        Some (mkConf 14 (zeros g0 ++ on :: L0) bl (on :: ones k ++ [bl; bl; on])))
        by (rewrite TM.run_S; reflexivity).
      pose proof (walk_F2_bl_on g0 L0 (on :: ones k ++ [bl; bl; on])) as Hf2.
      assert (Hf2_on : TM.run Eps1Tape.tbl 1
        (mkConf 14 L0 on (zeros (S g0) ++ on :: ones k ++ [bl; bl; on])) =
        Some (mkConf 16 (on :: L0) bl (zeros g0 ++ on :: ones k ++ [bl; bl; on])))
        by (rewrite TM.run_S; reflexivity).
      assert (Hf4_bl : TM.run Eps1Tape.tbl 1
        (mkConf 16 (on :: L0) bl (zeros g0 ++ on :: ones k ++ [bl; bl; on])) =
        Some (mkConf 12 (on :: on :: L0) bl (zeros g0 ++ ones (S k) ++ [bl; bl; on])))
        by (rewrite TM.run_S; reflexivity).
      destruct (IH g0 (on :: L0)) as [kf Hkf].
      exists (g0 + 1 + 1 + S g0 + 1 + 1 + kf).
      eapply run_tbl_cat; [exact Hf0|].
      eapply run_tbl_cat; [exact Hf0_on|].
      eapply run_tbl_cat; [exact Hf1_on|].
      eapply run_tbl_cat; [exact Hf2|].
      eapply run_tbl_cat; [exact Hf2_on|].
      eapply run_tbl_cat; [exact Hf4_bl|].
      replace (ones k ++ on :: on :: L0) with (ones (S k) ++ on :: L0) in Hkf
        by (rewrite <- ones_S_r, <- app_assoc; reflexivity).
      exact Hkf. }
  destruct (Hf_ind w g L_wall) as [kf Hkf].
  pose proof (walk_F0_bl g (ones w ++ on :: L_wall) [on; bl; bl; on]) as Hf_last.
  cbn [hd tl] in Hf_last.
  assert (Hf_on : TM.run Eps1Tape.tbl 1
    (mkConf 12 (zeros g ++ ones w ++ on :: L_wall) on [bl; bl; on]) =
    Some (mkConf 13 (bl :: zeros g ++ ones w ++ on :: L_wall) bl [bl; on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hf1_bl : TM.run Eps1Tape.tbl 1
    (mkConf 13 (bl :: zeros g ++ ones w ++ on :: L_wall) bl [bl; on]) =
    Some (mkConf 15 (bl :: zeros g ++ ones w ++ on :: L_wall) bl [bl; bl; on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hsplit : exists L_f3, ones w ++ on :: L_wall = on :: L_f3 /\ on :: on :: L_f3 = ones (S w) ++ on :: L_wall).
  { destruct w as [|w']; [exists L_wall | exists (ones w' ++ on :: L_wall)]; split; reflexivity. }
  destruct Hsplit as [L_f3 [HLf3_1 HLf3_2]].
  rewrite HLf3_1 in Hf1_bl.
  replace (bl :: zeros g ++ on :: L_f3) with (zeros (S g) ++ on :: L_f3) in Hf1_bl by reflexivity.
  pose proof (walk_F3_bl_on (S g) L_f3 [bl; bl; on]) as Hf3.
  assert (Hf3_on : TM.run Eps1Tape.tbl 1
    (mkConf 15 L_f3 on (zeros (S (S g)) ++ [bl; bl; on])) =
    Some (mkConf 17 (on :: L_f3) bl (zeros (S g) ++ [bl; bl; on])))
    by (rewrite TM.run_S; reflexivity).
  assert (Hf5_bl : TM.run Eps1Tape.tbl 1
    (mkConf 17 (on :: L_f3) bl (zeros (S g) ++ [bl; bl; on])) =
    Some (mkConf 18 (on :: on :: L_f3) bl (zeros (S g) ++ [bl; bl; on])))
    by (rewrite TM.run_S; reflexivity).
  rewrite HLf3_2 in Hf5_bl.
  replace (zeros (S g) ++ [bl; bl; on]) with (zeros (S (S (S g))) ++ [on]) in Hf5_bl
    by (rewrite <- !zeros_S_r, <- app_assoc; reflexivity).
  pose proof (walk_P0_bl (S (S (S g))) (ones (S w) ++ on :: L_wall) [on]) as Hp0.
  cbn [hd tl] in Hp0.
  assert (Hp0_on : TM.run Eps1Tape.tbl 1
    (mkConf 18 (zeros (S (S (S g))) ++ ones (S w) ++ on :: L_wall) on []) =
    Some (mkConf 19 (zeros (S (S g)) ++ ones (S w) ++ on :: L_wall) bl [on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hp1_bl : TM.run Eps1Tape.tbl 1
    (mkConf 19 (zeros (S (S g)) ++ ones (S w) ++ on :: L_wall) bl [on]) =
    Some (mkConf 20 (zeros (S g) ++ ones (S w) ++ on :: L_wall) bl [bl; on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hp2_bl : TM.run Eps1Tape.tbl 1
    (mkConf 20 (zeros (S g) ++ ones (S w) ++ on :: L_wall) bl [bl; on]) =
    Some (mkConf 0 (zeros g ++ ones (S w) ++ on :: L_wall) bl [on; bl; on]))
    by (rewrite TM.run_S; reflexivity).
  exists g, (1 + kf + g + 1 + 1 + S (S g) + 1 + 1 + S (S (S g)) + 1 + 1 + 1).
  eapply run_tbl_cat; [exact Hs4|].
  eapply run_tbl_cat; [exact Hkf|].
  eapply run_tbl_cat; [exact Hf_last|].
  eapply run_tbl_cat; [exact Hf_on|].
  eapply run_tbl_cat; [exact Hf1_bl|].
  eapply run_tbl_cat; [exact Hf3|].
  eapply run_tbl_cat; [exact Hf3_on|].
  eapply run_tbl_cat; [exact Hf5_bl|].
  eapply run_tbl_cat; [exact Hp0|].
  eapply run_tbl_cat; [exact Hp0_on|].
  eapply run_tbl_cat; [exact Hp1_bl|].
  exact Hp2_bl.
Qed.

(** * 5. K-Loop, Outer Stage Loop, and Parametric Rung Theorem *)

Fixpoint iter_2p1 (k q : nat) : nat :=
  match k with
  | 0 => q
  | S k' => iter_2p1 k' (2 * q + 1)
  end.

Lemma iter_2p1_closed : forall k q,
  iter_2p1 k q = 2 ^ k * (q + 1) - 1.
Proof.
  induction k as [|k IH]; intro q; simpl.
  - lia.
  - rewrite IH.
    assert (Hpos : 1 <= 2 ^ k) by (clear; induction k; simpl; lia).
    nia.
Qed.

Lemma iter_2p1_stage : forall k,
  iter_2p1 k 1 = Eps1Ladder.stage k.
Proof.
  intro k. rewrite iter_2p1_closed. unfold Eps1Ladder.stage.
  simpl (2 ^ (S k)). lia.
Qed.

Lemma walk_K2_bl_on : forall z L R,
  TM.run Eps1Tape.tbl (S z) (mkConf 27 L bl (zeros z ++ on :: R)) =
  Some (mkConf 27 (zeros (S z) ++ L) on R).
Proof.
  induction z as [|z IH]; intros L R.
  - cbn [zeros app]. rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Tape.tbl (mkConf 27 L bl (bl :: zeros z ++ on :: R)))
      with (Some (mkConf 27 (bl :: L) bl (zeros z ++ on :: R))).
    rewrite IH.
    replace (zeros (S z) ++ bl :: L) with (zeros (S (S z)) ++ L)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_K3_on_empty : forall n L,
  TM.run Eps1Tape.tbl (S n) (mkConf 28 L on (ones n)) =
  Some (mkConf 28 (ones (S n) ++ L) bl []).
Proof.
  induction n as [|n IH]; intro L.
  - rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [ones app].
    change (TM.step Eps1Tape.tbl (mkConf 28 L on (on :: ones n)))
      with (Some (mkConf 28 (on :: L) on (ones n))).
    rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_K6_bl_to_on : forall z L0 R,
  TM.run Eps1Tape.tbl (S z) (mkConf 31 (zeros z ++ on :: L0) bl R) =
  Some (mkConf 31 L0 on (zeros (S z) ++ R)).
Proof.
  induction z as [|z IH]; intros L0 R.
  - cbn [zeros app]. rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Tape.tbl (mkConf 31 (bl :: zeros z ++ on :: L0) bl R))
      with (Some (mkConf 31 (zeros z ++ on :: L0) bl (bl :: R))).
    rewrite IH.
    replace (zeros (S z) ++ bl :: R) with (zeros (S (S z)) ++ R)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_A5_bl_on : forall z L R,
  TM.run Eps1Tape.tbl (S z) (mkConf 6 L bl (zeros z ++ on :: R)) =
  Some (mkConf 6 (zeros (S z) ++ L) on R).
Proof.
  induction z as [|z IH]; intros L R.
  - cbn [zeros app]. rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [zeros app].
    change (TM.step Eps1Tape.tbl (mkConf 6 L bl (bl :: zeros z ++ on :: R)))
      with (Some (mkConf 6 (bl :: L) bl (zeros z ++ on :: R))).
    rewrite IH.
    replace (zeros (S z) ++ bl :: L) with (zeros (S (S z)) ++ L)
      by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
    reflexivity.
Qed.

Lemma walk_A6_on_empty : forall n L,
  TM.run Eps1Tape.tbl (S n) (mkConf 7 L on (ones n)) =
  Some (mkConf 7 (ones (S n) ++ L) bl []).
Proof.
  induction n as [|n IH]; intro L.
  - rewrite TM.run_S. reflexivity.
  - rewrite TM.run_S. cbn [ones app].
    change (TM.step Eps1Tape.tbl (mkConf 7 L on (on :: ones n)))
      with (Some (mkConf 7 (on :: L) on (ones n))).
    rewrite IH. rewrite <- ones_S_r, <- app_assoc. reflexivity.
Qed.

Lemma walk_S0_to_bl : forall k L R,
  TM.run Eps1Tape.tbl (S k) (mkConf 21 (ones k ++ bl :: L) on R) =
  Some (mkConf 21 L bl (ones (S k) ++ R)).
Proof.
  intros k L R.
  pose proof (walk_S0_on k (bl :: L) R) as H1.
  assert (H2 : TM.run Eps1Tape.tbl 1 (mkConf 21 (bl :: L) on (ones k ++ R)) =
               Some (mkConf 21 L bl (ones (S k) ++ R)))
    by (rewrite TM.run_S; reflexivity).
  pose proof (run_tbl_cat k 1 _ _ _ H1 H2) as H.
  replace (k + 1) with (S k) in H by lia. exact H.
Qed.

Lemma walk_S3_to_S4 : forall k L R,
  TM.run Eps1Tape.tbl (S (S k)) (mkConf 24 L on (ones k ++ bl :: R)) =
  Some (mkConf 25 (bl :: ones (S k) ++ L) (hd bl R) (tl R)).
Proof.
  intros k L R.
  pose proof (walk_S3_on k L R) as H1.
  assert (H2 : TM.run Eps1Tape.tbl 1 (mkConf 24 (ones k ++ L) on (bl :: R)) =
               Some (mkConf 24 (on :: ones k ++ L) bl R))
    by (rewrite TM.run_S; reflexivity).
  assert (H3 : TM.run Eps1Tape.tbl 1 (mkConf 24 (on :: ones k ++ L) bl R) =
               Some (mkConf 25 (bl :: on :: ones k ++ L) (hd bl R) (tl R)))
    by (rewrite TM.run_S; reflexivity).
  pose proof (run_tbl_cat k 1 _ _ _ H1 H2) as Ha.
  pose proof (run_tbl_cat (k + 1) 1 _ _ _ Ha H3) as Hb.
  replace (k + 1 + 1) with (S (S k)) in Hb by lia.
  exact Hb.
Qed.

Lemma stage_K_inner_step : forall k L_k zR q,
  TM.run Eps1Tape.tbl (2 * zR + 2 * q + 10)
    (mkConf 27 (on :: ones k ++ bl :: L_k) bl (zeros zR ++ ones (S q))) =
  Some (match k with
        | 0 => mkConf 6 (bl :: L_k) bl (zeros (S zR) ++ ones (S (S (S q))))
        | S k' => mkConf 27 (on :: ones k' ++ bl :: L_k) bl (zeros (S zR) ++ ones (S (S (S q))))
        end).
Proof.
  intros k L_k zR q.
  pose proof (walk_K2_bl_on zR (on :: ones k ++ bl :: L_k) (ones q)) as H1.
  cbn [ones app] in H1.
  assert (H2 : TM.run Eps1Tape.tbl 1
    (mkConf 27 (zeros (S zR) ++ on :: ones k ++ bl :: L_k) on (ones q)) =
    Some (mkConf 28 (on :: zeros (S zR) ++ on :: ones k ++ bl :: L_k) (hd bl (ones q)) (tl (ones q))))
    by (rewrite TM.run_S; reflexivity).
  assert (H3 : TM.run Eps1Tape.tbl (S q + 1)
    (mkConf 28 (on :: zeros (S zR) ++ on :: ones k ++ bl :: L_k) (hd bl (ones q)) (tl (ones q))) =
    Some (mkConf 29 (ones (S (S q)) ++ zeros (S zR) ++ on :: ones k ++ bl :: L_k) bl [])).
  { destruct q as [|q'].
    - cbn [ones app hd tl]. rewrite TM.run_S. reflexivity.
    - cbn [ones app hd tl].
      pose proof (walk_K3_on_empty q' (on :: zeros (S zR) ++ on :: ones k ++ bl :: L_k)) as Hk3.
      assert (Hk3b : TM.run Eps1Tape.tbl 1
        (mkConf 28 (ones (S q') ++ on :: zeros (S zR) ++ on :: ones k ++ bl :: L_k) bl []) =
        Some (mkConf 29 (on :: ones (S q') ++ on :: zeros (S zR) ++ on :: ones k ++ bl :: L_k) bl []))
        by (rewrite TM.run_S; reflexivity).
      pose proof (run_tbl_cat (S q') 1 _ _ _ Hk3 Hk3b) as Hk3c.
      replace (on :: ones (S q') ++ on :: zeros (S zR) ++ on :: ones k ++ bl :: L_k)
        with (ones (S (S (S q'))) ++ zeros (S zR) ++ on :: ones k ++ bl :: L_k) in Hk3c
        by (rewrite <- ones_S_r, <- app_assoc; reflexivity).
      exact Hk3c. }
  assert (H4 : TM.run Eps1Tape.tbl 1
    (mkConf 29 (ones (S (S q)) ++ zeros (S zR) ++ on :: ones k ++ bl :: L_k) bl []) =
    Some (mkConf 30 (ones (S q) ++ zeros (S zR) ++ on :: ones k ++ bl :: L_k) on [on]))
    by (rewrite TM.run_S; reflexivity).
  pose proof (walk_K5_on (S q) (zeros (S zR) ++ on :: ones k ++ bl :: L_k) [on]) as H5.
  assert (H5b : TM.run Eps1Tape.tbl 1
    (mkConf 30 (zeros (S zR) ++ on :: ones k ++ bl :: L_k) on (ones (S q) ++ [on])) =
    Some (mkConf 30 (zeros zR ++ on :: ones k ++ bl :: L_k) bl (ones (S (S q)) ++ [on])))
    by (rewrite TM.run_S; reflexivity).
  assert (H5c : TM.run Eps1Tape.tbl 1
    (mkConf 30 (zeros zR ++ on :: ones k ++ bl :: L_k) bl (ones (S (S q)) ++ [on])) =
    Some (mkConf 31 (tl (zeros zR ++ on :: ones k ++ bl :: L_k))
            (hd bl (zeros zR ++ on :: ones k ++ bl :: L_k))
            (bl :: ones (S (S q)) ++ [on])))
    by (rewrite TM.run_S; reflexivity).
  assert (H6 : TM.run Eps1Tape.tbl (S zR)
    (mkConf 31 (tl (zeros zR ++ on :: ones k ++ bl :: L_k))
            (hd bl (zeros zR ++ on :: ones k ++ bl :: L_k))
            (bl :: ones (S (S q)) ++ [on])) =
    Some (mkConf 32 (tl (ones k ++ bl :: L_k)) (hd bl (ones k ++ bl :: L_k))
            (bl :: zeros zR ++ bl :: ones (S (S q)) ++ [on]))).
  { destruct zR as [|zR'].
    - cbn [zeros app tl hd]. rewrite TM.run_S. reflexivity.
    - cbn [zeros app tl hd].
      pose proof (walk_K6_bl_to_on zR' (ones k ++ bl :: L_k) (bl :: ones (S (S q)) ++ [on])) as Hk6.
      assert (Hk6b : TM.run Eps1Tape.tbl 1
        (mkConf 31 (ones k ++ bl :: L_k) on (zeros (S zR') ++ bl :: ones (S (S q)) ++ [on])) =
        Some (mkConf 32 (tl (ones k ++ bl :: L_k)) (hd bl (ones k ++ bl :: L_k))
                (bl :: zeros (S zR') ++ bl :: ones (S (S q)) ++ [on])))
        by (rewrite TM.run_S; reflexivity).
      pose proof (run_tbl_cat (S zR') 1 _ _ _ Hk6 Hk6b) as Hk6c.
      replace (S zR' + 1) with (S (S zR')) in Hk6c by lia. exact Hk6c. }
  assert (H7 : TM.run Eps1Tape.tbl 1
    (mkConf 32 (tl (ones k ++ bl :: L_k)) (hd bl (ones k ++ bl :: L_k))
            (bl :: zeros zR ++ bl :: ones (S (S q)) ++ [on])) =
    Some (match k with
          | 0 => mkConf 6 (bl :: L_k) bl (zeros (S zR) ++ ones (S (S (S q))))
          | S k' => mkConf 27 (on :: ones k' ++ bl :: L_k) bl (zeros (S zR) ++ ones (S (S (S q))))
          end)).
  { destruct k as [|k'].
    - cbn [ones app tl hd]. rewrite TM.run_S.
      replace (zeros zR ++ bl :: ones (S (S q)) ++ [on])
        with (zeros (S zR) ++ ones (S (S (S q))))
        by (rewrite zeros_succ, <- ones_S_r, <- app_assoc; reflexivity).
      reflexivity.
    - cbn [ones app tl hd]. rewrite TM.run_S.
      replace (zeros zR ++ bl :: ones (S (S q)) ++ [on])
        with (zeros (S zR) ++ ones (S (S (S q))))
        by (rewrite zeros_succ, <- ones_S_r, <- app_assoc; reflexivity).
      reflexivity. }
  pose proof (run_tbl_cat (S zR) 1 _ _ _ H1 H2) as Ha.
  pose proof (run_tbl_cat _ (S q + 1) _ _ _ Ha H3) as Hb.
  pose proof (run_tbl_cat _ 1 _ _ _ Hb H4) as Hc.
  pose proof (run_tbl_cat _ (S q) _ _ _ Hc H5) as Hd.
  pose proof (run_tbl_cat _ 1 _ _ _ Hd H5b) as He.
  pose proof (run_tbl_cat _ 1 _ _ _ He H5c) as Hf.
  pose proof (run_tbl_cat _ (S zR) _ _ _ Hf H6) as Hg.
  pose proof (run_tbl_cat _ 1 _ _ _ Hg H7) as Hh.
  replace (S zR + 1 + (S q + 1) + 1 + S q + 1 + 1 + S zR + 1)
    with (2 * zR + 2 * q + 10) in Hh by lia.
  exact Hh.
Qed.

Lemma stage_K_inner_loop : forall k L_k zR q,
  exists k_in,
    TM.run Eps1Tape.tbl k_in
      (mkConf 27 (on :: ones k ++ bl :: L_k) bl (zeros zR ++ ones (S q))) =
    Some (mkConf 6 (bl :: L_k) bl (zeros (S (zR + k)) ++ ones (S (q + 2 * (S k))))).
Proof.
  induction k as [|k IH]; intros L_k zR q.
  - pose proof (stage_K_inner_step 0 L_k zR q) as H.
    exists (2 * zR + 2 * q + 10).
    replace (zR + 0) with zR by lia.
    replace (q + 2 * 1) with (S (S q)) by lia.
    exact H.
  - pose proof (stage_K_inner_step (S k) L_k zR q) as H1.
    destruct (IH L_k (S zR) (S (S q))) as [k2 H2].
    exists (2 * zR + 2 * q + 10 + k2).
    eapply run_tbl_cat; [exact H1|].
    replace (S (zR + S k)) with (S (S zR + k)) in * by lia.
    replace (S (q + 2 * S (S k))) with (S (S (S q) + 2 * S k)) in * by lia.
    exact H2.
Qed.

Lemma stage_K_step_run : forall zL zR v L_rest,
  exists k_st,
    TM.run Eps1Tape.tbl k_st
      (mkConf 0 (zeros zL ++ on :: on :: L_rest) bl (zeros zR ++ ones (S v) ++ [bl; on])) =
    Some (mkConf 0 (zeros (v + zL + zR + 2) ++ on :: L_rest) bl
            (zeros 1 ++ ones (2 * (S v) + 1) ++ [bl; on])).
Proof.
  intros zL zR v L_rest.
  pose proof (walk_R0_bl_on zL (on :: L_rest) (zeros zR ++ ones (S v) ++ [bl; on])) as H1.
  assert (H2 : TM.run Eps1Tape.tbl 1
    (mkConf 0 (on :: L_rest) on (zeros (S zL) ++ zeros zR ++ ones (S v) ++ [bl; on])) =
    Some (mkConf 1 L_rest on (on :: zeros (S zL) ++ zeros zR ++ ones (S v) ++ [bl; on])))
    by (rewrite TM.run_S; reflexivity).
  assert (H3 : TM.run Eps1Tape.tbl 2
    (mkConf 1 L_rest on (on :: zeros (S zL) ++ zeros zR ++ ones (S v) ++ [bl; on])) =
    Some (mkConf 3 (bl :: on :: L_rest) bl (zeros (S zL) ++ zeros zR ++ ones (S v) ++ [bl; on])))
    by (do 2 rewrite TM.run_S; reflexivity).
  replace (zeros (S zL) ++ zeros zR ++ ones (S v) ++ [bl; on])
    with (zeros (S zL + zR) ++ ones (S v) ++ [bl; on]) in H3
    by (rewrite zeros_app, app_assoc; reflexivity).
  pose proof (walk_R4_bl (S zL + zR) (bl :: on :: L_rest) (ones (S v) ++ [bl; on])) as H4.
  cbn [ones app hd tl] in H4.
  assert (H5 : TM.run Eps1Tape.tbl 1
    (mkConf 3 (zeros (S zL + zR) ++ bl :: on :: L_rest) on (ones v ++ [bl; on])) =
    Some (mkConf 4 (on :: zeros (S zL + zR) ++ bl :: on :: L_rest)
            (hd bl (ones v ++ [bl; on])) (tl (ones v ++ [bl; on]))))
    by (rewrite TM.run_S; reflexivity).
  assert (H6 : TM.run Eps1Tape.tbl (S v)
    (mkConf 4 (on :: zeros (S zL + zR) ++ bl :: on :: L_rest)
            (hd bl (ones v ++ [bl; on])) (tl (ones v ++ [bl; on]))) =
    Some (mkConf 4 (ones (S v) ++ zeros (S zL + zR) ++ bl :: on :: L_rest) bl [on])).
  { destruct v as [|v'].
    - cbn [ones app hd tl]. rewrite TM.run_S. reflexivity.
    - cbn [ones app hd tl].
      pose proof (walk_R5_on v' (on :: zeros (S zL + zR) ++ bl :: on :: L_rest) [on]) as Hr5.
      assert (Hr5b : TM.run Eps1Tape.tbl 1
        (mkConf 4 (ones v' ++ on :: zeros (S zL + zR) ++ bl :: on :: L_rest) on [bl; on]) =
        Some (mkConf 4 (on :: ones v' ++ on :: zeros (S zL + zR) ++ bl :: on :: L_rest) bl [on]))
        by (rewrite TM.run_S; reflexivity).
      pose proof (run_tbl_cat v' 1 _ _ _ Hr5 Hr5b) as Hr5c.
      replace (v' + 1) with (S v') in Hr5c by lia.
      replace (on :: ones v' ++ on :: zeros (S zL + zR) ++ bl :: on :: L_rest)
        with (ones (S (S v')) ++ zeros (S zL + zR) ++ bl :: on :: L_rest) in Hr5c
        by (rewrite <- ones_S_r, <- app_assoc; reflexivity).
      exact Hr5c. }
  assert (H7 : TM.run Eps1Tape.tbl 2
    (mkConf 4 (ones (S v) ++ zeros (S zL + zR) ++ bl :: on :: L_rest) bl [on]) =
    Some (mkConf 27 (on :: ones v ++ zeros (S zL + zR) ++ bl :: on :: L_rest) bl [on]))
    by (cbn [ones app]; do 2 rewrite TM.run_S; reflexivity).
  replace (zeros (S zL + zR) ++ bl :: on :: L_rest)
    with (bl :: zeros (S zL + zR) ++ on :: L_rest) in H7
    by (rewrite <- zeros_S_r, <- app_assoc; reflexivity).
  destruct (stage_K_inner_loop v (zeros (S zL + zR) ++ on :: L_rest) 0 0) as [k_in H8].
  cbn [zeros app] in H8.
  replace (S (0 + v)) with (S v) in H8 by lia.
  replace (S (0 + 2 * S v)) with (S (2 * v + 2)) in H8 by lia.
  pose proof (walk_A5_bl_on (S v) (bl :: zeros (S zL + zR) ++ on :: L_rest) (ones (2 * v + 2))) as H9.
  cbn [ones app] in H9.
  assert (H10 : TM.run Eps1Tape.tbl (2 * v + 2 + 1)
    (mkConf 6 (zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) on (ones (2 * v + 2))) =
    Some (mkConf 7 (ones (S (2 * v + 2)) ++ zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) bl [])).
  { assert (Ha5 : TM.run Eps1Tape.tbl 1
      (mkConf 6 (zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) on (ones (2 * v + 2))) =
      Some (mkConf 7 (on :: zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest)
              (hd bl (ones (2 * v + 2))) (tl (ones (2 * v + 2)))))
      by (rewrite TM.run_S; reflexivity).
    cbn [ones app hd tl] in Ha5.
    pose proof (walk_A6_on_empty (2 * v + 1) (on :: zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest)) as Ha6.
    pose proof (run_tbl_cat 1 (S (2 * v + 1)) _ _ _ Ha5 Ha6) as Ha7.
    replace (1 + S (2 * v + 1)) with (2 * v + 2 + 1) in Ha7 by lia.
    replace (ones (S (2 * v + 1)) ++ on :: zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest)
      with (ones (S (2 * v + 2)) ++ zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) in Ha7
      by (rewrite <- ones_S_r, <- app_assoc; reflexivity).
    exact Ha7. }
  assert (H11 : TM.run Eps1Tape.tbl 2
    (mkConf 7 (ones (S (2 * v + 2)) ++ zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) bl []) =
    Some (mkConf 9 (ones (S (2 * v + 2)) ++ zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) bl [on]))
    by (do 2 rewrite TM.run_S; reflexivity).
  assert (H12 : TM.run Eps1Tape.tbl 1
    (mkConf 9 (ones (S (2 * v + 2)) ++ zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) bl [on]) =
    Some (mkConf 10 (ones (2 * v + 2) ++ zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) on [bl; on]))
    by (rewrite TM.run_S; reflexivity).
  pose proof (walk_A9_on (2 * v + 2) (zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) [bl; on]) as H13.
  assert (H14 : TM.run Eps1Tape.tbl 1
    (mkConf 10 (zeros (S (S v)) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) on (ones (2 * v + 2) ++ [bl; on])) =
    Some (mkConf 10 (zeros (S v) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) bl (ones (S (2 * v + 2)) ++ [bl; on])))
    by (rewrite TM.run_S; reflexivity).
  assert (H15 : TM.run Eps1Tape.tbl 1
    (mkConf 10 (zeros (S v) ++ bl :: zeros (S zL + zR) ++ on :: L_rest) bl (ones (S (2 * v + 2)) ++ [bl; on])) =
    Some (mkConf 0 (zeros v ++ bl :: zeros (S zL + zR) ++ on :: L_rest) bl (bl :: ones (S (2 * v + 2)) ++ [bl; on])))
    by (rewrite TM.run_S; reflexivity).
  exists (S zL + 1 + 2 + (S zL + zR) + 1 + S v + 2 + k_in + S (S v) + (2 * v + 2 + 1) + 2 + 1 + (2 * v + 2) + 1 + 1).
  eapply run_tbl_cat; [exact H1|].
  eapply run_tbl_cat; [exact H2|].
  eapply run_tbl_cat; [exact H3|].
  eapply run_tbl_cat; [exact H4|].
  eapply run_tbl_cat; [exact H5|].
  eapply run_tbl_cat; [exact H6|].
  eapply run_tbl_cat; [exact H7|].
  eapply run_tbl_cat; [exact H8|].
  eapply run_tbl_cat; [exact H9|].
  eapply run_tbl_cat; [exact H10|].
  eapply run_tbl_cat; [exact H11|].
  eapply run_tbl_cat; [exact H12|].
  eapply run_tbl_cat; [exact H13|].
  eapply run_tbl_cat; [exact H14|].
  replace (zeros v ++ bl :: zeros (S zL + zR) ++ on :: L_rest)
    with (zeros (v + zL + zR + 2) ++ on :: L_rest) in H15
    by (rewrite zeros_succ, app_assoc, zeros_app; f_equal; f_equal; lia).
  replace (S (2 * v + 2)) with (2 * S v + 1) in H15 by lia.
  exact H15.
Qed.

Lemma stage_K_loop : forall k zL zR q L_rest,
  1 <= k ->
  1 <= q ->
  exists zL' zR' k_lp,
    1 <= zL' /    TM.run Eps1Tape.tbl k_lp
      (mkConf 0 (zeros zL ++ ones k ++ on :: L_rest) bl (zeros zR ++ ones q ++ [bl; on])) =
    Some (mkConf 0 (zeros zL' ++ on :: L_rest) bl (zeros zR' ++ ones (iter_2p1 k q) ++ [bl; on])).
Proof.
  induction k as [|k IH]; intros zL zR q L_rest Hk Hq; [lia|].
  destruct q as [|q']; [lia|].
  assert (Hrew : ones (S k) ++ on :: L_rest = on :: on :: (ones k ++ L_rest))
    by (cbn [ones app]; rewrite ones_succ; reflexivity).
  rewrite Hrew.
  destruct (stage_K_step_run zL zR q' (ones k ++ L_rest)) as [k1 H1].
  destruct k as [|k'].
  - exists (q' + zL + zR + 2), 1, k1. split; [lia|].
    cbn [ones app iter_2p1] in *. exact H1.
  - destruct (IH (q' + zL + zR + 2) 1 (2 * S q' + 1) L_rest ltac:(lia) ltac:(lia)) as [zL' [zR' [k2 [Hz H2]]]].
    exists zL', zR', (k1 + k2). split; [exact Hz|].
    eapply run_tbl_cat; [exact H1|].
    rewrite ones_succ in H2. exact H2.
Qed.

Lemma stage_to_S_exit : forall zL zR q blk d L_bud,
  1 <= zL ->
  1 <= q ->
  exists m' g' k_ex,
    TM.run Eps1Tape.tbl k_ex
      (mkConf 0 (zeros zL ++ on :: bl :: ones (S blk) ++ zeros (S d) ++ L_bud) bl (zeros zR ++ ones q ++ [bl; on])) =
    Some (match blk with
          | 0 => mkConf ENTRY (zeros (S m') ++ L_bud) on (zeros (S (S g')) ++ ones q ++ [bl; on])
          | S blk' => mkConf S4 (bl :: ones (S blk') ++ zeros (S m') ++ L_bud) on (zeros (S (S g')) ++ ones q ++ [bl; on])
          end).
Proof.
  intros zL zR q blk d L_bud HzL Hq.
  destruct zL as [|zL']; [lia|].
  pose proof (walk_R0_bl_on (S zL') (bl :: ones (S blk) ++ zeros (S d) ++ L_bud) (zeros zR ++ ones q ++ [bl; on])) as H1.
  assert (H2 : TM.run Eps1Tape.tbl 1
    (mkConf 0 (bl :: ones (S blk) ++ zeros (S d) ++ L_bud) on (zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])) =
    Some (mkConf 1 (ones (S blk) ++ zeros (S d) ++ L_bud) bl (on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])))
    by (rewrite TM.run_S; reflexivity).
  assert (H3 : TM.run Eps1Tape.tbl 1
    (mkConf 1 (ones (S blk) ++ zeros (S d) ++ L_bud) bl (on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])) =
    Some (mkConf 21 (ones blk ++ zeros (S d) ++ L_bud) on (bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])))
    by (cbn [ones app]; rewrite TM.run_S; reflexivity).
  pose proof (walk_S0_to_bl blk (zeros d ++ L_bud) (bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])) as H4.
  cbn [zeros app] in H4.
  assert (H5 : TM.run Eps1Tape.tbl 2
    (mkConf 21 (zeros d ++ L_bud) bl (ones (S blk) ++ bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])) =
    Some (mkConf 23 (bl :: bl :: zeros d ++ L_bud) (hd bl (ones (S blk) ++ bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on]))
            (tl (ones (S blk) ++ bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on]))))
    by (do 2 rewrite TM.run_S; reflexivity).
  destruct blk as [|blk'].
  - cbn [ones app hd tl] in H5.
    assert (H6 : TM.run Eps1Tape.tbl 1
      (mkConf 23 (bl :: bl :: zeros d ++ L_bud) bl (on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])) =
      Some (mkConf ENTRY (bl :: bl :: bl :: zeros d ++ L_bud) on (zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])))
      by (rewrite TM.run_S; reflexivity).
    exists (S (S d)), (zL' + zR), (S (S zL') + 1 + 1 + S 0 + 2 + 1).
    eapply run_tbl_cat; [exact H1|].
    eapply run_tbl_cat; [exact H2|].
    eapply run_tbl_cat; [exact H3|].
    eapply run_tbl_cat; [exact H4|].
    eapply run_tbl_cat; [exact H5|].
    replace (bl :: bl :: bl :: zeros d ++ L_bud) with (zeros (S (S (S d))) ++ L_bud) in H6 by reflexivity.
    replace (zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])
      with (zeros (S (S (zL' + zR))) ++ ones q ++ [bl; on]) in H6
      by (rewrite zeros_app, app_assoc; reflexivity).
    exact H6.
  - cbn [ones app hd tl] in H5.
    assert (H6 : TM.run Eps1Tape.tbl 1
      (mkConf 23 (bl :: bl :: zeros d ++ L_bud) on (ones blk' ++ bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])) =
      Some (mkConf 24 (on :: bl :: bl :: zeros d ++ L_bud)
              (hd bl (ones blk' ++ bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on]))
              (tl (ones blk' ++ bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on]))))
      by (rewrite TM.run_S; reflexivity).
    assert (H7 : TM.run Eps1Tape.tbl (S blk')
      (mkConf 24 (on :: bl :: bl :: zeros d ++ L_bud)
              (hd bl (ones blk' ++ bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on]))
              (tl (ones blk' ++ bl :: on :: zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on]))) =
      Some (mkConf S4 (bl :: ones (S blk') ++ bl :: bl :: zeros d ++ L_bud) on (zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on]))).
    { destruct blk' as [|blk''].
      - cbn [ones app hd tl]. rewrite TM.run_S. reflexivity.
      - cbn [ones app hd tl].
        pose proof (walk_S3_to_S4 blk'' (on :: bl :: bl :: zeros d ++ L_bud) (zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])) as Hs3.
        cbn [hd tl] in Hs3.
        replace (bl :: ones (S blk'') ++ on :: bl :: bl :: zeros d ++ L_bud)
          with (bl :: ones (S (S blk'')) ++ bl :: bl :: zeros d ++ L_bud) in Hs3
          by (rewrite <- ones_S_r, <- app_assoc; reflexivity).
        exact Hs3. }
    exists (S d), (zL' + zR), (S (S zL') + 1 + 1 + S (S blk') + 2 + 1 + S blk').
    eapply run_tbl_cat; [exact H1|].
    eapply run_tbl_cat; [exact H2|].
    eapply run_tbl_cat; [exact H3|].
    eapply run_tbl_cat; [exact H4|].
    eapply run_tbl_cat; [exact H5|].
    eapply run_tbl_cat; [exact H6|].
    replace (bl :: ones (S blk') ++ bl :: bl :: zeros d ++ L_bud)
      with (bl :: ones (S blk') ++ zeros (S (S d)) ++ L_bud) in H7 by reflexivity.
    replace (zeros (S (S zL')) ++ zeros zR ++ ones q ++ [bl; on])
      with (zeros (S (S (zL' + zR))) ++ ones q ++ [bl; on]) in H7
      by (rewrite zeros_app, app_assoc; reflexivity).
    exact H7.
Qed.

Lemma stage_F0_to_R0_tail1 : forall g w L_wall,
  exists z k_f0,
    TM.run Eps1Tape.tbl k_f0
      (mkConf S4 L_wall on (zeros (S (S g)) ++ ones (S w) ++ [bl; on])) =
    Some (mkConf 0 (zeros z ++ ones (S w) ++ on :: L_wall) bl [on; bl; on]).
Proof.
  intros g w L_wall.
  assert (Hs4 : TM.run Eps1Tape.tbl 1 (mkConf S4 L_wall on (zeros (S (S g)) ++ ones (S w) ++ [bl; on])) =
                Some (mkConf 12 (on :: L_wall) bl (zeros (S g) ++ ones (S w) ++ [bl; on])))
    by (rewrite TM.run_S, st_S4_on; reflexivity).
  assert (Hf_ind : forall k g0 L0,
    exists kf,
      TM.run Eps1Tape.tbl kf
        (mkConf 12 (on :: L0) bl (zeros g0 ++ ones (S k) ++ [bl; on])) =
      Some (mkConf 12 (ones k ++ on :: L0) bl (zeros g0 ++ [on; bl; on]))).
  { induction k as [|k IH]; intros g0 L0.
    - exists 0. reflexivity.
    - pose proof (walk_F0_bl g0 (on :: L0) (ones (S (S k)) ++ [bl; on])) as Hf0.
      cbn [ones app hd tl] in Hf0.
      assert (Hf0_on : TM.run Eps1Tape.tbl 1
        (mkConf 12 (zeros g0 ++ on :: L0) on (on :: ones k ++ [bl; on])) =
        Some (mkConf 13 (bl :: zeros g0 ++ on :: L0) on (ones k ++ [bl; on])))
        by (rewrite TM.run_S; reflexivity).
      assert (Hf1_on : TM.run Eps1Tape.tbl 1
        (mkConf 13 (bl :: zeros g0 ++ on :: L0) on (ones k ++ [bl; on])) =
        Some (mkConf 14 (zeros g0 ++ on :: L0) bl (on :: ones k ++ [bl; on])))
        by (rewrite TM.run_S; reflexivity).
      pose proof (walk_F2_bl_on g0 L0 (on :: ones k ++ [bl; on])) as Hf2.
      assert (Hf2_on : TM.run Eps1Tape.tbl 1
        (mkConf 14 L0 on (zeros (S g0) ++ on :: ones k ++ [bl; on])) =
        Some (mkConf 16 (on :: L0) bl (zeros g0 ++ on :: ones k ++ [bl; on])))
        by (rewrite TM.run_S; reflexivity).
      assert (Hf4_bl : TM.run Eps1Tape.tbl 1
        (mkConf 16 (on :: L0) bl (zeros g0 ++ on :: ones k ++ [bl; on])) =
        Some (mkConf 12 (on :: on :: L0) bl (zeros g0 ++ ones (S k) ++ [bl; on])))
        by (rewrite TM.run_S; reflexivity).
      destruct (IH g0 (on :: L0)) as [kf Hkf].
      exists (g0 + 1 + 1 + S g0 + 1 + 1 + kf).
      eapply run_tbl_cat; [exact Hf0|].
      eapply run_tbl_cat; [exact Hf0_on|].
      eapply run_tbl_cat; [exact Hf1_on|].
      eapply run_tbl_cat; [exact Hf2|].
      eapply run_tbl_cat; [exact Hf2_on|].
      eapply run_tbl_cat; [exact Hf4_bl|].
      replace (ones k ++ on :: on :: L0) with (ones (S k) ++ on :: L0) in Hkf
        by (rewrite <- ones_S_r, <- app_assoc; reflexivity).
      exact Hkf. }
  destruct (Hf_ind w (S g) L_wall) as [kf Hkf].
  pose proof (walk_F0_bl (S g) (ones w ++ on :: L_wall) [on; bl; on]) as Hf_last.
  cbn [hd tl] in Hf_last.
  assert (Hf_on : TM.run Eps1Tape.tbl 1
    (mkConf 12 (zeros (S g) ++ ones w ++ on :: L_wall) on [bl; on]) =
    Some (mkConf 13 (bl :: zeros (S g) ++ ones w ++ on :: L_wall) bl [on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hf1_bl : TM.run Eps1Tape.tbl 1
    (mkConf 13 (bl :: zeros (S g) ++ ones w ++ on :: L_wall) bl [on]) =
    Some (mkConf 15 (bl :: zeros (S g) ++ ones w ++ on :: L_wall) bl [bl; on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hsplit : exists L_f3, ones w ++ on :: L_wall = on :: L_f3 /\ on :: on :: L_f3 = ones (S w) ++ on :: L_wall).
  { destruct w as [|w']; [exists L_wall | exists (ones w' ++ on :: L_wall)]; split; reflexivity. }
  destruct Hsplit as [L_f3 [HLf3_1 HLf3_2]].
  rewrite HLf3_1 in Hf1_bl.
  replace (bl :: zeros (S g) ++ on :: L_f3) with (zeros (S (S g)) ++ on :: L_f3) in Hf1_bl by reflexivity.
  pose proof (walk_F3_bl_on (S (S g)) L_f3 [bl; on]) as Hf3.
  assert (Hf3_on : TM.run Eps1Tape.tbl 1
    (mkConf 15 L_f3 on (zeros (S (S (S g))) ++ [bl; on])) =
    Some (mkConf 17 (on :: L_f3) bl (zeros (S (S g)) ++ [bl; on])))
    by (rewrite TM.run_S; reflexivity).
  assert (Hf5_bl : TM.run Eps1Tape.tbl 1
    (mkConf 17 (on :: L_f3) bl (zeros (S (S g)) ++ [bl; on])) =
    Some (mkConf 18 (on :: on :: L_f3) bl (zeros (S (S g)) ++ [bl; on])))
    by (rewrite TM.run_S; reflexivity).
  rewrite HLf3_2 in Hf5_bl.
  replace (zeros (S (S g)) ++ [bl; on]) with (zeros (S (S (S g))) ++ [on]) in Hf5_bl
    by (rewrite <- !zeros_S_r, <- app_assoc; reflexivity).
  pose proof (walk_P0_bl (S (S (S g))) (ones (S w) ++ on :: L_wall) [on]) as Hp0.
  cbn [hd tl] in Hp0.
  assert (Hp0_on : TM.run Eps1Tape.tbl 1
    (mkConf 18 (zeros (S (S (S g))) ++ ones (S w) ++ on :: L_wall) on []) =
    Some (mkConf 19 (zeros (S (S g)) ++ ones (S w) ++ on :: L_wall) bl [on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hp1_bl : TM.run Eps1Tape.tbl 1
    (mkConf 19 (zeros (S (S g)) ++ ones (S w) ++ on :: L_wall) bl [on]) =
    Some (mkConf 20 (zeros (S g) ++ ones (S w) ++ on :: L_wall) bl [bl; on]))
    by (rewrite TM.run_S; reflexivity).
  assert (Hp2_bl : TM.run Eps1Tape.tbl 1
    (mkConf 20 (zeros (S g) ++ ones (S w) ++ on :: L_wall) bl [bl; on]) =
    Some (mkConf 0 (zeros g ++ ones (S w) ++ on :: L_wall) bl [on; bl; on]))
    by (rewrite TM.run_S; reflexivity).
  exists g, (1 + kf + S g + 1 + 1 + S (S (S g)) + 1 + 1 + S (S (S g)) + 1 + 1 + 1).
  eapply run_tbl_cat; [exact Hs4|].
  eapply run_tbl_cat; [exact Hkf|].
  eapply run_tbl_cat; [exact Hf_last|].
  eapply run_tbl_cat; [exact Hf_on|].
  eapply run_tbl_cat; [exact Hf1_bl|].
  eapply run_tbl_cat; [exact Hf3|].
  eapply run_tbl_cat; [exact Hf3_on|].
  eapply run_tbl_cat; [exact Hf5_bl|].
  eapply run_tbl_cat; [exact Hp0|].
  eapply run_tbl_cat; [exact Hp0_on|].
  eapply run_tbl_cat; [exact Hp1_bl|].
  exact Hp2_bl.
Qed.

Lemma eps0_stage_loop_tail1 : forall blk g w d L_bud,
  exists m' g' k_lp,
    TM.run Eps1Tape.tbl k_lp
      (mkConf S4 (bl :: ones (S blk) ++ zeros (S d) ++ L_bud) on
              (zeros (S (S g)) ++ ones (S w) ++ [bl; on])) =
    Some (mkConf ENTRY (zeros (S m') ++ L_bud) on
            (zeros (S (S g')) ++ ones (Eps1Ladder.run (S blk) (S w)) ++ [bl; on])).
Proof.
  induction blk as [|blk IH]; intros g w d L_bud.
  - destruct (stage_F0_to_R0_tail1 g w (bl :: ones 1 ++ zeros (S d) ++ L_bud)) as [z [k1 H1]].
    destruct (stage_K_loop (S w) z 0 1 (bl :: ones 1 ++ zeros (S d) ++ L_bud) ltac:(lia) ltac:(lia))
      as [zL' [zR' [k2 [Hz H2]]]].
    cbn [zeros app] in H2. rewrite iter_2p1_stage in H2.
    assert (Hst : 1 <= Eps1Ladder.stage (S w)) by (pose proof (Eps1Ladder.stage_ge (S w)); lia).
    destruct (stage_to_S_exit zL' zR' (Eps1Ladder.stage (S w)) 0 d L_bud Hz Hst) as [m' [g' [k3 H3]]].
    exists m', g', (k1 + k2 + k3).
    eapply run_tbl_cat; [exact H1|].
    eapply run_tbl_cat; [exact H2|].
    exact H3.
  - destruct (stage_F0_to_R0_tail1 g w (bl :: ones (S (S blk)) ++ zeros (S d) ++ L_bud)) as [z [k1 H1]].
    destruct (stage_K_loop (S w) z 0 1 (bl :: ones (S (S blk)) ++ zeros (S d) ++ L_bud) ltac:(lia) ltac:(lia))
      as [zL' [zR' [k2 [Hz H2]]]].
    cbn [zeros app] in H2. rewrite iter_2p1_stage in H2.
    assert (Hst : 1 <= Eps1Ladder.stage (S w)) by (pose proof (Eps1Ladder.stage_ge (S w)); lia).
    destruct (stage_to_S_exit zL' zR' (Eps1Ladder.stage (S w)) (S blk) d L_bud Hz Hst) as [m' [g' [k3 H3]]].
    destruct (Eps1Ladder.stage (S w)) as [|w'] eqn:Ew; [lia|].
    destruct (IH g' w' m' L_bud) as [m'' [g'' [k4 H4]]].
    exists m'', g'', (k1 + k2 + k3 + k4).
    eapply run_tbl_cat; [exact H1|].
    eapply run_tbl_cat; [exact H2|].
    eapply run_tbl_cat; [exact H3|].
    simpl (Eps1Ladder.run (S (S blk)) (S w)). rewrite Ew. exact H4.
Qed.

Lemma eps0_stage_loop : forall g w d L_bud,
  exists m' g' k_lp,
    TM.run Eps1Tape.tbl k_lp
      (mkConf S4 (bl :: ones (S w) ++ zeros (S d) ++ L_bud) on
              (zeros (S g) ++ ones (S w) ++ [bl; bl; on])) =
    Some (mkConf ENTRY (zeros (S m') ++ L_bud) on
            (zeros (S (S g')) ++ ones (Eps1Ladder.run (S w) (S w)) ++ [bl; on])).
Proof.
  intros g w d L_bud.
  destruct (stage_F0_to_R0 g w (bl :: ones (S w) ++ zeros (S d) ++ L_bud)) as [z [k1 H1]].
  destruct (stage_K_loop (S w) z 0 1 (bl :: ones (S w) ++ zeros (S d) ++ L_bud) ltac:(lia) ltac:(lia))
    as [zL' [zR' [k2 [Hz H2]]]].
  cbn [zeros app] in H2. rewrite iter_2p1_stage in H2.
  assert (Hst : 1 <= Eps1Ladder.stage (S w)) by (pose proof (Eps1Ladder.stage_ge (S w)); lia).
  destruct w as [|w'].
  - destruct (stage_to_S_exit zL' zR' (Eps1Ladder.stage 1) 0 d L_bud Hz Hst) as [m' [g' [k3 H3]]].
    exists m', g', (k1 + k2 + k3).
    eapply run_tbl_cat; [exact H1|].
    eapply run_tbl_cat; [exact H2|].
    exact H3.
  - destruct (stage_to_S_exit zL' zR' (Eps1Ladder.stage (S (S w'))) (S w') d L_bud Hz Hst) as [m' [g' [k3 H3]]].
    destruct (Eps1Ladder.stage (S (S w'))) as [|w_s] eqn:Ew; [lia|].
    destruct (eps0_stage_loop_tail1 w' g' w_s m' L_bud) as [m'' [g'' [k4 H4]]].
    exists m'', g'', (k1 + k2 + k3 + k4).
    eapply run_tbl_cat; [exact H1|].
    eapply run_tbl_cat; [exact H2|].
    eapply run_tbl_cat; [exact H3|].
    simpl (Eps1Ladder.run (S (S w')) (S (S w'))). rewrite Ew. exact H4.
Qed.

Fixpoint iter_diag (a v : nat) : nat :=
  match a with
  | 0 => v
  | S a' => Eps1Ladder.run (iter_diag a' v) (iter_diag a' v)
  end.

Lemma iter_diag_S_in : forall a v,
  iter_diag (S a) v = iter_diag a (Eps1Ladder.run v v).
Proof.
  induction a as [|a IH]; intro v; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma lvl_le_iter_diag : forall a v,
  Eps1Ladder.lvl a v <= iter_diag a v.
Proof.
  induction a as [|a IH]; intro v; simpl.
  - lia.
  - apply Nat.le_trans with (Eps1Ladder.run (iter_diag a v) v).
    + apply Eps1Ladder.run_mono_n. apply IH.
    + apply Eps1Ladder.run_mono_v. apply Eps1Ladder.lvl_ge.
Qed.

Theorem eps1_tbl_rung_halts : forall a m b0 g w,
  exists m' b' k_run cf,
    TM.run Eps1Tape.tbl k_run
      (mkConf ENTRY (zeros (S m) ++ ones (S a) ++ zeros b0) on
              (zeros (S (S g)) ++ ones (S w) ++ [bl; on])) = Some cf /    TM.halted Eps1Tape.tbl cf /    cf = mkConf G2 (zeros b') on (zeros (m' + 2) ++ ones (iter_diag a (S w)) ++ [bl; on]) /    Eps1Ladder.lvl a (S w) <= iter_diag a (S w) /    iter_diag a (S w) <= k_run.
Proof.
  induction a as [|a IH]; intros m b0 g w.
  - destruct (rung_halts_conf_gen m b0 (zeros (S (S g)) ++ ones (S w) ++ [bl; on]) eq_refl)
      as [cf [Hrun [Hhalt Heq]]].
    exists m, b0, (m + 3), cf.
    repeat split; try exact Hrun; try exact Hhalt; try exact Heq; simpl; lia.
  - set (V := zeros (S (S g)) ++ ones (S w) ++ [bl; on]).
    pose proof (rung_reaches_copy_gen m a b0 V eq_refl) as H1.
    unfold V in H1. cbn [zeros app tl] in H1.
    pose proof (copy_to_S4_g g m a b0 w) as H2.
    replace (S w + b0) with (S (w + b0)) in H2 by lia.
    destruct H2 as [k2 H2].
    destruct (eps0_stage_loop g w m (ones (S (S a)) ++ zeros (1 + b0))) as [m1 [g1 [k3 H3]]].
    replace (bl :: ones (S w) ++ bl :: zeros (S m) ++ ones (S (S a)) ++ zeros (1 + b0))
      with (bl :: ones (S w) ++ zeros (S (S m)) ++ ones (S (S a)) ++ zeros (1 + b0)) in H2
      by reflexivity.
    destruct (Eps1Ladder.run (S w) (S w)) as [|w_next] eqn:Ew.
    { pose proof (Eps1Ladder.run_ge (S w) (S w)) as Hge. lia. }
    destruct (IH m1 (1 + b0) g1 w_next) as [m' [b' [k4 [cf [H4 [Hhalt [Heq [_ Hk4]]]]]]]].
    exists m', b', (2 * m + 7 + k2 + k3 + k4), cf.
    repeat split.
    + eapply run_tbl_cat; [exact H1|].
      eapply run_tbl_cat; [exact H2|].
      eapply run_tbl_cat; [exact H3|].
      exact H4.
    + exact Hhalt.
    + rewrite iter_diag_S_in, Ew. exact Heq.
    + apply lvl_le_iter_diag.
    + rewrite iter_diag_S_in, Ew. lia.
Qed.

(** * 6. Parametric Blank-Tape FGH Machine btbl_eps1 *)

Definition btbl_eps1 (a : nat) : TM.table := fun s b =>
  if Nat.ltb s (S a) then
    match b with
    | bl => Some (on, true, S s)
    | on => None
    end
  else if Nat.eqb s (S a) then
    match b with bl => Some (bl, true, a + 2) | on => None end
  else if Nat.eqb s (a + 2) then
    match b with bl => Some (on, true, a + 3) | on => None end
  else if Nat.eqb s (a + 3) then
    match b with bl => Some (bl, true, a + 4) | on => None end
  else if Nat.eqb s (a + 4) then
    match b with bl => Some (bl, true, a + 5) | on => None end
  else if Nat.eqb s (a + 5) then
    match b with bl => Some (on, true, a + 6) | on => None end
  else if Nat.eqb s (a + 6) then
    match b with bl => Some (bl, true, a + 7) | on => None end
  else if Nat.eqb s (a + 7) then
    match b with bl => Some (on, false, a + 8) | on => None end
  else if Nat.eqb s (a + 8) then
    match b with bl => Some (bl, false, a + 9) | on => None end
  else if Nat.eqb s (a + 9) then
    match b with on => Some (on, false, a + 10) | bl => None end
  else if Nat.eqb s (a + 10) then
    match b with bl => Some (bl, false, a + 11) | on => None end
  else if Nat.eqb s (a + 11) then
    match b with bl => Some (bl, false, a + 12) | on => None end
  else if Nat.eqb s (a + 12) then
    match b with bl => Some (bl, false, (a + 13) + ENTRY) | on => None end
  else
    match Eps1Tape.tbl (s - (a + 13)) b with
    | Some (w, d, ns) => Some (w, d, (a + 13) + ns)
    | None => None
    end.

Definition c0_eps1 : TM.conf := {| cst := 0; ccur := bl; clft := []; crgt := [] |}.

Definition shift_conf (off : nat) (c : TM.conf) : TM.conf :=
  {| cst := off + cst c; ccur := ccur c; clft := clft c; crgt := crgt c |}.

Lemma btbl_eps1_shift_step : forall a c c',
  TM.step Eps1Tape.tbl c = Some c' ->
  TM.step (btbl_eps1 a) (shift_conf (a + 13) c) = Some (shift_conf (a + 13) c').
Proof.
  intros a c c' H.
  unfold TM.step in *.
  change (cst (shift_conf (a + 13) c)) with (a + 13 + cst c).
  change (ccur (shift_conf (a + 13) c)) with (ccur c).
  unfold btbl_eps1.
  destruct (Nat.ltb_spec (a + 13 + cst c) (S a)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (S a)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 2)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 3)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 4)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 5)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 6)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 7)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 8)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 9)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 10)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 11)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 12)); [lia|].
  replace (a + 13 + cst c - (a + 13)) with (cst c) by lia.
  destruct (Eps1Tape.tbl (cst c) (ccur c)) as [[[w d] ns]|]; [|discriminate].
  injection H as <-. destruct d; reflexivity.
Qed.

Lemma btbl_eps1_shift_run : forall a k c c',
  TM.run Eps1Tape.tbl k c = Some c' ->
  TM.run (btbl_eps1 a) k (shift_conf (a + 13) c) = Some (shift_conf (a + 13) c').
Proof.
  intros a k. induction k as [|k IH]; intros c c' H.
  - injection H as <-. reflexivity.
  - rewrite TM.run_S in H |- *.
    destruct (TM.step Eps1Tape.tbl c) as [c1|] eqn:E; [|discriminate].
    rewrite (btbl_eps1_shift_step a c c1 E). apply IH. exact H.
Qed.

Lemma btbl_eps1_shift_halted : forall a c,
  TM.halted Eps1Tape.tbl c ->
  TM.halted (btbl_eps1 a) (shift_conf (a + 13) c).
Proof.
  intros a c H. unfold TM.halted in *.
  change (cst (shift_conf (a + 13) c)) with (a + 13 + cst c).
  change (ccur (shift_conf (a + 13) c)) with (ccur c).
  unfold btbl_eps1.
  destruct (Nat.ltb_spec (a + 13 + cst c) (S a)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (S a)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 2)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 3)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 4)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 5)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 6)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 7)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 8)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 9)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 10)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 11)); [lia|].
  destruct (Nat.eqb_spec (a + 13 + cst c) (a + 12)); [lia|].
  replace (a + 13 + cst c - (a + 13)) with (cst c) by lia.
  destruct (Eps1Tape.tbl (cst c) (ccur c)) as [[[w d] ns]|]; [discriminate | reflexivity].
Qed.

Lemma btbl_eps1_prologue_ones : forall a k L,
  k <= S a ->
  TM.run (btbl_eps1 a) k (mkConf 0 L bl []) =
  Some (mkConf k (ones k ++ L) bl []).
Proof.
  intros a k. induction k as [|k IH]; intros L Hk.
  - reflexivity.
  - replace (S k) with (k + 1) by lia.
    rewrite TM.run_add, (IH L ltac:(lia)).
    cbn [TM.run TM.step btbl_eps1].
    destruct (Nat.ltb_spec k (S a)); [|lia].
    rewrite ones_S_r, <- app_assoc. reflexivity.
Qed.

Ltac btbl_step :=
  rewrite TM.run_S; cbn [TM.step]; unfold btbl_eps1;
  repeat match goal with
  | |- context [Nat.ltb ?x ?y] =>
      let E := fresh in destruct (Nat.ltb_spec x y) as [E|E]; [lia|]
  | |- context [Nat.eqb ?x ?y] =>
      let E := fresh in destruct (Nat.eqb_spec x y) as [E|E]; [try lia|try lia]
  end; cbn [hd tl].

Lemma btbl_eps1_prologue : forall a,
  TM.run (btbl_eps1 a) (a + 13) c0_eps1 =
  Some (shift_conf (a + 13)
          (mkConf ENTRY (zeros 1 ++ ones (S a)) on (zeros 2 ++ ones 1 ++ [bl; on]))).
Proof.
  intro a.
  pose proof (btbl_eps1_prologue_ones a (S a) [] ltac:(lia)) as H0.
  rewrite app_nil_r in H0.
  assert (H1 : TM.run (btbl_eps1 a) 12 (mkConf (S a) (ones (S a)) bl []) =
    Some (shift_conf (a + 13)
            (mkConf ENTRY (zeros 1 ++ ones (S a)) on (zeros 2 ++ ones 1 ++ [bl; on])))).
  { do 12 btbl_step. reflexivity. }
  replace (a + 13) with (S a + 12) by lia.
  rewrite TM.run_add, H0. cbn. exact H1.
Qed.

Theorem eps1_blank_tape_halts : forall a,
  exists k_tot cf_fin,
    TM.run (btbl_eps1 a) k_tot c0_eps1 = Some cf_fin /    TM.halted (btbl_eps1 a) cf_fin /    Eps1Ladder.lvl a 1 <= TM.score cf_fin /    Eps1Ladder.lvl a 1 <= k_tot.
Proof.
  intro a.
  destruct (eps1_tbl_rung_halts a 0 0 0 0) as [m' [b' [k_run [cf [Hrun [Hhalt [Heq [Hlvl Hk]]]]]]]].
  exists (a + 13 + k_run), (shift_conf (a + 13) cf).
  repeat split.
  - rewrite TM.run_add, (btbl_eps1_prologue a). cbn.
    apply btbl_eps1_shift_run. exact Hrun.
  - apply btbl_eps1_shift_halted. exact Hhalt.
  - subst cf. cbn [shift_conf TM.score].
    rewrite !TM.count_on_app.
    assert (Hones : forall n, TM.count_on (ones n) = n)
      by (clear; induction n; simpl; [reflexivity | lia]).
    rewrite Hones. cbn [Eps1Ladder.lvl] in *. lia.
  - lia.
Qed.

(** Concrete instantiation for a = 1: halts at step 102 with score 5 (3 + 2) *)

Definition btbl_eps1_a1 : TM.table := btbl_eps1 1.

Definition cf_a1 : TM.conf := {|
  cst := 70;
  ccur := bl;
  clft := [];
  crgt := [bl; bl; bl; bl; on; bl; bl; bl; bl; on; on; on; bl; on]
|}.

Theorem eps1_a1_halts_at_102 :
  TM.run btbl_eps1_a1 102 c0_eps1 = Some cf_a1 /  TM.halted btbl_eps1_a1 cf_a1 /  TM.score cf_a1 = 5.
Proof.
  repeat split; [vm_compute; reflexivity | unfold TM.halted; vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Print Assumptions eps1_blank_tape_halts.
Print Assumptions eps1_a1_halts_at_102.
