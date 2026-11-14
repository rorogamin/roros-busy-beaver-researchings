(* The parametric round of the eps_0 drive.

   [Eps0Drive.round_v0] proves one round when the value has one mark.  This
   file proves the same round for an arbitrary value length: one counter mark
   is spent, the value v (with [v >= 1]) becomes [2 v + 1] marks, and the gap
   grows by [v + 2].

   The statement is exactly the one recorded as step 3d in
   FGH_MACHINES_PLAN.md, with [S v] written for the value length so that the
   phase lemmas' [ones (S v)] indices match.

   All phases are the existing parametric walk lemmas from Eps0Drive.v; only
   the assembly and the two arithmetical index rewrites at the A7/A8 boundary
   are new. *)

From Stdlib Require Import List Arith Lia.
From Top Require Import TM ModuleK Eps0Drive.
Import ListNotations.
Open Scope nat_scope.

Lemma zeros_app_assoc : forall a b L,
  zeros a ++ zeros b ++ L = zeros (a + b) ++ L.
Proof.
  intros a b L.
  rewrite app_assoc.
  rewrite <- zeros_app.
  reflexivity.
Qed.

Lemma zeros_shift : forall v m L,
  zeros v ++ bl :: zeros m ++ L = zeros (v + S m) ++ L.
Proof.
  intros v m L.
  rewrite zeros_succ.
  rewrite (zeros_app_assoc (S v) m L).
  replace (S v + m) with (v + S m) by lia.
  reflexivity.
Qed.

Lemma round_v : forall m v L,
  run dtbl (round_sum m v)
    (mkConf R1 (on :: L) on
            (on :: zeros m ++ ones (S v) ++ bl :: on :: [])) =
  Some (mkConf R1 L on
          (on :: zeros (m + S v + 2) ++ ones (2 * S v + 1) ++ bl :: on :: [])).
Proof.
  intros m v L.
  set (A := bl :: ones 2 ++ L).
  set (B := bl :: zeros m ++ ones 2 ++ L).
  set (E := mkConf R1 (on :: L) on
                   (on :: zeros m ++ ones (S v) ++ bl :: on :: [])).
  set (C1 := mkConf R2 (ones 2 ++ L) on
                    (zeros m ++ ones (S v) ++ bl :: on :: [])).
  set (C2 := mkConf R4 (bl :: ones 2 ++ L)
                   (hd bl (zeros m ++ ones (S v) ++ bl :: on :: []))
                   (tl (zeros m ++ ones (S v) ++ bl :: on :: []))).
  set (C3 := mkConf R5 (on :: zeros m ++ A)
                   (hd bl (ones v ++ bl :: on :: []))
                   (tl (ones v ++ bl :: on :: []))).
  set (C4 := mkConf R6 (ones v ++ zeros (S m) ++ ones 2 ++ L)
                   on (bl :: on :: [])).
  set (C5 := mkConf (SH + K2) (ones (S v) ++ zeros (S m) ++ ones 2 ++ L)
                   bl (on :: [])).
  set (C6 := mkConf A5 (bl :: zeros m ++ ones 2 ++ L)
                   bl (zeros (S v) ++ ones (S (S (S (2 * v)))))).
  set (C7 := mkConf A6 (on :: zeros (S (S v)) ++ B)
                   on (ones (S (2 * v)))).
  set (C8 := mkConf A7 (bl :: ones (S (S (2 * v))) ++ on ::
                        zeros (S (S v)) ++ B) bl []).
  set (C9 := mkConf A8 (ones (S (S (2 * v))) ++ on ::
                        zeros (S (S v)) ++ B) bl (on :: [])).
  set (C10 := mkConf A9
                   (ones (S (S (2 * v))) ++ zeros (S (S v)) ++ B)
                   on (bl :: on :: [])).
  set (C11 := mkConf AA
                    (zeros v ++ B)
                    bl (bl :: ones (2 * v + 3) ++ bl :: on :: [])).
  set (C12 := mkConf R1 L on
                    (on :: zeros (S (v + m) + 1) ++
                     bl :: ones (2 * v + 3) ++ bl :: on :: [])).

  assert (H1 : run dtbl 1 E = Some C1).
  { subst E C1. rewrite run_S, dR1_on. cbn. reflexivity. }
  assert (H2 : run dtbl 1 C1 = Some C2).
  { subst C1 C2. rewrite run_S, dR2_on. cbn. reflexivity. }
  assert (H3 : run dtbl (m + 1) C2 = Some C3).
  { subst C2 C3. apply walk_R4_phase. }

  assert (H4 : run dtbl (v + 1) C3 = Some C4).
  { destruct v as [|v'].
    - subst C3 C4.
      change (run dtbl 1
        (mkConf R5 (on :: zeros m ++ bl :: ones 2 ++ L) bl (on :: [])) =
        Some (mkConf R6 (zeros (S m) ++ ones 2 ++ L) on (bl :: on :: []))).
      rewrite walk_bl_R5, zeros_succ. cbn. reflexivity.
    - subst C3 C4.
      replace (S v' + 1) with (v' + 2) by lia.
      change (run dtbl (v' + 2)
        (mkConf R5 (on :: zeros m ++ bl :: ones 2 ++ L) on
                (ones v' ++ bl :: on :: [])) =
        Some (mkConf R6 (ones (S v') ++ zeros (S m) ++ ones 2 ++ L)
                on (bl :: on :: []))).
      rewrite (walk_on_R5 v' (on :: zeros m ++ bl :: ones 2 ++ L)
                 (on :: [])).
      rewrite ones_succ, zeros_succ. reflexivity. }

  assert (H5 : run dtbl 1 C4 = Some C5).
  { subst C4 C5. rewrite run_S, dR6_on. cbn. reflexivity. }

  assert (H6 : run dtbl (k_pre (S v) 0 0 + 1) C5 = Some C6).
  { subst C5 C6.
    change (run dtbl (k_pre (S v) 0 0 + 1)
      (mkConf (SH + K2) (ones (S v) ++ zeros (S m) ++ ones 2 ++ L) bl
              (zeros 0 ++ ones (S 0))) =
      Some (mkConf A5 (bl :: zeros m ++ ones 2 ++ L)
              bl (zeros (S v) ++ ones (S (S (S (2 * v))))))).
    rewrite (k_block_drive_exit v 0 0 m (ones 2 ++ L)).
    replace (0 + v + 2) with (S (S v)) by lia.
    rewrite hd_zeros, tl_zeros. cbn. reflexivity. }

  assert (H7 : run dtbl (v + 3) C6 = Some C7).
  { subst C6 C7.
    replace (v + 3) with (S v + 2) by lia.
    replace (S (S v)) with (S v + 1) by lia.
    apply walk_bl_A5. }

  assert (H8 : run dtbl (2 * v + 3) C7 = Some C8).
  { subst C7 C8.
    replace (2 * v + 3) with (S (2 * v) + 2) by lia.
    change (run dtbl (S (2 * v) + 2)
      (mkConf A6 (on :: zeros (S (S v)) ++ bl :: zeros m ++ ones 2 ++ L)
              on (ones (S (2 * v)))) =
      Some (mkConf A7
              (bl :: ones (S (S (2 * v))) ++
               on :: zeros (S (S v)) ++ bl :: zeros m ++ ones 2 ++ L) bl [])).
    rewrite (walk_on_A6 (S (2 * v))
              (on :: zeros (S (S v)) ++ bl :: zeros m ++ ones 2 ++ L)).
    replace (S (2 * v) + 1) with (S (S (2 * v))) by lia.
    reflexivity. }

  assert (H9 : run dtbl 1 C8 = Some C9).
  { subst C8 C9. rewrite run_S, dA7_bl. cbn. reflexivity. }

  assert (H10 : run dtbl 1 C9 = Some C10).
  { subst C9 C10. rewrite run_S, dA8_bl. cbn.
    rewrite ones_succ. reflexivity. }

  assert (H11 : run dtbl (2 * v + 4) C10 = Some C11).
  { subst C10 C11.
    replace (2 * v + 4) with (S (S (2 * v)) + 2) by lia.
    change (run dtbl (S (S (2 * v)) + 2)
      (mkConf A9
        (ones (S (S (2 * v))) ++ bl :: zeros (S v) ++ B)
        on (bl :: on :: [])) =
      Some (mkConf AA
              (zeros v ++ B) bl
              (bl :: ones (2 * v + 3) ++ bl :: on :: []))).
    rewrite (walk_A9 (S (S (2 * v)))
              (zeros (S v) ++ B)
              (bl :: on :: [])).
    unfold zeros.
    replace (S (S (2 * v)) + 1) with (2 * v + 3) by lia.
    reflexivity. }

  assert (H12 : run dtbl (v + m + 3) C11 = Some C12).
  { subst C11 C12. subst B.
    replace (v + m + 3) with (S (v + m) + 2) by lia.
    change (run dtbl (S (v + m) + 2)
      (mkConf AA (zeros v ++ bl :: zeros m ++ ones 2 ++ L) bl
              (bl :: ones (2 * v + 3) ++ bl :: on :: [])) =
      Some (mkConf R1 L on
              (on :: zeros (S (v + m) + 1) ++
               bl :: ones (2 * v + 3) ++ bl :: on :: []))).
    rewrite (zeros_shift v m (ones 2 ++ L)).
    replace (v + S m) with (S (v + m)) by lia.
    change (run dtbl (S (v + m) + 2)
      (mkConf AA (zeros (S (v + m)) ++ on :: ones 1 ++ L) bl
              (bl :: ones (2 * v + 3) ++ bl :: on :: [])) =
      Some (mkConf R1 L on
              (on :: zeros (S (v + m) + 1) ++
               bl :: ones (2 * v + 3) ++ bl :: on :: []))).
    rewrite (walk_AA (S (v + m)) (ones 1 ++ L)
              (bl :: ones (2 * v + 3) ++ bl :: on :: [])).
    reflexivity. }

  pose proof (run_cat_d 1 1 E C1 C2 H1 H2) as H12_.
  pose proof (run_cat_d (1 + 1) (m + 1) E C2 C3 H12_ H3) as H123.
  pose proof (run_cat_d (1 + 1 + (m + 1)) (v + 1) E C3 C4 H123 H4) as H1234.
  pose proof (run_cat_d (1 + 1 + (m + 1) + (v + 1)) 1 E C4 C5 H1234 H5) as H12345.
  pose proof (run_cat_d (1 + 1 + (m + 1) + (v + 1) + 1)
                (k_pre (S v) 0 0 + 1) E C5 C6 H12345 H6) as H123456.
  pose proof (run_cat_d (1 + 1 + (m + 1) + (v + 1) + 1 +
                         (k_pre (S v) 0 0 + 1)) (v + 3) E C6 C7 H123456 H7) as H7'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + (v + 1) + 1 +
                         (k_pre (S v) 0 0 + 1) + (v + 3))
                (2 * v + 3) E C7 C8 H7' H8) as H8'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + (v + 1) + 1 +
                         (k_pre (S v) 0 0 + 1) + (v + 3) + (2 * v + 3))
                1 E C8 C9 H8' H9) as H9'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + (v + 1) + 1 +
                         (k_pre (S v) 0 0 + 1) + (v + 3) + (2 * v + 3) + 1)
                1 E C9 C10 H9' H10) as H10'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + (v + 1) + 1 +
                         (k_pre (S v) 0 0 + 1) + (v + 3) + (2 * v + 3) + 1 + 1)
                (2 * v + 4) E C10 C11 H10' H11) as H11'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + (v + 1) + 1 +
                         (k_pre (S v) 0 0 + 1) + (v + 3) + (2 * v + 3) + 1 + 1 +
                         (2 * v + 4))
                (v + m + 3) E C11 C12 H11' H12) as H12''.

  subst E C12.
  replace (on :: zeros (S (v + m) + 1) ++ bl :: ones (2 * v + 3) ++
           bl :: on :: [])
    with (on :: zeros (m + S v + 2) ++ ones (2 * S v + 1) ++
          bl :: on :: []) in H12''
    by (replace (S (v + m) + 1) with (S (S (v + m))) by lia;
        rewrite zeros_succ;
        replace (S (S (S (v + m)))) with (m + S v + 2) by lia;
        replace (2 * v + 3) with (2 * S v + 1) by lia;
        reflexivity).
  replace (round_sum m v)
    with (1 + 1 + (m + 1) + (v + 1) + 1 +
          (k_pre (S v) 0 0 + 1) + (v + 3) + (2 * v + 3) + 1 + 1 +
          (2 * v + 4) + (v + m + 3))
    by (unfold round_sum; lia).
  exact H12''.
Qed.

Print Assumptions round_v.
