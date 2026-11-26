From Stdlib Require Import Arith Lia.

(** Holdout #758: the J-phase length bound.

    In U(u,d) coordinates e = u - 2*d.  A j step sends
    (u,d) -> (u+2, 3*d-u+1), hence e -> 3*e.  While the phase continues
    d <= (u-1)/2, so e <= u/3.  After n steps:

      3^n * e <= u + 2*n.

    With u <= 2^465 and e >= 1 this gives n <= 465. *)

Definition JIter (n e : nat) : nat := 3^n * e.

Lemma JIter_zero (e:nat) : JIter 0 e = e.
Proof. unfold JIter. rewrite Nat.pow_0_r. lia. Qed.

Lemma JIter_succ (n e:nat) : JIter (S n) e = 3 * JIter n e.
Proof.
  unfold JIter. rewrite Nat.pow_succ_r'.
  replace (3 * (3^n * e)) with (3 * 3^n * e) by ring.
  reflexivity.
Qed.

Lemma add_diag_mul2 (x:nat) : x + x = x * 2.
Proof. induction x as [|x IH]; simpl; lia. Qed.

Lemma nine32_lt_1024 : 932 < 1024.
Proof. lia. Qed.

Lemma two_pow_gt_1024 : 1024 <= 2^465.
Proof.
  change (2^10 <= 2^465).
  apply Nat.pow_le_mono_r; [discriminate|lia].
Qed.

Lemma nine32_lt_two_pow : 932 < 2^465.
Proof. apply Nat.lt_le_trans with 1024; [exact nine32_lt_1024|exact two_pow_gt_1024]. Qed.

Lemma two_pow_465_add : 2^465 + 932 < 2^466.
Proof.
  assert (hadd : 2^465 + 932 < 2^465 + 2^465)
    by (apply Nat.add_lt_mono_l; exact nine32_lt_two_pow).
  assert (hdouble : 2^465 + 2^465 = 2^466).
  { transitivity (2^465 * 2).
    - apply add_diag_mul2.
    - rewrite Nat.mul_comm. symmetry. apply Nat.pow_succ_r'. }
  rewrite <- hdouble. exact hadd.
Qed.

Lemma two_pow_lt_three_pow : 2^466 < 3^466.
Proof. apply Nat.pow_lt_mono_l; [discriminate|lia]. Qed.

Lemma three_pow_gt_linear (n:nat) (hn:466<=n) :
  2^465 + 2*n < 3^n.
Proof.
  induction n as [|n IH].
  - lia.
  - destruct (Nat.leb 466 n) eqn:E.
    + apply Nat.leb_le in E.
      specialize (IH E).
      replace (2 * S n) with (2*n + 2) by lia.
      assert (h3 : 3 <= 3^n).
      { change (3^1 <= 3^n). apply Nat.pow_le_mono_r; [discriminate|lia]. }
      replace (3^S n) with (3 * 3^n) by (symmetry; apply Nat.pow_succ_r').
      replace (3 * 3^n) with (3^n + 3^n + 3^n) by ring.
      set (x := 3^n).
      set (y := 2^465).
      change (y + (2*n + 2) < x + x + x).
      fold x in IH. fold x in h3. fold y in IH.
      lia.
    + apply Nat.leb_gt in E.
      assert (n = 465) by lia. subst n.
      change (2^465 + 932 < 3^466).
      apply Nat.lt_trans with (2^466);
        [exact two_pow_465_add|exact two_pow_lt_three_pow].
Qed.

Lemma J_phase_length_le_465 (n e u:nat) (he:1<=e) (hu:u<=2^465)
  (hcont:3^n * e <= u + 2*n) : n<=465.
Proof.
  assert (Hnot : ~ 466 <= n).
  { intro hn.
    pose proof (three_pow_gt_linear n hn) as hlin.
    assert (hpow:3^n <= 3^n * e) by nia.
    assert (hle:3^n <= u + 2*n) by lia.
    assert (hle':3^n <= 2^465 + 2*n) by lia.
    assert (hbad : 3^n < 3^n) by lia.
    exact (Nat.lt_irrefl (3^n) hbad). }
  lia.
Qed.

Print Assumptions J_phase_length_le_465.
