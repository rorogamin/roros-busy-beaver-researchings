module

public import RequestProject.Halt.Feed

/-!
# Correctness of the engine, part 4: the eventually periodic level words

`pwUpTo_spec`: if the engine computes `pwUpTo q = some w`, then for every `k`
the level word of cell `q` for the arrival prefix `word (1 + 5 * (w.a + w.b * k))` is
the prefix `pwX w` followed by `k` copies of the period `pwY w`.
-/

@[expose] public section

namespace BCM.Eng

open HaltEngine

/-- `k` copies of `Y`. -/
def rep {α : Type} (Y : List α) : Nat → List α
  | 0 => []
  | k + 1 => Y ++ rep Y k

theorem rep_add {α : Type} (Y : List α) (m n : Nat) : rep Y (m + n) = rep Y m ++ rep Y n := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [show m + 1 + n = (m + n) + 1 by omega, rep, rep, ih, List.append_assoc]

theorem rep_succ' {α : Type} (Y : List α) (k : Nat) : rep Y (k + 1) = rep Y k ++ Y := by
  rw [rep_add]; simp [rep]

theorem rep_two_mul {α : Type} (Y : List α) (k : Nat) : rep Y (2 * k) = rep (Y ++ Y) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, rep, rep, rep, ih, List.append_assoc]

theorem map_ofB_toB (l : List St) : (l.map toB).map ofB = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- Initial cell states, decoded: every cell starts blank. -/
theorem initD_eq (p : Nat) :
    dec (initSt p) = (hdz (([] : List Sym).drop p), nbr (([] : List Sym).drop p)) := by
  rw [List.drop_nil]; unfold initSt; decide

theorem lev_step (xs : List St) (p : Nat) :
    lev [] xs (p + 1) = cellOut (dec (initSt p)).1 (dec (initSt p)).2 (lev [] xs p) := by
  rw [lev_succ', initD_eq]

theorem cellOut_rep {s : Sym × Bool} {Y : List St} (h : cellEnd s.1 s.2 Y = some s) :
    ∀ k, cellOut s.1 s.2 (rep Y k) = rep (cellOut s.1 s.2 Y) k ∧
      cellEnd s.1 s.2 (rep Y k) = some s := by
  intro k
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [rep, rep, cellOut_append_of_end _ _ _ _ _ _ h, ih.1, cellEnd_append _ _ _ _ _ _ h, ih.2]
    exact ⟨rfl, rfl⟩

/-- The period of the arrival stream. -/
def Y0 : List St := [.B, .A, .B, .A, .B]

theorem word_five (k : Nat) : word (1 + 5 * k) = [.A] ++ rep Y0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rep_succ', ← List.append_assoc, ← ih, show 1 + 5 * (k + 1) = 1 + 5 * k + 4 + 1 by omega]
    simp only [word_succ, List.append_assoc]
    have e : ∀ r, r < 5 → (5 * k + r) % 5 = r := fun r hr => by omega
    have e0 : (5 * k) % 5 = 0 := by omega
    rw [show 1 + 5 * k + 3 + 1 = 1 + 5 * k + 4 by omega]
    simp only [inSt, show 1 + 5 * k = (5 * k) + 1 by omega,
      e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e0]
    rfl

/-- The letters of the prefix and of the period of a `PW`. -/
def pwX (w : PW) : List St := (rd w.x 0 w.nx).map ofB
def pwY (w : PW) : List St := (rd w.y 0 w.ny).map ofB

/-- `w` describes the level word of cell `q`. -/
def PWGood (q : Nat) (w : PW) : Prop :=
  ∀ k, lev [] (word (1 + 5 * (w.a + w.b * k))) q = pwX w ++ rep (pwY w) k

theorem pw0_good : PWGood 0 pw0 := by
  intro k
  have hY : pwY pw0 = Y0 := by decide
  have hX : pwX pw0 = [.A] := by decide
  rw [hX, hY, show pw0.a + pw0.b * k = k by simp [pw0]]
  exact word_five k

theorem feedRep_spec (y : ByteArray) (ny : Nat) : ∀ r st a, st.toNat < 10 → AccValid a →
    FeedOK (dec st) (rep ((rd y 0 ny).map ofB) r) a (feedRep y ny r st a) := by
  intro r
  induction r with
  | zero => intro st a hst ha; exact FeedOK_nil st a hst ha
  | succ r ih =>
    intro st a hst ha
    simp only [feedRep, rep]
    have hf := feed_spec y 0 ny st a hst ha
    revert hf
    cases feed y 0 ny st a with
    | ok st' a' =>
      intro hf
      obtain ⟨h1, h2, h3, h4⟩ := hf
      exact FeedOK_append h2 h4 (ih st' a' h1 h3)
    | halt q => intro hf; exact FeedOK_halt hf.1 hf.2

/-- Read back a closed accumulator. -/
theorem close_letters (a : Acc) (ha : AccValid a) (l : List St) (h : accBits a = [] ++ l.map toB) :
    (rd a.close.1 0 a.close.2).map ofB = l := by
  rw [close_spec a ha, h, List.nil_append, map_ofB_toB]


theorem initSt_lt (p : Nat) : (initSt p).toNat < 10 := by
  unfold initSt; decide

theorem good_of (q : Nat) (w v : PW) (r m : Nat) (s1 : Sym × Bool) (Yb : List St)
    (hw : PWGood q w) (hA : v.a = w.a + r * w.b) (hB : v.b = m * w.b)
    (hYb : ∀ k, rep (pwY w) (m * k) = rep Yb k)
    (hEnd : cellEnd (dec (initSt q)).1 (dec (initSt q)).2 (pwX w ++ rep (pwY w) r) = some s1)
    (hcyc : cellEnd s1.1 s1.2 Yb = some s1)
    (hX : pwX v = cellOut (dec (initSt q)).1 (dec (initSt q)).2 (pwX w ++ rep (pwY w) r))
    (hY : pwY v = cellOut s1.1 s1.2 Yb) : PWGood (q + 1) v := by
  intro k
  rw [lev_step, hA, hB]
  have e : 1 + 5 * (w.a + r * w.b + m * w.b * k) = 1 + 5 * (w.a + w.b * (r + m * k)) := by
    rw [Nat.mul_add w.b, Nat.mul_comm r w.b, Nat.mul_assoc, Nat.mul_left_comm m w.b k, Nat.add_assoc]
  rw [e, hw (r + m * k), rep_add, hYb, ← List.append_assoc,
    cellOut_append_of_end _ _ _ _ _ _ hEnd, (cellOut_rep hcyc k).1, hX, hY]

theorem tryStep_spec (q : Nat) (w v : PW) (r : Nat) (hw : PWGood q w)
    (h : w.tryStep (initSt q) r = some v) : PWGood (q + 1) v := by
  have hst := initSt_lt q
  obtain ⟨fv1, fb1⟩ := fresh_spec (w.nx / 8 + 64)
  obtain ⟨fv2, fb2⟩ := fresh_spec (w.ny / 4 + 64)
  unfold PW.tryStep at h
  split at h
  · cases h
  next s0 a0 e0 =>
  have f0 := feed_spec w.x 0 w.nx (initSt q) _ hst fv1
  rw [e0] at f0
  obtain ⟨g1, g2, g3, g4⟩ := f0
  split at h
  · cases h
  next s1 ax e1 =>
  have f1 := feedRep_spec w.y w.ny r s0 a0 g1 g3
  rw [e1] at f1
  have fx := FeedOK_append g2 g4 f1
  obtain ⟨x1, x2, x3, x4⟩ := fx
  rw [fb1] at x4
  split at h
  · cases h
  next s2 ay e2 =>
  have f2 := feed_spec w.y 0 w.ny s1 _ x1 fv2
  rw [e2] at f2
  have hX : pwX ⟨ax.close.1, ax.close.2, ay.close.1, ay.close.2, 0, 0⟩ =
      cellOut (dec (initSt q)).1 (dec (initSt q)).2 (pwX w ++ rep (pwY w) r) :=
    close_letters ax x3 _ x4
  obtain ⟨y1, y2, y3, y4⟩ := f2
  rw [fb2] at y4
  have hX' : cellOut (dec (initSt q)).1 (dec (initSt q)).2 (pwX w ++ rep (pwY w) r) =
      (rd ax.close.1 0 ax.close.2).map ofB := hX.symm
  split at h
  next hs =>
    have hs' : s2 = s1 := by simpa using hs
    rw [hs'] at y2
    have hY : (rd ay.close.1 0 ay.close.2).map ofB =
        cellOut (dec s1).1 (dec s1).2 (pwY w) := close_letters ay y3 _ y4
    generalize ax.close = cx at h hX'
    generalize ay.close = cy at h hY
    obtain ⟨x', nx'⟩ := cx
    obtain ⟨y', ny'⟩ := cy
    simp only [Option.some.injEq] at h
    subst h
    exact good_of q w _ r 1 (dec s1) (pwY w) hw rfl (Nat.one_mul _).symm
      (fun k => by rw [Nat.one_mul]) x2 y2 hX'.symm hY
  next hs =>
  split at h
  · cases h
  next s3 ay2 e3 =>
  have f3 := feed_spec w.y 0 w.ny s2 ay y1 y3
  rw [e3] at f3
  have f23 := FeedOK_append (a := Acc.fresh (w.ny / 4 + 64)) y2 (by rw [y4, fb2]) f3
  obtain ⟨z1, z2, z3, z4⟩ := f23
  split at h
  next hs3 =>
    have hs' : s3 = s1 := by simpa using hs3
    rw [hs'] at z2
    have hY : (rd ay2.close.1 0 ay2.close.2).map ofB =
        cellOut (dec s1).1 (dec s1).2 (pwY w ++ pwY w) := close_letters ay2 z3 _ z4
    generalize ax.close = cx at h hX'
    generalize ay2.close = cy at h hY
    obtain ⟨x', nx'⟩ := cx
    obtain ⟨y', ny'⟩ := cy
    simp only [Option.some.injEq] at h
    subst h
    exact good_of q w _ r 2 (dec s1) (pwY w ++ pwY w) hw rfl rfl
      (fun k => rep_two_mul _ k) x2 z2 hX'.symm hY
  · cases h


theorem step_spec (q : Nat) (w v : PW) (hw : PWGood q w) (h : w.step (initSt q) = some v) :
    PWGood (q + 1) v := by
  unfold PW.step at h
  split at h
  · next v' e => cases h; exact tryStep_spec q w _ 0 hw e
  split at h
  · next v' e => cases h; exact tryStep_spec q w _ 1 hw e
  exact tryStep_spec q w _ 2 hw h

theorem pwUpTo_spec : ∀ q w, pwUpTo q = some w → PWGood q w := by
  intro q
  induction q with
  | zero => intro w h; cases h; exact pw0_good
  | succ q ih =>
    intro w h
    simp only [pwUpTo] at h
    split at h
    · cases h
    · next w' e => exact step_spec q w' w (ih w' e) h

end BCM.Eng
