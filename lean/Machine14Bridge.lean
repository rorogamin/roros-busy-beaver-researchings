import Machine14TwoSided

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace M14

/-- Raw encoding of a left block. -/
def encL : LTok → List Nat
  | .L => [1, 1]
  | .U => [0, 1]
  | .W => [1, 1]
  | .F => [0, 3]
  | .Y => [0, 3, 1]
  | .Q => [1]

/-- Raw encoding of a right block. -/
def encR : RTok → List Nat
  | .R => [1]
  | .X => [1, 4, 2]
  | .V => [2, 2]
  | .C => [1, 4]
  | .C1 => [2, 4]
  | .C2 => [2, 1]
  | .P => [2]

/-- Raw encoding of a nearest-first right block list. -/
def encRs (r : List RTok) : List Nat := r.flatMap encR

/-- Raw cells strictly left of the head, nearest-first. -/
def rawLeft (s : BState) : List Nat :=
  s.left.flatMap (fun t => (encL t).reverse)

/-- The deterministic raw encoding of a block state.

The boundary gap is `0` for `<` and `>`, and `1` for `w>`.  The latter gap
is the blank immediately left of the first right block. -/
def rawOf (s : BState) : RState :=
  match s.head with
  | .l => ⟨0, (rawLeft s).tail, (rawLeft s).headD 0, encRs s.right⟩
  | .r => ⟨0, rawLeft s, (encRs s.right).headD 0, (encRs s.right).tail⟩
  | .wr => ⟨1, 0 :: rawLeft s, (encRs s.right).headD 0, (encRs s.right).tail⟩

/-- Exactly `n` raw steps. -/
def rawRunK : Nat → RState → Option RState
  | 0, c => some c
  | n + 1, c => (rawRunK n c).bind rawStep

/-! ## The 19 local macro rules -/

theorem raw_lt_L (c : RTok) (cs : List RTok) :
    rawRunK 5 (rawOf ⟨.l, [.L], c :: cs⟩) =
      some (rawOf ⟨.wr, [.L], c :: cs⟩) := by
  cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_lt_U (y : LTok) (ys : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 3 (rawOf ⟨.l, .U :: y :: ys, c :: cs⟩) =
      some (rawOf ⟨.r, .W :: y :: ys, c :: cs⟩) := by
  cases y <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_lt_W (y : LTok) (ys : List LTok) (r : List RTok) :
    rawRunK 2 (rawOf ⟨.l, .W :: y :: ys, r⟩) =
      some (rawOf ⟨.l, y :: ys, .V :: r⟩) := by
  cases y <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_lt_F (y : LTok) (ys : List LTok) (r : List RTok) :
    rawRunK 2 (rawOf ⟨.l, .F :: y :: ys, r⟩) =
      some (rawOf ⟨.l, y :: ys, .C :: r⟩) := by
  cases y <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_lt_Y (y : LTok) (ys : List LTok) (r : List RTok) :
    rawRunK 3 (rawOf ⟨.l, .Y :: y :: ys, r⟩) =
      some (rawOf ⟨.l, y :: ys, .X :: r⟩) := by
  cases y <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_lt_Q (y : LTok) (ys : List LTok) (r : List RTok) :
    rawRunK 1 (rawOf ⟨.l, .Q :: y :: ys, r⟩) =
      some (rawOf ⟨.l, y :: ys, .P :: r⟩) := by
  cases y <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_gt_X (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 1 (rawOf ⟨.r, a :: as, .X :: c :: cs⟩) =
      some (rawOf ⟨.l, a :: as, .C1 :: .P :: c :: cs⟩) := by
  cases a <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_gt_V (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 2 (rawOf ⟨.r, a :: as, .V :: c :: cs⟩) =
      some (rawOf ⟨.r, .U :: a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_gt_C (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 1 (rawOf ⟨.r, a :: as, .C :: c :: cs⟩) =
      some (rawOf ⟨.l, a :: as, .C1 :: c :: cs⟩) := by
  cases a <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_gt_C1 (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 5 (rawOf ⟨.r, a :: as, .C1 :: c :: cs⟩) =
      some (rawOf ⟨.l, a :: as, .C2 :: c :: cs⟩) := by
  cases a <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_gt_C2 (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 2 (rawOf ⟨.r, a :: as, .C2 :: c :: cs⟩) =
      some (rawOf ⟨.r, .F :: a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_gt_P (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 1 (rawOf ⟨.r, a :: as, .P :: c :: cs⟩) =
      some (rawOf ⟨.wr, a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_wr_R (a : LTok) (as : List LTok) :
    rawRunK 6 (rawOf ⟨.wr, a :: as, [.R]⟩) =
      some (rawOf ⟨.l, a :: as, .X :: [.R]⟩) := by
  cases a <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_wr_X (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 3 (rawOf ⟨.wr, a :: as, .X :: c :: cs⟩) =
      some (rawOf ⟨.wr, .Y :: a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_wr_V (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 2 (rawOf ⟨.wr, a :: as, .V :: c :: cs⟩) =
      some (rawOf ⟨.wr, .U :: a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_wr_C (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 2 (rawOf ⟨.wr, a :: as, .C :: c :: cs⟩) =
      some (rawOf ⟨.r, .Q :: .F :: a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_wr_C1 (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 2 (rawOf ⟨.wr, a :: as, .C1 :: c :: cs⟩) =
      some (rawOf ⟨.r, .Q :: .U :: a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_wr_C2 (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 6 (rawOf ⟨.wr, a :: as, .C2 :: c :: cs⟩) =
      some (rawOf ⟨.wr, .W :: a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

theorem raw_wr_P (a : LTok) (as : List LTok) (c : RTok) (cs : List RTok) :
    rawRunK 1 (rawOf ⟨.wr, a :: as, .P :: c :: cs⟩) =
      some (rawOf ⟨.r, .U :: a :: as, c :: cs⟩) := by
  cases a <;> cases c <;>
    simp [rawRunK, rawOf, rawLeft, encL, encRs, encR, rawStep, RState.wL,
      RState.wR]

/-- A nonempty left word has a first block. -/
theorem LeftOK.exists_cons {l : List LTok} (h : LeftOK l) :
    ∃ a as, l = a :: as := by
  cases h with
  | nilL => exact ⟨LTok.L, [], rfl⟩
  | cons hx h => exact ⟨_, _, rfl⟩

/-- A nonempty right word has a first block. -/
theorem RightOK.exists_cons {r : List RTok} (h : RightOK r) :
    ∃ a as, r = a :: as := by
  cases h with
  | nilR => exact ⟨RTok.R, [], rfl⟩
  | cons hx h => exact ⟨_, _, rfl⟩

/-- The deterministic encoding starts at the raw `L U Q < R` state. -/
theorem rawOf_init : rawOf initB = initRaw := by
  decide

/-- Inversion for the left language: either the far-end singleton or a block
followed by a shorter left word. -/
theorem LeftOK.cases_cons {l : List LTok} (h : LeftOK l) :
    l = [LTok.L] ∨
      ∃ x l', x ≠ LTok.L ∧ LeftOK l' ∧ l = x :: l' := by
  cases h with
  | nilL => exact Or.inl rfl
  | cons hx hl => exact Or.inr ⟨_, _, hx, hl, rfl⟩

/-- Inversion for the right language: either the far-end singleton or a block
followed by a shorter right word. -/
theorem RightOK.cases_cons {r : List RTok} (h : RightOK r) :
    r = [RTok.R] ∨
      ∃ x r', x ≠ RTok.R ∧ RightOK r' ∧ r = x :: r' := by
  cases h with
  | nilR => exact Or.inl rfl
  | cons hx hr => exact Or.inr ⟨_, _, hx, hr, rfl⟩

/-- Every defined block step is implemented by a raw macro of at most six
steps, and the deterministic encoding is preserved exactly. -/
theorem rawOf_stepB {s s' : BState} (h : Inv2 s)
    (hs : stepB s = some s') :
    ∃ k, k ≤ 6 ∧ rawRunK k (rawOf s) = some (rawOf s') := by
  rcases s with ⟨head, left, right⟩
  rcases h with ⟨hL, hR⟩
  cases head with
  | l =>
      rcases LeftOK.cases_cons hL with rfl | ⟨x, rest, hx, hrest, rfl⟩
      · rcases RightOK.exists_cons hR with ⟨c, cs, rfl⟩
        simp [stepB] at hs
        subst s'
        exact ⟨5, by decide, raw_lt_L c cs⟩
      · rcases LeftOK.exists_cons hrest with ⟨y, ys, rfl⟩
        cases x with
        | L => exact (hx rfl).elim
        | U =>
            rcases RightOK.exists_cons hR with ⟨c, cs, rfl⟩
            simp [stepB] at hs
            subst s'
            exact ⟨3, by decide, raw_lt_U y ys c cs⟩
        | W =>
            simp [stepB] at hs
            subst s'
            exact ⟨2, by decide, raw_lt_W y ys right⟩
        | F =>
            simp [stepB] at hs
            subst s'
            exact ⟨2, by decide, raw_lt_F y ys right⟩
        | Y =>
            simp [stepB] at hs
            subst s'
            exact ⟨3, by decide, raw_lt_Y y ys right⟩
        | Q =>
            simp [stepB] at hs
            subst s'
            exact ⟨1, by decide, raw_lt_Q y ys right⟩
  | r =>
      rcases LeftOK.exists_cons hL with ⟨a, as, rfl⟩
      rcases RightOK.cases_cons hR with rfl | ⟨x, rest, hx, hrest, rfl⟩
      · simp [stepB] at hs
      · rcases RightOK.exists_cons hrest with ⟨c, cs, rfl⟩
        cases x with
        | R => exact (hx rfl).elim
        | X =>
            simp [stepB] at hs
            subst s'
            exact ⟨1, by decide, raw_gt_X a as c cs⟩
        | V =>
            simp [stepB] at hs
            subst s'
            exact ⟨2, by decide, raw_gt_V a as c cs⟩
        | C =>
            simp [stepB] at hs
            subst s'
            exact ⟨1, by decide, raw_gt_C a as c cs⟩
        | C1 =>
            simp [stepB] at hs
            subst s'
            exact ⟨5, by decide, raw_gt_C1 a as c cs⟩
        | C2 =>
            simp [stepB] at hs
            subst s'
            exact ⟨2, by decide, raw_gt_C2 a as c cs⟩
        | P =>
            simp [stepB] at hs
            subst s'
            exact ⟨1, by decide, raw_gt_P a as c cs⟩
  | wr =>
      rcases LeftOK.exists_cons hL with ⟨a, as, rfl⟩
      rcases RightOK.cases_cons hR with rfl | ⟨x, rest, hx, hrest, rfl⟩
      · simp [stepB] at hs
        subst s'
        exact ⟨6, by decide, raw_wr_R a as⟩
      · rcases RightOK.exists_cons hrest with ⟨c, cs, rfl⟩
        cases x with
        | R => exact (hx rfl).elim
        | X =>
            simp [stepB] at hs
            subst s'
            exact ⟨3, by decide, raw_wr_X a as c cs⟩
        | V =>
            simp [stepB] at hs
            subst s'
            exact ⟨2, by decide, raw_wr_V a as c cs⟩
        | C =>
            simp [stepB] at hs
            subst s'
            exact ⟨2, by decide, raw_wr_C a as c cs⟩
        | C1 =>
            simp [stepB] at hs
            subst s'
            exact ⟨2, by decide, raw_wr_C1 a as c cs⟩
        | C2 =>
            simp [stepB] at hs
            subst s'
            exact ⟨6, by decide, raw_wr_C2 a as c cs⟩
        | P =>
            simp [stepB] at hs
            subst s'
            exact ⟨1, by decide, raw_wr_P a as c cs⟩

/-- Concatenation of exact raw runs. -/
theorem rawRunK_comp {a b : Nat} {c c' c'' : RState}
    (h1 : rawRunK a c = some c') (h2 : rawRunK b c' = some c'') :
    rawRunK (a + b) c = some c'' := by
  induction b generalizing c' c'' with
  | zero =>
      simp [rawRunK] at h2
      subst c''
      simpa using h1
  | succ b ih =>
      simp [rawRunK] at h2
      cases hb : rawRunK b c' with
      | none => simp [hb] at h2
      | some d =>
          simp [hb] at h2
          have hmid : rawRunK (a + b) c = some d := ih h1 hb
          rw [Nat.add_succ]
          simp [rawRunK, hmid, h2]

/-- Every defined block run is matched by a raw run from the encoded start. -/
theorem rawOf_runB : ∀ n s, runB n = some s →
    ∃ k, rawRunK k (rawOf initB) = some (rawOf s)
  | 0, s, hs => by
      simp [runB] at hs
      subst s
      exact ⟨0, rfl⟩
  | n + 1, s, hs => by
      simp [runB, ostepB] at hs
      cases h : runB n with
      | none => simp [h] at hs
      | some s0 =>
          simp [h] at hs
          rcases rawOf_runB n s0 h with ⟨k, hk⟩
          rcases rawOf_stepB (runB_inv2 n s0 h) hs with ⟨j, _, hj⟩
          exact ⟨k + j, rawRunK_comp hk hj⟩

/-- `rawRunK` from the initial raw state is the ordinary raw run. -/
theorem rawRunK_from_start : ∀ n, rawRun n = rawRunK n rawStart
  | 0 => rfl
  | n + 1 => by
      simp [rawRun, rawRunK, rawRunK_from_start n]

/-- After the concrete 14-step prefix, a raw macro run from `initRaw` is an
ordinary raw run from `rawStart`. -/
theorem rawRun_after_prefix {k : Nat} {c : RState}
    (hk : rawRunK k initRaw = some c) :
    rawRun (14 + k) = some c := by
  have h14 : rawRunK 14 rawStart = some initRaw := by
    rw [← rawRunK_from_start]
    exact raw_prefix_14
  have hcomp : rawRunK (14 + k) rawStart = some c := rawRunK_comp h14 hk
  rw [← rawRunK_from_start] at hcomp
  exact hcomp

/-- Every defined stage of the block run is reached by the actual raw machine,
starting from `rawStart`, after the 14-step prefix plus a finite macro run. -/
theorem rawRun_bridges_runB {n : Nat} {s : BState} (h : runB n = some s) :
    ∃ k, rawRun (14 + k) = some (rawOf s) := by
  rcases rawOf_runB n s h with ⟨k, hk⟩
  rw [rawOf_init] at hk
  exact ⟨k, rawRun_after_prefix hk⟩

end M14

#print axioms M14.rawOf_init
#print axioms M14.rawOf_stepB
#print axioms M14.rawRunK_comp
#print axioms M14.rawOf_runB
#print axioms M14.rawRunK_from_start
#print axioms M14.rawRun_after_prefix
#print axioms M14.rawRun_bridges_runB
