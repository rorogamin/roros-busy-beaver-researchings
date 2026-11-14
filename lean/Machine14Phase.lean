/-
  Machine 14: the right-buffer phase grammar and four checked
  non-inductiveness patterns.

  The empirical right-buffer language is

      (V | C | C1 | C2 | P)* X* R.

  We formalize that language as `RightPhase`, add the local no-bad
  conditions used in `machine14_phase_grammar.py`, and prove that four
  grammar-conforming states step to states that violate the combined
  predicate.  The targets still satisfy `RightPhase`; what fails is the
  local exclusion of the `> R` dead end.  Thus the combined predicate is
  not inductive.  This is a negative/formalization result, not a
  totality or nonhalting proof.
-/

import Machine14TwoSided

namespace M14

/-- The five phase tokens that may occur before the right-buffer `X` run. -/
inductive PhaseTok : RTok → Prop
  | V : PhaseTok RTok.V
  | C : PhaseTok RTok.C
  | C1 : PhaseTok RTok.C1
  | C2 : PhaseTok RTok.C2
  | P : PhaseTok RTok.P

/-- A (possibly empty) prefix of phase tokens. -/
inductive PhasePrefix : List RTok → Prop
  | nil : PhasePrefix []
  | cons {t : RTok} {p : List RTok} (ht : PhaseTok t) (hp : PhasePrefix p) :
      PhasePrefix (t :: p)

/-- A (possibly empty) run of `X` tokens. -/
inductive XRun : List RTok → Prop
  | nil : XRun []
  | cons {x : List RTok} (hx : XRun x) : XRun (RTok.X :: x)

/-- The right-buffer grammar `(V|C|C1|C2|P)* X* R`. -/
def RightPhase (r : List RTok) : Prop :=
  ∃ p x : List RTok, PhasePrefix p ∧ XRun x ∧ r = p ++ x ++ [RTok.R]

/-- Introduce a word by its phase prefix and `X` run. -/
theorem RightPhase.of_prefix {p x : List RTok}
    (hp : PhasePrefix p) (hx : XRun x) :
    RightPhase (p ++ x ++ [RTok.R]) :=
  ⟨p, x, hp, hx, rfl⟩

@[simp] theorem rightPhase_R : RightPhase [RTok.R] := by
  simpa using
    (RightPhase.of_prefix (p := []) (x := []) PhasePrefix.nil XRun.nil)

@[simp] theorem rightPhase_VR : RightPhase [RTok.V, RTok.R] := by
  simpa using
    (RightPhase.of_prefix (p := [RTok.V]) (x := [])
      (PhasePrefix.cons PhaseTok.V PhasePrefix.nil) XRun.nil)

@[simp] theorem rightPhase_CR : RightPhase [RTok.C, RTok.R] := by
  simpa using
    (RightPhase.of_prefix (p := [RTok.C]) (x := [])
      (PhasePrefix.cons PhaseTok.C PhasePrefix.nil) XRun.nil)

@[simp] theorem rightPhase_C1R : RightPhase [RTok.C1, RTok.R] := by
  simpa using
    (RightPhase.of_prefix (p := [RTok.C1]) (x := [])
      (PhasePrefix.cons PhaseTok.C1 PhasePrefix.nil) XRun.nil)

@[simp] theorem rightPhase_C2R : RightPhase [RTok.C2, RTok.R] := by
  simpa using
    (RightPhase.of_prefix (p := [RTok.C2]) (x := [])
      (PhasePrefix.cons PhaseTok.C2 PhasePrefix.nil) XRun.nil)

@[simp] theorem rightPhase_PCR : RightPhase [RTok.P, RTok.C, RTok.R] := by
  simpa using
    (RightPhase.of_prefix (p := [RTok.P, RTok.C]) (x := [])
      (PhasePrefix.cons PhaseTok.P
        (PhasePrefix.cons PhaseTok.C PhasePrefix.nil)) XRun.nil)

@[simp] theorem rightPhase_PR : RightPhase [RTok.P, RTok.R] := by
  simpa using
    (RightPhase.of_prefix (p := [RTok.P]) (x := [])
      (PhasePrefix.cons PhaseTok.P PhasePrefix.nil) XRun.nil)

/-- Boolean test for the phase alphabet. -/
def isPhase : RTok → Bool
  | RTok.V | RTok.C | RTok.C1 | RTok.C2 | RTok.P => true
  | _ => false

/-- The local exclusions from the phase search.  This returns `true` exactly
when the state is one of the locally bad phase patterns. -/
def badPhase : Head → Option LTok → List RTok → Bool
  | Head.r, _, RTok.R :: _ => true
  | Head.wr, _, RTok.C :: RTok.R :: _ => true
  | Head.wr, _, RTok.C1 :: RTok.R :: _ => true
  | Head.wr, _, RTok.P :: RTok.R :: _ => true
  | Head.l, some LTok.L, RTok.C :: RTok.R :: _ => true
  | Head.l, some LTok.L, RTok.C1 :: RTok.R :: _ => true
  | Head.l, some LTok.L, RTok.P :: RTok.R :: _ => true
  | Head.l, some LTok.U, RTok.R :: _ => true
  | Head.l, some LTok.Y, t :: _ => isPhase t
  | _, _, _ => false

/-- The combined right-phase candidate: the grammar plus the local no-bad
conditions. -/
def PhaseOK (s : BState) : Prop :=
  RightPhase s.right ∧ badPhase s.head s.left.head? s.right = false

/-- A state failing `badPhase` cannot satisfy `PhaseOK`. -/
theorem not_phaseOK_of_bad {s : BState}
    (h : badPhase s.head s.left.head? s.right = true) : ¬ PhaseOK s := by
  intro hs
  have hf : badPhase s.head s.left.head? s.right = false := hs.2
  rw [h] at hf
  cases hf

/-- One checked non-inductiveness pattern: a phase-conforming source steps to
a phase-conforming target that the local predicate rejects. -/
def PhaseFailure (s s' : BState) : Prop :=
  PhaseOK s ∧ stepB s = some s' ∧ RightPhase s'.right ∧ ¬ PhaseOK s'

/-! ## The four one-step failures -/

/-- `> V R -> > U R`: the source is phase-conforming and locally allowed;
the target is the `> R` dead end. -/
def sVR : BState := ⟨Head.r, [LTok.L], [RTok.V, RTok.R]⟩
def sVR' : BState := ⟨Head.r, [LTok.U, LTok.L], [RTok.R]⟩

theorem phaseOK_VR : PhaseOK sVR := by
  refine ⟨rightPhase_VR, ?_⟩
  decide

theorem stepB_VR : stepB sVR = some sVR' := rfl

theorem not_phaseOK_VR' : ¬ PhaseOK sVR' :=
  not_phaseOK_of_bad (by decide)

theorem phase_failure_VR : PhaseFailure sVR sVR' :=
  ⟨phaseOK_VR, stepB_VR, rightPhase_R, not_phaseOK_VR'⟩

/-- `> C R -> < L C1 R`: the target is phase-conforming but violates the
left-`L`/`C1 R` local exclusion. -/
def sCR : BState := ⟨Head.r, [LTok.L], [RTok.C, RTok.R]⟩
def sCR' : BState := ⟨Head.l, [LTok.L], [RTok.C1, RTok.R]⟩

theorem phaseOK_CR : PhaseOK sCR := by
  refine ⟨rightPhase_CR, ?_⟩
  decide

theorem stepB_CR : stepB sCR = some sCR' := rfl

theorem not_phaseOK_CR' : ¬ PhaseOK sCR' :=
  not_phaseOK_of_bad (by decide)

theorem phase_failure_CR : PhaseFailure sCR sCR' :=
  ⟨phaseOK_CR, stepB_CR, rightPhase_C1R, not_phaseOK_CR'⟩

/-- `> C2 R -> > F R`: the target is again the `> R` dead end. -/
def sC2R : BState := ⟨Head.r, [LTok.L], [RTok.C2, RTok.R]⟩
def sC2R' : BState := ⟨Head.r, [LTok.F, LTok.L], [RTok.R]⟩

theorem phaseOK_C2R : PhaseOK sC2R := by
  refine ⟨rightPhase_C2R, ?_⟩
  decide

theorem stepB_C2R : stepB sC2R = some sC2R' := rfl

theorem not_phaseOK_C2R' : ¬ PhaseOK sC2R' :=
  not_phaseOK_of_bad (by decide)

theorem phase_failure_C2R : PhaseFailure sC2R sC2R' :=
  ⟨phaseOK_C2R, stepB_C2R, rightPhase_R, not_phaseOK_C2R'⟩

/-- `> P C R -> w> L C R`: the target is phase-conforming but violates the
`w>`/`C R` local exclusion. -/
def sPCR : BState := ⟨Head.r, [LTok.L], [RTok.P, RTok.C, RTok.R]⟩
def sPCR' : BState := ⟨Head.wr, [LTok.L], [RTok.C, RTok.R]⟩

theorem phaseOK_PCR : PhaseOK sPCR := by
  refine ⟨rightPhase_PCR, ?_⟩
  decide

theorem stepB_PCR : stepB sPCR = some sPCR' := rfl

theorem not_phaseOK_PCR' : ¬ PhaseOK sPCR' :=
  not_phaseOK_of_bad (by decide)

theorem phase_failure_PCR : PhaseFailure sPCR sPCR' :=
  ⟨phaseOK_PCR, stepB_PCR, rightPhase_CR, not_phaseOK_PCR'⟩

/-- All four failure patterns together: the combined phase predicate is not
inductive.  Every target still satisfies the right-buffer grammar. -/
theorem phase_not_inductive :
    PhaseFailure sVR sVR' ∧ PhaseFailure sCR sCR' ∧
      PhaseFailure sC2R sC2R' ∧ PhaseFailure sPCR sPCR' :=
  ⟨phase_failure_VR, phase_failure_CR, phase_failure_C2R, phase_failure_PCR⟩

/-- In particular, `PhaseOK` has a one-step counterexample. -/
theorem phase_failure_exists :
    ∃ s s' : BState, PhaseOK s ∧ stepB s = some s' ∧ ¬ PhaseOK s' := by
  rcases phase_failure_VR with ⟨hP, hstep, _hgrammar, hbad⟩
  exact ⟨sVR, sVR', hP, hstep, hbad⟩

/-- The phase predicate excludes the original `> R` dead end. -/
theorem phaseOK_excludes_gtR : ¬ PhaseOK ⟨Head.r, [LTok.L], [RTok.R]⟩ := by
  apply not_phaseOK_of_bad
  decide

/-! ## Left-context gate -/

/-- A checked left-context gate: the left buffer is a valid `L (U|W|F|Y|Q)*`
word, and a `>` head has at least two left blocks.  The length condition
exactly blocks the four bare-left sources used in the first phase failures. -/
def LeftGate (s : BState) : Prop :=
  LeftOK s.left ∧ (s.head ≠ Head.r ∨ 2 ≤ s.left.length)

/-- The first local left-phase exclusions found after the gate: at `<`, the
sources `L F | R` and `L Q | R` step to locally bad targets. -/
def badLeftPhaseFQ : Head → List LTok → List RTok → Bool
  | Head.l, LTok.F :: LTok.L :: [], RTok.R :: [] => true
  | Head.l, LTok.Q :: LTok.L :: [], RTok.R :: [] => true
  | _, _, _ => false

/-- The next exclusion: any left context ending in `Y W` is bad regardless
of the right buffer. -/
def badLeftPhaseYW : Head → List LTok → List RTok → Bool
  | Head.l, LTok.W :: LTok.Y :: _, _ => true
  | _, _, _ => false

/-- The next exclusion: any left context ending in `Y F` is bad regardless
of the right buffer. -/
def badLeftPhaseYF : Head → List LTok → List RTok → Bool
  | Head.l, LTok.F :: LTok.Y :: _, _ => true
  | _, _, _ => false

/-- The next exclusion: any left context ending in `Y Q` is bad regardless
of the right buffer. -/
def badLeftPhaseYQ : Head → List LTok → List RTok → Bool
  | Head.l, LTok.Q :: LTok.Y :: _, _ => true
  | _, _, _ => false

/-- The backward-closed `< Y` family: scan the nearest run of `Y/W/F/Q`
tokens and reject it if it contains `W Y`, `F Y`, or `Q Y`. -/
def badLeftPhaseY : Head → List LTok → Bool
  | Head.l, LTok.W :: LTok.Y :: _ => true
  | Head.l, LTok.F :: LTok.Y :: _ => true
  | Head.l, LTok.Q :: LTok.Y :: _ => true
  | Head.l, LTok.W :: rest => badLeftPhaseY Head.l rest
  | Head.l, LTok.F :: rest => badLeftPhaseY Head.l rest
  | Head.l, LTok.Q :: rest => badLeftPhaseY Head.l rest
  | Head.l, LTok.Y :: rest => badLeftPhaseY Head.l rest
  | _, _ => false

/-- A checked `>`-head source: `> V R` steps to the dead end `> U R`. -/
def badRightVR : Head → List RTok → Bool
  | Head.r, RTok.V :: RTok.R :: _ => true
  | _, _ => false

/-- The phase predicate with the structural left gate only.  Kept so the
earlier checked counterexamples remain available. -/
def PhaseOKL0 (s : BState) : Prop :=
  PhaseOK s ∧ LeftGate s

/-- The predicate after the two `< F R`/`< Q R` exclusions. -/
def PhaseOKL1 (s : BState) : Prop :=
  PhaseOKL0 s ∧ badLeftPhaseFQ s.head s.left s.right = false

/-- The predicate after the `< Y W` exclusion. -/
def PhaseOKL2 (s : BState) : Prop :=
  PhaseOKL1 s ∧ badLeftPhaseYW s.head s.left s.right = false

/-- The predicate after the `< Y F` exclusion. -/
def PhaseOKL3 (s : BState) : Prop :=
  PhaseOKL2 s ∧ badLeftPhaseYF s.head s.left s.right = false

/-- The predicate after the `< Y Q` exclusion. -/
def PhaseOKL4 (s : BState) : Prop :=
  PhaseOKL3 s ∧ badLeftPhaseYQ s.head s.left s.right = false

/-- The predicate after the backward-closed `< Y` family. -/
def PhaseOKL5 (s : BState) : Prop :=
  PhaseOKL4 s ∧ badLeftPhaseY s.head s.left = false

/-- The current predicate: the left-phase family plus the checked `> V R`
source exclusion. -/
def PhaseOKL (s : BState) : Prop :=
  PhaseOKL5 s ∧ badRightVR s.head s.right = false

/-- The four old source patterns are all excluded by the gate. -/
theorem leftGate_excludes_four :
    ¬ PhaseOKL sVR ∧ ¬ PhaseOKL sCR ∧ ¬ PhaseOKL sC2R ∧ ¬ PhaseOKL sPCR := by
  simp [PhaseOKL, PhaseOKL5, PhaseOKL4, PhaseOKL3, PhaseOKL2, PhaseOKL1,
    PhaseOKL0, LeftGate, badLeftPhaseFQ, badLeftPhaseYW, badLeftPhaseYF,
    badLeftPhaseYQ, badLeftPhaseY, badRightVR, sVR, sCR, sC2R, sPCR]

/-- The initial block state satisfies the gate and all checked exclusions. -/
theorem phaseOKL_init : PhaseOKL initB := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · refine ⟨?_, ?_⟩
              · refine ⟨rightPhase_R, ?_⟩
                decide
              · refine ⟨?_, Or.inl (by decide)⟩
                exact LeftOK.cons (by decide) (LeftOK.cons (by decide) LeftOK.nilL)
            · decide
          · decide
        · decide
      · decide
    · decide
  · decide

/-- A new source exposed after adding the left gate: the left word is `L F`
(far-to-near), the head is `<`, and the right buffer is `R`. -/
def sFR : BState := ⟨Head.l, [LTok.F, LTok.L], [RTok.R]⟩

/-- Its target is `< L | C R`, which violates the left-`L`/`C R` exclusion. -/
def sFR' : BState := ⟨Head.l, [LTok.L], [RTok.C, RTok.R]⟩

theorem phaseOKL0_FR : PhaseOKL0 sFR := by
  refine ⟨?_, ?_⟩
  · refine ⟨rightPhase_R, ?_⟩
    decide
  · refine ⟨?_, Or.inl (by decide)⟩
    exact LeftOK.cons (by decide) LeftOK.nilL

theorem stepB_FR : stepB sFR = some sFR' := rfl

theorem not_phaseOK_FR' : ¬ PhaseOK sFR' :=
  not_phaseOK_of_bad (by decide)

theorem not_phaseOKL0_FR' : ¬ PhaseOKL0 sFR' := by
  intro h
  exact not_phaseOK_FR' h.1

theorem not_phaseOKL_FR' : ¬ PhaseOKL sFR' := by
  intro h
  exact not_phaseOK_FR' h.1.1.1.1.1.1.1

/-- The previous gate allowed `< F R`, which steps to a locally bad state.
This remains a checked counterexample for `PhaseOKL0`. -/
theorem phaseL0_failure_FR :
    PhaseOKL0 sFR ∧ stepB sFR = some sFR' ∧
      RightPhase sFR'.right ∧ ¬ PhaseOKL0 sFR' :=
  ⟨phaseOKL0_FR, stepB_FR, rightPhase_CR, not_phaseOKL0_FR'⟩

/-- The previous left-gated predicate is not inductive. -/
theorem phaseL0_not_inductive :
    ∃ s s' : BState,
      PhaseOKL0 s ∧ stepB s = some s' ∧ RightPhase s'.right ∧ ¬ PhaseOKL0 s' := by
  rcases phaseL0_failure_FR with ⟨hP, hstep, hR, hbad⟩
  exact ⟨sFR, sFR', hP, hstep, hR, hbad⟩

/-- The second new source, `< Q R`, is excluded along with `< F R`. -/
def sQR : BState := ⟨Head.l, [LTok.Q, LTok.L], [RTok.R]⟩

/-- Both newly identified left-phase sources are rejected by the checked
exclusion. -/
theorem leftPhase_excludes_FR_QR :
    ¬ PhaseOKL sFR ∧ ¬ PhaseOKL sQR := by
  simp [PhaseOKL, PhaseOKL5, PhaseOKL4, PhaseOKL3, PhaseOKL2, PhaseOKL1,
    PhaseOKL0, badLeftPhaseFQ, badLeftPhaseYW, badLeftPhaseYF,
    badLeftPhaseYQ, badLeftPhaseY, badRightVR, sFR, sQR]

/-- The next failure after adding the `< F R`/`< Q R` exclusion: `< W R`
steps to `< Y V R`, which is locally bad. -/
def sYWR : BState := ⟨Head.l, [LTok.W, LTok.Y, LTok.L], [RTok.R]⟩
def sYWR' : BState := ⟨Head.l, [LTok.Y, LTok.L], [RTok.V, RTok.R]⟩

theorem phaseOKL1_YWR : PhaseOKL1 sYWR := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨rightPhase_R, ?_⟩
      decide
    · refine ⟨?_, Or.inl (by decide)⟩
      exact LeftOK.cons (by decide) (LeftOK.cons (by decide) LeftOK.nilL)
  · decide

theorem stepB_YWR : stepB sYWR = some sYWR' := rfl

theorem not_phaseOK_YWR' : ¬ PhaseOK sYWR' :=
  not_phaseOK_of_bad (by decide)

theorem not_phaseOKL1_YWR' : ¬ PhaseOKL1 sYWR' := by
  intro h
  exact not_phaseOK_YWR' h.1.1

/-- The predicate after the `< F R`/`< Q R` exclusions still allows
`< W R`, which reaches the forbidden `< Y`/phase pattern. -/
theorem phaseL2_failure_YWR :
    PhaseOKL1 sYWR ∧ stepB sYWR = some sYWR' ∧
      RightPhase sYWR'.right ∧ ¬ PhaseOKL1 sYWR' :=
  ⟨phaseOKL1_YWR, stepB_YWR, rightPhase_VR, not_phaseOKL1_YWR'⟩

/-- The predicate after the `< F R`/`< Q R` exclusions is not inductive. -/
theorem phaseL2_not_inductive :
    ∃ s s' : BState,
      PhaseOKL1 s ∧ stepB s = some s' ∧ RightPhase s'.right ∧ ¬ PhaseOKL1 s' := by
  rcases phaseL2_failure_YWR with ⟨hP, hstep, hR, hbad⟩
  exact ⟨sYWR, sYWR', hP, hstep, hR, hbad⟩

/-- The `< Y W` source is now rejected in every right-buffer context. -/
theorem leftPhase_excludes_YW : ¬ PhaseOKL sYWR := by
  simp [PhaseOKL, PhaseOKL5, PhaseOKL4, PhaseOKL3, PhaseOKL2, PhaseOKL1,
    PhaseOKL0, badLeftPhaseFQ, badLeftPhaseYW, badLeftPhaseYF,
    badLeftPhaseYQ, badLeftPhaseY, badRightVR, sYWR]

/-- The next failure after excluding `< Y W`: `< Y F R` steps to
`< Y C R`, which violates the local `< Y`/phase exclusion. -/
def sYFR : BState := ⟨Head.l, [LTok.F, LTok.Y, LTok.L], [RTok.R]⟩
def sYFR' : BState := ⟨Head.l, [LTok.Y, LTok.L], [RTok.C, RTok.R]⟩

theorem phaseOKL2_YFR : PhaseOKL2 sYFR := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨rightPhase_R, ?_⟩
        decide
      · refine ⟨?_, Or.inl (by decide)⟩
        exact LeftOK.cons (by decide) (LeftOK.cons (by decide) LeftOK.nilL)
    · decide
  · decide

theorem stepB_YFR : stepB sYFR = some sYFR' := rfl

theorem not_phaseOK_YFR' : ¬ PhaseOK sYFR' :=
  not_phaseOK_of_bad (by decide)

theorem not_phaseOKL2_YFR' : ¬ PhaseOKL2 sYFR' := by
  intro h
  exact not_phaseOK_YFR' h.1.1.1

/-- The `< Y W` exclusion does not close the predicate: `< Y F R` is still
allowed and reaches the forbidden `< Y`/phase pattern. -/
theorem phaseL3_failure_YFR :
    PhaseOKL2 sYFR ∧ stepB sYFR = some sYFR' ∧
      RightPhase sYFR'.right ∧ ¬ PhaseOKL2 sYFR' :=
  ⟨phaseOKL2_YFR, stepB_YFR, rightPhase_CR, not_phaseOKL2_YFR'⟩

/-- The predicate after the `< Y W` exclusion is still not inductive. -/
theorem phaseL3_not_inductive :
    ∃ s s' : BState,
      PhaseOKL2 s ∧ stepB s = some s' ∧ RightPhase s'.right ∧ ¬ PhaseOKL2 s' := by
  rcases phaseL3_failure_YFR with ⟨hP, hstep, hR, hbad⟩
  exact ⟨sYFR, sYFR', hP, hstep, hR, hbad⟩

/-- The `< Y F` source is now rejected in every right-buffer context. -/
theorem leftPhase_excludes_YF : ¬ PhaseOKL sYFR := by
  simp [PhaseOKL, PhaseOKL5, PhaseOKL4, PhaseOKL3, PhaseOKL2, PhaseOKL1,
    PhaseOKL0, badLeftPhaseFQ, badLeftPhaseYW, badLeftPhaseYF,
    badLeftPhaseYQ, badLeftPhaseY, badRightVR, sYFR]

/-- The next failure after excluding `< Y F`: `< Y Q R` steps to
`< Y P R`, which violates the local `< Y`/phase exclusion. -/
def sYQR : BState := ⟨Head.l, [LTok.Q, LTok.Y, LTok.L], [RTok.R]⟩
def sYQR' : BState := ⟨Head.l, [LTok.Y, LTok.L], [RTok.P, RTok.R]⟩

theorem phaseOKL3_YQR : PhaseOKL3 sYQR := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨rightPhase_R, ?_⟩
          decide
        · refine ⟨?_, Or.inl (by decide)⟩
          exact LeftOK.cons (by decide) (LeftOK.cons (by decide) LeftOK.nilL)
      · decide
    · decide
  · decide

theorem stepB_YQR : stepB sYQR = some sYQR' := rfl

theorem not_phaseOK_YQR' : ¬ PhaseOK sYQR' :=
  not_phaseOK_of_bad (by decide)

theorem not_phaseOKL3_YQR' : ¬ PhaseOKL3 sYQR' := by
  intro h
  exact not_phaseOK_YQR' h.1.1.1.1

/-- The `< Y F` exclusion does not close the predicate: `< Y Q R` is still
allowed and reaches the forbidden `< Y`/phase pattern. -/
theorem phaseL4_failure_YQR :
    PhaseOKL3 sYQR ∧ stepB sYQR = some sYQR' ∧
      RightPhase sYQR'.right ∧ ¬ PhaseOKL3 sYQR' :=
  ⟨phaseOKL3_YQR, stepB_YQR, rightPhase_PR, not_phaseOKL3_YQR'⟩

/-- The predicate after the `< Y F` exclusion is still not inductive. -/
theorem phaseL4_not_inductive :
    ∃ s s' : BState,
      PhaseOKL3 s ∧ stepB s = some s' ∧ RightPhase s'.right ∧ ¬ PhaseOKL3 s' := by
  rcases phaseL4_failure_YQR with ⟨hP, hstep, hR, hbad⟩
  exact ⟨sYQR, sYQR', hP, hstep, hR, hbad⟩

/-- The `< Y Q` source is now rejected in every right-buffer context. -/
theorem leftPhase_excludes_YQ : ¬ PhaseOKL sYQR := by
  simp [PhaseOKL, PhaseOKL5, PhaseOKL4, PhaseOKL3, PhaseOKL2, PhaseOKL1,
    PhaseOKL0, badLeftPhaseFQ, badLeftPhaseYW, badLeftPhaseYF,
    badLeftPhaseYQ, badLeftPhaseY, badRightVR, sYQR]

/-- The next failure after excluding `< Y Q`: the source `< Y W W R` steps
to `< Y W V R`, which violates the earlier `< Y W` exclusion. -/
def sYWW : BState := ⟨Head.l, [LTok.W, LTok.W, LTok.Y, LTok.L], [RTok.R]⟩
def sYWW' : BState := ⟨Head.l, [LTok.W, LTok.Y, LTok.L], [RTok.V, RTok.R]⟩

theorem phaseOKL4_YWW : PhaseOKL4 sYWW := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · refine ⟨rightPhase_R, ?_⟩
            decide
          · refine ⟨?_, Or.inl (by decide)⟩
            exact LeftOK.cons (by decide)
              (LeftOK.cons (by decide) (LeftOK.cons (by decide) LeftOK.nilL))
        · decide
      · decide
    · decide
  · decide

theorem stepB_YWW : stepB sYWW = some sYWW' := rfl

theorem not_phaseOKL4_YWW' : ¬ PhaseOKL4 sYWW' := by
  intro h
  have hbad : badLeftPhaseYW sYWW'.head sYWW'.left sYWW'.right = true := rfl
  have hfalse := h.1.1.2
  rw [hbad] at hfalse
  cases hfalse

/-- The `< Y Q` exclusion does not close the predicate: `< Y W W R` reaches
a target excluded by `< Y W`. -/
theorem phaseL5_failure_YWW :
    PhaseOKL4 sYWW ∧ stepB sYWW = some sYWW' ∧
      RightPhase sYWW'.right ∧ ¬ PhaseOKL4 sYWW' :=
  ⟨phaseOKL4_YWW, stepB_YWW, rightPhase_VR, not_phaseOKL4_YWW'⟩

/-- The predicate after the `< Y Q` exclusion is still not inductive. -/
theorem phaseL5_not_inductive :
    ∃ s s' : BState,
      PhaseOKL4 s ∧ stepB s = some s' ∧ RightPhase s'.right ∧ ¬ PhaseOKL4 s' := by
  rcases phaseL5_failure_YWW with ⟨hP, hstep, hR, hbad⟩
  exact ⟨sYWW, sYWW', hP, hstep, hR, hbad⟩

/-- The backward-closed family rejects the cascade source `< Y W W`. -/
theorem leftPhase_excludes_YWW : ¬ PhaseOKL sYWW := by
  simp [PhaseOKL, PhaseOKL5, PhaseOKL4, PhaseOKL3, PhaseOKL2, PhaseOKL1,
    PhaseOKL0, badLeftPhaseFQ, badLeftPhaseYW, badLeftPhaseYF,
    badLeftPhaseYQ, badLeftPhaseY, badRightVR, sYWW]

/-- The unified `< Y` family exposes a source with an extra left block:
`> V R` with left `L U` steps to the dead end `> U R`. -/
def sUV : BState := ⟨Head.r, [LTok.U, LTok.L], [RTok.V, RTok.R]⟩
def sUV' : BState := ⟨Head.r, [LTok.U, LTok.U, LTok.L], [RTok.R]⟩

theorem phaseOKL5_UV : PhaseOKL5 sUV := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · refine ⟨rightPhase_VR, ?_⟩
              decide
            · refine ⟨?_, ?_⟩
              · exact LeftOK.cons (by decide) LeftOK.nilL
              · exact Or.inr (by decide)
          · decide
        · decide
      · decide
    · decide
  · decide

theorem stepB_UV : stepB sUV = some sUV' := rfl

theorem not_phaseOK_UV' : ¬ PhaseOK sUV' :=
  not_phaseOK_of_bad (by decide)

theorem not_phaseOKL5_UV' : ¬ PhaseOKL5 sUV' := by
  intro h
  exact not_phaseOK_UV' h.1.1.1.1.1.1

/-- The unified `< Y` family does not close the predicate: `> V R` with
left `L U` reaches `> U R`. -/
theorem phaseL6_failure_UV :
    PhaseOKL5 sUV ∧ stepB sUV = some sUV' ∧
      RightPhase sUV'.right ∧ ¬ PhaseOKL5 sUV' :=
  ⟨phaseOKL5_UV, stepB_UV, rightPhase_R, not_phaseOKL5_UV'⟩

/-- The predicate after the unified `< Y` family is still not inductive. -/
theorem phaseL6_not_inductive :
    ∃ s s' : BState,
      PhaseOKL5 s ∧ stepB s = some s' ∧ RightPhase s'.right ∧ ¬ PhaseOKL5 s' := by
  rcases phaseL6_failure_UV with ⟨hP, hstep, hR, hbad⟩
  exact ⟨sUV, sUV', hP, hstep, hR, hbad⟩

/-- The checked `> V R` rule rejects the source with left `L U`. -/
theorem rightPhase_excludes_VR : ¬ PhaseOKL sUV := by
  simp [PhaseOKL, PhaseOKL5, PhaseOKL4, PhaseOKL3, PhaseOKL2, PhaseOKL1,
    PhaseOKL0, badLeftPhaseFQ, badLeftPhaseYW, badLeftPhaseYF,
    badLeftPhaseYQ, badLeftPhaseY, badRightVR, sUV]

/-- The `> V R` exclusion exposes its `< U` predecessor: `< U V R` steps to
`> W V R`, which the new rule rejects. -/
def sUVR : BState := ⟨Head.l, [LTok.U, LTok.L], [RTok.V, RTok.R]⟩
def sUVR' : BState := ⟨Head.r, [LTok.W, LTok.L], [RTok.V, RTok.R]⟩

theorem phaseOKL_UVR : PhaseOKL sUVR := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · refine ⟨?_, ?_⟩
              · refine ⟨rightPhase_VR, ?_⟩
                decide
              · refine ⟨?_, ?_⟩
                · exact LeftOK.cons (by decide) LeftOK.nilL
                · exact Or.inr (by decide)
            · decide
          · decide
        · decide
      · decide
    · decide
  · decide

theorem stepB_UVR : stepB sUVR = some sUVR' := rfl

theorem not_phaseOKL_UVR' : ¬ PhaseOKL sUVR' := by
  intro h
  have hbad : badRightVR sUVR'.head sUVR'.right = true := rfl
  have hfalse := h.2
  rw [hbad] at hfalse
  cases hfalse

/-- The `> V R` exclusion does not close the predicate: `< U V R` reaches
the excluded `> W V R` source. -/
theorem phaseL7_failure_UVR :
    PhaseOKL sUVR ∧ stepB sUVR = some sUVR' ∧
      RightPhase sUVR'.right ∧ ¬ PhaseOKL sUVR' :=
  ⟨phaseOKL_UVR, stepB_UVR, rightPhase_VR, not_phaseOKL_UVR'⟩

/-- The strengthened predicate is still not inductive. -/
theorem phaseL7_not_inductive :
    ∃ s s' : BState,
      PhaseOKL s ∧ stepB s = some s' ∧ RightPhase s'.right ∧ ¬ PhaseOKL s' := by
  rcases phaseL7_failure_UVR with ⟨hP, hstep, hR, hbad⟩
  exact ⟨sUVR, sUVR', hP, hstep, hR, hbad⟩

#print axioms M14.rightPhase_R
#print axioms M14.rightPhase_VR
#print axioms M14.rightPhase_PCR
#print axioms M14.rightPhase_PR
#print axioms M14.phase_failure_VR
#print axioms M14.phase_failure_CR
#print axioms M14.phase_failure_C2R
#print axioms M14.phase_failure_PCR
#print axioms M14.phase_not_inductive
#print axioms M14.phase_failure_exists
#print axioms M14.phaseOK_excludes_gtR
#print axioms M14.leftGate_excludes_four
#print axioms M14.phaseOKL_init
#print axioms M14.phaseL0_failure_FR
#print axioms M14.phaseL0_not_inductive
#print axioms M14.leftPhase_excludes_FR_QR
#print axioms M14.phaseL2_failure_YWR
#print axioms M14.phaseL2_not_inductive
#print axioms M14.leftPhase_excludes_YW
#print axioms M14.phaseL3_failure_YFR
#print axioms M14.phaseL3_not_inductive
#print axioms M14.leftPhase_excludes_YF
#print axioms M14.phaseL4_failure_YQR
#print axioms M14.phaseL4_not_inductive
#print axioms M14.leftPhase_excludes_YQ
#print axioms M14.phaseL5_failure_YWW
#print axioms M14.phaseL5_not_inductive
#print axioms M14.leftPhase_excludes_YWW
#print axioms M14.phaseL6_failure_UV
#print axioms M14.phaseL6_not_inductive
#print axioms M14.rightPhase_excludes_VR
#print axioms M14.phaseL7_failure_UVR
#print axioms M14.phaseL7_not_inductive

end M14
