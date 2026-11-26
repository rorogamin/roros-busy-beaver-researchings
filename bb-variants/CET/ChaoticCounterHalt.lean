/-
  CET(4) Chaotic Counter + Slow Glider:
  AG1 = 1RB0RB_1LC1RA_1LD0LC_0RA0LD (rightward chaotic counter)
  AG2 = 1RC0RC_1LA0RC_1LA1RD_1LD1LB (P=22, D=2 rightward glider leaving solid 1-wall)

  Proves:
  1. AG2 is a P=22, D=2 glider on blank tape.
  2. AG1 in state A or B on a solid 1-wall sprints right at speed +1/step.
  3. 40 out of 44 arrival (phase mod 22, s1 in {A,B}) configurations collide and halt.
-/

set_option maxRecDepth 200000

inductive St
  | A | B | C | D
  deriving DecidableEq, Repr

structure TMTrans where
  w : Bool
  d : Int
  ns : St
  deriving DecidableEq, Repr

def ag1Step : St → Bool → TMTrans
  | .A, false => ⟨true,   1, .B⟩
  | .A, true  => ⟨false,  1, .B⟩
  | .B, false => ⟨true,  -1, .C⟩
  | .B, true  => ⟨true,   1, .A⟩
  | .C, false => ⟨true,  -1, .D⟩
  | .C, true  => ⟨false, -1, .C⟩
  | .D, false => ⟨false,  1, .A⟩
  | .D, true  => ⟨false, -1, .D⟩

def ag2Step : St → Bool → TMTrans
  | .A, false => ⟨true,   1, .C⟩
  | .A, true  => ⟨false,  1, .C⟩
  | .B, false => ⟨true,  -1, .A⟩
  | .B, true  => ⟨false,  1, .C⟩
  | .C, false => ⟨true,  -1, .A⟩
  | .C, true  => ⟨true,   1, .D⟩
  | .D, false => ⟨true,  -1, .D⟩
  | .D, true  => ⟨true,  -1, .B⟩

/-- Finite tape window [0..N-1] represented as a List Bool -/
def getCell (tape : List Bool) (i : Nat) : Bool :=
  tape.getD i false

def setCell (tape : List Bool) (i : Nat) (v : Bool) : List Bool :=
  tape.set i v

structure SingleCfg where
  tape : List Bool
  pos : Nat
  st : St

def stepSingle (rule : St → Bool → TMTrans) (c : SingleCfg) : SingleCfg :=
  let tr := rule c.st (getCell c.tape c.pos)
  let tape' := setCell c.tape c.pos tr.w
  let pos' := (Int.ofNat c.pos + tr.d).toNat
  ⟨tape', pos', tr.ns⟩

def runSingle (rule : St → Bool → TMTrans) : Nat → SingleCfg → SingleCfg
  | 0, c => c
  | n + 1, c => runSingle rule n (stepSingle rule c)

/-- Verify AG2 on blank tape is at pos=12 at t=110 and pos=14 at t=132 (P=22, D=2) -/
theorem ag2_period_22 :
    let c0 : SingleCfg := ⟨List.replicate 64 false, 20, .A⟩
    let c1 := runSingle ag2Step 110 c0
    let c2 := runSingle ag2Step 22 c1
    c1.st = c2.st ∧ c2.pos = c1.pos + 2 := by
  decide

/-- Verify AG1 sprints right at +1/step on an all-1 tape in state A or B -/
theorem ag1_sprint_A :
    let c0 : SingleCfg := ⟨List.replicate 16 true, 2, .A⟩
    let c1 := runSingle ag1Step 2 c0
    c1.st = .A ∧ c1.pos = 4 := by
  decide

theorem ag1_sprint_B :
    let c0 : SingleCfg := ⟨List.replicate 16 true, 2, .B⟩
    let c1 := runSingle ag1Step 2 c0
    c1.st = .B ∧ c1.pos = 4 := by
  decide

structure CetCfg where
  tape : List Bool
  p1 : Nat
  s1 : St
  p2 : Nat
  s2 : St

def stepCet (c : CetCfg) : Option CetCfg :=
  if c.p1 == c.p2 then none
  else
    let tr1 := ag1Step c.s1 (getCell c.tape c.p1)
    let tr2 := ag2Step c.s2 (getCell c.tape c.p2)
    let tape1 := setCell c.tape c.p2 tr2.w
    let tape2 := setCell tape1 c.p1 tr1.w
    let p1' := (Int.ofNat c.p1 + tr1.d).toNat
    let p2' := (Int.ofNat c.p2 + tr2.d).toNat
    if p1' == p2' then none
    else some ⟨tape2, p1', tr1.ns, p2', tr2.ns⟩

def haltsWithin : Nat → CetCfg → Bool
  | 0, _ => false
  | n + 1, c =>
    match stepCet c with
    | none => true
    | some c' => haltsWithin n c'

/-- Build AG2's tape at phase k (after 110 + k steps from blank), with 1s to the left of p2 - 15 -/
def mkPhaseCfg (k : Nat) (s1 : St) : CetCfg :=
  let ag2_200 := runSingle ag2Step (199 + k) ⟨List.replicate 64 false, 20, .A⟩
  let wallLen := ag2_200.pos - 15
  let tape := List.replicate wallLen true ++ ag2_200.tape.drop wallLen
  ⟨tape, ag2_200.pos - 20, s1, ag2_200.pos, ag2_200.st⟩

def checkAllPhases : Bool :=
  (List.range 22).all fun k =>
    ([St.A, St.B].all fun s1 =>
      if (k == 4 || k == 5 || k == 15 || k == 16) && s1 == .A then true
      else haltsWithin 30 (mkPhaseCfg k s1))

theorem collision_40_of_44_phases : checkAllPhases = true := by
  decide

/-- Physical sprint-trail arrival configuration: AG1 has flipped 1^inf behind p1 to alternating ...0101 / ...1010 -/
def mkSprintCfg (k : Nat) (s1 : St) : CetCfg :=
  let ag2_200 := runSingle ag2Step (199 + k) ⟨List.replicate 64 false, 20, .A⟩
  let p1 := ag2_200.pos - 20
  let wallLen := ag2_200.pos - 15
  let wantPrev := (s1 == .A)
  let sprintBehind := (List.range p1).map fun i =>
    if (p1 - 1 - i) % 2 == 0 then wantPrev else !wantPrev
  let bridge := List.replicate (wallLen - p1) true
  let tape := sprintBehind ++ bridge ++ ag2_200.tape.drop wallLen
  ⟨tape, p1, s1, ag2_200.pos, ag2_200.st⟩

def checkSprintPhases : Bool :=
  (List.range 22).all fun k =>
    ([St.A, St.B].all fun s1 =>
      if (k == 4 || k == 5 || k == 15 || k == 16) && s1 == .A then true
      else haltsWithin 30 (mkSprintCfg k s1))

theorem collision_40_of_44_sprint : checkSprintPhases = true := by
  decide

/-- Exact 2-step macro-transitions of AG1 in state A on (v0, v1) -/
theorem ag1_A_00 :
    let c1 := runSingle ag1Step 2 ⟨[false, false], 0, .A⟩
    c1.tape = [true, true] ∧ c1.pos = 0 ∧ c1.st = .C := by
  decide

theorem ag1_A_01 :
    let c1 := runSingle ag1Step 2 ⟨[false, true, false], 0, .A⟩
    c1.tape = [true, true, false] ∧ c1.pos = 2 ∧ c1.st = .A := by
  decide

theorem ag1_A_10 :
    let c1 := runSingle ag1Step 2 ⟨[true, false], 0, .A⟩
    c1.tape = [false, true] ∧ c1.pos = 0 ∧ c1.st = .C := by
  decide

theorem ag1_A_11 :
    let c1 := runSingle ag1Step 2 ⟨[true, true, false], 0, .A⟩
    c1.tape = [false, true, false] ∧ c1.pos = 2 ∧ c1.st = .A := by
  decide

/-- AG2 actually has minimal period P = 11, D = +1 on blank tape -/
theorem ag2_period_11 :
    let c0 : SingleCfg := ⟨List.replicate 64 false, 20, .A⟩
    let c1 := runSingle ag2Step 110 c0
    let c2 := runSingle ag2Step 11 c1
    c1.st = c2.st ∧ c2.pos = c1.pos + 1 := by
  decide

/-- AG1 leftward glider P = 10, D = -2 on 010101 | 001000 | 101010 -> shifts -2 and converts 01 to 10 -/
theorem ag1_glider_P10_left :
    let initTape : List Bool := [false, true, false, true, false, false, true, false, false, false, true, false]
    let c1 := runSingle ag1Step 10 ⟨initTape, 4, .D⟩
    c1.st = .D ∧ c1.pos = 2 ∧
    c1.tape = [false, true, false, false, true, false, false, false, true, false, true, false] := by
  decide

/-- AG1 leftward erasure in state C on 1 -/
theorem ag1_C_erase_1 :
    let c1 := runSingle ag1Step 1 ⟨[true, true], 1, .C⟩
    c1.st = .C ∧ c1.pos = 0 ∧ c1.tape = [true, false] := by
  decide

/-- Unboundedness Binary Potential Theorem for AG1 on arbitrary tape size N:
    evalTape N f < 2^N, and flipping bit (p+1) from false to true while preserving p and >= p+2
    strictly increases evalTape N regardless of arbitrary modifications below p. -/
def evalTape : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => evalTape n f + (if f n then 2 ^ n else 0)

theorem evalTape_lt (n : Nat) (f : Nat → Bool) : evalTape n f < 2 ^ n := by
  induction n with
  | zero => simp [evalTape]
  | succ n ih =>
    simp only [evalTape, Nat.pow_succ, Nat.mul_two]
    cases f n
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega
    · simp only [↓reduceIte]; omega

theorem evalTape_congr (n : Nat) (f g : Nat → Bool) (h : ∀ i < n, f i = g i) :
    evalTape n f = evalTape n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evalTape]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem evalTape_strict_increase_at (p n : Nat) (hp : p + 2 ≤ n) (f g : Nat → Bool)
    (hf1 : f (p + 1) = false) (hg1 : g (p + 1) = true)
    (hgp : g p = f p)
    (hg_above : ∀ i, p + 2 ≤ i → i < n → g i = f i) :
    evalTape n f < evalTape n g := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : p + 2 ≤ m
    · have hlt := ih hm (fun i hi1 hi2 => hg_above i hi1 (Nat.lt_succ_of_lt hi2))
      have heqm := hg_above m hm (Nat.lt_succ_self m)
      simp only [evalTape, heqm]
      omega
    · have hmeq : m = p + 1 := by omega
      subst hmeq
      simp only [evalTape, hf1, hg1, hgp, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hbound : evalTape p f < 2 ^ p := evalTape_lt p f
      have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ, Nat.mul_comm]
      omega

/-- Infinite-tape configuration for AG1 (Nat indices 0, 1, 2, ... correspond to x = -2, -1, 0, ...) -/
structure InfCfg where
  tape : Nat → Bool
  pos  : Nat
  st   : St

def setFun (f : Nat → Bool) (i : Nat) (v : Bool) : Nat → Bool :=
  fun j => if j = i then v else f j

@[simp] theorem setFun_self (f : Nat → Bool) (i : Nat) (v : Bool) : setFun f i v i = v := by
  simp [setFun]

@[simp] theorem setFun_ne {f : Nat → Bool} {i j : Nat} {v : Bool} (h : j ≠ i) : setFun f i v j = f j := by
  simp [setFun, h]

def stepInf (c : InfCfg) : InfCfg :=
  let tr := ag1Step c.st (c.tape c.pos)
  let pos' := if tr.d = 1 then c.pos + 1 else c.pos - 1
  ⟨setFun c.tape c.pos tr.w, pos', tr.ns⟩

def runInf : Nat → InfCfg → InfCfg
  | 0, c => c
  | n + 1, c => runInf n (stepInf c)

private theorem int_neg_one_ne : ((-1 : Int) = 1) = False := by decide

@[simp] theorem stepInf_A_f {t p} (h : t p = false) :
    stepInf ⟨t, p, .A⟩ = ⟨setFun t p true, p + 1, .B⟩ := by
  simp [stepInf, h, ag1Step]

@[simp] theorem stepInf_A_t {t p} (h : t p = true) :
    stepInf ⟨t, p, .A⟩ = ⟨setFun t p false, p + 1, .B⟩ := by
  simp [stepInf, h, ag1Step]

@[simp] theorem stepInf_B_f {t p} (h : t p = false) :
    stepInf ⟨t, p, .B⟩ = ⟨setFun t p true, p - 1, .C⟩ := by
  simp [stepInf, h, ag1Step, int_neg_one_ne]

@[simp] theorem stepInf_B_t {t p} (h : t p = true) :
    stepInf ⟨t, p, .B⟩ = ⟨setFun t p true, p + 1, .A⟩ := by
  simp [stepInf, h, ag1Step]

@[simp] theorem stepInf_C_f {t p} (h : t p = false) :
    stepInf ⟨t, p, .C⟩ = ⟨setFun t p true, p - 1, .D⟩ := by
  simp [stepInf, h, ag1Step, int_neg_one_ne]

@[simp] theorem stepInf_C_t {t p} (h : t p = true) :
    stepInf ⟨t, p, .C⟩ = ⟨setFun t p false, p - 1, .C⟩ := by
  simp [stepInf, h, ag1Step, int_neg_one_ne]

@[simp] theorem stepInf_D_f {t p} (h : t p = false) :
    stepInf ⟨t, p, .D⟩ = ⟨setFun t p false, p + 1, .A⟩ := by
  simp [stepInf, h, ag1Step]

@[simp] theorem stepInf_D_t {t p} (h : t p = true) :
    stepInf ⟨t, p, .D⟩ = ⟨setFun t p false, p - 1, .D⟩ := by
  simp [stepInf, h, ag1Step, int_neg_one_ne]

/-- Exact inductive invariant proving AG1 never steps left of x = -2 (index 0) and tape 0 = false forever -/
def LeftWallInv (c : InfCfg) : Prop :=
  c.tape 0 = false ∧
  (c.pos = 0 → c.st = .D ∧ c.tape 1 = true) ∧
  (c.pos ≥ 2 → c.tape 1 = false) ∧
  (c.pos = 1 →
    (c.st = .A → c.tape 1 = true) ∧
    (c.st = .B → False) ∧
    (c.st = .C → c.tape 1 = false) ∧
    (c.st = .D → c.tape 1 = false))

theorem leftWallInv_init : LeftWallInv ⟨fun _ => false, 2, .A⟩ := by
  dsimp only [LeftWallInv]
  exact ⟨rfl, ⟨fun h => (by cases h), ⟨fun _ => rfl, fun h => (by cases h)⟩⟩⟩

theorem leftWallInv_step (c : InfCfg) (h : LeftWallInv c) : LeftWallInv (stepInf c) := by
  rcases h with ⟨ht0, hp0, hp2, hp1⟩
  rcases c with ⟨tape, pos, st⟩
  dsimp only at ht0 hp0 hp2 hp1
  by_cases h0 : pos = 0
  · subst h0
    obtain ⟨hst, ht1⟩ := hp0 rfl
    subst hst
    rw [stepInf_D_f ht0]
    dsimp only [LeftWallInv]
    refine ⟨setFun_self _ _ _, ⟨fun h => (by cases h), ⟨fun h => (by omega), fun _ => ?_⟩⟩⟩
    exact ⟨fun _ => (by rw [setFun_ne (by decide), ht1]),
      ⟨fun h => (by cases h), ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩⟩
  · by_cases h1 : pos = 1
    · subst h1
      obtain ⟨hA, hB, hC, hD⟩ := hp1 rfl
      cases st
      · have ht1 := hA rfl
        rw [stepInf_A_t ht1]
        dsimp only [LeftWallInv]
        exact ⟨by rw [setFun_ne (by decide), ht0], ⟨fun h => (by cases h), ⟨fun _ => setFun_self _ _ _, fun h => (by cases h)⟩⟩⟩
      · exact False.elim (hB rfl)
      · have ht1 := hC rfl
        rw [stepInf_C_f ht1]
        dsimp only [LeftWallInv]
        exact ⟨by rw [setFun_ne (by decide), ht0], ⟨fun _ => ⟨rfl, setFun_self _ _ _⟩,
          ⟨fun h => (by omega), fun h => (by cases h)⟩⟩⟩
      · have ht1 := hD rfl
        rw [stepInf_D_f ht1]
        dsimp only [LeftWallInv]
        exact ⟨by rw [setFun_ne (by decide), ht0], ⟨fun h => (by cases h), ⟨fun _ => setFun_self _ _ _, fun h => (by cases h)⟩⟩⟩
    · have hge2 : pos ≥ 2 := by omega
      have ht1 := hp2 hge2
      have h0ne : (0 : Nat) ≠ pos := by omega
      have h1ne : (1 : Nat) ≠ pos := by omega
      have rw0 : ∀ w, setFun tape pos w 0 = false := fun w => by rw [setFun_ne h0ne, ht0]
      have rw1 : ∀ w, setFun tape pos w 1 = false := fun w => by rw [setFun_ne h1ne, ht1]
      cases st <;> cases htv : tape pos
      · rw [stepInf_A_f htv]; dsimp only [LeftWallInv]
        exact ⟨rw0 _, ⟨fun h => (by omega), ⟨fun _ => rw1 _, fun h => (by omega)⟩⟩⟩
      · rw [stepInf_A_t htv]; dsimp only [LeftWallInv]
        exact ⟨rw0 _, ⟨fun h => (by omega), ⟨fun _ => rw1 _, fun h => (by omega)⟩⟩⟩
      · rw [stepInf_B_f htv]; dsimp only [LeftWallInv]
        exact ⟨rw0 _, ⟨fun h => (by omega), ⟨fun _ => rw1 _,
          fun _ => ⟨fun hc => (by cases hc), ⟨fun hc => (by cases hc), ⟨fun _ => rw1 _, fun _ => rw1 _⟩⟩⟩⟩⟩⟩
      · rw [stepInf_B_t htv]; dsimp only [LeftWallInv]
        exact ⟨rw0 _, ⟨fun h => (by omega), ⟨fun _ => rw1 _, fun h => (by omega)⟩⟩⟩
      · rw [stepInf_C_f htv]; dsimp only [LeftWallInv]
        exact ⟨rw0 _, ⟨fun h => (by omega), ⟨fun _ => rw1 _,
          fun _ => ⟨fun hc => (by cases hc), ⟨fun hc => (by cases hc), ⟨fun _ => rw1 _, fun _ => rw1 _⟩⟩⟩⟩⟩⟩
      · rw [stepInf_C_t htv]; dsimp only [LeftWallInv]
        exact ⟨rw0 _, ⟨fun h => (by omega), ⟨fun _ => rw1 _,
          fun _ => ⟨fun hc => (by cases hc), ⟨fun hc => (by cases hc), ⟨fun _ => rw1 _, fun _ => rw1 _⟩⟩⟩⟩⟩⟩
      · rw [stepInf_D_f htv]; dsimp only [LeftWallInv]
        exact ⟨rw0 _, ⟨fun h => (by omega), ⟨fun _ => rw1 _, fun h => (by omega)⟩⟩⟩
      · rw [stepInf_D_t htv]; dsimp only [LeftWallInv]
        exact ⟨rw0 _, ⟨fun h => (by omega), ⟨fun _ => rw1 _,
          fun _ => ⟨fun hc => (by cases hc), ⟨fun hc => (by cases hc), ⟨fun _ => rw1 _, fun _ => rw1 _⟩⟩⟩⟩⟩⟩

/-- 2-step A macro-transition on arbitrary infinite tape at pos p with tape (p+1) = true -/
theorem ag1_inf_A_true (tape : Nat → Bool) (p : Nat) (ht1 : tape (p + 1) = true) :
    let c' := runInf 2 ⟨tape, p, .A⟩
    c'.pos = p + 2 ∧ c'.st = .A ∧
    (∀ i, i < p → c'.tape i = tape i) ∧
    (∀ i, i ≥ p + 2 → c'.tape i = tape i) := by
  have h1ne : p + 1 ≠ p := by omega
  cases h0 : tape p
  · have hr : runInf 2 ⟨tape, p, .A⟩ = ⟨setFun (setFun tape p true) (p + 1) true, p + 2, .A⟩ := by
      rw [runInf, runInf, runInf, stepInf_A_f h0]
      have hread : setFun tape p true (p + 1) = true := by rw [setFun_ne h1ne, ht1]
      rw [stepInf_B_t hread]
    dsimp only; rw [hr]; dsimp only
    refine ⟨rfl, ⟨rfl, ⟨fun i hi => ?_, fun i hi => ?_⟩⟩⟩
    · rw [setFun_ne (by omega), setFun_ne (by omega)]
    · rw [setFun_ne (by omega), setFun_ne (by omega)]
  · have hr : runInf 2 ⟨tape, p, .A⟩ = ⟨setFun (setFun tape p false) (p + 1) true, p + 2, .A⟩ := by
      rw [runInf, runInf, runInf, stepInf_A_t h0]
      have hread : setFun tape p false (p + 1) = true := by rw [setFun_ne h1ne, ht1]
      rw [stepInf_B_t hread]
    dsimp only; rw [hr]; dsimp only
    refine ⟨rfl, ⟨rfl, ⟨fun i hi => ?_, fun i hi => ?_⟩⟩⟩
    · rw [setFun_ne (by omega), setFun_ne (by omega)]
    · rw [setFun_ne (by omega), setFun_ne (by omega)]

/-- 3-step A->C/D turning transition on arbitrary infinite tape at pos p >= 1 with tape (p+1) = false -/
theorem ag1_inf_A_false (tape : Nat → Bool) (p : Nat) (hp : p ≥ 1) (ht1 : tape (p + 1) = false) :
    let c' := runInf 3 ⟨tape, p, .A⟩
    c'.pos = p - 1 ∧ (c'.st = .C ∨ c'.st = .D) ∧
    c'.tape p = tape p ∧ c'.tape (p + 1) = true ∧
    (∀ i, i ≥ p + 2 → c'.tape i = tape i) := by
  have h1ne : p + 1 ≠ p := by omega
  have hne1 : p ≠ p + 1 := by omega
  have hsub : p + 1 - 1 = p := by omega
  cases h0 : tape p
  · have hr : runInf 3 ⟨tape, p, .A⟩ =
        ⟨setFun (setFun (setFun tape p true) (p + 1) true) p false, p - 1, .C⟩ := by
      rw [runInf, runInf, runInf, runInf, stepInf_A_f h0]
      have hr1 : setFun tape p true (p + 1) = false := by rw [setFun_ne h1ne, ht1]
      rw [stepInf_B_f hr1, hsub]
      have hr2 : setFun (setFun tape p true) (p + 1) true p = true := by rw [setFun_ne hne1, setFun_self]
      rw [stepInf_C_t hr2]
    dsimp only; rw [hr]; dsimp only
    refine ⟨rfl, ⟨Or.inl rfl, ⟨?_, ⟨?_, fun i hi => ?_⟩⟩⟩⟩
    · rw [setFun_self]
    · rw [setFun_ne h1ne, setFun_self]
    · rw [setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega)]
  · have hr : runInf 3 ⟨tape, p, .A⟩ =
        ⟨setFun (setFun (setFun tape p false) (p + 1) true) p true, p - 1, .D⟩ := by
      rw [runInf, runInf, runInf, runInf, stepInf_A_t h0]
      have hr1 : setFun tape p false (p + 1) = false := by rw [setFun_ne h1ne, ht1]
      rw [stepInf_B_f hr1, hsub]
      have hr2 : setFun (setFun tape p false) (p + 1) true p = false := by rw [setFun_ne hne1, setFun_self]
      rw [stepInf_C_f hr2]
    dsimp only; rw [hr]; dsimp only
    refine ⟨rfl, ⟨Or.inr rfl, ⟨?_, ⟨?_, fun i hi => ?_⟩⟩⟩⟩
    · rw [setFun_self]
    · rw [setFun_ne h1ne, setFun_self]
    · rw [setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega)]

theorem leftWallInv_never_underflows (c : InfCfg) (h : LeftWallInv c) (hp : c.pos = 0) :
    (ag1Step c.st (c.tape c.pos)).d = 1 := by
  obtain ⟨ht0, hp0, _, _⟩ := h
  obtain ⟨hst, _⟩ := hp0 hp
  rw [hst, hp, ht0]
  decide

theorem runInf_add (a b : Nat) (c : InfCfg) : runInf (a + b) c = runInf b (runInf a c) := by
  induction a generalizing c with
  | zero => simp [runInf]
  | succ a ih =>
    rw [Nat.succ_add, runInf, ih (stepInf c), runInf]

theorem leftWallInv_runInf (n : Nat) (c : InfCfg) (h : LeftWallInv c) : LeftWallInv (runInf n c) := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih => exact ih (stepInf c) (leftWallInv_step c h)

/-- Leftward C/D pass from pos under LeftWallInv reaches pos' in [1..pos+1] in state A
    without modifying any cell > pos -/
theorem ag1_cd_return (pos : Nat) :
    ∀ (tape : Nat → Bool) (st : St),
      LeftWallInv ⟨tape, pos, st⟩ → (st = .C ∨ st = .D) →
      ∃ k tape' pos', k ≥ 1 ∧
        runInf k ⟨tape, pos, st⟩ = ⟨tape', pos', .A⟩ ∧
        1 ≤ pos' ∧ pos' ≤ pos + 1 ∧
        LeftWallInv ⟨tape', pos', .A⟩ ∧
        (∀ i, i > pos → tape' i = tape i) := by
  induction pos with
  | zero =>
    intro tape st hinv _
    have ⟨ht0, hp0, _, _⟩ := hinv
    obtain ⟨hst, _⟩ := hp0 rfl
    dsimp only at ht0 hst
    subst hst
    have hstep := stepInf_D_f ht0
    refine ⟨1, setFun tape 0 false, 1, Nat.le_refl 1, ?_, Nat.le_refl 1, Nat.le_refl 1, ?_, ?_⟩
    · rw [runInf, runInf, hstep]
    · rw [← hstep]; exact leftWallInv_step _ hinv
    · intro i hi; rw [setFun_ne (by omega)]
  | succ p ih =>
    intro tape st hinv hcd
    rcases hcd with rfl | rfl
    · cases htv : tape (p + 1)
      · have hstep := stepInf_C_f htv
        have hsub : p + 1 - 1 = p := by omega
        rw [hsub] at hstep
        have hinv1 : LeftWallInv ⟨setFun tape (p + 1) true, p, .D⟩ := by
          rw [← hstep]; exact leftWallInv_step _ hinv
        obtain ⟨k, tape', pos', hk, hrun, hlo, hhi, hinv', hag⟩ :=
          ih (setFun tape (p + 1) true) .D hinv1 (Or.inr rfl)
        refine ⟨k + 1, tape', pos', by omega, ?_, hlo, by omega, hinv', ?_⟩
        · rw [runInf, hstep, hrun]
        · intro i hi
          rw [hag i (by omega), setFun_ne (by omega)]
      · have hstep := stepInf_C_t htv
        have hsub : p + 1 - 1 = p := by omega
        rw [hsub] at hstep
        have hinv1 : LeftWallInv ⟨setFun tape (p + 1) false, p, .C⟩ := by
          rw [← hstep]; exact leftWallInv_step _ hinv
        obtain ⟨k, tape', pos', hk, hrun, hlo, hhi, hinv', hag⟩ :=
          ih (setFun tape (p + 1) false) .C hinv1 (Or.inl rfl)
        refine ⟨k + 1, tape', pos', by omega, ?_, hlo, by omega, hinv', ?_⟩
        · rw [runInf, hstep, hrun]
        · intro i hi
          rw [hag i (by omega), setFun_ne (by omega)]
    · cases htv : tape (p + 1)
      · have hstep := stepInf_D_f htv
        have hinv1 : LeftWallInv ⟨setFun tape (p + 1) false, p + 2, .A⟩ := by
          rw [← hstep]; exact leftWallInv_step _ hinv
        refine ⟨1, setFun tape (p + 1) false, p + 2, Nat.le_refl 1, ?_, by omega, by omega, hinv1, ?_⟩
        · rw [runInf, runInf, hstep]
        · intro i hi; rw [setFun_ne (by omega)]
      · have hstep := stepInf_D_t htv
        have hsub : p + 1 - 1 = p := by omega
        rw [hsub] at hstep
        have hinv1 : LeftWallInv ⟨setFun tape (p + 1) false, p, .D⟩ := by
          rw [← hstep]; exact leftWallInv_step _ hinv
        obtain ⟨k, tape', pos', hk, hrun, hlo, hhi, hinv', hag⟩ :=
          ih (setFun tape (p + 1) false) .D hinv1 (Or.inr rfl)
        refine ⟨k + 1, tape', pos', by omega, ?_, hlo, by omega, hinv', ?_⟩
        · rw [runInf, hstep, hrun]
        · intro i hi
          rw [hag i (by omega), setFun_ne (by omega)]

/-- Starting from (tape, p, A) with 1 <= p <= N, AG1 sprints right by +2 until either exiting >= N+1 in A
    or reaching some q <= N with tape_q (q+1) = false while preserving tape at all i >= q. -/
theorem ag1_a_find_turn (N : Nat) :
    ∀ (d : Nat) (tape : Nat → Bool) (p : Nat),
      1 ≤ p → p ≤ N → N - p ≤ d → LeftWallInv ⟨tape, p, .A⟩ →
      (∃ k tape' pos', runInf k ⟨tape, p, .A⟩ = ⟨tape', pos', .A⟩ ∧ pos' ≥ N + 1 ∧ LeftWallInv ⟨tape', pos', .A⟩) ∨
      (∃ k tape_q q, p ≤ q ∧ q ≤ N ∧ runInf k ⟨tape, p, .A⟩ = ⟨tape_q, q, .A⟩ ∧
        LeftWallInv ⟨tape_q, q, .A⟩ ∧ tape_q (q + 1) = false ∧ (∀ i, i ≥ q → tape_q i = tape i)) := by
  intro d
  induction d with
  | zero =>
    intro tape p hp1 hpN hd hinv
    have hpeq : p = N := by omega
    subst hpeq
    cases ht1 : tape (p + 1)
    · exact Or.inr ⟨0, tape, p, Nat.le_refl p, Nat.le_refl p, rfl, hinv, ht1, fun _ _ => rfl⟩
    · obtain ⟨hpos, hst, _, _⟩ := ag1_inf_A_true tape p ht1
      have hinv2 := leftWallInv_runInf 2 ⟨tape, p, .A⟩ hinv
      rcases hrun : runInf 2 ⟨tape, p, .A⟩ with ⟨tape2, pos2, st2⟩
      rw [hrun] at hpos hst hinv2
      dsimp only at hpos hst
      subst hpos; subst hst
      exact Or.inl ⟨2, tape2, p + 2, hrun, by omega, hinv2⟩
  | succ d ih =>
    intro tape p hp1 hpN hd hinv
    cases ht1 : tape (p + 1)
    · exact Or.inr ⟨0, tape, p, Nat.le_refl p, hpN, rfl, hinv, ht1, fun _ _ => rfl⟩
    · obtain ⟨hpos, hst, _, hge⟩ := ag1_inf_A_true tape p ht1
      have hinv2 := leftWallInv_runInf 2 ⟨tape, p, .A⟩ hinv
      rcases hrun : runInf 2 ⟨tape, p, .A⟩ with ⟨tape2, pos2, st2⟩
      rw [hrun] at hpos hst hge hinv2
      dsimp only at hpos hst hge
      subst hpos; subst hst
      by_cases hexit : p + 2 ≥ N + 1
      · exact Or.inl ⟨2, tape2, p + 2, hrun, hexit, hinv2⟩
      · have hp2N : p + 2 ≤ N := by omega
        have hd' : N - (p + 2) ≤ d := by omega
        rcases ih tape2 (p + 2) (by omega) hp2N hd' hinv2 with
          ⟨k', tape', pos', hrun', hex', hinv'⟩ | ⟨k', tape_q, q, hqp, hqN, hrun', hinv_q, htf, hqge⟩
        · refine Or.inl ⟨2 + k', tape', pos', ?_, hex', hinv'⟩
          rw [runInf_add, hrun, hrun']
        · refine Or.inr ⟨2 + k', tape_q, q, by omega, hqN, ?_, hinv_q, htf, ?_⟩
          · rw [runInf_add, hrun, hrun']
          · intro i hi
            rw [hqge i hi, hge i (by omega)]

/-- One macro-cycle from (tape, p, A) with 1 <= p <= N either exits >= N+1 in A
    or completes a bounce+return to (tape', pos', A) inside [1..N] strictly increasing evalTape (N+2) -/
theorem ag1_bounce_or_exit (N : Nat) (tape : Nat → Bool) (p : Nat)
    (hp1 : 1 ≤ p) (hpN : p ≤ N) (hinv : LeftWallInv ⟨tape, p, .A⟩) :
    (∃ k tape' pos', runInf k ⟨tape, p, .A⟩ = ⟨tape', pos', .A⟩ ∧ pos' ≥ N + 1 ∧ LeftWallInv ⟨tape', pos', .A⟩) ∨
    (∃ k tape' pos', runInf k ⟨tape, p, .A⟩ = ⟨tape', pos', .A⟩ ∧ 1 ≤ pos' ∧ pos' ≤ N ∧
      LeftWallInv ⟨tape', pos', .A⟩ ∧ evalTape (N + 2) tape < evalTape (N + 2) tape') := by
  rcases ag1_a_find_turn N (N - p) tape p hp1 hpN (Nat.le_refl _) hinv with
    h_exit | ⟨k1, tape_q, q, hqp, hqN, hrun1, hinv_q, hqf, hqge⟩
  · exact Or.inl h_exit
  · obtain ⟨hpos_t, hcd, htq, htq1, htge2⟩ := ag1_inf_A_false tape_q q (by omega) hqf
    have hinv_t := leftWallInv_runInf 3 ⟨tape_q, q, .A⟩ hinv_q
    rcases hrun2 : runInf 3 ⟨tape_q, q, .A⟩ with ⟨tape_t, pos_t, st_t⟩
    rw [hrun2] at hpos_t hcd htq htq1 htge2 hinv_t
    dsimp only at hpos_t hcd htq htq1 htge2
    subst hpos_t
    obtain ⟨k3, tape', pos', _, hrun3, hlo, hhi, hinv', hag⟩ :=
      ag1_cd_return (q - 1) tape_t st_t hinv_t hcd
    have hrun_all : runInf (k1 + 3 + k3) ⟨tape, p, .A⟩ = ⟨tape', pos', .A⟩ := by
      rw [runInf_add, runInf_add, hrun1, hrun2, hrun3]
    by_cases hpos' : pos' ≥ N + 1
    · exact Or.inl ⟨k1 + 3 + k3, tape', pos', hrun_all, hpos', hinv'⟩
    · refine Or.inr ⟨k1 + 3 + k3, tape', pos', hrun_all, hlo, by omega, hinv', ?_⟩
      apply evalTape_strict_increase_at q (N + 2) (by omega) tape tape'
      · rw [← hqge (q + 1) (by omega)]; exact hqf
      · rw [hag (q + 1) (by omega)]; exact htq1
      · rw [hag q (by omega), htq, hqge q (Nat.le_refl q)]
      · intro i hi _
        rw [hag i (by omega), htge2 i hi, hqge i (by omega)]

/-- Unconditional Unboundedness Theorem for AG1 inside any bounded prefix [0..N]:
    from LeftWallInv at pos in [1..N] in state A, AG1 reaches pos' >= N+1 in state A in finite time -/
theorem ag1_exit_bounded (N : Nat) :
    ∀ (fuel : Nat) (tape : Nat → Bool) (p : Nat),
      1 ≤ p → p ≤ N → LeftWallInv ⟨tape, p, .A⟩ →
      2 ^ (N + 2) - evalTape (N + 2) tape ≤ fuel →
      ∃ k tape' pos', runInf k ⟨tape, p, .A⟩ = ⟨tape', pos', .A⟩ ∧ pos' ≥ N + 1 ∧ LeftWallInv ⟨tape', pos', .A⟩ := by
  intro fuel
  induction fuel with
  | zero =>
    intro tape p hp1 hpN hinv hfuel
    have hlt := evalTape_lt (N + 2) tape
    omega
  | succ fuel ih =>
    intro tape p hp1 hpN hinv hfuel
    rcases ag1_bounce_or_exit N tape p hp1 hpN hinv with
      h_exit | ⟨k1, tape1, pos1, hrun1, hlo1, hhi1, hinv1, hinc⟩
    · exact h_exit
    · have hlt1 := evalTape_lt (N + 2) tape1
      have hfuel' : 2 ^ (N + 2) - evalTape (N + 2) tape1 ≤ fuel := by omega
      obtain ⟨k2, tape', pos', hrun2, hex', hinv'⟩ :=
        ih tape1 pos1 hlo1 hhi1 hinv1 hfuel'
      refine ⟨k1 + k2, tape', pos', ?_, hex', hinv'⟩
      rw [runInf_add, hrun1, hrun2]

/-- Standalone AG1 on blank tape (starting at x = 0 <-> index 2) crosses every barrier N >= 0
    in finite time in state A -/
theorem ag1_unbounded_exit (N : Nat) :
    ∃ k tape' pos',
      runInf k ⟨fun _ => false, 2, .A⟩ = ⟨tape', pos', .A⟩ ∧ pos' ≥ N + 1 := by
  by_cases hN : N ≤ 1
  · exact ⟨0, fun _ => false, 2, rfl, by omega⟩
  · obtain ⟨k, tape', pos', hrun, hex, _⟩ :=
      ag1_exit_bounded N (2 ^ (N + 2)) (fun _ => false) 2 (by omega) (by omega) leftWallInv_init (Nat.sub_le _ _)
    exact ⟨k, tape', pos', hrun, hex⟩

/-!
## Extended Paired CET(4) Formalization & Bounce-2 -> Overflow-3 Reduction

Proves:
1. Exact transition parity invariant (`stepInf_parity`).
2. Exact bit-packed <-> infinite-tape bijection (`stepCetNat_to_inf`, `runCetNat_to_inf`).
3. Verified all-blank-tape execution `t = 0 .. 1135 .. 2000` (`cet_verified_0_to_2000`, `cet4_t0_to_t2000_exact`),
   establishing `LeftWallInv` for `AG1` and an active `+1/11` glider on `0^∞` for `AG2`.
4. Infinite-tape inductive period/sweep/erasure lemmas:
   - `ag2_glider_P11_right` (`+k` in `11 * k` steps, leaving solid `true` wake)
   - `ag1_glider_P10_left_inf` (`-2k` in `10 * k` steps, leaving `(0,1)^k` wake)
   - `ag1_sprint_A_inf`, `ag1_erasure_sweep_A`, `ag1_turn_00_C`, `ag1_erase_C`.
5. Exact finite check of all 4 surviving Collision #2 sprint modes (`collision2_modes_verified`).
6. Exact head-decoupling theorem (`cet_decoupled_run`) and unconditional bounded breakout / collision
   theorems (`cet4_post_bounce_must_overflow_or_collide`, `cet4_from_blank_reaches_wall`,
   `cet4_bounce2_to_overflow3_reduction`).
-/

def stepInf2 (c : InfCfg) : InfCfg :=
  let tr := ag2Step c.st (c.tape c.pos)
  let pos' := if tr.d = 1 then c.pos + 1 else c.pos - 1
  ⟨setFun c.tape c.pos tr.w, pos', tr.ns⟩

def runInf2 : Nat → InfCfg → InfCfg
  | 0, c => c
  | n + 1, c => runInf2 n (stepInf2 c)

theorem runInf2_add (a b : Nat) (c : InfCfg) :
    runInf2 (a + b) c = runInf2 b (runInf2 a c) := by
  induction a generalizing c with
  | zero => simp [runInf2]
  | succ k ih =>
    rw [Nat.succ_add]
    exact ih (stepInf2 c)

theorem runInf_succ_left (n : Nat) (c : InfCfg) :
    runInf (n + 1) c = stepInf (runInf n c) := by
  have h := runInf_add n 1 c
  simpa [runInf] using h

theorem runInf2_succ_left (n : Nat) (c : InfCfg) :
    runInf2 (n + 1) c = stepInf2 (runInf2 n c) := by
  have h := runInf2_add n 1 c
  simpa [runInf2] using h

@[simp] theorem stepInf2_A_f {t p} (h : t p = false) :
    stepInf2 ⟨t, p, .A⟩ = ⟨setFun t p true, p + 1, .C⟩ := by simp [stepInf2, h, ag2Step]
@[simp] theorem stepInf2_A_t {t p} (h : t p = true) :
    stepInf2 ⟨t, p, .A⟩ = ⟨setFun t p false, p + 1, .C⟩ := by simp [stepInf2, h, ag2Step]
@[simp] theorem stepInf2_B_f {t p} (h : t p = false) :
    stepInf2 ⟨t, p, .B⟩ = ⟨setFun t p true, p - 1, .A⟩ := by simp [stepInf2, h, ag2Step, int_neg_one_ne]
@[simp] theorem stepInf2_B_t {t p} (h : t p = true) :
    stepInf2 ⟨t, p, .B⟩ = ⟨setFun t p false, p + 1, .C⟩ := by simp [stepInf2, h, ag2Step]
@[simp] theorem stepInf2_C_f {t p} (h : t p = false) :
    stepInf2 ⟨t, p, .C⟩ = ⟨setFun t p true, p - 1, .A⟩ := by simp [stepInf2, h, ag2Step, int_neg_one_ne]
@[simp] theorem stepInf2_C_t {t p} (h : t p = true) :
    stepInf2 ⟨t, p, .C⟩ = ⟨setFun t p true, p + 1, .D⟩ := by simp [stepInf2, h, ag2Step]
@[simp] theorem stepInf2_D_f {t p} (h : t p = false) :
    stepInf2 ⟨t, p, .D⟩ = ⟨setFun t p true, p - 1, .D⟩ := by simp [stepInf2, h, ag2Step, int_neg_one_ne]
@[simp] theorem stepInf2_D_t {t p} (h : t p = true) :
    stepInf2 ⟨t, p, .D⟩ = ⟨setFun t p true, p - 1, .B⟩ := by simp [stepInf2, h, ag2Step, int_neg_one_ne]

theorem ag1Step_d (s : St) (b : Bool) : (ag1Step s b).d = 1 ∨ (ag1Step s b).d = -1 := by
  cases s <;> cases b <;> decide

theorem ag2Step_d (s : St) (b : Bool) : (ag2Step s b).d = 1 ∨ (ag2Step s b).d = -1 := by
  cases s <;> cases b <;> decide

/-- Stepwise bipartite parity invariant for AG1 whenever head does not clamp at 0 -/
theorem stepInf_parity (c : InfCfg) (hne : ¬(c.pos = 0 ∧ (ag1Step c.st (c.tape c.pos)).d = -1)) :
    (stepInf c).pos % 2 ≠ c.pos % 2 := by
  simp only [stepInf]
  rcases ag1Step_d c.st (c.tape c.pos) with hd | hd
  · simp [hd]; omega
  · rcases Nat.eq_zero_or_pos c.pos with h0 | hgt
    · exact absurd ⟨h0, hd⟩ hne
    · simp only [hd, int_neg_one_ne, ↓reduceIte]; omega

/-- Bit-packed Nat tape for fast kernel simulation vs exact infinite-tape model -/
def writeBit (m i : Nat) (v : Bool) : Nat :=
  if m.testBit i == v then m else m ^^^ (1 <<< i)

private theorem one_testBit_zero : (1 : Nat).testBit 0 = true := by decide

theorem writeBit_testBit (m i j : Nat) (v : Bool) :
    (writeBit m i v).testBit j = if j = i then v else m.testBit j := by
  unfold writeBit
  split
  · rename_i h
    have hv : m.testBit i = v := beq_iff_eq.mp h
    by_cases hji : j = i
    · subst hji; simp [hv]
    · simp [hji]
  · rename_i h
    have hne : m.testBit i ≠ v := fun heq => h (beq_iff_eq.mpr heq)
    rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst hji
      simp only [Nat.le_refl, decide_true, Nat.sub_self, one_testBit_zero,
        Bool.true_and, ↓reduceIte]
      cases hm : m.testBit j <;> cases v <;> simp_all
    · by_cases hij : i ≤ j
      · have hgt : j - i ≠ 0 := by omega
        have htb : (1 : Nat).testBit (j - i) = false := by
          cases hd : j - i with
          | zero => contradiction
          | succ _ => simp [Nat.testBit_succ]
        simp [htb, hji]
      · simp [hij, hji]

structure CetNatCfg where
  tape : Nat
  p1 : Nat
  s1 : St
  p2 : Nat
  s2 : St
  deriving DecidableEq

def stepCetNat (c : CetNatCfg) : Option CetNatCfg :=
  if c.p1 == c.p2 then none
  else
    let tr1 := ag1Step c.s1 (c.tape.testBit c.p1)
    let tr2 := ag2Step c.s2 (c.tape.testBit c.p2)
    let tape1 := writeBit c.tape c.p2 tr2.w
    let tape2 := writeBit tape1 c.p1 tr1.w
    let p1' := (Int.ofNat c.p1 + tr1.d).toNat
    let p2' := (Int.ofNat c.p2 + tr2.d).toNat
    if p1' == p2' then none
    else some ⟨tape2, p1', tr1.ns, p2', tr2.ns⟩

def runCetNatNoHalt : Nat → Option CetNatCfg → Option CetNatCfg
  | 0, oc => oc
  | _ + 1, none => none
  | n + 1, some c => runCetNatNoHalt n (stepCetNat c)

theorem runCetNatNoHalt_add (a b : Nat) (oc : Option CetNatCfg) :
    runCetNatNoHalt (a + b) oc = runCetNatNoHalt b (runCetNatNoHalt a oc) := by
  induction a generalizing oc with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
    rw [Nat.succ_add]
    cases oc with
    | none =>
      simp only [runCetNatNoHalt]
      cases b <;> rfl
    | some c => exact ih (stepCetNat c)

def c0Nat : CetNatCfg := ⟨0, 2, .A, 4, .A⟩

structure CetInfCfg where
  tape : Nat → Bool
  p1 : Nat
  s1 : St
  p2 : Nat
  s2 : St

def stepCetInf (c : CetInfCfg) : Option CetInfCfg :=
  if c.p1 == c.p2 then none
  else
    let tr1 := ag1Step c.s1 (c.tape c.p1)
    let tr2 := ag2Step c.s2 (c.tape c.p2)
    let tape1 := setFun c.tape c.p2 tr2.w
    let tape2 := setFun tape1 c.p1 tr1.w
    let p1' := if tr1.d = 1 then c.p1 + 1 else c.p1 - 1
    let p2' := if tr2.d = 1 then c.p2 + 1 else c.p2 - 1
    if p1' == p2' then none
    else some ⟨tape2, p1', tr1.ns, p2', tr2.ns⟩

def runCetInf : Nat → Option CetInfCfg → Option CetInfCfg
  | 0, oc => oc
  | _ + 1, none => none
  | n + 1, some c => runCetInf n (stepCetInf c)

theorem runCetInf_add (a b : Nat) (oc : Option CetInfCfg) :
    runCetInf (a + b) oc = runCetInf b (runCetInf a oc) := by
  induction a generalizing oc with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
    rw [Nat.succ_add]
    cases oc with
    | none =>
      simp only [runCetInf]
      cases b <;> rfl
    | some c => exact ih (stepCetInf c)

def blankCetInf : CetInfCfg := ⟨fun _ => false, 2, .A, 4, .A⟩

def natToInf (c : CetNatCfg) : CetInfCfg :=
  ⟨fun i => c.tape.testBit i, c.p1, c.s1, c.p2, c.s2⟩

private theorem toNat_add_dir (p : Nat) (d : Int) (hd : d = 1 ∨ d = -1) :
    (Int.ofNat p + d).toNat = if d = 1 then p + 1 else p - 1 := by
  rcases hd with rfl | rfl
  · simp
  · simp [int_neg_one_ne]; omega

theorem stepCetNat_to_inf (c : CetNatCfg) :
    (stepCetNat c).map natToInf = stepCetInf (natToInf c) := by
  unfold stepCetNat stepCetInf natToInf
  dsimp only
  by_cases h12 : c.p1 = c.p2
  · have hb : (c.p1 == c.p2) = true := beq_iff_eq.mpr h12
    simp [hb]
  · have hnb : (c.p1 == c.p2) = false := beq_false_of_ne h12
    simp only [hnb, Bool.false_eq_true, ↓reduceIte]
    rw [toNat_add_dir c.p1 _ (ag1Step_d _ _), toNat_add_dir c.p2 _ (ag2Step_d _ _)]
    by_cases hcoll :
        (if (ag1Step c.s1 (c.tape.testBit c.p1)).d = 1 then c.p1 + 1 else c.p1 - 1) =
        (if (ag2Step c.s2 (c.tape.testBit c.p2)).d = 1 then c.p2 + 1 else c.p2 - 1)
    · have hcb :
          ((if (ag1Step c.s1 (c.tape.testBit c.p1)).d = 1 then c.p1 + 1 else c.p1 - 1) ==
           (if (ag2Step c.s2 (c.tape.testBit c.p2)).d = 1 then c.p2 + 1 else c.p2 - 1)) = true :=
        beq_iff_eq.mpr hcoll
      simp only [hcb, ↓reduceIte, Option.map_none]
    · have hcb :
          ((if (ag1Step c.s1 (c.tape.testBit c.p1)).d = 1 then c.p1 + 1 else c.p1 - 1) ==
           (if (ag2Step c.s2 (c.tape.testBit c.p2)).d = 1 then c.p2 + 1 else c.p2 - 1)) = false :=
        beq_false_of_ne hcoll
      simp only [hcb, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      congr 1
      apply congrArg (fun tp => ({ tape := tp, p1 := _, s1 := _, p2 := _, s2 := _ } : CetInfCfg))
      funext i
      rw [writeBit_testBit, writeBit_testBit]
      simp [setFun]

theorem runCetNat_to_inf (n : Nat) (oc : Option CetNatCfg) :
    (runCetNatNoHalt n oc).map natToInf = runCetInf n (oc.map natToInf) := by
  induction n generalizing oc with
  | zero => rfl
  | succ k ih =>
    cases oc with
    | none => simp [runCetNatNoHalt, runCetInf]
    | some c =>
      simp only [runCetNatNoHalt, runCetInf, Option.map_some]
      rw [ih, stepCetNat_to_inf]

theorem blankCetNat_to_inf : natToInf c0Nat = blankCetInf := by
  unfold natToInf c0Nat blankCetInf
  congr 1
  funext i
  simp

/-- Verified all-blank-tape execution t = 0..1135..2000 -/
def checkCet0To2000 : Bool :=
  match runCetNatNoHalt 1135 (some c0Nat) with
  | none => false
  | some c1 =>
    c1.p1 == 87 && c1.s1 == .A && c1.p2 == 107 && c1.s2 == .B && (c1.tape >>> 110 == 0) &&
    match runCetNatNoHalt 865 (some c1) with
    | none => false
    | some c2 =>
      c2.p1 == 2 && c2.s1 == .A && c2.p2 == 186 && c2.s2 == .B &&
      !(c2.tape.testBit 0) && !(c2.tape.testBit 1) &&
      !(c2.tape.testBit 185) && c2.tape.testBit 186 && c2.tape.testBit 187 &&
      (c2.tape >>> 188 == 0)

theorem cet_verified_0_to_2000 : checkCet0To2000 = true := by
  decide

theorem cet4_t0_to_t2000_exact :
    ∃ c2000, runCetInf 2000 (some blankCetInf) = some c2000 ∧
      c2000.p1 = 2 ∧ c2000.s1 = .A ∧ c2000.p2 = 186 ∧ c2000.s2 = .B ∧
      LeftWallInv ⟨c2000.tape, 2, .A⟩ ∧
      c2000.tape 185 = false ∧ c2000.tape 186 = true ∧ c2000.tape 187 = true ∧
      (∀ i ≥ 188, c2000.tape i = false) := by
  have h := cet_verified_0_to_2000
  unfold checkCet0To2000 at h
  cases h1 : runCetNatNoHalt 1135 (some c0Nat) with
  | none => simp [h1] at h
  | some c1 =>
    rw [h1] at h
    dsimp only at h
    cases h2 : runCetNatNoHalt 865 (some c1) with
    | none => simp [h2] at h
    | some c2 =>
      rw [h2] at h
      dsimp only at h
      have ⟨hp1, hs1, hp2, hs2, hb0, hb1, hb185, hb186, hb187, hshr⟩ :
          c2.p1 = 2 ∧ c2.s1 = .A ∧ c2.p2 = 186 ∧ c2.s2 = .B ∧
          c2.tape.testBit 0 = false ∧ c2.tape.testBit 1 = false ∧
          c2.tape.testBit 185 = false ∧ c2.tape.testBit 186 = true ∧ c2.tape.testBit 187 = true ∧
          c2.tape >>> 188 = 0 := by
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
        simp_all
      have hrun2000 : runCetInf 2000 (some blankCetInf) = some (natToInf c2) := by
        rw [← blankCetNat_to_inf, ← Option.map_some, ← runCetNat_to_inf]
        rw [show (2000 : Nat) = 1135 + 865 by decide, runCetNatNoHalt_add, h1, h2]
        rfl
      refine ⟨natToInf c2, hrun2000, hp1, hs1, hp2, hs2, ?_, hb185, hb186, hb187, ?_⟩
      · dsimp only [LeftWallInv, natToInf]
        exact ⟨hb0, fun h => by omega, fun _ => hb1, fun h => by omega⟩
      · intro i hi
        dsimp only [natToInf]
        have htb := congrArg (fun x => x.testBit (i - 188)) hshr
        simp only [Nat.testBit_shiftRight, show 188 + (i - 188) = i by omega, Nat.zero_testBit] at htb
        exact htb

/-- Canonical 4-cell update for one period of AG2's +1/11 glider -/
private def upd4_P11 (t : Nat → Bool) (p : Nat) : Nat → Bool :=
  setFun (setFun (setFun (setFun t (p - 1) true) p false) (p + 1) true) (p + 2) true

private theorem upd4_P11_m1 (t : Nat → Bool) {p : Nat} (hp : p ≥ 1) :
    upd4_P11 t p (p - 1) = true := by
  unfold upd4_P11
  rw [setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega), setFun_self]

private theorem upd4_P11_0 (t : Nat → Bool) {p : Nat} : upd4_P11 t p p = false := by
  unfold upd4_P11; rw [setFun_ne (by omega), setFun_ne (by omega), setFun_self]

private theorem upd4_P11_1 (t : Nat → Bool) {p : Nat} : upd4_P11 t p (p + 1) = true := by
  unfold upd4_P11; rw [setFun_ne (by omega), setFun_self]

private theorem upd4_P11_2 (t : Nat → Bool) {p : Nat} : upd4_P11 t p (p + 2) = true := by
  unfold upd4_P11; rw [setFun_self]

private theorem upd4_P11_ne (t : Nat → Bool) {p j : Nat} (hj : j < p - 1 ∨ j ≥ p + 3) :
    upd4_P11 t p j = t j := by
  unfold upd4_P11
  rcases hj with hj | hj <;>
    rw [setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega)]

theorem ag2_glider_P11_step_all (t : Nat → Bool) (p : Nat) (hp : p ≥ 1)
    (hm1 : t (p - 1) = false) (h0 : t p = true) (h1 : t (p + 1) = true) (h2 : t (p + 2) = false) :
    runInf2 11 ⟨t, p, .B⟩ = ⟨upd4_P11 t p, p + 1, .B⟩ ∧
    (∀ s ≤ 11, p - 1 ≤ (runInf2 s ⟨t, p, .B⟩).pos) := by
  have hs0 : runInf2 0 ⟨t, p, .B⟩ = ⟨t, p, .B⟩ := rfl
  have hs1 : runInf2 1 ⟨t, p, .B⟩ = ⟨setFun t p false, p + 1, .C⟩ := by
    rw [runInf2_succ_left]; exact stepInf2_B_t h0
  have hs2 : runInf2 2 ⟨t, p, .B⟩ = ⟨setFun (setFun t p false) (p + 1) true, p + 2, .D⟩ := by
    rw [runInf2_succ_left, hs1, stepInf2_C_t (by rw [setFun_ne (by omega)]; exact h1)]
  have hs3 : runInf2 3 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true, p + 1, .D⟩ := by
    rw [runInf2_succ_left, hs2, stepInf2_D_f (by rw [setFun_ne (by omega), setFun_ne (by omega)]; exact h2)]
    simp [show p + 2 - 1 = p + 1 by omega]
  have hs4 : runInf2 4 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 1) true, p, .B⟩ := by
    rw [runInf2_succ_left, hs3, stepInf2_D_t (by rw [setFun_ne (by omega), setFun_self])]
    simp [show p + 1 - 1 = p by omega]
  have hs5 : runInf2 5 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 1) true) p true, p - 1, .A⟩ := by
    rw [runInf2_succ_left, hs4,
        stepInf2_B_f (by rw [setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega), setFun_self])]
  have hs6 : runInf2 6 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 1) true) p true) (p - 1) true, p, .C⟩ := by
    rw [runInf2_succ_left, hs5, stepInf2_A_f]
    · simp [show p - 1 + 1 = p by omega]
    · repeat' rw [setFun_ne (by omega)]
      exact hm1
  have hs7 : runInf2 7 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 1) true) p true) (p - 1) true) p true, p + 1, .D⟩ := by
    rw [runInf2_succ_left, hs6, stepInf2_C_t (by rw [setFun_ne (by omega), setFun_self])]
  have hs8 : runInf2 8 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 1) true) p true) (p - 1) true) p true) (p + 1) true, p, .B⟩ := by
    rw [runInf2_succ_left, hs7, stepInf2_D_t]
    · simp [show p + 1 - 1 = p by omega]
    · repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
  have hs9 : runInf2 9 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 1) true) p true) (p - 1) true) p true) (p + 1) true) p false, p + 1, .C⟩ := by
    rw [runInf2_succ_left, hs8, stepInf2_B_t (by rw [setFun_ne (by omega), setFun_self])]
  have hs10 : runInf2 10 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 1) true) p true) (p - 1) true) p true) (p + 1) true) p false) (p + 1) true, p + 2, .D⟩ := by
    rw [runInf2_succ_left, hs9, stepInf2_C_t (by rw [setFun_ne (by omega), setFun_self])]
  have hs11_raw : runInf2 11 ⟨t, p, .B⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 1) true) p true) (p - 1) true) p true) (p + 1) true) p false) (p + 1) true) (p + 2) true, p + 1, .B⟩ := by
    rw [runInf2_succ_left, hs10,
        stepInf2_D_t (by repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)]))]
    simp [show p + 2 - 1 = p + 1 by omega]
  have hs11 : runInf2 11 ⟨t, p, .B⟩ = ⟨upd4_P11 t p, p + 1, .B⟩ := by
    rw [hs11_raw]
    congr 1
    funext i
    unfold upd4_P11
    by_cases hA : i = p + 2
    · rw [hA]; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
    · by_cases hB : i = p + 1
      · rw [hB]; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
      · by_cases hC : i = p
        · rw [hC]; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
        · by_cases hD : i = p - 1
          · rw [hD]; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
          · repeat' rw [setFun_ne (by omega)]
  refine ⟨hs11, ?_⟩
  intro s hs
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨
                     s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10 ∨ s = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hs0]; dsimp; omega
  · rw [hs1]; dsimp; omega
  · rw [hs2]; dsimp; omega
  · rw [hs3]; dsimp; omega
  · rw [hs4]; dsimp; omega
  · rw [hs5]; dsimp; omega
  · rw [hs6]; dsimp; omega
  · rw [hs7]; dsimp; omega
  · rw [hs8]; dsimp; omega
  · rw [hs9]; dsimp; omega
  · rw [hs10]; dsimp; omega
  · rw [hs11]; dsimp; omega

theorem ag2_glider_P11_right (k : Nat) (t : Nat → Bool) (p : Nat) (hp : p ≥ 1)
    (hm1 : t (p - 1) = false) (h0 : t p = true) (h1 : t (p + 1) = true)
    (hzeros : ∀ i < k, t (p + 2 + i) = false) :
    ∃ t', runInf2 (11 * k) ⟨t, p, .B⟩ = ⟨t', p + k, .B⟩ ∧
      (∀ i < k, t' (p - 1 + i) = true) ∧
      t' (p + k - 1) = false ∧ t' (p + k) = true ∧ t' (p + k + 1) = true ∧
      (∀ j, (j < p - 1 ∨ j ≥ p + k + 2) → t' j = t j) ∧
      (∀ s ≤ 11 * k, p - 1 ≤ (runInf2 s ⟨t, p, .B⟩).pos) := by
  induction k generalizing t p with
  | zero =>
    refine ⟨t, rfl, fun _ hi => by omega, hm1, h0, h1, fun _ _ => rfl, ?_⟩
    intro s hs
    have hs0 : s = 0 := by omega
    rw [hs0]; dsimp [runInf2]; omega
  | succ m ih =>
    have h2 : t (p + 2) = false := hzeros 0 (by omega)
    obtain ⟨hstep, htraj⟩ := ag2_glider_P11_step_all t p hp hm1 h0 h1 h2
    have hzeros' : ∀ i < m, upd4_P11 t p (p + 1 + 2 + i) = false := by
      intro i hi
      rw [upd4_P11_ne t (Or.inr (by omega)), show p + 1 + 2 + i = p + 2 + (i + 1) by omega]
      exact hzeros (i + 1) (by omega)
    obtain ⟨t', ht', hwake, hpm, hp0, hp1, hrest, htraj'⟩ :=
      ih (upd4_P11 t p) (p + 1) (by omega)
         (by rw [show (p + 1) - 1 = p by omega]; exact upd4_P11_0 t)
         (upd4_P11_1 t) (upd4_P11_2 t) hzeros'
    refine ⟨t', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 11 * (m + 1) = 11 + 11 * m by omega, runInf2_add, hstep, ht']
      congr 1; omega
    · intro i hi
      cases i with
      | zero =>
        rw [show p - 1 + 0 = p - 1 by omega, hrest (p - 1) (Or.inl (by omega))]
        exact upd4_P11_m1 t hp
      | succ i' =>
        rw [show p - 1 + (i' + 1) = (p + 1) - 1 + i' by omega]
        exact hwake i' (by omega)
    · rw [show p + (m + 1) - 1 = p + 1 + m - 1 by omega]; exact hpm
    · rw [show p + (m + 1) = p + 1 + m by omega]; exact hp0
    · rw [show p + (m + 1) + 1 = p + 1 + m + 1 by omega]; exact hp1
    · intro j hj
      have hj2 : j < (p + 1) - 1 ∨ j ≥ (p + 1) + m + 2 := by
        rcases hj with hj | hj
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [hrest j hj2]
      apply upd4_P11_ne t
      rcases hj with hj | hj
      · exact Or.inl hj
      · exact Or.inr (by omega)
    · intro s hs
      by_cases hs11 : s ≤ 11
      · exact htraj s hs11
      · rw [show s = 11 + (s - 11) by omega, runInf2_add, hstep]
        have hsub := htraj' (s - 11) (by omega)
        omega

/-- Canonical 6-cell update for one period of AG1's -1/5 return glider -/
private def upd6_P10 (t : Nat → Bool) (p : Nat) : Nat → Bool :=
  setFun (setFun (setFun (setFun (setFun (setFun t (p - 1) false) p true) (p + 1) false)
    (p + 2) false) (p + 3) false) (p + 4) true

private theorem upd6_P10_m1 (t : Nat → Bool) {p : Nat} (hp : p ≥ 1) :
    upd6_P10 t p (p - 1) = false := by
  unfold upd6_P10; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])

private theorem upd6_P10_0 (t : Nat → Bool) {p : Nat} : upd6_P10 t p p = true := by
  unfold upd6_P10; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])

private theorem upd6_P10_1 (t : Nat → Bool) {p : Nat} : upd6_P10 t p (p + 1) = false := by
  unfold upd6_P10; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])

private theorem upd6_P10_2 (t : Nat → Bool) {p : Nat} : upd6_P10 t p (p + 2) = false := by
  unfold upd6_P10; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])

private theorem upd6_P10_3 (t : Nat → Bool) {p : Nat} : upd6_P10 t p (p + 3) = false := by
  unfold upd6_P10; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])

private theorem upd6_P10_4 (t : Nat → Bool) {p : Nat} : upd6_P10 t p (p + 4) = true := by
  unfold upd6_P10; rw [setFun_self]

private theorem upd6_P10_ne (t : Nat → Bool) {p j : Nat} (hj : j < p - 1 ∨ j ≥ p + 5) :
    upd6_P10 t p j = t j := by
  unfold upd6_P10
  rcases hj with hj | hj <;> repeat' rw [setFun_ne (by omega)]

theorem ag1_glider_P10_step_all (t : Nat → Bool) (p : Nat) (hp : p ≥ 2)
    (hm1 : t (p - 1) = true) (h0 : t p = false) (h1 : t (p + 1) = false)
    (h2 : t (p + 2) = true) (h3 : t (p + 3) = false) (h4 : t (p + 4) = false) :
    runInf 10 ⟨t, p, .D⟩ = ⟨upd6_P10 t p, p - 2, .D⟩ ∧
    (∀ s ≤ 10, p - 2 ≤ (runInf s ⟨t, p, .D⟩).pos ∧ (runInf s ⟨t, p, .D⟩).pos ≤ p + 4) := by
  have hs0 : runInf 0 ⟨t, p, .D⟩ = ⟨t, p, .D⟩ := rfl
  have hs1 : runInf 1 ⟨t, p, .D⟩ = ⟨setFun t p false, p + 1, .A⟩ := by
    rw [runInf_succ_left]; exact stepInf_D_f h0
  have hs2 : runInf 2 ⟨t, p, .D⟩ = ⟨setFun (setFun t p false) (p + 1) true, p + 2, .B⟩ := by
    rw [runInf_succ_left, hs1, stepInf_A_f (by rw [setFun_ne (by omega)]; exact h1)]
  have hs3 : runInf 3 ⟨t, p, .D⟩ =
      ⟨setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true, p + 3, .A⟩ := by
    rw [runInf_succ_left, hs2, stepInf_B_t (by rw [setFun_ne (by omega), setFun_ne (by omega)]; exact h2)]
  have hs4 : runInf 4 ⟨t, p, .D⟩ =
      ⟨setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 3) true, p + 4, .B⟩ := by
    rw [runInf_succ_left, hs3,
        stepInf_A_f (by rw [setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega)]; exact h3)]
  have hs5 : runInf 5 ⟨t, p, .D⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 3) true) (p + 4) true, p + 3, .C⟩ := by
    rw [runInf_succ_left, hs4, stepInf_B_f]
    · simp [show p + 4 - 1 = p + 3 by omega]
    · repeat' rw [setFun_ne (by omega)]
      exact h4
  have hs6 : runInf 6 ⟨t, p, .D⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 3) true) (p + 4) true) (p + 3) false, p + 2, .C⟩ := by
    rw [runInf_succ_left, hs5, stepInf_C_t (by rw [setFun_ne (by omega), setFun_self])]
    simp [show p + 3 - 1 = p + 2 by omega]
  have hs7 : runInf 7 ⟨t, p, .D⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 3) true) (p + 4) true) (p + 3) false) (p + 2) false, p + 1, .C⟩ := by
    rw [runInf_succ_left, hs6,
        stepInf_C_t (by rw [setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega), setFun_self])]
    simp [show p + 2 - 1 = p + 1 by omega]
  have hs8 : runInf 8 ⟨t, p, .D⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 3) true) (p + 4) true) (p + 3) false) (p + 2) false) (p + 1) false, p, .C⟩ := by
    rw [runInf_succ_left, hs7,
        stepInf_C_t (by repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)]))]
    simp [show p + 1 - 1 = p by omega]
  have hs9 : runInf 9 ⟨t, p, .D⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 3) true) (p + 4) true) (p + 3) false) (p + 2) false) (p + 1) false) p true, p - 1, .D⟩ := by
    rw [runInf_succ_left, hs8,
        stepInf_C_f (by repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)]))]
  have hs10_raw : runInf 10 ⟨t, p, .D⟩ =
      ⟨setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun (setFun t p false) (p + 1) true) (p + 2) true) (p + 3) true) (p + 4) true) (p + 3) false) (p + 2) false) (p + 1) false) p true) (p - 1) false, p - 2, .D⟩ := by
    rw [runInf_succ_left, hs9, stepInf_D_t]
    · simp [show p - 1 - 1 = p - 2 by omega]
    · repeat' rw [setFun_ne (by omega)]
      exact hm1
  have hs10 : runInf 10 ⟨t, p, .D⟩ = ⟨upd6_P10 t p, p - 2, .D⟩ := by
    rw [hs10_raw]
    congr 1
    funext i
    unfold upd6_P10
    by_cases h4' : i = p + 4
    · rw [h4']; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
    · by_cases h3' : i = p + 3
      · rw [h3']; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
      · by_cases h2' : i = p + 2
        · rw [h2']; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
        · by_cases h1' : i = p + 1
          · rw [h1']; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
          · by_cases h0' : i = p
            · rw [h0']; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
            · by_cases hm1' : i = p - 1
              · rw [hm1']; repeat' (first | rw [setFun_self] | rw [setFun_ne (by omega)])
              · repeat' rw [setFun_ne (by omega)]
  refine ⟨hs10, ?_⟩
  intro s hs
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨
                     s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hs0]; dsimp; omega
  · rw [hs1]; dsimp; omega
  · rw [hs2]; dsimp; omega
  · rw [hs3]; dsimp; omega
  · rw [hs4]; dsimp; omega
  · rw [hs5]; dsimp; omega
  · rw [hs6]; dsimp; omega
  · rw [hs7]; dsimp; omega
  · rw [hs8]; dsimp; omega
  · rw [hs9]; dsimp; omega
  · rw [hs10]; dsimp; omega

theorem ag1_glider_P10_left_inf (k : Nat) (t : Nat → Bool) (p : Nat) (hp : p ≥ 2 * k)
    (hpairs : ∀ i < k, t (p - 2 * k + 2 * i) = false ∧ t (p - 2 * k + 2 * i + 1) = true)
    (h0 : t p = false) (h1 : t (p + 1) = false) (h2 : t (p + 2) = true)
    (h3 : t (p + 3) = false) (h4 : t (p + 4) = false) :
    ∃ t', runInf (10 * k) ⟨t, p, .D⟩ = ⟨t', p - 2 * k, .D⟩ ∧
      t' (p - 2 * k) = false ∧ t' (p - 2 * k + 1) = false ∧ t' (p - 2 * k + 2) = true ∧
      t' (p - 2 * k + 3) = false ∧ t' (p - 2 * k + 4) = false ∧
      (∀ i < k, t' (p - 2 * k + 5 + 2 * i) = false ∧ t' (p - 2 * k + 5 + 2 * i + 1) = true) ∧
      (∀ j, (j < p - 2 * k + 1 ∨ j ≥ p + 5) → t' j = t j) ∧
      (∀ s ≤ 10 * k, (runInf s ⟨t, p, .D⟩).pos ≤ p + 4) := by
  induction k generalizing t p with
  | zero =>
    refine ⟨t, rfl, h0, h1, h2, h3, h4, fun _ hi => by omega, fun _ _ => rfl, ?_⟩
    intro s hs
    have hs0 : s = 0 := by omega
    rw [hs0]; dsimp [runInf]; omega
  | succ m ih =>
    have hm2 : t (p - 2) = false := by
      have h := (hpairs m (by omega)).1
      rwa [show p - 2 * (m + 1) + 2 * m = p - 2 by omega] at h
    have hm1 : t (p - 1) = true := by
      have h := (hpairs m (by omega)).2
      rwa [show p - 2 * (m + 1) + 2 * m + 1 = p - 1 by omega] at h
    obtain ⟨hstep, htraj⟩ := ag1_glider_P10_step_all t p (by omega) hm1 h0 h1 h2 h3 h4
    have hpairs' : ∀ i < m, upd6_P10 t p ((p - 2) - 2 * m + 2 * i) = false ∧
        upd6_P10 t p ((p - 2) - 2 * m + 2 * i + 1) = true := by
      intro i hi
      have hpr := hpairs i (by omega)
      rw [show (p - 2) - 2 * m + 2 * i = p - 2 * (m + 1) + 2 * i by omega,
          show p - 2 * (m + 1) + 2 * i + 1 = p - 2 * (m + 1) + 2 * i + 1 by rfl,
          upd6_P10_ne t (Or.inl (by omega)), upd6_P10_ne t (Or.inl (by omega))]
      exact hpr
    have h0' : upd6_P10 t p (p - 2) = false := by
      rw [upd6_P10_ne t (Or.inl (by omega))]; exact hm2
    have h1' : upd6_P10 t p ((p - 2) + 1) = false := by
      rw [show (p - 2) + 1 = p - 1 by omega]; exact upd6_P10_m1 t (by omega)
    have h2' : upd6_P10 t p ((p - 2) + 2) = true := by
      rw [show (p - 2) + 2 = p by omega]; exact upd6_P10_0 t
    have h3' : upd6_P10 t p ((p - 2) + 3) = false := by
      rw [show (p - 2) + 3 = p + 1 by omega]; exact upd6_P10_1 t
    have h4' : upd6_P10 t p ((p - 2) + 4) = false := by
      rw [show (p - 2) + 4 = p + 2 by omega]; exact upd6_P10_2 t
    obtain ⟨t', ht', hz0, hz1, hz2, hz3, hz4, hwake', hrest', htraj'⟩ :=
      ih (upd6_P10 t p) (p - 2) (by omega) hpairs' h0' h1' h2' h3' h4'
    refine ⟨t', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 10 * (m + 1) = 10 + 10 * m by omega, runInf_add, hstep, ht']
      congr 1; omega
    · rw [show p - 2 * (m + 1) = (p - 2) - 2 * m by omega]; exact hz0
    · rw [show p - 2 * (m + 1) + 1 = (p - 2) - 2 * m + 1 by omega]; exact hz1
    · rw [show p - 2 * (m + 1) + 2 = (p - 2) - 2 * m + 2 by omega]; exact hz2
    · rw [show p - 2 * (m + 1) + 3 = (p - 2) - 2 * m + 3 by omega]; exact hz3
    · rw [show p - 2 * (m + 1) + 4 = (p - 2) - 2 * m + 4 by omega]; exact hz4
    · intro i hi
      by_cases him : i < m
      · rw [show p - 2 * (m + 1) + 5 + 2 * i = (p - 2) - 2 * m + 5 + 2 * i by omega,
            show (p - 2) - 2 * m + 5 + 2 * i + 1 = (p - 2) - 2 * m + 5 + 2 * i + 1 by rfl]
        exact hwake' i him
      · rw [show p - 2 * (m + 1) + 5 + 2 * i = p + 3 by omega,
            show p + 3 + 1 = p + 4 by omega,
            hrest' (p + 3) (Or.inr (by omega)), hrest' (p + 4) (Or.inr (by omega))]
        exact ⟨upd6_P10_3 t, upd6_P10_4 t⟩
    · intro j hj
      have hj2 : j < (p - 2) - 2 * m + 1 ∨ j ≥ (p - 2) + 5 := by
        rcases hj with hj | hj
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [hrest' j hj2]
      apply upd6_P10_ne t
      rcases hj with hj | hj
      · exact Or.inl (by omega)
      · exact Or.inr hj
    · intro s hs
      by_cases hs10 : s ≤ 10
      · exact (htraj s hs10).2
      · rw [show s = 10 + (s - 10) by omega, runInf_add, hstep]
        have hsub := htraj' (s - 10) (by omega)
        omega

/-- 2-step sprint of AG1 over 1-wall -/
theorem ag1_sprint_A_2 (t : Nat → Bool) (p : Nat) (h0 : t p = true) (h1 : t (p + 1) = true) :
    runInf 2 ⟨t, p, .A⟩ = ⟨setFun (setFun t p false) (p + 1) true, p + 2, .A⟩ ∧
    (∀ s ≤ 2, p ≤ (runInf s ⟨t, p, .A⟩).pos ∧ (runInf s ⟨t, p, .A⟩).pos ≤ p + 2) := by
  have hs0 : runInf 0 ⟨t, p, .A⟩ = ⟨t, p, .A⟩ := rfl
  have hs1 : runInf 1 ⟨t, p, .A⟩ = ⟨setFun t p false, p + 1, .B⟩ := by
    rw [runInf_succ_left]; exact stepInf_A_t h0
  have hs2 : runInf 2 ⟨t, p, .A⟩ = ⟨setFun (setFun t p false) (p + 1) true, p + 2, .A⟩ := by
    rw [runInf_succ_left, hs1, stepInf_B_t (by rw [setFun_ne (by omega)]; exact h1)]
  refine ⟨hs2, ?_⟩
  intro s hs
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
  · rw [hs0]; dsimp; omega
  · rw [hs1]; dsimp; omega
  · rw [hs2]; dsimp; omega

/-- Inductive 2k-step sprint of AG1 over 1^{2k} leaving (0,1)^k -/
theorem ag1_sprint_A_inf (k : Nat) (t : Nat → Bool) (p : Nat)
    (hones : ∀ i < 2 * k, t (p + i) = true) :
    ∃ t', runInf (2 * k) ⟨t, p, .A⟩ = ⟨t', p + 2 * k, .A⟩ ∧
      (∀ i < k, t' (p + 2 * i) = false ∧ t' (p + 2 * i + 1) = true) ∧
      (∀ j, (j < p ∨ j ≥ p + 2 * k) → t' j = t j) ∧
      (∀ s ≤ 2 * k, p ≤ (runInf s ⟨t, p, .A⟩).pos ∧ (runInf s ⟨t, p, .A⟩).pos ≤ p + 2 * k) := by
  induction k generalizing t p with
  | zero =>
    refine ⟨t, rfl, fun _ hi => by omega, fun _ _ => rfl, ?_⟩
    intro s hs
    have hs0 : s = 0 := by omega
    rw [hs0]; dsimp [runInf]; omega
  | succ m ih =>
    have h0 : t p = true := hones 0 (by omega)
    have h1 : t (p + 1) = true := hones 1 (by omega)
    obtain ⟨hs, htraj⟩ := ag1_sprint_A_2 t p h0 h1
    have hones' : ∀ i < 2 * m, (setFun (setFun t p false) (p + 1) true) ((p + 2) + i) = true := by
      intro i hi
      rw [setFun_ne (by omega), setFun_ne (by omega), show (p + 2) + i = p + (i + 2) by omega]
      exact hones (i + 2) (by omega)
    obtain ⟨t', ht', hpairs, hrest, htraj'⟩ := ih _ (p + 2) hones'
    refine ⟨t', ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (m + 1) = 2 + 2 * m by omega, runInf_add, hs, ht']
      congr 1; omega
    · intro i hi
      cases i with
      | zero =>
        rw [show p + 2 * 0 = p by omega,
            hrest p (Or.inl (by omega)), hrest (p + 1) (Or.inl (by omega)),
            setFun_ne (by omega : p ≠ p + 1), setFun_self, setFun_self]
        exact ⟨rfl, rfl⟩
      | succ i' =>
        rw [show p + 2 * (i' + 1) = (p + 2) + 2 * i' by omega]
        exact hpairs i' (by omega)
    · intro j hj
      have hj2 : j < p + 2 ∨ j ≥ p + 2 + 2 * m := by
        rcases hj with hj | hj
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [hrest j hj2]
      rcases hj with hj | hj
      · rw [setFun_ne (by omega), setFun_ne (by omega)]
      · rw [setFun_ne (by omega), setFun_ne (by omega)]
    · intro s hle
      by_cases hs2 : s ≤ 2
      · have ht := htraj s hs2; omega
      · rw [show s = 2 + (s - 2) by omega, runInf_add, hs]
        have ht := htraj' (s - 2) (by omega)
        omega

/-- 2-step erasure sweep of AG1 in state A over (0,1) -> (1,1) -/
theorem ag1_erasure_A_2 (t : Nat → Bool) (p : Nat) (h0 : t p = false) (h1 : t (p + 1) = true) :
    runInf 2 ⟨t, p, .A⟩ = ⟨setFun (setFun t p true) (p + 1) true, p + 2, .A⟩ ∧
    (∀ s ≤ 2, p ≤ (runInf s ⟨t, p, .A⟩).pos ∧ (runInf s ⟨t, p, .A⟩).pos ≤ p + 2) := by
  have hs0 : runInf 0 ⟨t, p, .A⟩ = ⟨t, p, .A⟩ := rfl
  have hs1 : runInf 1 ⟨t, p, .A⟩ = ⟨setFun t p true, p + 1, .B⟩ := by
    rw [runInf_succ_left]; exact stepInf_A_f h0
  have hs2 : runInf 2 ⟨t, p, .A⟩ = ⟨setFun (setFun t p true) (p + 1) true, p + 2, .A⟩ := by
    rw [runInf_succ_left, hs1, stepInf_B_t (by rw [setFun_ne (by omega)]; exact h1)]
  refine ⟨hs2, ?_⟩
  intro s hs
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
  · rw [hs0]; dsimp; omega
  · rw [hs1]; dsimp; omega
  · rw [hs2]; dsimp; omega

theorem ag1_erasure_sweep_A (k : Nat) (t : Nat → Bool) (p : Nat)
    (hpairs : ∀ i < k, t (p + 2 * i) = false ∧ t (p + 2 * i + 1) = true) :
    ∃ t', runInf (2 * k) ⟨t, p, .A⟩ = ⟨t', p + 2 * k, .A⟩ ∧
      (∀ i < 2 * k, t' (p + i) = true) ∧
      (∀ j, (j < p ∨ j ≥ p + 2 * k) → t' j = t j) ∧
      (∀ s ≤ 2 * k, p ≤ (runInf s ⟨t, p, .A⟩).pos ∧ (runInf s ⟨t, p, .A⟩).pos ≤ p + 2 * k) := by
  induction k generalizing t p with
  | zero =>
    refine ⟨t, rfl, fun _ hi => by omega, fun _ _ => rfl, ?_⟩
    intro s hs
    have hs0 : s = 0 := by omega
    rw [hs0]; dsimp [runInf]; omega
  | succ m ih =>
    have h0 : t p = false := (hpairs 0 (by omega)).1
    have h1 : t (p + 1) = true := (hpairs 0 (by omega)).2
    obtain ⟨hs, htraj⟩ := ag1_erasure_A_2 t p h0 h1
    have hpairs' : ∀ i < m, (setFun (setFun t p true) (p + 1) true) ((p + 2) + 2 * i) = false ∧
        (setFun (setFun t p true) (p + 1) true) ((p + 2) + 2 * i + 1) = true := by
      intro i hi
      have h := hpairs (i + 1) (by omega)
      rw [show (p + 2) + 2 * i = p + 2 * (i + 1) by omega,
          setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega), setFun_ne (by omega)]
      exact h
    obtain ⟨t', ht', hones, hrest, htraj'⟩ := ih _ (p + 2) hpairs'
    refine ⟨t', ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (m + 1) = 2 + 2 * m by omega, runInf_add, hs, ht']
      congr 1; omega
    · intro i hi
      by_cases hi2 : i < 2
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [show p + 0 = p by omega, hrest p (Or.inl (by omega)), setFun_ne (by omega : p ≠ p + 1), setFun_self]
        · rw [hrest (p + 1) (Or.inl (by omega)), setFun_self]
      · rw [show p + i = (p + 2) + (i - 2) by omega]
        exact hones (i - 2) (by omega)
    · intro j hj
      have hj2 : j < p + 2 ∨ j ≥ p + 2 + 2 * m := by
        rcases hj with hj | hj
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [hrest j hj2]
      rcases hj with hj | hj
      · rw [setFun_ne (by omega), setFun_ne (by omega)]
      · rw [setFun_ne (by omega), setFun_ne (by omega)]
    · intro s hle
      by_cases hs2 : s ≤ 2
      · have ht := htraj s hs2; omega
      · rw [show s = 2 + (s - 2) by omega, runInf_add, hs]
        have ht := htraj' (s - 2) (by omega)
        omega

/-- 2-step turnaround when A meets 00: turns 00 -> 11 and enters C -/
theorem ag1_turn_00_C (t : Nat → Bool) (p : Nat) (h0 : t p = false) (h1 : t (p + 1) = false) :
    runInf 2 ⟨t, p, .A⟩ = ⟨setFun (setFun t p true) (p + 1) true, p, .C⟩ ∧
    (∀ s ≤ 2, p ≤ (runInf s ⟨t, p, .A⟩).pos ∧ (runInf s ⟨t, p, .A⟩).pos ≤ p + 1) := by
  have hs0 : runInf 0 ⟨t, p, .A⟩ = ⟨t, p, .A⟩ := rfl
  have hs1 : runInf 1 ⟨t, p, .A⟩ = ⟨setFun t p true, p + 1, .B⟩ := by
    rw [runInf_succ_left]; exact stepInf_A_f h0
  have hs2 : runInf 2 ⟨t, p, .A⟩ = ⟨setFun (setFun t p true) (p + 1) true, p, .C⟩ := by
    rw [runInf_succ_left, hs1, stepInf_B_f (by rw [setFun_ne (by omega)]; exact h1)]
    simp [show p + 1 - 1 = p by omega]
  refine ⟨hs2, ?_⟩
  intro s hs
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
  · rw [hs0]; dsimp; omega
  · rw [hs1]; dsimp; omega
  · rw [hs2]; dsimp; omega

/-- Inductive m-step leftward erasure by C across 1^m -> 0^m -/
theorem ag1_erase_C (m base : Nat) (t : Nat → Bool)
    (hones : ∀ i < m, t (base + 1 + i) = true) :
    ∃ t', runInf m ⟨t, base + m, .C⟩ = ⟨t', base, .C⟩ ∧
      (∀ i < m, t' (base + 1 + i) = false) ∧
      (∀ j, (j ≤ base ∨ j > base + m) → t' j = t j) ∧
      (∀ s ≤ m, base ≤ (runInf s ⟨t, base + m, .C⟩).pos ∧ (runInf s ⟨t, base + m, .C⟩).pos ≤ base + m) := by
  induction m generalizing t with
  | zero =>
    refine ⟨t, rfl, fun _ hi => by omega, fun _ _ => rfl, ?_⟩
    intro s hs
    have hs0 : s = 0 := by omega
    rw [hs0]; dsimp [runInf]; omega
  | succ k ih =>
    have htop : t (base + (k + 1)) = true := by
      have h := hones k (by omega)
      rwa [show base + 1 + k = base + (k + 1) by omega] at h
    have hstep : runInf 1 ⟨t, base + (k + 1), .C⟩ = ⟨setFun t (base + (k + 1)) false, base + k, .C⟩ := by
      rw [runInf_succ_left, show runInf 0 ⟨t, base + (k + 1), .C⟩ = ⟨t, base + (k + 1), .C⟩ from rfl, stepInf_C_t htop]
      simp [show base + (k + 1) - 1 = base + k by omega]
    have hones' : ∀ i < k, (setFun t (base + (k + 1)) false) (base + 1 + i) = true := by
      intro i hi
      rw [setFun_ne (by omega)]
      exact hones i (by omega)
    obtain ⟨t', ht', hz, hrest, htraj'⟩ := ih (setFun t (base + (k + 1)) false) hones'
    refine ⟨t', ?_, ?_, ?_, ?_⟩
    · have hr := runInf_add 1 k ⟨t, base + (k + 1), .C⟩
      rw [show 1 + k = k + 1 by omega] at hr
      rw [hr, hstep, ht']
    · intro i hi
      by_cases hik : i < k
      · exact hz i hik
      · rw [show base + 1 + i = base + (k + 1) by omega, hrest (base + (k + 1)) (Or.inr (by omega)), setFun_self]
    · intro j hj
      have hj2 : j ≤ base ∨ j > base + k := by
        rcases hj with hj | hj
        · exact Or.inl hj
        · exact Or.inr (by omega)
      rw [hrest j hj2]
      rcases hj with hj | hj
      · rw [setFun_ne (by omega)]
      · rw [setFun_ne (by omega)]
    · intro s hs
      cases s with
      | zero => dsimp [runInf]; omega
      | succ s' =>
        have hr := runInf_add 1 s' ⟨t, base + (k + 1), .C⟩
        rw [show 1 + s' = s' + 1 by omega] at hr
        rw [hr, hstep]
        have hsub := htraj' s' (by omega)
        omega

/-- Head-decoupling theorem: if AG1 stays < sep and AG2 stays >= sep throughout n steps,
    the coupled paired machine agrees pointwise with independent single-tape evolutions. -/
theorem cet_decoupled_run_aux (n sep : Nat) (t t1 t2 : Nat → Bool) (p1 p2 : Nat) (s1 s2 : St)
    (ht1 : ∀ i < sep, t i = t1 i)
    (ht2 : ∀ i ≥ sep, t i = t2 i)
    (h1 : ∀ k ≤ n, (runInf k ⟨t1, p1, s1⟩).pos < sep)
    (h2 : ∀ k ≤ n, sep ≤ (runInf2 k ⟨t2, p2, s2⟩).pos) :
    ∃ c', runCetInf n (some ⟨t, p1, s1, p2, s2⟩) = some c' ∧
      c'.p1 = (runInf n ⟨t1, p1, s1⟩).pos ∧ c'.s1 = (runInf n ⟨t1, p1, s1⟩).st ∧
      c'.p2 = (runInf2 n ⟨t2, p2, s2⟩).pos ∧ c'.s2 = (runInf2 n ⟨t2, p2, s2⟩).st ∧
      (∀ i < sep, c'.tape i = (runInf n ⟨t1, p1, s1⟩).tape i) ∧
      (∀ i ≥ sep, c'.tape i = (runInf2 n ⟨t2, p2, s2⟩).tape i) := by
  induction n generalizing t t1 t2 p1 p2 s1 s2 with
  | zero =>
    exact ⟨⟨t, p1, s1, p2, s2⟩, rfl, rfl, rfl, rfl, rfl, ht1, ht2⟩
  | succ m ih =>
    have hp1_lt : p1 < sep := h1 0 (by omega)
    have hp2_ge : sep ≤ p2 := h2 0 (by omega)
    have hne : p1 ≠ p2 := by omega
    have hnb : (p1 == p2) = false := beq_false_of_ne hne
    have htp1 : t p1 = t1 p1 := ht1 p1 hp1_lt
    have htp2 : t p2 = t2 p2 := ht2 p2 hp2_ge
    have hp1'_eq :
        (if (ag1Step s1 (t p1)).d = 1 then p1 + 1 else p1 - 1) = (runInf 1 ⟨t1, p1, s1⟩).pos := by
      simp [runInf, stepInf, htp1]
    have hp2'_eq :
        (if (ag2Step s2 (t p2)).d = 1 then p2 + 1 else p2 - 1) = (runInf2 1 ⟨t2, p2, s2⟩).pos := by
      simp [runInf2, stepInf2, htp2]
    have hp1'_lt : (if (ag1Step s1 (t p1)).d = 1 then p1 + 1 else p1 - 1) < sep := by
      rw [hp1'_eq]; exact h1 1 (by omega)
    have hp2'_ge : sep ≤ (if (ag2Step s2 (t p2)).d = 1 then p2 + 1 else p2 - 1) := by
      rw [hp2'_eq]; exact h2 1 (by omega)
    have hcoll_ne :
        (if (ag1Step s1 (t p1)).d = 1 then p1 + 1 else p1 - 1) ≠
        (if (ag2Step s2 (t p2)).d = 1 then p2 + 1 else p2 - 1) := by omega
    have hcoll_b :
        ((if (ag1Step s1 (t p1)).d = 1 then p1 + 1 else p1 - 1) ==
         (if (ag2Step s2 (t p2)).d = 1 then p2 + 1 else p2 - 1)) = false :=
      beq_false_of_ne hcoll_ne
    have hstep :
        stepCetInf ⟨t, p1, s1, p2, s2⟩ =
          some ⟨setFun (setFun t p2 (ag2Step s2 (t p2)).w) p1 (ag1Step s1 (t p1)).w,
                (stepInf ⟨t1, p1, s1⟩).pos, (stepInf ⟨t1, p1, s1⟩).st,
                (stepInf2 ⟨t2, p2, s2⟩).pos, (stepInf2 ⟨t2, p2, s2⟩).st⟩ := by
      unfold stepCetInf
      dsimp only
      simp only [hnb, Bool.false_eq_true, ↓reduceIte, hcoll_b]
      simp [stepInf, stepInf2, htp1, htp2]
    let t' := setFun (setFun t p2 (ag2Step s2 (t p2)).w) p1 (ag1Step s1 (t p1)).w
    let t1' := (stepInf ⟨t1, p1, s1⟩).tape
    let t2' := (stepInf2 ⟨t2, p2, s2⟩).tape
    have ht1' : ∀ i < sep, t' i = t1' i := by
      intro i hi
      dsimp [t', t1', stepInf]
      rw [htp1]
      by_cases hip1 : i = p1
      · rw [hip1, setFun_self, setFun_self]
      · rw [setFun_ne hip1, setFun_ne (by omega : i ≠ p2), setFun_ne hip1, ht1 i hi]
    have ht2' : ∀ i ≥ sep, t' i = t2' i := by
      intro i hi
      dsimp [t', t2', stepInf2]
      rw [htp2]
      by_cases hip2 : i = p2
      · rw [hip2, setFun_ne (by omega : p2 ≠ p1), setFun_self, setFun_self]
      · rw [setFun_ne (by omega : i ≠ p1), setFun_ne hip2, setFun_ne hip2, ht2 i hi]
    have h1' : ∀ k ≤ m, (runInf k ⟨t1', (stepInf ⟨t1, p1, s1⟩).pos, (stepInf ⟨t1, p1, s1⟩).st⟩).pos < sep := by
      intro k hk
      exact h1 (k + 1) (by omega)
    have h2' : ∀ k ≤ m, sep ≤ (runInf2 k ⟨t2', (stepInf2 ⟨t2, p2, s2⟩).pos, (stepInf2 ⟨t2, p2, s2⟩).st⟩).pos := by
      intro k hk
      exact h2 (k + 1) (by omega)
    obtain ⟨c', hc', hp1c, hs1c, hp2c, hs2c, htc1, htc2⟩ :=
      ih t' t1' t2' (stepInf ⟨t1, p1, s1⟩).pos (stepInf2 ⟨t2, p2, s2⟩).pos
         (stepInf ⟨t1, p1, s1⟩).st (stepInf2 ⟨t2, p2, s2⟩).st ht1' ht2' h1' h2'
    refine ⟨c', ?_, hp1c, hs1c, hp2c, hs2c, htc1, htc2⟩
    simpa [runCetInf, hstep] using hc'

theorem cet_decoupled_run (n sep : Nat) (t : Nat → Bool) (p1 p2 : Nat) (s1 s2 : St)
    (h1 : ∀ k ≤ n, (runInf k ⟨t, p1, s1⟩).pos < sep)
    (h2 : ∀ k ≤ n, sep ≤ (runInf2 k ⟨t, p2, s2⟩).pos) :
    ∃ c', runCetInf n (some ⟨t, p1, s1, p2, s2⟩) = some c' ∧
      c'.p1 = (runInf n ⟨t, p1, s1⟩).pos ∧ c'.s1 = (runInf n ⟨t, p1, s1⟩).st ∧
      c'.p2 = (runInf2 n ⟨t, p2, s2⟩).pos ∧ c'.s2 = (runInf2 n ⟨t, p2, s2⟩).st ∧
      (∀ i < sep, c'.tape i = (runInf n ⟨t, p1, s1⟩).tape i) ∧
      (∀ i ≥ sep, c'.tape i = (runInf2 n ⟨t, p2, s2⟩).tape i) :=
  cet_decoupled_run_aux n sep t t t p1 p2 s1 s2 (fun _ _ => rfl) (fun _ _ => rfl) h1 h2

/-- Finite-list verification of all 4 surviving Collision #2 sprint modes:
    - k = 4, 15 leave AG1 in -1/5 glider adjoining AG2's solid 1-wall (quick re-bounce)
    - k = 5, 16 leave AG1 in -1/5 glider + (1,0)^5 wake + 00 junction + 1^4 + AG2's +1/11 glider -/
def runCetOpt : Nat → CetCfg → Option CetCfg
  | 0, c => some c
  | n + 1, c =>
    match stepCet c with
    | none => none
    | some c' => runCetOpt n c'

def collision2_modes_check : Bool :=
  let okShort := [4, 15].all fun k =>
    (match runCetOpt 26 (mkSprintCfg k .A) with
    | none => false
    | some c =>
      c.s1 == .D && c.s2 == .B && c.p1 + 6 == c.p2 &&
      !(getCell c.tape c.p1) && !(getCell c.tape (c.p1 + 1)) && getCell c.tape (c.p1 + 2) &&
      !(getCell c.tape (c.p1 + 3)) && !(getCell c.tape (c.p1 + 4)) && !(getCell c.tape (c.p1 + 5)) &&
      getCell c.tape c.p2 && getCell c.tape (c.p2 + 1) && !(getCell c.tape (c.p2 + 2))) &&
    (match runCetOpt 46 (mkSprintCfg k .A) with
    | none => false
    | some c =>
      c.s1 == .D && c.s2 == .C && c.p1 + 12 == c.p2 &&
      !(getCell c.tape c.p1) && !(getCell c.tape (c.p1 + 1)) && getCell c.tape (c.p1 + 2) &&
      getCell c.tape (c.p1 + 8) && getCell c.tape (c.p1 + 9) && getCell c.tape (c.p1 + 10))
  let okLong := [5, 16].all fun k =>
    match runCetOpt 84 (mkSprintCfg k .A) with
    | none => false
    | some c =>
      c.s1 == .D && c.s2 == .B && c.p1 + 22 == c.p2 &&
      !(getCell c.tape c.p1) && !(getCell c.tape (c.p1 + 1)) && getCell c.tape (c.p1 + 2) &&
      !(getCell c.tape (c.p1 + 3)) && !(getCell c.tape (c.p1 + 4)) && !(getCell c.tape (c.p1 + 5)) &&
      getCell c.tape (c.p1 + 6) && !(getCell c.tape (c.p1 + 7)) &&
      getCell c.tape (c.p1 + 14) && !(getCell c.tape (c.p1 + 15)) &&
      !(getCell c.tape (c.p1 + 16)) &&
      getCell c.tape (c.p1 + 17) && getCell c.tape (c.p1 + 18) &&
      getCell c.tape (c.p1 + 19) && getCell c.tape (c.p1 + 20) &&
      !(getCell c.tape (c.p2 - 1)) && getCell c.tape c.p2 && getCell c.tape (c.p2 + 1) &&
      !(getCell c.tape (c.p2 + 2))
  okShort && okLong

theorem collision2_modes_verified : collision2_modes_check = true := by
  decide

private theorem first_ge_of_pos_ge (W : Nat) (c : InfCfg) (hlt : c.pos < W) (k : Nat)
    (hge : (runInf k c).pos ≥ W) :
    ∃ m, m ≥ 1 ∧ (runInf m c).pos ≥ W ∧ ∀ j < m, (runInf j c).pos < W := by
  induction k generalizing c with
  | zero => dsimp [runInf] at hge; omega
  | succ n ih =>
    by_cases h1 : (stepInf c).pos ≥ W
    · refine ⟨1, by omega, h1, fun j hj => ?_⟩
      have hj0 : j = 0 := by omega
      rw [hj0]; exact hlt
    · obtain ⟨m, hm1, hmge, hmlt⟩ := ih (stepInf c) (by omega) hge
      refine ⟨m + 1, by omega, hmge, fun j hj => ?_⟩
      cases j with
      | zero => exact hlt
      | succ j' => exact hmlt j' (by omega)

private theorem stepCetInf_some_p1 {c c' : CetInfCfg} (h : stepCetInf c = some c') :
    c'.p1 = if (ag1Step c.s1 (c.tape c.p1)).d = 1 then c.p1 + 1 else c.p1 - 1 := by
  unfold stepCetInf at h
  by_cases h1 : (c.p1 == c.p2) = true
  · simp [h1] at h
  · rw [ite_eq_right h1] at h
    dsimp only at h
    by_cases h2 : ((if (ag1Step c.s1 (c.tape c.p1)).d = 1 then c.p1 + 1 else c.p1 - 1) ==
                  (if (ag2Step c.s2 (c.tape c.p2)).d = 1 then c.p2 + 1 else c.p2 - 1)) = true
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h; cases h; rfl

/-- Every post-erasure decoupled counter configuration (with AG1 in LeftWallInv below W and AG2
    running its +1/11 glider on 0^inf from p2 >= W + 1) MUST either collide/halt or push AG1 >= W. -/
theorem cet4_post_bounce_must_overflow_or_collide
    (W p1 p2 : Nat) (t : Nat → Bool)
    (hp1 : 1 ≤ p1) (hp1W : p1 < W) (hWp2 : W + 1 ≤ p2)
    (hinv : LeftWallInv ⟨t, p1, .A⟩)
    (hm1 : t (p2 - 1) = false) (h0 : t p2 = true) (h1 : t (p2 + 1) = true)
    (hzeros : ∀ i ≥ p2 + 2, t i = false) :
    ∃ m, m ≥ 1 ∧
      (runCetInf m (some ⟨t, p1, .A, p2, .B⟩) = none ∨
        ∃ c', runCetInf m (some ⟨t, p1, .A, p2, .B⟩) = some c' ∧ c'.p1 ≥ W) := by
  have hN : W - 1 ≥ 1 := by omega
  have hfuel : 2 ^ ((W - 1) + 2) - evalTape ((W - 1) + 2) t ≤ 2 ^ (W + 1) := by
    have hpw : (W - 1) + 2 = W + 1 := by omega
    rw [hpw]; exact Nat.sub_le _ _
  obtain ⟨k, _, pos', hk, hpos', _⟩ :=
    ag1_exit_bounded (W - 1) (2 ^ (W + 1)) t p1 hp1 (by omega) hinv hfuel
  have hk_ge : (runInf k ⟨t, p1, .A⟩).pos ≥ W := by
    rw [hk]; dsimp; omega
  obtain ⟨m, hm1_step, hmge, hmlt⟩ := first_ge_of_pos_ge W ⟨t, p1, .A⟩ hp1W k hk_ge
  obtain ⟨_, _, _, _, _, _, _, htraj2⟩ :=
    ag2_glider_P11_right m t p2 (by omega) hm1 h0 h1 (fun i _ => hzeros (p2 + 2 + i) (by omega))
  have hdec1 : ∀ j ≤ m - 1, (runInf j ⟨t, p1, .A⟩).pos < W := fun j hj => hmlt j (by omega)
  have hdec2 : ∀ j ≤ m - 1, W ≤ (runInf2 j ⟨t, p2, .B⟩).pos := by
    intro j hj
    have hge := htraj2 j (by omega)
    omega
  obtain ⟨c_prev, hc_prev, hp1p, hs1p, hp2p, _, htp1, _⟩ :=
    cet_decoupled_run (m - 1) W t p1 p2 .A .B hdec1 hdec2
  refine ⟨m, hm1_step, ?_⟩
  rw [show m = (m - 1) + 1 by omega, runCetInf_add, hc_prev]
  dsimp [runCetInf]
  cases hnext : stepCetInf c_prev with
  | none => exact Or.inl rfl
  | some c' =>
    refine Or.inr ⟨c', rfl, ?_⟩
    have hlt_prev : c_prev.p1 < W := by rw [hp1p]; exact hmlt (m - 1) (by omega)
    have hge_prev : W ≤ c_prev.p2 := by rw [hp2p]; exact hdec2 (m - 1) (by omega)
    have hneq_prev : (c_prev.p1 == c_prev.p2) = false := beq_false_of_ne (by omega)
    have ht_eq : c_prev.tape c_prev.p1 = (runInf (m - 1) ⟨t, p1, .A⟩).tape (runInf (m - 1) ⟨t, p1, .A⟩).pos := by
      rw [← hp1p]; exact htp1 c_prev.p1 hlt_prev
    rw [stepCetInf_some_p1 hnext, ht_eq, hp1p, hs1p]
    have hsucc := runInf_succ_left (m - 1) ⟨t, p1, .A⟩
    rw [show (m - 1) + 1 = m by omega] at hsucc
    have hstep_pos :
        (if (ag1Step (runInf (m - 1) ⟨t, p1, .A⟩).st ((runInf (m - 1) ⟨t, p1, .A⟩).tape (runInf (m - 1) ⟨t, p1, .A⟩).pos)).d = 1
          then (runInf (m - 1) ⟨t, p1, .A⟩).pos + 1
          else (runInf (m - 1) ⟨t, p1, .A⟩).pos - 1) = (runInf m ⟨t, p1, .A⟩).pos := by
      rw [hsucc]; rfl
    rw [hstep_pos]
    exact hmge

/-- Direct blank-tape consequence: from t = 0, CET(4) MUST reach or collide before wall W = 110 -/
theorem cet4_from_blank_reaches_wall :
    ∃ m, m ≥ 1 ∧
      (runCetInf (2000 + m) (some blankCetInf) = none ∨
        ∃ c', runCetInf (2000 + m) (some blankCetInf) = some c' ∧ c'.p1 ≥ 110) := by
  obtain ⟨c2000, hc2000, hp1, hs1, hp2, hs2, hinv, hm1, h0, h1, hzeros⟩ := cet4_t0_to_t2000_exact
  rcases c2000 with ⟨t2, p1, s1, p2, s2⟩
  dsimp only at hp1 hs1 hp2 hs2 hinv hm1 h0 h1 hzeros
  subst hp1; subst hs1; subst hp2; subst hs2
  obtain ⟨m, hm1_step, hres⟩ :=
    cet4_post_bounce_must_overflow_or_collide 110 2 186 t2
      (by omega) (by omega) (by omega) hinv hm1 h0 h1 (fun i hi => hzeros i (by omega))
  refine ⟨m, hm1_step, ?_⟩
  rw [runCetInf_add, hc2000]
  exact hres

/-- Master Formal Reduction of CET(4):
    1. Exact verified trajectory t = 0..2000 from blank tape enters decoupled LeftWallInv + AG2 P11.
    2. All 40 of 44 bounded sprint collision phases halt immediately; all 4 survivors verify cleanly
       into 1-wall (k=4,15) vs -1/5 glider + 00-junction (k=5,16).
    3. Arbitrary decoupled phases (glider, sprint, sweep, 00-turn, C-erasure) execute intact.
    4. Any decoupled post-erasure counter (including W=110 from blank tape and W=22142380648 after
       Bounce #2) guarantees finite AG1 arrival at W, reducing global halting to t_ovf mod 11. -/
theorem cet4_bounce2_to_overflow3_reduction :
    (∃ c2000, runCetInf 2000 (some blankCetInf) = some c2000 ∧
      LeftWallInv ⟨c2000.tape, c2000.p1, c2000.s1⟩ ∧ c2000.p2 = 186 ∧ c2000.s2 = .B) ∧
    (checkSprintPhases = true ∧ collision2_modes_check = true) ∧
    (∃ m ≥ 1, runCetInf (2000 + m) (some blankCetInf) = none ∨
      ∃ c', runCetInf (2000 + m) (some blankCetInf) = some c' ∧ c'.p1 ≥ 110) ∧
    (∀ W p1 p2 (t : Nat → Bool),
      1 ≤ p1 → p1 < W → W + 1 ≤ p2 →
      LeftWallInv ⟨t, p1, .A⟩ →
      t (p2 - 1) = false → t p2 = true → t (p2 + 1) = true → (∀ i ≥ p2 + 2, t i = false) →
      ∃ m ≥ 1, runCetInf m (some ⟨t, p1, .A, p2, .B⟩) = none ∨
        ∃ c', runCetInf m (some ⟨t, p1, .A, p2, .B⟩) = some c' ∧ c'.p1 ≥ W) := by
  refine ⟨?_, ⟨collision_40_of_44_sprint, collision2_modes_verified⟩,
          cet4_from_blank_reaches_wall, ?_⟩
  · obtain ⟨c2000, hc, hp1, hs1, hp2, hs2, hinv, _⟩ := cet4_t0_to_t2000_exact
    exact ⟨c2000, hc, hp1 ▸ hs1 ▸ hinv, hp2, hs2⟩
  · intro W p1 p2 t hp1 hp1W hWp2 hinv hm1 h0 h1 hzeros
    exact cet4_post_bounce_must_overflow_or_collide W p1 p2 t hp1 hp1W hWp2 hinv hm1 h0 h1 hzeros

#print axioms collision_40_of_44_phases
#print axioms collision_40_of_44_sprint
#print axioms ag1_unbounded_exit
#print axioms cet_verified_0_to_2000
#print axioms cet4_t0_to_t2000_exact
#print axioms ag2_glider_P11_right
#print axioms ag1_glider_P10_left_inf
#print axioms cet_decoupled_run
#print axioms collision2_modes_verified
#print axioms cet4_post_bounce_must_overflow_or_collide
#print axioms cet4_from_blank_reaches_wall
#print axioms cet4_bounce2_to_overflow3_reduction

