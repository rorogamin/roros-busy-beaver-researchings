import RequestProject.TM

/-!
# The closed block system and its soundness

Blocks (tape words):

```
left blocks   W = 1 1,  U = 0 1,  D = 0 4          (left end L = 0^ω 1 1)
right blocks  V = 2 2,  C = 1 3,  C1 = 2 3,  G = 3 3,  P = 2,  S = 3,  Q = 1
                                                   (right end = 0^ω)
```

Heads: `<` (state A reading leftwards), `>` (state A reading rightwards),
`w>` (a `0` cell, then state B reading rightwards), `lB` (state B reading
leftwards).

Main results:
* `astep_next` : every block step is a genuine machine computation of positive
  length (each rule is checked by `rfl` for an arbitrary tape context);
* `astep_loop` : the configuration `L lB` runs forever;
* `not_halts_of_never` : if the block system started at `L W < C R` (reached
  after 21 machine steps) never reaches the halting pattern `D lB`, the machine
  never halts.
-/

namespace TM25

open St Dir

/-! ## Blocks and block configurations -/

/-- Blocks occurring to the left of the head. -/
inductive LB | W | U | D
  deriving DecidableEq, Repr

/-- Blocks occurring to the right of the head. -/
inductive RB | V | C | C1 | G | P | S | Q
  deriving DecidableEq, Repr

/-- The four kinds of head. -/
inductive Hd | lt | gt | wgt | lB
  deriving DecidableEq, Repr

/-- A block configuration; both block lists are stored nearest-to-the-head
first; the left end `L` and the blank right end are implicit. -/
structure ACfg where
  bs : List LB
  h : Hd
  rs : List RB
  deriving DecidableEq, Repr

/-- Tape cells of a left block, nearest cell first. -/
def LB.cells : LB → List Nat
  | LB.W => [1, 1]
  | LB.U => [1, 0]
  | LB.D => [4, 0]

/-- Tape cells of a right block, nearest cell first. -/
def RB.cells : RB → List Nat
  | RB.V => [2, 2]
  | RB.C => [1, 3]
  | RB.C1 => [2, 3]
  | RB.G => [3, 3]
  | RB.P => [2]
  | RB.S => [3]
  | RB.Q => [1]

/-- The left part of the tape, nearest cell first; `[1,1]` is the left end `L`. -/
def lraw (bs : List LB) : List Nat := bs.flatMap LB.cells ++ [1, 1]

/-- The right part of the tape, nearest cell first. -/
def rraw (rs : List RB) : List Nat := rs.flatMap RB.cells

/-- The machine configuration described by a block configuration. -/
def conc (a : ACfg) : Cfg :=
  match a.h with
  | Hd.lt => ⟨A, Dir.L, lraw a.bs, rraw a.rs⟩
  | Hd.gt => ⟨A, Dir.R, lraw a.bs, rraw a.rs⟩
  | Hd.wgt => ⟨B, Dir.R, 0 :: lraw a.bs, rraw a.rs⟩
  | Hd.lB => ⟨B, Dir.L, lraw a.bs, rraw a.rs⟩

/-! ## The block step function -/

/-- The result of one block step. -/
inductive AStep
  | next (a : ACfg)
  | halt
  | loop
  deriving DecidableEq, Repr

open LB RB Hd in
/-- One step of the closed block system. -/
def astep : ACfg → AStep
  | ⟨[], lt, rs⟩ => AStep.next ⟨[], wgt, rs⟩
  | ⟨W :: bs, lt, rs⟩ => AStep.next ⟨bs, lt, V :: rs⟩
  | ⟨U :: bs, lt, rs⟩ => AStep.next ⟨W :: bs, gt, rs⟩
  | ⟨D :: bs, lt, rs⟩ => AStep.next ⟨bs, lt, C :: rs⟩
  | ⟨bs, gt, []⟩ => AStep.next ⟨bs, lt, [P, Q]⟩
  | ⟨bs, gt, V :: rs⟩ => AStep.next ⟨U :: bs, gt, rs⟩
  | ⟨bs, gt, C :: rs⟩ => AStep.next ⟨bs, lt, C1 :: rs⟩
  | ⟨bs, gt, C1 :: rs⟩ => AStep.next ⟨D :: bs, gt, rs⟩
  | ⟨bs, gt, G :: rs⟩ => AStep.next ⟨bs, lt, C :: rs⟩
  | ⟨bs, gt, P :: rs⟩ => AStep.next ⟨bs, wgt, rs⟩
  | ⟨bs, gt, S :: rs⟩ => AStep.next ⟨bs, lt, Q :: rs⟩
  | ⟨bs, gt, Q :: rs⟩ => AStep.next ⟨bs, lt, P :: rs⟩
  | ⟨bs, wgt, []⟩ => AStep.next ⟨bs, lB, [G]⟩
  | ⟨bs, wgt, V :: rs⟩ => AStep.next ⟨U :: bs, wgt, rs⟩
  | ⟨bs, wgt, C :: rs⟩ => AStep.next ⟨bs, lt, C :: S :: rs⟩
  | ⟨bs, wgt, C1 :: rs⟩ => AStep.next ⟨bs, lt, P :: V :: rs⟩
  | ⟨bs, wgt, G :: rs⟩ => AStep.next ⟨bs, lt, C :: Q :: rs⟩
  | ⟨bs, wgt, P :: rs⟩ => AStep.next ⟨U :: bs, gt, rs⟩
  | ⟨bs, wgt, S :: rs⟩ => AStep.next ⟨D :: bs, gt, rs⟩
  | ⟨bs, wgt, Q :: rs⟩ => AStep.next ⟨bs, lt, C :: rs⟩
  | ⟨[], lB, _⟩ => AStep.loop
  | ⟨U :: bs, lB, rs⟩ => AStep.next ⟨bs, lt, C :: rs⟩
  | ⟨W :: bs, lB, rs⟩ => AStep.next ⟨bs, lB, G :: rs⟩
  | ⟨D :: _, lB, _⟩ => AStep.halt

/-! ## Soundness of the block steps -/

open LB RB Hd

/-- Every `next` step of the block system is a real computation of the machine
of positive length. -/
theorem astep_next {a a' : ACfg} (h : astep a = AStep.next a') :
    ∃ n, 0 < n ∧ run n (conc a) = some (conc a') := by
  obtain ⟨bs, hd, rs⟩ := a
  match bs, hd, rs with
  | [], Hd.lt, rs => simp only [astep] at h; cases h; exact ⟨5, by decide, rfl⟩
  | W :: bs, Hd.lt, rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | U :: bs, Hd.lt, rs => simp only [astep] at h; cases h; exact ⟨3, by decide, rfl⟩
  | D :: bs, Hd.lt, rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | bs, Hd.gt, [] => simp only [astep] at h; cases h; exact ⟨3, by decide, rfl⟩
  | bs, Hd.gt, V :: rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | bs, Hd.gt, C :: rs => simp only [astep] at h; cases h; exact ⟨1, by decide, rfl⟩
  | bs, Hd.gt, C1 :: rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | bs, Hd.gt, G :: rs => simp only [astep] at h; cases h; exact ⟨1, by decide, rfl⟩
  | bs, Hd.gt, P :: rs => simp only [astep] at h; cases h; exact ⟨1, by decide, rfl⟩
  | bs, Hd.gt, S :: rs => simp only [astep] at h; cases h; exact ⟨1, by decide, rfl⟩
  | bs, Hd.gt, Q :: rs => simp only [astep] at h; cases h; exact ⟨1, by decide, rfl⟩
  | bs, Hd.wgt, [] => simp only [astep] at h; cases h; exact ⟨4, by decide, rfl⟩
  | bs, Hd.wgt, V :: rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | bs, Hd.wgt, C :: rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | bs, Hd.wgt, C1 :: rs => simp only [astep] at h; cases h; exact ⟨8, by decide, rfl⟩
  | bs, Hd.wgt, G :: rs => simp only [astep] at h; cases h; exact ⟨4, by decide, rfl⟩
  | bs, Hd.wgt, P :: rs => simp only [astep] at h; cases h; exact ⟨1, by decide, rfl⟩
  | bs, Hd.wgt, S :: rs => simp only [astep] at h; cases h; exact ⟨1, by decide, rfl⟩
  | bs, Hd.wgt, Q :: rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | [], Hd.lB, rs => exact absurd h (by simp [astep])
  | U :: bs, Hd.lB, rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | W :: bs, Hd.lB, rs => simp only [astep] at h; cases h; exact ⟨2, by decide, rfl⟩
  | D :: bs, Hd.lB, rs => exact absurd h (by simp [astep])

/-- At the left end, a left-going head in state `B` shifts two cells left every
four steps. -/
theorem loop_step (r : List Nat) :
    run 4 ⟨B, Dir.L, [], r⟩ = some ⟨B, Dir.L, [], 3 :: 3 :: r⟩ := rfl

theorem loop_never_halts (n : Nat) (r : List Nat) : (run n ⟨B, Dir.L, [], r⟩).isSome := by
  induction n using Nat.strongRecOn generalizing r with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | (m + 4) =>
        rw [Nat.add_comm m 4, run_bind, loop_step]
        simpa using ih m (by omega) (3 :: 3 :: r)

/-- The looping block configuration `L lB` really runs forever. -/
theorem astep_loop {a : ACfg} (h : astep a = AStep.loop) (n : Nat) :
    (run n (conc a)).isSome := by
  obtain ⟨bs, hd, rs⟩ := a
  match bs, hd, rs with
  | [], Hd.lB, rs =>
    have h2 : run 2 (conc ⟨[], Hd.lB, rs⟩) = some ⟨B, Dir.L, [], 3 :: 3 :: rraw rs⟩ := rfl
    match n with
    | 0 => rfl
    | 1 => rfl
    | m + 2 =>
      rw [Nat.add_comm m 2, run_bind, h2]
      simpa using loop_never_halts m (3 :: 3 :: rraw rs)
  | [], Hd.lt, rs | W :: _, Hd.lt, _ | U :: _, Hd.lt, _ | D :: _, Hd.lt, _
  | _, Hd.gt, [] | _, Hd.gt, V :: _ | _, Hd.gt, C :: _ | _, Hd.gt, C1 :: _
  | _, Hd.gt, G :: _ | _, Hd.gt, P :: _ | _, Hd.gt, S :: _ | _, Hd.gt, Q :: _
  | _, Hd.wgt, [] | _, Hd.wgt, V :: _ | _, Hd.wgt, C :: _ | _, Hd.wgt, C1 :: _
  | _, Hd.wgt, G :: _ | _, Hd.wgt, P :: _ | _, Hd.wgt, S :: _ | _, Hd.wgt, Q :: _
  | D :: _, Hd.lB, _ | U :: _, Hd.lB, _ | W :: _, Hd.lB, _ => exact absurd h (by simp [astep])

/-! ## Running the block system -/

/-- `arun n a` is the block configuration after `n` block steps, or `none` if
the run halted or entered the left-end loop first. -/
def arun : Nat → ACfg → Option ACfg
  | 0, a => some a
  | n + 1, a => match astep a with
    | AStep.next a' => arun n a'
    | _ => none

theorem arun_add (m n : Nat) (a : ACfg) :
    arun (m + n) a = (arun m a).bind (arun n) := by
  induction m generalizing a with
  | zero => simp [arun]
  | succ k ih =>
      rw [Nat.add_right_comm, arun, arun]
      cases astep a with
      | next b => exact ih b
      | halt => rfl
      | loop => rfl

theorem arun_comp {m n : Nat} {a b c : ACfg} (h₁ : arun m a = some b) (h₂ : arun n b = some c) :
    arun (m + n) a = some c := by
  rw [arun_add, h₁]; simpa using h₂

theorem arun_isSome_of_le {m n : Nat} (hmn : m ≤ n) {a : ACfg} (h : (arun n a).isSome) :
    (arun m a).isSome := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [arun_add] at h
  cases hm : arun m a with
  | none => rw [hm] at h; simp at h
  | some c => simp

/-- The block run from `a` never reaches the halting configuration `D lB`. -/
def ANeverHalts (a : ACfg) : Prop :=
  ∀ n a', arun n a = some a' → astep a' ≠ AStep.halt

/-- If the block system started at `a` never reaches `D lB`, then the machine
started at `conc a` never halts. -/
theorem no_ahalt_no_halt (a : ACfg) (H : ANeverHalts a) (n : Nat) :
    (run n (conc a)).isSome := by
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    cases hs : astep a with
    | halt => exact absurd (H 0 a rfl) (by simp [hs])
    | loop => exact astep_loop hs n
    | next a' =>
        obtain ⟨k, hk, hrun⟩ := astep_next hs
        rcases Nat.lt_or_ge n k with hn | hn
        · exact run_isSome_of_le (Nat.le_of_lt hn) (by rw [hrun]; simp)
        · obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
          have H' : ANeverHalts a' := by
            intro j b hb
            exact H (j + 1) b (by rw [arun, hs]; exact hb)
          rw [run_bind, hrun]
          simpa using ih m (by omega) a' H'

/-! ## Start-up -/

/-- The block configuration reached after 21 steps: `L W < C R`. -/
def astart : ACfg := ⟨[LB.W], Hd.lt, [RB.C]⟩

/-- After 21 steps the machine is in the configuration `L W < C R`. -/
theorem start_21 : run 21 init = some (conc astart) := rfl

theorem not_halts_of_never (H : ANeverHalts astart) : ¬ Halts := by
  rintro ⟨n, hn⟩
  have key : ∀ k, (run k (conc astart)).isSome := no_ahalt_no_halt astart H
  rcases Nat.lt_or_ge n 21 with hlt | hge
  · have : (run n init).isSome := run_isSome_of_le (Nat.le_of_lt hlt) (by rw [start_21]; simp)
    rw [hn] at this; simp at this
  · obtain ⟨m, rfl⟩ : ∃ m, n = 21 + m := ⟨n - 21, by omega⟩
    rw [run_bind, start_21] at hn
    have := key m
    simp only [Option.bind_some] at hn
    rw [hn] at this
    simp at this

end TM25
