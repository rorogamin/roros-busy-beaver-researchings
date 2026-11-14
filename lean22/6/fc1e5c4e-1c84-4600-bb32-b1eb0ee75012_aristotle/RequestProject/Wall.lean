module

public import RequestProject.TM

/-!
# The left-hand bouncer ("wall") of `1RB4RA1LA4RB2LA_2LB3LA1RB2RA---`

The tape splits at cell `0`.  Every time the head moves from cell `0` into the
left half-tape it does so in state `A`, performs an excursion into the left
half, and comes back to cell `0`.  This file proves that the left half is an
autonomous *bouncer*: its contents are always one of five explicit wall words,
and from each of them the machine runs for an explicitly given number of steps,
without halting and without reading anything of the right half-tape, and comes
back to cell `0` with the wall advanced to the next phase.  After five
excursions the wall has grown by one block `E = [4,4,1]` (three cells), and the
states in which the head comes back are `B, A, B, A, B` (then periodically).

Configurations are zippers: `left` lists the cells to the left of the head,
nearest first.  The wall words below are the left half-tape (cells `-1, -2, …`)
read nearest first.

This eliminates the bouncer from the analysis of the machine: what is left is
the dynamics on the right half-tape (cells `≥ 0`), driven by the stream of
return states `A (B A B A B)^ω` (the initial `A` is the start of the machine).
-/

@[expose] public section

namespace BCM

/-- `Lp l n` is the `n`-fold concatenation `l ++ l ++ ... ++ l`. -/
def Lp (l : List Sym) : Nat → List Sym
  | 0 => []
  | n + 1 => l ++ Lp l n

/-- The block by which the wall grows (nearest cell first): the wall reads
`…144144` from left to right. -/
def E : List Sym := [4, 4, 1]

/-- The block written during a leftward sweep (it reads `212` in both
directions). -/
def F : List Sym := [2, 1, 2]

theorem Lp_succ (l : List Sym) (n : Nat) : Lp l (n + 1) = l ++ Lp l n := rfl

theorem Lp_comm (l : List Sym) (n : Nat) : Lp l n ++ l = l ++ Lp l n := by
  induction n with
  | zero => simp [Lp]
  | succ m ih => rw [Lp_succ, List.append_assoc, ih]

/-! ## The sweep lemmas -/

/-- One block of a leftward sweep: `144` (under and left of the head) becomes
`212`; the cell further left is entered but not read. -/
theorem sweepL (L R : List Sym) :
    run 5 ⟨.A, 4 :: 1 :: L, 4, R⟩ = some ⟨.A, tlz L, hdz L, 2 :: 1 :: 2 :: R⟩ := rfl

/-- A complete leftward sweep over `E^m`, ending on the blank cell beyond the
wall. -/
theorem sweepL_iter (m : Nat) : ∀ R : List Sym,
    run (5 * m) ⟨.A, tlz (Lp E m), hdz (Lp E m), R⟩ = some ⟨.A, [], 0, Lp F m ++ R⟩ := by
  induction m with
  | zero => intro R; rfl
  | succ p ih =>
      intro R
      have h1 : run 5 ⟨.A, tlz (Lp E (p + 1)), hdz (Lp E (p + 1)), R⟩
          = some ⟨.A, tlz (Lp E p), hdz (Lp E p), F ++ R⟩ := sweepL (Lp E p) R
      have h2 := ih (F ++ R)
      have h3 := run_comp h1 h2
      rw [show 5 * (p + 1) = 5 + 5 * p from by omega, h3, ← List.append_assoc, Lp_comm]
      rfl

/-- The turnaround at the far left end of the wall: the blank cell becomes
part of the wall. -/
theorem turn (y : Sym) (R : List Sym) :
    run 5 ⟨.A, [], 0, 2 :: 1 :: y :: R⟩ = some ⟨.B, [4, 4, 1], y, R⟩ := rfl

/-- One block of a rightward sweep. -/
theorem sweepR (L : List Sym) (y : Sym) (R : List Sym) :
    run 5 ⟨.B, L, 2, 2 :: 1 :: y :: R⟩ = some ⟨.B, 4 :: 4 :: 1 :: L, y, R⟩ := rfl

/-- `m` blocks of a rightward sweep. -/
theorem sweepR_iter (m : Nat) : ∀ L R : List Sym,
    run (5 * m) ⟨.B, L, 2, Lp F m ++ R⟩ = some ⟨.B, Lp E m ++ L, 2, R⟩ := by
  induction m with
  | zero => intro L R; rfl
  | succ p ih =>
      intro L R
      have h1 : run 5 ⟨.B, L, 2, Lp F (p + 1) ++ R⟩ = some ⟨.B, E ++ L, 2, Lp F p ++ R⟩ :=
        sweepR L 2 (Lp F p ++ R)
      have h2 := ih (E ++ L) R
      rw [show 5 * (p + 1) = 5 + 5 * p from by omega, run_comp h1 h2, ← List.append_assoc,
        Lp_comm]
      rfl

/-! ## The five wall phases -/

/-- The wall (left half-tape, nearest cell first) in phase `ph` with `n`
complete `E`-blocks. -/
def wall : Nat → Nat → List Sym
  | 0, n => Lp E n
  | 1, n => 1 :: Lp E n
  | 2, n => 4 :: Lp E n
  | 3, n => 1 :: 1 :: Lp E n
  | _, n => 4 :: 1 :: Lp E n

/-- The state in which the head comes back to cell `0`, for each phase. -/
def outSt : Nat → St
  | 0 => .B
  | 1 => .A
  | 2 => .B
  | 3 => .A
  | _ => .B

/-- The number of steps of the excursion in phase `ph` with `n` blocks. -/
def wsteps : Nat → Nat → Nat
  | 0, n => 10 * n + 1
  | 1, _ => 1
  | 2, n => 10 * n + 3
  | 3, _ => 1
  | _, n => 10 * n + 9

/-- The next phase. -/
def nextPh : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | _ => 0

/-- The number of blocks after the excursion. -/
def nextN : Nat → Nat → Nat
  | 4, n => n + 1
  | _, n => n

/-- The configuration just after the head has moved from cell `0` (the first
cell of `R`) into the wall, in state `A`. -/
def wcfg (ph n : Nat) (R : List Sym) : Cfg := ⟨.A, tlz (wall ph n), hdz (wall ph n), R⟩

/-- The configuration when the head is back on cell `0` (content `x`, the
rest `R` of the right half-tape untouched), with the wall in its next phase. -/
def wexit (ph n : Nat) (x : Sym) (R : List Sym) : Cfg :=
  ⟨outSt ph, wall (nextPh ph) (nextN ph n), x, R⟩

theorem phase0 (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 0 n) (wcfg 0 n (x :: R)) = some (wexit 0 n x R) := by
  cases n with
  | zero => rfl
  | succ m =>
      have e1 := sweepL_iter (m + 1) (x :: R)
      have e2 : run 5 ⟨.A, [], 0, Lp F (m + 1) ++ x :: R⟩
          = some ⟨.B, [4, 4, 1], 2, Lp F m ++ x :: R⟩ := turn 2 (Lp F m ++ x :: R)
      have e3 := sweepR_iter m [4, 4, 1] (x :: R)
      have e4 : run 1 ⟨.B, Lp E m ++ [4, 4, 1], 2, x :: R⟩
          = some ⟨.B, 1 :: (Lp E m ++ [4, 4, 1]), x, R⟩ := rfl
      have h := run_comp (run_comp (run_comp e1 e2) e3) e4
      rw [show wsteps 0 (m + 1) = 5 * (m + 1) + 5 + 5 * m + 1 from by simp [wsteps]; omega]
      rw [show wcfg 0 (m + 1) (x :: R) = ⟨.A, tlz (Lp E (m + 1)), hdz (Lp E (m + 1)), x :: R⟩
        from rfl, h]
      have : Lp E m ++ [4, 4, 1] = Lp E (m + 1) := Lp_comm E m
      rw [this]
      rfl

theorem phase1 (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 1 n) (wcfg 1 n (x :: R)) = some (wexit 1 n x R) := rfl

theorem phase2 (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 2 n) (wcfg 2 n (x :: R)) = some (wexit 2 n x R) := by
  cases n with
  | zero => rfl
  | succ m =>
      have e0 : run 1 (wcfg 2 (m + 1) (x :: R))
          = some ⟨.A, tlz (Lp E (m + 1)), hdz (Lp E (m + 1)), 2 :: x :: R⟩ := rfl
      have e1 := sweepL_iter (m + 1) (2 :: x :: R)
      have e2 : run 5 ⟨.A, [], 0, Lp F (m + 1) ++ 2 :: x :: R⟩
          = some ⟨.B, [4, 4, 1], 2, Lp F m ++ 2 :: x :: R⟩ := turn 2 (Lp F m ++ 2 :: x :: R)
      have e3 := sweepR_iter m [4, 4, 1] (2 :: x :: R)
      have e4 : run 2 ⟨.B, Lp E m ++ [4, 4, 1], 2, 2 :: x :: R⟩
          = some ⟨.B, 1 :: 1 :: (Lp E m ++ [4, 4, 1]), x, R⟩ := rfl
      have h := run_comp (run_comp (run_comp (run_comp e0 e1) e2) e3) e4
      rw [show wsteps 2 (m + 1) = 1 + 5 * (m + 1) + 5 + 5 * m + 2 from by simp [wsteps]; omega,
        h]
      have : Lp E m ++ [4, 4, 1] = Lp E (m + 1) := Lp_comm E m
      rw [this]
      rfl

theorem phase3 (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 3 n) (wcfg 3 n (x :: R)) = some (wexit 3 n x R) := rfl

theorem phase4 (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 4 n) (wcfg 4 n (x :: R)) = some (wexit 4 n x R) := by
  cases n with
  | zero => rfl
  | succ m =>
      have e0 : run 4 (wcfg 4 (m + 1) (x :: R))
          = some ⟨.A, tlz (Lp E (m + 1)), hdz (Lp E (m + 1)), 2 :: 1 :: x :: R⟩ := rfl
      have e1 := sweepL_iter (m + 1) (2 :: 1 :: x :: R)
      have e2 : run 5 ⟨.A, [], 0, Lp F (m + 1) ++ 2 :: 1 :: x :: R⟩
          = some ⟨.B, [4, 4, 1], 2, Lp F m ++ 2 :: 1 :: x :: R⟩ :=
        turn 2 (Lp F m ++ 2 :: 1 :: x :: R)
      have e3 := sweepR_iter m [4, 4, 1] (2 :: 1 :: x :: R)
      have e4 := sweepR (Lp E m ++ [4, 4, 1]) x R
      have h := run_comp (run_comp (run_comp (run_comp e0 e1) e2) e3) e4
      rw [show wsteps 4 (m + 1) = 4 + 5 * (m + 1) + 5 + 5 * m + 5 from by simp [wsteps]; omega,
        h]
      have : Lp E m ++ [4, 4, 1] = Lp E (m + 1) := Lp_comm E m
      rw [this]
      rfl

/-- **Bouncer elimination.**  From each of the five wall configurations the
machine performs a complete excursion into the left half-tape: it runs for
`wsteps ph n` steps without halting, never reads the right half-tape beyond
cell `0` (whose content `x` is also untouched), and comes back to cell `0` in
state `outSt ph`, with the wall in phase `nextPh ph`.  Over the five phases
`0 → 1 → 2 → 3 → 4 → 0` the wall gains one block `E` and the head comes back in
the states `B, A, B, A, B`. -/
theorem wall_excursion (ph : Nat) (hph : ph < 5) (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps ph n) (wcfg ph n (x :: R)) = some (wexit ph n x R) := by
  match ph, hph with
  | 0, _ => exact phase0 n x R
  | 1, _ => exact phase1 n x R
  | 2, _ => exact phase2 n x R
  | 3, _ => exact phase3 n x R
  | 4, _ => exact phase4 n x R

end BCM
