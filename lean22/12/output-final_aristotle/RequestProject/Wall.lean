module

public import RequestProject.TM

/-!
# The left-hand bouncer ("wall") of `1RB3RB3LA4LA2RB_2LB3RA---1RA1LA`

Empirically the head of this machine always enters the left region of the tape
in state `A`, sweeps back and forth inside it for a while, and comes back out
to the right of the region.  This file proves that this left region really is
an autonomous *bouncer*: from each of eight explicit "wall" configurations the
machine runs for an explicitly given number of steps, without halting and
without reading anything of the right-hand context, and returns the head to the
first cell of the right-hand context, with the wall advanced to the next of the
eight phases.  After eight such excursions the wall has grown by exactly one
block `E = [1,3,2,3,3]` (five cells).

Concretely the wall (the list of tape cells to the left of the head, nearest
first) is always of the form `wpre r ++ E^n` and the cell under the head is
`curOf r`, for one of eight phases `r`.

This eliminates the bouncer from the analysis of the machine: what is left is
the dynamics on the right-hand half-tape, driven by the eight-phase wall.
-/

set_option maxRecDepth 20000

@[expose] public section

namespace TM5

/-- `Lp l n` is the `n`-fold concatenation `l ++ l ++ ... ++ l`. -/
def Lp (l : List Sym) : Nat → List Sym
  | 0 => []
  | n + 1 => l ++ Lp l n

/-- The block by which the wall grows, as seen from the right. -/
def E : List Sym := [1, 3, 2, 3, 3]

/-- The leftmost part of the wall. -/
def Tw : List Sym := [3, 2, 3, 3]

/-- The block written on the right during a leftward sweep. -/
def Cw : List Sym := [4, 3, 4, 4, 1]

/-- The block written on the left during a rightward sweep. -/
def Dw : List Sym := [3, 1, 3, 2, 3]

theorem Lp_succ (l : List Sym) (n : Nat) : Lp l (n + 1) = l ++ Lp l n := rfl

theorem Lp_comm (l : List Sym) (n : Nat) : Lp l n ++ l = l ++ Lp l n := by
  induction n with
  | zero => simp [Lp]
  | succ m ih => rw [Lp_succ, List.append_assoc, ih]

/-- `Dw^n ++ [3] = 3 :: E^n`: the wall as produced by the rightward sweeps is
the wall in its canonical `E`-block form. -/
theorem Dw_pow_eq (n : Nat) : Lp Dw n ++ [3] = (3 : Sym) :: Lp E n := by
  induction n with
  | zero => simp [Lp]
  | succ m ih => rw [Lp_succ, Lp_succ, List.append_assoc, ih]; rfl

/-! ## The two sweep lemmas -/

/-- A rightward sweep: the head moves five cells to the right over
`[4,3,4,4,x]`, writing one block `Dw = [3,1,3,2,3]` on the left.  The fifth
cell `x` is arbitrary: it is entered but not read. -/
theorem sweepR (L R : List Sym) (x : Sym) :
    run 9 ⟨.B, L, 1, 4 :: 3 :: 4 :: 4 :: x :: R⟩
      = some ⟨.B, 3 :: 1 :: 3 :: 2 :: 3 :: L, x, R⟩ := rfl

/-- The turnaround at the far left end of the wall. -/
theorem turn (Y : List Sym) :
    run 10 ⟨.A, Tw, 1, 4 :: Y⟩ = some ⟨.B, [3], 1, Cw ++ Y⟩ := rfl

/-- Leftward sweep in terms of the canonical `E`-block form of the wall. -/
theorem sweepL_E (m : Nat) (R : List Sym) :
    run 7 ⟨.A, Tw ++ Lp E (m + 1), 1, 4 :: R⟩
      = some ⟨.A, Tw ++ Lp E m, 1, 4 :: (Cw ++ R)⟩ := rfl

/-- `m` leftward sweeps eat the whole `E^m` part of the wall and deposit `Cw^m`
on the right. -/
theorem sweepL_iter (m : Nat) : ∀ R : List Sym,
    run (7 * m) ⟨.A, Tw ++ Lp E m, 1, 4 :: R⟩
      = some ⟨.A, Tw, 1, 4 :: (Lp Cw m ++ R)⟩ := by
  induction m with
  | zero => intro R; rfl
  | succ p ih =>
      intro R
      have h1 := sweepL_E p R
      have h2 := ih (Cw ++ R)
      have h3 := run_comp h1 h2
      have harith : 7 * (p + 1) = 7 + 7 * p := by omega
      rw [harith, h3]
      have : Lp Cw p ++ (Cw ++ R) = Lp Cw (p + 1) ++ R := by
        rw [Lp_succ, ← List.append_assoc, Lp_comm, List.append_assoc]
      rw [this]

/-- `m` rightward sweeps eat `Cw^m` on the right and deposit `Dw^m` on the left. -/
theorem sweepR_iter (m : Nat) : ∀ L R : List Sym,
    run (9 * m) ⟨.B, L, 1, Lp Cw m ++ R⟩ = some ⟨.B, Lp Dw m ++ L, 1, R⟩ := by
  induction m with
  | zero => intro L R; rfl
  | succ p ih =>
      intro L R
      have h1 : run 9 ⟨.B, L, 1, Lp Cw (p + 1) ++ R⟩
          = some ⟨.B, Dw ++ L, 1, Lp Cw p ++ R⟩ := rfl
      have h2 := ih (Dw ++ L) R
      have h3 := run_comp h1 h2
      have harith : 9 * (p + 1) = 9 + 9 * p := by omega
      rw [harith, h3]
      have : Lp Dw p ++ (Dw ++ L) = Lp Dw (p + 1) ++ L := by
        rw [Lp_succ, ← List.append_assoc, Lp_comm, List.append_assoc]
      rw [this]

/-! ## The eight wall phases -/

/-- The part of the wall to the left of the `E`-blocks, for each of the eight
phases. -/
def wpre : Nat → List Sym
  | 0 => [3, 2, 3, 3]
  | 1 => []
  | 2 => [3]
  | 3 => [3, 3]
  | 4 => [2, 3, 3]
  | 5 => [2, 3, 3]
  | 6 => [1, 2, 3, 3]
  | _ => [3, 2, 3, 3]

/-- The symbol under the head when the head enters the wall, for each phase. -/
def curOf : Nat → Sym
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | _ => 1

/-- The state in which the head leaves the wall, for each phase. -/
def outSt : Nat → St
  | 0 => .B
  | 1 => .A
  | 2 => .B
  | 3 => .A
  | 4 => .B
  | 5 => .B
  | 6 => .A
  | _ => .B

/-- Number of steps of the excursion, as a function of the phase and of the
number `n` of `E`-blocks in the wall. -/
def wsteps : Nat → Nat → Nat
  | 0, n => 16 * n + 17
  | 1, n => 16 * n + 5
  | 2, n => 16 * n + 7
  | 3, n => 16 * n + 9
  | 4, _ => 1
  | 5, n => 16 * n + 11
  | 6, _ => 3
  | _, _ => 1

/-- The next phase. -/
def nextPh : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | _ => 0

/-- The number of `E`-blocks after the excursion (it grows only at phase 0,
where the new block appears; over a full cycle of eight phases the wall gains
exactly one block). -/
def nextN : Nat → Nat → Nat
  | 0, n => n + 1
  | _, n => n

/-- The configuration in which the head enters the wall: state `A`, head on the
cell `curOf r` (the cell just left of the right-hand context `R`), wall
`wpre r ++ E^n` further left. -/
def wcfg (r n : Nat) (R : List Sym) : Cfg := ⟨.A, wpre r ++ Lp E n, curOf r, R⟩

/-- The configuration in which the head leaves the wall: the head has moved one
cell to the right, onto the first cell `x` of the right-hand context, which is
untouched; the wall is in its next phase. -/
def wexit (r n : Nat) (x : Sym) (R : List Sym) : Cfg :=
  ⟨outSt r, curOf (nextPh r) :: (wpre (nextPh r) ++ Lp E (nextN r n)), x, R⟩

/-! ### The individual phase excursions -/

theorem phase0 (m : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 0 (m + 1)) (wcfg 0 (m + 1) (x :: R)) = some (wexit 0 (m + 1) x R) := by
  have e1 : run 5 (wcfg 0 (m + 1) (x :: R))
      = some ⟨.A, Tw ++ Lp E m, 1, 4 :: (4 :: 3 :: 4 :: 4 :: x :: R)⟩ := rfl
  have e2 := sweepL_iter m (4 :: 3 :: 4 :: 4 :: x :: R)
  have e3 := turn (Lp Cw m ++ (4 :: 3 :: 4 :: 4 :: x :: R))
  have e4 : run (9 * (m + 1)) ⟨.B, [(3 : Sym)], 1,
      Cw ++ (Lp Cw m ++ (4 :: 3 :: 4 :: 4 :: x :: R))⟩
      = some ⟨.B, Lp Dw (m + 1) ++ [3], 1, 4 :: 3 :: 4 :: 4 :: x :: R⟩ :=
    sweepR_iter (m + 1) [3] (4 :: 3 :: 4 :: 4 :: x :: R)
  have e5 := sweepR (Lp Dw (m + 1) ++ [(3 : Sym)]) R x
  have h := run_comp (run_comp (run_comp (run_comp e1 e2) e3) e4) e5
  have harith : wsteps 0 (m + 1) = 5 + 7 * m + 10 + 9 * (m + 1) + 9 := by
    simp [wsteps]; omega
  rw [harith, h]
  have hw : (3 : Sym) :: 1 :: 3 :: 2 :: 3 :: (Lp Dw (m + 1) ++ [3])
      = 3 :: Lp E (m + 2) := by
    have : (3 : Sym) :: 1 :: 3 :: 2 :: 3 :: (Lp Dw (m + 1) ++ [3])
        = Lp Dw (m + 2) ++ [3] := rfl
    rw [this, Dw_pow_eq]
  simp only [wexit, nextPh, nextN, outSt, curOf, wpre, List.nil_append, hw]

theorem phase1 (m : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 1 (m + 1)) (wcfg 1 (m + 1) (x :: R)) = some (wexit 1 (m + 1) x R) := by
  have e1 : run 1 (wcfg 1 (m + 1) (x :: R))
      = some ⟨.A, Tw ++ Lp E m, 1, 4 :: (x :: R)⟩ := rfl
  have e2 := sweepL_iter m (x :: R)
  have e3 := turn (Lp Cw m ++ (x :: R))
  have e4 : run (9 * (m + 1)) ⟨.B, [(3 : Sym)], 1, Cw ++ (Lp Cw m ++ (x :: R))⟩
      = some ⟨.B, Lp Dw (m + 1) ++ [3], 1, x :: R⟩ :=
    sweepR_iter (m + 1) [3] (x :: R)
  have e5 : run 1 ⟨.B, Lp Dw (m + 1) ++ [(3 : Sym)], 1, x :: R⟩
      = some ⟨.A, 3 :: (Lp Dw (m + 1) ++ [3]), x, R⟩ := rfl
  have h := run_comp (run_comp (run_comp (run_comp e1 e2) e3) e4) e5
  have harith : wsteps 1 (m + 1) = 1 + 7 * m + 10 + 9 * (m + 1) + 1 := by
    simp [wsteps]; omega
  rw [harith, h]
  rw [Dw_pow_eq]
  rfl

theorem phase2 (m : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 2 (m + 1)) (wcfg 2 (m + 1) (x :: R)) = some (wexit 2 (m + 1) x R) := by
  have e1 : run 2 (wcfg 2 (m + 1) (x :: R))
      = some ⟨.A, Tw ++ Lp E m, 1, 4 :: (4 :: x :: R)⟩ := rfl
  have e2 := sweepL_iter m (4 :: x :: R)
  have e3 := turn (Lp Cw m ++ (4 :: x :: R))
  have e4 : run (9 * (m + 1)) ⟨.B, [(3 : Sym)], 1, Cw ++ (Lp Cw m ++ (4 :: x :: R))⟩
      = some ⟨.B, Lp Dw (m + 1) ++ [3], 1, 4 :: x :: R⟩ :=
    sweepR_iter (m + 1) [3] (4 :: x :: R)
  have e5 : run 2 ⟨.B, Lp Dw (m + 1) ++ [(3 : Sym)], 1, 4 :: x :: R⟩
      = some ⟨.B, 2 :: 3 :: (Lp Dw (m + 1) ++ [3]), x, R⟩ := rfl
  have h := run_comp (run_comp (run_comp (run_comp e1 e2) e3) e4) e5
  have harith : wsteps 2 (m + 1) = 2 + 7 * m + 10 + 9 * (m + 1) + 2 := by
    simp [wsteps]; omega
  rw [harith, h]
  rw [Dw_pow_eq]
  rfl

theorem phase3 (m : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 3 (m + 1)) (wcfg 3 (m + 1) (x :: R)) = some (wexit 3 (m + 1) x R) := by
  have e1 : run 3 (wcfg 3 (m + 1) (x :: R))
      = some ⟨.A, Tw ++ Lp E m, 1, 4 :: (4 :: 3 :: x :: R)⟩ := rfl
  have e2 := sweepL_iter m (4 :: 3 :: x :: R)
  have e3 := turn (Lp Cw m ++ (4 :: 3 :: x :: R))
  have e4 : run (9 * (m + 1)) ⟨.B, [(3 : Sym)], 1, Cw ++ (Lp Cw m ++ (4 :: 3 :: x :: R))⟩
      = some ⟨.B, Lp Dw (m + 1) ++ [3], 1, 4 :: 3 :: x :: R⟩ :=
    sweepR_iter (m + 1) [3] (4 :: 3 :: x :: R)
  have e5 : run 3 ⟨.B, Lp Dw (m + 1) ++ [(3 : Sym)], 1, 4 :: 3 :: x :: R⟩
      = some ⟨.A, 1 :: 2 :: 3 :: (Lp Dw (m + 1) ++ [3]), x, R⟩ := rfl
  have h := run_comp (run_comp (run_comp (run_comp e1 e2) e3) e4) e5
  have harith : wsteps 3 (m + 1) = 3 + 7 * m + 10 + 9 * (m + 1) + 3 := by
    simp [wsteps]; omega
  rw [harith, h]
  rw [Dw_pow_eq]
  rfl

theorem phase4 (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 4 n) (wcfg 4 n (x :: R)) = some (wexit 4 n x R) := rfl

theorem phase5 (m : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 5 (m + 1)) (wcfg 5 (m + 1) (x :: R)) = some (wexit 5 (m + 1) x R) := by
  have e1 : run 4 (wcfg 5 (m + 1) (x :: R))
      = some ⟨.A, Tw ++ Lp E m, 1, 4 :: (4 :: 3 :: 4 :: x :: R)⟩ := rfl
  have e2 := sweepL_iter m (4 :: 3 :: 4 :: x :: R)
  have e3 := turn (Lp Cw m ++ (4 :: 3 :: 4 :: x :: R))
  have e4 : run (9 * (m + 1)) ⟨.B, [(3 : Sym)], 1, Cw ++ (Lp Cw m ++ (4 :: 3 :: 4 :: x :: R))⟩
      = some ⟨.B, Lp Dw (m + 1) ++ [3], 1, 4 :: 3 :: 4 :: x :: R⟩ :=
    sweepR_iter (m + 1) [3] (4 :: 3 :: 4 :: x :: R)
  have e5 : run 4 ⟨.B, Lp Dw (m + 1) ++ [(3 : Sym)], 1, 4 :: 3 :: 4 :: x :: R⟩
      = some ⟨.B, 2 :: 1 :: 2 :: 3 :: (Lp Dw (m + 1) ++ [3]), x, R⟩ := rfl
  have h := run_comp (run_comp (run_comp (run_comp e1 e2) e3) e4) e5
  have harith : wsteps 5 (m + 1) = 4 + 7 * m + 10 + 9 * (m + 1) + 4 := by
    simp [wsteps]; omega
  rw [harith, h]
  rw [Dw_pow_eq]
  rfl

theorem phase6 (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 6 n) (wcfg 6 n (x :: R)) = some (wexit 6 n x R) := rfl

theorem phase7 (n : Nat) (x : Sym) (R : List Sym) :
    run (wsteps 7 n) (wcfg 7 n (x :: R)) = some (wexit 7 n x R) := rfl

/-- **Wall lemma / bouncer elimination.**  From every one of the eight wall
entry configurations (with at least one `E`-block in the wall) the machine
performs a complete excursion into the left region: it runs for `wsteps r n`
steps without halting, never reads the right-hand context `R`, and comes back
with the head on the first cell `x` of the context and the wall advanced to the
next phase.  Over a full cycle of the eight phases the wall gains exactly one
block `E` (five cells). -/
theorem wall_excursion (r : Nat) (hr : r < 8) (m : Nat) (x : Sym) (R : List Sym) :
    run (wsteps r (m + 1)) (wcfg r (m + 1) (x :: R)) = some (wexit r (m + 1) x R) := by
  match r, hr with
  | 0, _ => exact phase0 m x R
  | 1, _ => exact phase1 m x R
  | 2, _ => exact phase2 m x R
  | 3, _ => exact phase3 m x R
  | 4, _ => exact phase4 (m + 1) x R
  | 5, _ => exact phase5 m x R
  | 6, _ => exact phase6 (m + 1) x R
  | 7, _ => exact phase7 (m + 1) x R
  | (j + 8), h => exact absurd h (by omega)

/-- Starting from the blank tape, after 310 steps the machine is in the phase-0
wall configuration with one `E`-block and right-hand context
`[4,4,4,4,4,1,4,4,3]`; from then on the wall analysis above applies. -/
theorem init_reaches_wall :
    run 310 init = some (wcfg 0 1 [4, 4, 4, 4, 4, 1, 4, 4, 3]) := rfl

end TM5
