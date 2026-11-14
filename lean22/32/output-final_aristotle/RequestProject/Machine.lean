/-
# The Turing machine `1LB3RB0LB---2RB_2RA3LA4LB2LB0RA`

A 2-state, 5-symbol Turing machine.  States are `A`, `B`; tape symbols are `0`-`4`
(`0` is the blank symbol).  The transition table is

```
      0     1     2     3     4
A    1LB   3RB   0LB   ---   2RB
B    2RA   3LA   4LB   2LB   0RA
```

`---` means the machine halts (state `A` reading symbol `3`).

This file sets up the machine, the configuration zipper, the step function and
the basic infrastructure for reasoning about finite runs.
-/

namespace SOC

/-- The two states of the machine. -/
inductive St
  | A : St
  | B : St
deriving DecidableEq, Repr

/-- Tape symbols: `0,1,2,3,4`, with `0` the blank symbol. -/
abbrev Sym := Fin 5

/--
A configuration: the tape is `… l.reverse ++ r ++ …` with blanks on both sides,
the head sitting on the first cell of `r` (or on a blank cell if `r = []`).
`l` lists the cells strictly to the left of the head, *nearest first*.
-/
structure Cfg where
  l : List Sym
  q : St
  r : List Sym
deriving DecidableEq, Repr

namespace Cfg

/-- The symbol on a tape half, `0` if we are beyond the written part. -/
def hd (xs : List Sym) : Sym := xs.headD 0

@[simp] theorem hd_nil : hd [] = 0 := rfl
@[simp] theorem hd_cons (a : Sym) (xs : List Sym) : hd (a :: xs) = a := rfl

/-- Write `w` on the current cell, move right, enter state `q`. -/
def mvR (w : Sym) (q : St) (c : Cfg) : Cfg := ⟨w :: c.l, q, c.r.tail⟩

/-- Write `w` on the current cell, move left, enter state `q`. -/
def mvL (w : Sym) (q : St) (c : Cfg) : Cfg := ⟨c.l.tail, q, hd c.l :: w :: c.r.tail⟩

end Cfg

open Cfg

/-- One step of the machine; `none` means the machine has halted. -/
def step (c : Cfg) : Option Cfg :=
  match c.q, hd c.r with
  | St.A, 0 => some (mvL 1 St.B c)
  | St.A, 1 => some (mvR 3 St.B c)
  | St.A, 2 => some (mvL 0 St.B c)
  | St.A, 3 => none
  | St.A, 4 => some (mvR 2 St.B c)
  | St.B, 0 => some (mvR 2 St.A c)
  | St.B, 1 => some (mvL 3 St.A c)
  | St.B, 2 => some (mvL 4 St.B c)
  | St.B, 3 => some (mvL 2 St.B c)
  | St.B, 4 => some (mvR 0 St.A c)

/-- `run c n` runs the machine for `n` steps from `c`. -/
def run (c : Cfg) : Nat → Option Cfg
  | 0 => some c
  | n + 1 => (step c).bind (fun c' => run c' n)

@[simp] theorem run_zero (c : Cfg) : run c 0 = some c := rfl

theorem run_succ (c : Cfg) (n : Nat) :
    run c (n + 1) = (step c).bind (fun c' => run c' n) := rfl

/-- Running `m + n` steps is running `m` steps and then `n` steps. -/
theorem run_add (c : Cfg) (m n : Nat) :
    run c (m + n) = (run c m).bind (fun c' => run c' n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
      have : m + 1 + n = (m + n) + 1 := by omega
      rw [this, run_succ, run_succ]
      cases step c with
      | none => simp
      | some c' => simpa using ih c'

/-- Composing two finite runs. -/
theorem run_trans {c d e : Cfg} {m n : Nat} (h₁ : run c m = some d) (h₂ : run d n = some e) :
    run c (m + n) = some e := by
  rw [run_add, h₁]; simpa using h₂

/-- `c ⟶* d` : `d` is reachable from `c` in some number of steps. -/
def Reaches (c d : Cfg) : Prop := ∃ n, run c n = some d

@[inherit_doc] infixr:50 " ⟶* " => Reaches

theorem Reaches.refl (c : Cfg) : c ⟶* c := ⟨0, rfl⟩

theorem Reaches.trans {c d e : Cfg} (h₁ : c ⟶* d) (h₂ : d ⟶* e) : c ⟶* e := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, by rw [run_add, hm]; simpa using hn⟩

theorem reaches_of_run {c d : Cfg} {n : Nat} (h : run c n = some d) : c ⟶* d := ⟨n, h⟩

/-- `c ⟶+ d` : `d` is reachable from `c` in at least one step. -/
def Reaches1 (c d : Cfg) : Prop := ∃ n, 0 < n ∧ run c n = some d

@[inherit_doc] infixr:50 " ⟶+ " => Reaches1

theorem reaches1_of_run {c d : Cfg} {n : Nat} (hn : 0 < n) (h : run c n = some d) : c ⟶+ d :=
  ⟨n, hn, h⟩

theorem Reaches1.trans {c d e : Cfg} (h₁ : c ⟶+ d) (h₂ : d ⟶+ e) : c ⟶+ e := by
  obtain ⟨m, hm, hm'⟩ := h₁
  obtain ⟨n, hn, hn'⟩ := h₂
  exact ⟨m + n, by omega, by rw [run_add, hm']; simpa using hn'⟩

theorem Reaches1.reaches {c d : Cfg} (h : c ⟶+ d) : c ⟶* d := by
  obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

/-- If the machine is still running after `N` steps it is running after every
`n ≤ N` steps. -/
theorem isSome_of_run_le {c : Cfg} {N n : Nat} (h : (run c N).isSome) (hn : n ≤ N) :
    (run c n).isSome := by
  have hsplit : run c N = (run c n).bind (fun c' => run c' (N - n)) := by
    rw [← run_add]
    congr 1
    omega
  cases hrn : run c n with
  | none =>
      rw [hrn] at hsplit
      simp only [Option.bind] at hsplit
      rw [hsplit] at h
      simp at h
  | some _ => simp

/-- The initial configuration: blank tape, state `A`. -/
def init : Cfg := ⟨[], St.A, []⟩

/-- The machine never halts when started from the blank tape. -/
def NeverHalts : Prop := ∀ n, (run init n).isSome

/-- If `c` can reach `d` and the machine runs forever from `d`, it runs forever from `c`. -/
theorem forever_of_reaches {c d : Cfg} (h : c ⟶* d)
    (hd : ∀ n, (run d n).isSome) : ∀ n, (run c n).isSome := by
  obtain ⟨m, hm⟩ := h
  intro n
  -- after `m` steps we are at `d`; before that, all intermediate runs are defined
  by_cases hmn : n ≤ m
  · -- `run c n` is defined because `run c m` is
    have : run c m = (run c n).bind (fun c' => run c' (m - n)) := by
      rw [← run_add]
      congr 1
      omega
    rw [hm] at this
    cases hrn : run c n with
    | none => rw [hrn] at this; simp at this
    | some _ => simp
  · have : run c n = (run c m).bind (fun c' => run c' (n - m)) := by
      rw [← run_add]
      congr 1
      omega
    rw [hm] at this
    rw [this]
    simpa using hd (n - m)

end SOC
