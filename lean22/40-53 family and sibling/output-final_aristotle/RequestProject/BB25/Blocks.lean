/-
# The block ("longitudinal") system and its soundness

This file turns the longitudinal table into an executable *block simulator*,
of the kind used to run the machines of the family for astronomically many
steps, and proves that it is sound: one block step is a fixed number of base
steps of the Turing machine.

Blocks, in the notation of the family notes:

```
  left of the head :  L = ^11   W = 03   X = 11   Z = 01
                      J = 023   J1 = 013  J0 = 003  K0 = 001  K1 = 011
  right of the head:  R = $   R1 = 1$   R2 = 2$   U = 12   V = 21   X = 11
                      Y = 22  F = 141   G = 241   P1 = 1>   P2 = 2>
                      N1 = 101   N2 = 201
  head states       :  Rt = A>   Lt = <A   Bt = <B1
```

The blocks `J, J1, J0, K0, K1, N1, N2` are the extra blocks created by
individual members of the family; `P1`/`P2` are the *pending digits* `1>`,
`2>`, which are not machine steps at all but a shift of the phase of the block
decomposition.

`bstep` is undefined (`none`) exactly on the configurations for which the
longitudinal analysis breaks down.  The important ones are `A> 2> 141` and
`A> 2> 241` -- a pending `2` meeting an `F` or `G` block -- which make the
machine halt in three steps, and `L <B1`, the head
reaching the left end of the tape in state `<B1`, which makes it run forever
(see `BB25.not_halts_leftend_B1`).  A pending `1` meeting an `F` or `G` block
is harmless in itself (`A> 1> 141 → <A 2> 141`) and is a rule of `bstep`.
-/
import RequestProject.BB25.Machine

namespace BB25

/-- Blocks occurring on the left of the head. -/
inductive LB | L | W | X | Z | J | J1 | J0 | K0 | K1
deriving DecidableEq, Repr

/-- Blocks occurring on the right of the head. -/
inductive RB | R | R1 | R2 | U | V | X | Y | F | G | P1 | P2 | N1 | N2
deriving DecidableEq, Repr

/-- The three "higher level" states: `A>`, `<A`, `<B1`. -/
inductive HSt | Rt | Lt | Bt
deriving DecidableEq, Repr

/-- A block-level configuration.  Both lists start next to the head. -/
structure BCfg where
  lt : List LB
  st : HSt
  rt : List RB
deriving DecidableEq, Repr

/-- The cells of a left block, nearest to the head first. -/
def LB.den : LB → List Sym
  | L => [1, 1]
  | W => [3, 0]
  | X => [1, 1]
  | Z => [1, 0]
  | J => [3, 2, 0]
  | J1 => [3, 1, 0]
  | J0 => [3, 0, 0]
  | K0 => [1, 0, 0]
  | K1 => [1, 1, 0]

/-- The cells of a right block, nearest to the head first. -/
def RB.den : RB → List Sym
  | R => []
  | R1 => [1]
  | R2 => [2]
  | U => [1, 2]
  | V => [2, 1]
  | X => [1, 1]
  | Y => [2, 2]
  | F => [1, 4, 1]
  | G => [2, 4, 1]
  | P1 => [1]
  | P2 => [2]
  | N1 => [1, 0, 1]
  | N2 => [2, 0, 1]

def denL : List LB → List Sym
  | [] => []
  | b :: bs => b.den ++ denL bs

def denR : List RB → List Sym
  | [] => []
  | b :: bs => b.den ++ denR bs

/-- The base configuration denoted by a block configuration.  In state `Bt`
the extra `1` belongs to the marker `<B1`. -/
def BCfg.den : BCfg → Cfg
  | ⟨lt, .Rt, rt⟩ => ⟨denL lt, .A, .R, denR rt⟩
  | ⟨lt, .Lt, rt⟩ => ⟨denL lt, .A, .L, denR rt⟩
  | ⟨lt, .Bt, rt⟩ => ⟨denL lt, .B, .L, 1 :: denR rt⟩

/-- The interaction of the head with a `G = 241` block: the one rule in which
the members of the family differ. -/
def gStep (b4 : Option (Sym × Dir × St)) (lt : List LB) (rest : List RB) :
    Option (BCfg × ℕ) :=
  match b4 with
  | some (2, .L, .B) => some (⟨lt, .Lt, .U :: .P1 :: rest⟩, 3)
  | some (2, .R, .B) => some (⟨.J :: lt, .Rt, rest⟩, 3)
  | some (1, .L, .B) => some (⟨lt, .Lt, .X :: .P1 :: rest⟩, 3)
  | some (1, .R, .B) => some (⟨.J1 :: lt, .Rt, rest⟩, 3)
  | some (0, .L, .B) => some (⟨lt, .Lt, .N1 :: rest⟩, 3)
  | some (0, .R, .B) => some (⟨.J0 :: lt, .Rt, rest⟩, 3)
  | some (3, .R, .A) => some (⟨lt, .Lt, .X :: .P2 :: rest⟩, 5)
  | some (2, .L, .A) => some (⟨lt, .Lt, .Y :: .P2 :: rest⟩, 7)
  | some (2, .R, .A) => some (⟨.K0 :: lt, .Rt, rest⟩, 5)
  | some (1, .L, .A) => some (⟨lt, .Bt, .Y :: rest⟩, 9)
  | some (1, .R, .A) => some (⟨.X :: lt, .Rt, .P2 :: rest⟩, 6)
  | some (0, .L, .A) => some (⟨lt, .Lt, .V :: .P1 :: rest⟩, 5)
  | some (0, .R, .A) => some (⟨.K1 :: lt, .Rt, rest⟩, 5)
  | _ => none

/--
One step of the block simulator: the new configuration and the number of base
steps it takes.  `none` means that the analysis breaks down here.
-/
def bstep (b4 : Option (Sym × Dir × St)) : BCfg → Option (BCfg × ℕ)
  -- pending digit `1>`: a pure re-parsing of the tape, 0 base steps
  | ⟨lt, .Rt, [.P1]⟩ => some (⟨lt, .Rt, [.R1]⟩, 0)
  | ⟨lt, .Rt, .P1 :: .R :: rest⟩ => some (⟨lt, .Rt, .R1 :: rest⟩, 0)
  | ⟨lt, .Rt, .P1 :: .R1 :: rest⟩ => some (⟨lt, .Rt, .X :: .R :: rest⟩, 0)
  | ⟨lt, .Rt, .P1 :: .R2 :: rest⟩ => some (⟨lt, .Rt, .U :: .R :: rest⟩, 0)
  | ⟨lt, .Rt, .P1 :: .X :: rest⟩ => some (⟨lt, .Rt, .X :: .P1 :: rest⟩, 0)
  | ⟨lt, .Rt, .P1 :: .V :: rest⟩ => some (⟨lt, .Rt, .U :: .P1 :: rest⟩, 0)
  | ⟨lt, .Rt, .P1 :: .Y :: rest⟩ => some (⟨lt, .Rt, .U :: .P2 :: rest⟩, 0)
  | ⟨lt, .Rt, .P1 :: .U :: rest⟩ => some (⟨lt, .Rt, .X :: .P2 :: rest⟩, 0)
  | ⟨lt, .Rt, .P1 :: .P1 :: rest⟩ => some (⟨lt, .Rt, .X :: rest⟩, 0)
  | ⟨lt, .Rt, .P1 :: .P2 :: rest⟩ => some (⟨lt, .Rt, .U :: rest⟩, 0)
  -- pending digit `2>`
  | ⟨lt, .Rt, [.P2]⟩ => some (⟨lt, .Rt, [.R2]⟩, 0)
  | ⟨lt, .Rt, .P2 :: .R :: rest⟩ => some (⟨lt, .Rt, .R2 :: rest⟩, 0)
  | ⟨lt, .Rt, .P2 :: .R1 :: rest⟩ => some (⟨lt, .Rt, .V :: .R :: rest⟩, 0)
  | ⟨lt, .Rt, .P2 :: .R2 :: rest⟩ => some (⟨lt, .Rt, .Y :: .R :: rest⟩, 0)
  | ⟨lt, .Rt, .P2 :: .X :: rest⟩ => some (⟨lt, .Rt, .V :: .P1 :: rest⟩, 0)
  | ⟨lt, .Rt, .P2 :: .V :: rest⟩ => some (⟨lt, .Rt, .Y :: .P1 :: rest⟩, 0)
  | ⟨lt, .Rt, .P2 :: .Y :: rest⟩ => some (⟨lt, .Rt, .Y :: .P2 :: rest⟩, 0)
  | ⟨lt, .Rt, .P2 :: .U :: rest⟩ => some (⟨lt, .Rt, .V :: .P2 :: rest⟩, 0)
  | ⟨lt, .Rt, .P2 :: .P1 :: rest⟩ => some (⟨lt, .Rt, .V :: rest⟩, 0)
  | ⟨lt, .Rt, .P2 :: .P2 :: rest⟩ => some (⟨lt, .Rt, .Y :: rest⟩, 0)
  -- the right end of the tape
  | ⟨lt, .Rt, []⟩ => some (⟨lt, .Lt, [.V, .R]⟩, 3)
  | ⟨lt, .Rt, [.R]⟩ => some (⟨lt, .Lt, [.V, .R]⟩, 3)
  | ⟨lt, .Rt, [.R1]⟩ => some (⟨lt, .Lt, [.R2]⟩, 1)
  | ⟨lt, .Rt, [.R2]⟩ => some (⟨lt, .Bt, [.Y, .R1]⟩, 11)
  -- the head moving right
  | ⟨lt, .Rt, .X :: rest⟩ => some (⟨lt, .Lt, .V :: rest⟩, 1)
  | ⟨lt, .Rt, .V :: rest⟩ => some (⟨.W :: lt, .Rt, rest⟩, 2)
  | ⟨lt, .Rt, .Y :: rest⟩ => some (⟨.Z :: lt, .Rt, rest⟩, 2)
  | ⟨lt, .Rt, .U :: rest⟩ => some (⟨lt, .Lt, .Y :: rest⟩, 1)
  | ⟨lt, .Rt, .F :: rest⟩ => some (⟨lt, .Lt, .G :: rest⟩, 1)
  -- a pending `1>` in front of a `141`/`241` block: the head turns around and
  -- leaves a pending `2>` behind (`A> 1> 141 → <A 2> 141`)
  | ⟨lt, .Rt, .P1 :: .F :: rest⟩ => some (⟨lt, .Lt, .P2 :: .F :: rest⟩, 1)
  | ⟨lt, .Rt, .P1 :: .G :: rest⟩ => some (⟨lt, .Lt, .P2 :: .G :: rest⟩, 1)
  | ⟨lt, .Rt, .N1 :: rest⟩ => some (⟨lt, .Lt, .N2 :: rest⟩, 1)
  | ⟨lt, .Rt, .N2 :: rest⟩ => some (⟨lt, .Bt, .Y :: rest⟩, 9)
  | ⟨lt, .Rt, .G :: rest⟩ => gStep b4 lt rest
  -- the head moving left in state A
  | ⟨[.L], .Lt, rt⟩ => some (⟨[.L], .Rt, .P2 :: rt⟩, 4)
  | ⟨.W :: rest, .Lt, rt⟩ => some (⟨rest, .Lt, .X :: rt⟩, 2)
  | ⟨.Z :: rest, .Lt, rt⟩ => some (⟨.X :: rest, .Rt, rt⟩, 3)
  | ⟨.X :: rest, .Lt, rt⟩ => some (⟨rest, .Lt, .Y :: rt⟩, 2)
  | ⟨.J :: rest, .Lt, rt⟩ => some (⟨.X :: rest, .Rt, .P2 :: rt⟩, 6)
  | ⟨.J1 :: rest, .Lt, rt⟩ => some (⟨rest, .Lt, .X :: .P2 :: rt⟩, 5)
  | ⟨.J0 :: rest, .Lt, rt⟩ => some (⟨rest, .Bt, .Y :: rt⟩, 9)
  | ⟨.K0 :: rest, .Lt, rt⟩ => some (⟨.K1 :: rest, .Rt, rt⟩, 3)
  | ⟨.K1 :: rest, .Lt, rt⟩ => some (⟨.X :: rest, .Rt, .P2 :: rt⟩, 4)
  -- the head moving left in state B
  | ⟨.W :: rest, .Bt, rt⟩ => some (⟨rest, .Lt, .F :: rt⟩, 2)
  | ⟨.Z :: rest, .Bt, rt⟩ => some (⟨rest, .Lt, .X :: .P2 :: rt⟩, 4)
  | ⟨.X :: rest, .Bt, rt⟩ => some (⟨rest, .Bt, .Y :: rt⟩, 6)
  | _ => none

/-- Soundness of the `G = 241` rule, for each of the 13 members. -/
theorem gStep_sound (b4 : Option (Sym × Dir × St)) (lt : List LB) (rest : List RB)
    (c' : BCfg) (k : ℕ) (h : gStep b4 lt rest = some (c', k)) :
    steps (M b4) k (BCfg.den ⟨lt, .Rt, .G :: rest⟩) = some c'.den := by
  rcases b4 with _ | ⟨w, d, q⟩
  · simp [gStep] at h
  · fin_cases w <;> cases d <;> cases q <;>
      first
        | (simp only [gStep, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h
           rfl)
        | simp [gStep] at h

/-- **Soundness of the block simulator.**  One block step is exactly the
announced number of base steps of the Turing machine. -/
theorem bstep_sound (b4 : Option (Sym × Dir × St)) (c c' : BCfg) (k : ℕ)
    (h : bstep b4 c = some (c', k)) : steps (M b4) k c.den = some c'.den := by
  unfold bstep at h
  split at h <;>
    first
      | (rw [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         rfl)
      | exact gStep_sound b4 _ _ _ _ h
      | simp at h

/-! ## Iterating the block simulator -/

/-- `n` block steps, together with the total number of base steps. -/
def bsteps (b4 : Option (Sym × Dir × St)) : ℕ → BCfg → Option (BCfg × ℕ)
  | 0, c => some (c, 0)
  | n + 1, c =>
      (bstep b4 c).bind fun p => (bsteps b4 n p.1).map fun q => (q.1, p.2 + q.2)

theorem bsteps_sound (b4 : Option (Sym × Dir × St)) : ∀ (n : ℕ) (c c' : BCfg) (k : ℕ),
    bsteps b4 n c = some (c', k) → steps (M b4) k c.den = some c'.den := by
  intro n
  induction n with
  | zero =>
      intro c c' k h
      simp only [bsteps, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | succ n ih =>
      intro c c' k h
      rw [bsteps, Option.bind_eq_some_iff] at h
      obtain ⟨⟨c₁, k₁⟩, hb, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨c₂, k₂⟩, hr, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact steps_trans (bstep_sound b4 c c₁ k₁ hb) (ih c₁ c₂ k₂ hr)

end BB25
