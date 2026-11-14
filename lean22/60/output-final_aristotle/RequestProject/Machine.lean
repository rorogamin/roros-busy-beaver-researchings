module

/-!
# The machine `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`

Transition table (states `A`, `B`; symbols `0,1,2,3,4`):

| state | 0     | 1     | 2     | 3     | 4     |
|-------|-------|-------|-------|-------|-------|
| `A`   | `1RB` | `2LA` | `3LB` | `4LB` | halt  |
| `B`   | `0LA` | `4LB` | `3RA` | `4LA` | `0RB` |

The only halting transition is `A` reading `4`.  This file is the complete trusted
specification: the machine, the run from the blank tape, and the halting predicate.
-/

@[expose] public section

namespace BB25

/-- Machine states.  `H` is the (absorbing) halting state. -/
inductive St
  | A : St
  | B : St
  | H : St
  deriving DecidableEq, Repr

/-- Tape symbols. -/
abbrev Sym := Fin 5

/-- A configuration: current state, head position, tape contents. -/
structure Cfg where
  st : St
  pos : Int
  tape : Int → Sym

/-- Write `v` at position `p` of tape `T`. -/
def wr (T : Int → Sym) (p : Int) (v : Sym) : Int → Sym := fun i => if i = p then v else T i

/-- One step of the machine. -/
def step (c : Cfg) : Cfg :=
  match c.st, (c.tape c.pos).val with
  | .H, _ => c
  | .A, 0 => ⟨.B, c.pos + 1, wr c.tape c.pos 1⟩
  | .A, 1 => ⟨.A, c.pos - 1, wr c.tape c.pos 2⟩
  | .A, 2 => ⟨.B, c.pos - 1, wr c.tape c.pos 3⟩
  | .A, 3 => ⟨.B, c.pos - 1, wr c.tape c.pos 4⟩
  | .A, _ => ⟨.H, c.pos, c.tape⟩
  | .B, 0 => ⟨.A, c.pos - 1, c.tape⟩
  | .B, 1 => ⟨.B, c.pos - 1, wr c.tape c.pos 4⟩
  | .B, 2 => ⟨.A, c.pos + 1, wr c.tape c.pos 3⟩
  | .B, 3 => ⟨.A, c.pos - 1, wr c.tape c.pos 4⟩
  | .B, _ => ⟨.B, c.pos + 1, wr c.tape c.pos 0⟩

/-- The initial configuration: state `A`, head at `0`, blank (all `0`) tape. -/
def init : Cfg := ⟨.A, 0, fun _ => 0⟩

/-- The configuration after `n` steps. -/
def run : Nat → Cfg
  | 0 => init
  | n + 1 => step (run n)

/-- The machine has halted in configuration `c`. -/
def Halted (c : Cfg) : Prop := c.st = St.H

end BB25
