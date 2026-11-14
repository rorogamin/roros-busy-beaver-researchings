import RequestProject.Rules

/-!
# A digit-level macro model of `1LB3RB0LB---2RB_2RA3LA4LB2LB0RA`

The tape of the machine is always of the shape

```
.22 (left counter) [head, state B] (right material) .
```

where the left counter is a sequence of two-cell *digits*

```
02   22   23   03
```

written *leftmost first* on the tape.  Read with the digit nearest the head as
the least significant one, the counter is a mixed-radix counter: `02`/`22` are
the two values of a radix-2 position and `23`/`03` the two values of a
radix-3/2 position.  The leftward sweeps of the machine (state `B` running left
over `2`s and `3`s) are exactly the `+1` of this counter.

This file introduces

* the digit type `LD` and the encoding `lzz` of a digit string into the tape;
* the increment relation `Inc` of the counter;
* `inc_sweep` — the theorem that a leftward sweep of the machine performs `Inc`,
  for an arbitrary counter and an arbitrary tape context.  This is the
  "one sweep" theorem that all the macro rules are built from.

The digits are listed **least significant first** (i.e. nearest the head first),
which is the order in which the machine meets them.
-/

namespace SOC

open Cfg

/-- A digit of the left counter: `d0 = 02`, `d1 = 22` (the radix-2 digits),
`dA = 23`, `dB = 03` (the radix-3/2 digits). -/
inductive LD
  | d0 | d1 | dA | dB
deriving DecidableEq, Repr

/-- The two cells of a digit, **nearest the head first** (i.e. reversed with
respect to the tape order `02`, `22`, `23`, `03`). -/
def revc : LD → List Sym
  | .d0 => [2, 0]
  | .d1 => [2, 2]
  | .dA => [3, 2]
  | .dB => [3, 0]

/-- The left half of the tape holding the counter `w` (least significant digit
first), as the `l`-component of a configuration: the cells nearest the head
first, ending with the marker `22` at the left edge of the written tape. -/
def lzz : List LD → List Sym
  | [] => [2, 2]
  | d :: w => revc d ++ lzz w

@[simp] theorem lzz_nil : lzz [] = [2, 2] := rfl

@[simp] theorem lzz_cons (d : LD) (w : List LD) : lzz (d :: w) = revc d ++ lzz w := rfl

/--
`Inc w w'` : incrementing the counter `w` (least significant digit first)
yields `w'`.

* a digit `02` absorbs the increment and becomes `22`;
* a digit `22` becomes `02` and carries;
* a digit `03` becomes `23` and carries **once**;
* a digit `23` becomes `03` and carries **twice** — this is the radix-3/2
  position.

If no derivation exists the counter overflows (the sweep runs into the marker).
-/
inductive Inc : List LD → List LD → Prop
  | d0 (w : List LD) : Inc (.d0 :: w) (.d1 :: w)
  | d1 {w w' : List LD} : Inc w w' → Inc (.d1 :: w) (.d0 :: w')
  | dB {w w' : List LD} : Inc w w' → Inc (.dB :: w) (.dA :: w')
  | dA {w w' w'' : List LD} : Inc w w' → Inc w' w'' → Inc (.dA :: w) (.dB :: w'')

/-! ## The sweep theorem

A head in state `B` that reads a `2` just right of the counter sweeps left,
performs the increment, and comes back to exactly the same place, leaving a `4`
where the `2` was.  Reading a `3` instead, it leaves a `2`.
-/

/-- **The sweep performs an increment.**  `w B> 2 r ⟶+ inc(w) B> 4 r`. -/
theorem inc_sweep {w w' : List LD} (h : Inc w w') :
    ∀ r : List Sym, (⟨lzz w, St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w', St.B, 4 :: r⟩ := by
  induction h with
  | d0 w =>
      intro r
      exact reaches1_of_run (n := 4) (by decide) rfl
  | @d1 w w' _ ih =>
      intro r
      -- two steps across the digit `22`, then the increment of `w`, then `B> 44 ⟶ 02 B>`
      have h1 : (⟨lzz (.d1 :: w), St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 4 :: 4 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      exact h1.trans (((ih _).trans (reaches1_of_run (by decide) (rule_44 (lzz w') (4 :: r)))))
  | @dB w w' _ ih =>
      intro r
      have h1 : (⟨lzz (.dB :: w), St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 0 :: 4 :: r⟩ :=
        reaches1_of_run (n := 4) (by decide) rfl
      exact h1.trans ((ih _).trans (reaches1_of_run (by decide) (rule_40 (lzz w') (4 :: r))))
  | @dA w w' w'' _ _ ih1 ih2 =>
      intro r
      have h1 : (⟨lzz (.dA :: w), St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 2 :: 4 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      have h2 : (⟨lzz w', St.B, 4 :: 2 :: 4 :: r⟩ : Cfg) ⟶+ ⟨lzz w', St.B, 2 :: 1 :: 4 :: r⟩ :=
        reaches1_of_run (by decide) (rule_42 (lzz w') (4 :: r))
      exact h1.trans ((ih1 _).trans (h2.trans ((ih2 _).trans
        (reaches1_of_run (by decide) (rule_41 (lzz w'') (4 :: r))))))

/-- **The sweep started on a `3`.**  `w B> 3 r ⟶+ inc(w) B> 2 r`. -/
theorem inc_sweep3 {w w' : List LD} (h : Inc w w') :
    ∀ r : List Sym, (⟨lzz w, St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz w', St.B, 2 :: r⟩ := by
  cases h with
  | d0 w =>
      intro r
      exact reaches1_of_run (n := 4) (by decide) rfl
  | @d1 w w' h =>
      intro r
      have h1 : (⟨lzz (.d1 :: w), St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 4 :: 2 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      exact h1.trans ((inc_sweep h _).trans (reaches1_of_run (by decide) (rule_44 (lzz w') (2 :: r))))
  | @dB w w' h =>
      intro r
      have h1 : (⟨lzz (.dB :: w), St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 0 :: 2 :: r⟩ :=
        reaches1_of_run (n := 4) (by decide) rfl
      exact h1.trans ((inc_sweep h _).trans (reaches1_of_run (by decide) (rule_40 (lzz w') (2 :: r))))
  | @dA w w' w'' h1' h2' =>
      intro r
      have h1 : (⟨lzz (.dA :: w), St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 2 :: 2 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      have h2 : (⟨lzz w', St.B, 4 :: 2 :: 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w', St.B, 2 :: 1 :: 2 :: r⟩ :=
        reaches1_of_run (by decide) (rule_42 (lzz w') (2 :: r))
      exact h1.trans ((inc_sweep h1' _).trans (h2.trans ((inc_sweep h2' _).trans
        (reaches1_of_run (by decide) (rule_41 (lzz w'') (2 :: r))))))

/-! ## Overflow of the counter

If no increment is possible — every digit of the counter carries — the sweep
runs all the way into the marker `.22`, turns around on the first blank cell and
rebuilds the marker one cell further to the left.  The cells of the old counter
are left *to the right* of the head and become the new right-hand material.

`Ovf w s` records that the counter `w` overflows and releases the cells `s`
(listed in tape order, leftmost first); `Ovf3 w s` is the variant in which the
sweep is started by a `3` instead of a `2`.
-/

/-- The counter `w` overflows, releasing the cells `s`. -/
inductive Ovf : List LD → List Sym → Prop
  | nil : Ovf [] []
  | d1 {w s} : Ovf w s → Ovf (.d1 :: w) (s ++ [4, 4])
  | dB {w s} : Ovf w s → Ovf (.dB :: w) (s ++ [0, 4])
  | dA1 {w s} : Ovf w s → Ovf (.dA :: w) (s ++ [2, 4])
  | dA2 {w w' s} : Inc w w' → Ovf w' s → Ovf (.dA :: w) (s ++ [1, 4])

/-- The counter `w` overflows when the sweep is started by a `3`. -/
inductive Ovf3 : List LD → List Sym → Prop
  | nil : Ovf3 [] [2]
  | d1 {w s} : Ovf w s → Ovf3 (.d1 :: w) (4 :: (s ++ [4, 2]))
  | dB {w s} : Ovf w s → Ovf3 (.dB :: w) (4 :: (s ++ [0, 2]))
  | dA1 {w s} : Ovf w s → Ovf3 (.dA :: w) (4 :: (s ++ [2, 2]))
  | dA2 {w w' s} : Inc w w' → Ovf w' s → Ovf3 (.dA :: w) (4 :: (s ++ [1, 2]))

/-- **Left overflow.**  `w B> 2 r ⟶+ .22 B> 44 s r`, where the tape has grown by
one cell at the left and `s` are the released cells of the old counter. -/
theorem ovf_sweep {w : List LD} {s : List Sym} (h : Ovf w s) :
    ∀ r : List Sym, (⟨lzz w, St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz [], St.B, 4 :: 4 :: (s ++ r)⟩ := by
  induction h with
  | nil => intro r; exact reaches1_of_run (n := 5) (by decide) rfl
  | @d1 w s _ ih =>
      intro r
      have h1 : (⟨lzz (.d1 :: w), St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 4 :: 4 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      have h2 := ih (4 :: 4 :: r)
      simpa using h1.trans h2
  | @dB w s _ ih =>
      intro r
      have h1 : (⟨lzz (.dB :: w), St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 0 :: 4 :: r⟩ :=
        reaches1_of_run (n := 4) (by decide) rfl
      have h2 := ih (0 :: 4 :: r)
      simpa using h1.trans h2
  | @dA1 w s _ ih =>
      intro r
      have h1 : (⟨lzz (.dA :: w), St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 2 :: 4 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      have h2 := ih (2 :: 4 :: r)
      simpa using h1.trans h2
  | @dA2 w w' s hinc _ ih =>
      intro r
      have h1 : (⟨lzz (.dA :: w), St.B, 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 2 :: 4 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      have h2 : (⟨lzz w', St.B, 4 :: 2 :: 4 :: r⟩ : Cfg) ⟶+ ⟨lzz w', St.B, 2 :: 1 :: 4 :: r⟩ :=
        reaches1_of_run (by decide) (rule_42 (lzz w') (4 :: r))
      have h3 := ih (1 :: 4 :: r)
      simpa using h1.trans ((inc_sweep hinc _).trans (h2.trans h3))

/-- **Left overflow, sweep started on a `3`.** -/
theorem ovf_sweep3 {w : List LD} {s : List Sym} (h : Ovf3 w s) :
    ∀ r : List Sym, (⟨lzz w, St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz [], St.B, 4 :: (s ++ r)⟩ := by
  cases h with
  | nil => intro r; exact reaches1_of_run (n := 5) (by decide) rfl
  | @d1 w s h =>
      intro r
      have h1 : (⟨lzz (.d1 :: w), St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 4 :: 2 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      have h2 := ovf_sweep h (4 :: 2 :: r)
      simpa using h1.trans h2
  | @dB w s h =>
      intro r
      have h1 : (⟨lzz (.dB :: w), St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 0 :: 2 :: r⟩ :=
        reaches1_of_run (n := 4) (by decide) rfl
      have h2 := ovf_sweep h (0 :: 2 :: r)
      simpa using h1.trans h2
  | @dA1 w s h =>
      intro r
      have h1 : (⟨lzz (.dA :: w), St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 2 :: 2 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      have h2 := ovf_sweep h (2 :: 2 :: r)
      simpa using h1.trans h2
  | @dA2 w w' s hinc h =>
      intro r
      have h1 : (⟨lzz (.dA :: w), St.B, 3 :: r⟩ : Cfg) ⟶+ ⟨lzz w, St.B, 2 :: 2 :: 2 :: r⟩ :=
        reaches1_of_run (n := 2) (by decide) rfl
      have h2 : (⟨lzz w', St.B, 4 :: 2 :: 2 :: r⟩ : Cfg) ⟶+ ⟨lzz w', St.B, 2 :: 1 :: 2 :: r⟩ :=
        reaches1_of_run (by decide) (rule_42 (lzz w') (2 :: r))
      have h3 := ovf_sweep h (1 :: 2 :: r)
      simpa using h1.trans ((inc_sweep hinc _).trans (h2.trans h3))

end SOC
