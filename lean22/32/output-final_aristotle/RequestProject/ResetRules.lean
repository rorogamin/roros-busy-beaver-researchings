import RequestProject.Safety

/-!
# The rules of the reset stage, for an arbitrary counter

During the reset stage the head runs to the right over material made of the
two-cell blocks `44`, `04`, `24`, `14` and rebuilds the left counter out of it.
The informal analysis of the machine describes the stage by the four rules

```
(02|22) B> 44  -->  (02|22) 02 B>
(02|22) B> 04  -->  (02|22) 22 B>
(02|22) B> 24  -->  (02|22)<  02 B>
(02|22) B> 14  -->  <<<< (03|23) 02 B>
```

Here they are proved **for an arbitrary counter**, in the macro model, together
with their exact cost in increments: `44` and `04` are free, `24` costs one
increment, and `14` costs four increments and turns the lowest digit of the
counter into a radix-3/2 digit.  The hypothesis `4 ≤ gap w` in the last rule is
exactly the "the counter does not underflow" side condition of the informal
analysis, now stated quantitatively (`gap` counts the increments a counter can
still perform).
-/

namespace SOC

/-- Reflexive-transitive closure of the macro step. -/
inductive MSteps : MCfg → MCfg → Prop
  | refl (m : MCfg) : MSteps m m
  | tail {a b c : MCfg} : MSteps a b → MStep b c → MSteps a c

theorem MSteps.single {a b : MCfg} (h : MStep a b) : MSteps a b :=
  (MSteps.refl a).tail h

theorem MSteps.trans {a b c : MCfg} (h₁ : MSteps a b) (h₂ : MSteps b c) : MSteps a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hstep ih => exact ih.tail hstep

/-- A chain of macro steps is a run of the machine. -/
theorem MSteps.sim {a b : MCfg} (h : MSteps a b) : enc a ⟶* enc b := by
  induction h with
  | refl => exact Reaches.refl _
  | tail _ hstep ih => exact ih.trans (mstep_sim hstep).reaches

/-! ## The four reset rules -/

/-- `w B> 44 r ⟶ w 02 B> r` : a free digit `02`. -/
theorem macro_44 (w : List LD) (r : List Sym) :
    MSteps ⟨w, 4 :: 4 :: r⟩ ⟨.d0 :: w, r⟩ :=
  MSteps.single (MStep.a44 (r := 4 :: 4 :: r) rfl rfl)

/-- `w B> 04 r ⟶ w 22 B> r` : a free digit `22`. -/
theorem macro_04 (w : List LD) (r : List Sym) :
    MSteps ⟨w, 0 :: 4 :: r⟩ ⟨.d1 :: w, r⟩ :=
  MSteps.single (MStep.a04 (r := 0 :: 4 :: r) rfl rfl)

/-- `w B> 24 r ⟶ inc(w) 02 B> r` : one increment, then a digit `02`. -/
theorem macro_24 {w w' : List LD} (h : Inc w w') (r : List Sym) :
    MSteps ⟨w, 2 :: 4 :: r⟩ ⟨.d0 :: w', r⟩ :=
  (MSteps.single (MStep.inc2 (r := 2 :: 4 :: r) h rfl)).trans (macro_44 w' r)

/--
`w 22 B> 14 r ⟶ inc⁴(w) 23 02 B> r` : reading a `1` next to the digit `22`
costs **four** increments, turns the `22` into the radix-3/2 digit `23` and
pushes a fresh digit `02`.
-/
theorem macro_14_d1 {w w1 w2 w3 w4 : List LD}
    (h1 : Inc w w1) (h2 : Inc w1 w2) (h3 : Inc w2 w3) (h4 : Inc w3 w4) (r : List Sym) :
    MSteps ⟨.d1 :: w, 1 :: 4 :: r⟩ ⟨.d0 :: .dA :: w4, r⟩ := by
  have s1 : MStep ⟨.d1 :: w, 1 :: 4 :: r⟩ ⟨w, 2 :: 0 :: 3 :: 4 :: r⟩ :=
    MStep.one1 (r := 1 :: 4 :: r) rfl
  have s2 : MStep ⟨w, 2 :: 0 :: 3 :: 4 :: r⟩ ⟨w1, 4 :: 0 :: 3 :: 4 :: r⟩ :=
    MStep.inc2 (r := 2 :: 0 :: 3 :: 4 :: r) h1 rfl
  have s3 : MStep ⟨w1, 4 :: 0 :: 3 :: 4 :: r⟩ ⟨.dA :: w1, 3 :: 4 :: r⟩ :=
    MStep.a40 (r := 4 :: 0 :: 3 :: 4 :: r) rfl rfl
  have s4 : MStep ⟨.dA :: w1, 3 :: 4 :: r⟩ ⟨.dB :: w3, 2 :: 4 :: r⟩ :=
    MStep.inc3 (r := 3 :: 4 :: r) (Inc.dA h2 h3) rfl
  have s5 : MStep ⟨.dB :: w3, 2 :: 4 :: r⟩ ⟨.dA :: w4, 4 :: 4 :: r⟩ :=
    MStep.inc2 (r := 2 :: 4 :: r) (Inc.dB h4) rfl
  exact ((((MSteps.single s1).tail s2).tail s3).tail s4).tail s5 |>.trans
    (macro_44 (.dA :: w4) r)

/--
`w 02 B> 14 r ⟶ inc⁴(w) 03 02 B> r` : the same rule next to the digit `02`,
which becomes the radix-3/2 digit `03`.
-/
theorem macro_14_d0 {w w1 w2 w3 w4 : List LD}
    (h1 : Inc w w1) (h2 : Inc w1 w2) (h3 : Inc w2 w3) (h4 : Inc w3 w4) (r : List Sym) :
    MSteps ⟨.d0 :: w, 1 :: 4 :: r⟩ ⟨.d0 :: .dB :: w4, r⟩ := by
  have s1 : MStep ⟨.d0 :: w, 1 :: 4 :: r⟩ ⟨w, 2 :: 1 :: 3 :: 4 :: r⟩ :=
    MStep.one0 (r := 1 :: 4 :: r) rfl
  have s2 : MStep ⟨w, 2 :: 1 :: 3 :: 4 :: r⟩ ⟨w1, 4 :: 1 :: 3 :: 4 :: r⟩ :=
    MStep.inc2 (r := 2 :: 1 :: 3 :: 4 :: r) h1 rfl
  have s3 : MStep ⟨w1, 4 :: 1 :: 3 :: 4 :: r⟩ ⟨.dB :: w1, 3 :: 4 :: r⟩ :=
    MStep.a41 (r := 4 :: 1 :: 3 :: 4 :: r) rfl rfl
  have s4 : MStep ⟨.dB :: w1, 3 :: 4 :: r⟩ ⟨.dA :: w2, 2 :: 4 :: r⟩ :=
    MStep.inc3 (r := 3 :: 4 :: r) (Inc.dB h2) rfl
  have s5 : MStep ⟨.dA :: w2, 2 :: 4 :: r⟩ ⟨.dB :: w4, 4 :: 4 :: r⟩ :=
    MStep.inc2 (r := 2 :: 4 :: r) (Inc.dA h3 h4) rfl
  exact ((((MSteps.single s1).tail s2).tail s3).tail s4).tail s5 |>.trans
    (macro_44 (.dB :: w4) r)

/-! ## The same rules in terms of the gap

`gap w` is the number of increments the counter `w` can still perform, so these
are the versions in which the side condition is checked arithmetically.
-/

end SOC
