import RequestProject.NormalPhase

/-!
# Bulk increments: an executable model of the counter

The macro model of `RequestProject.MacroMachine` is exact but it is *not* fast:
the increment relation `Inc` is defined digit by digit and a radix-3/2 digit
carries **twice**, so a naive evaluation of one increment can cost `2^k` steps
for a counter with `k` radix-3/2 positions — exactly the cost of running the
Turing machine itself.

This file removes that blow-up.  Instead of applying increments one at a time,
a position is told *how many* increments it receives and reports *how many*
carries it produces:

| digit | value | carries produced by `t` increments | digit afterwards |
|---|---|---|---|
| `02` | `0` | `t / 2` | `02`/`22` by the parity of `t` |
| `22` | `1` | `(t+1) / 2` | `22`/`02` |
| `03` | `0` | `3t / 2` | `03`/`23` |
| `23` | `1` | `3(t+1)/2 - 1` | `23`/`03` |

`addT w t` applies `t` increments to the whole counter in **one pass**, stopping
as soon as the number of carries reaches `0`, and returns `none` if the counter
overflows on the way.  The two theorems that make it usable are

* `addT_add` — `t` increments followed by `u` increments are `t + u`
  increments; and
* `addT_one_inc` / `inc_addT_one` — one bulk increment is exactly one `Inc`.

Together they say that `addT w t = some w'` holds exactly when the counter `w`
reaches `w'` after `t` increments of the macro model.
-/

namespace SOC

/-! ## The digit-local arithmetic -/

/-- The other digit of the same position: `02 ↔ 22` and `03 ↔ 23`. -/
def flipD : LD → LD
  | .d0 => .d1
  | .d1 => .d0
  | .dB => .dA
  | .dA => .dB

@[simp] theorem flipD_flipD (d : LD) : flipD (flipD d) = d := by cases d <;> rfl

/-- The digit a position holds after receiving `t` increments. -/
def nextD (d : LD) (t : Nat) : LD := if t % 2 = 0 then d else flipD d

/-- The number of carries a position emits when it receives `t` increments.
A radix-2 position emits one carry per two increments, a radix-3/2 position
three carries per two increments. -/
def carries : LD → Nat → Nat
  | .d0, t => t / 2
  | .d1, t => (t + 1) / 2
  | .dB, t => 3 * t / 2
  | .dA, t => (3 * (t + 1)) / 2 - 1

@[simp] theorem carries_zero (d : LD) : carries d 0 = 0 := by cases d <;> rfl

@[simp] theorem nextD_zero (d : LD) : nextD d 0 = d := by simp [nextD]

/-- Carries add up: receiving `a` and then `b` increments emits as many carries
as receiving `a + b` at once. -/
theorem carries_add (d : LD) (a b : Nat) :
    carries d (a + b) = carries d a + carries (nextD d a) b := by
  by_cases h : a % 2 = 0 <;>
    cases d <;> simp only [nextD, flipD, h, carries, reduceIte] <;> omega

theorem nextD_add (d : LD) (a b : Nat) : nextD (nextD d a) b = nextD d (a + b) := by
  unfold nextD
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0 <;>
    simp [ha, hb, Nat.add_mod]
  intro h
  exfalso
  omega

/-! ## Bulk increments of the whole counter -/

/--
`addT w t` performs `t` increments of the counter `w` in one pass, or returns
`none` if `w` overflows before the `t`-th increment.  The recursion stops as
soon as a position emits no carry, so a single increment costs only as much as
the carry chain it triggers.
-/
def addT : List LD → Nat → Option (List LD)
  | w, 0 => some w
  | [], _ => none
  | d :: w, t => (addT w (carries d t)).map (fun u => nextD d t :: u)

@[simp] theorem addT_zero (w : List LD) : addT w 0 = some w := by cases w <;> rfl

theorem addT_nil {t : Nat} (ht : t ≠ 0) : addT [] t = none := by
  cases t with
  | zero => simp at ht
  | succ n => rfl

theorem addT_cons (d : LD) (w : List LD) {t : Nat} (ht : t ≠ 0) :
    addT (d :: w) t = (addT w (carries d t)).map (fun u => nextD d t :: u) := by
  cases t with
  | zero => simp at ht
  | succ n => rfl

/-- **Bulk increments compose.** -/
theorem addT_add : ∀ (w : List LD) (a b : Nat),
    addT w (a + b) = (addT w a).bind (fun u => addT u b)
  | [], a, b => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · rw [addT_nil (by omega), addT_nil (by omega)]; rfl
  | d :: w, a, b => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · rw [addT_cons d w (by omega : a + b ≠ 0), addT_cons d w (by omega : a ≠ 0),
          carries_add d a b, addT_add w (carries d a) (carries (nextD d a) b)]
        cases h : addT w (carries d a) with
        | none => simp
        | some v =>
            simp only [Option.bind_some, Option.map_some]
            rcases Nat.eq_zero_or_pos b with rfl | hb
            · simp
            · rw [addT_cons (nextD d a) v (by omega : b ≠ 0), nextD_add]

/-! ### A tail-recursive implementation

`addT` as defined above recurses through the carry chain, which can be
thousands of positions long; evaluating it would overflow the stack.  The
following accumulator version is tail recursive and is registered as the
implementation of `addT` (`@[csimp]`, so the replacement is checked by the
kernel).
-/

/-- Tail-recursive implementation of `addT`: `acc` holds the digits already
processed, in reverse order. -/
def addTAux : List LD → Nat → List LD → Option (List LD)
  | w, 0, acc => some (acc.reverseAux w)
  | [], _, _ => none
  | d :: w, t, acc => addTAux w (carries d t) (nextD d t :: acc)

theorem addTAux_cons (d : LD) (w : List LD) {t : Nat} (acc : List LD) (ht : t ≠ 0) :
    addTAux (d :: w) t acc = addTAux w (carries d t) (nextD d t :: acc) := by
  cases t with
  | zero => simp at ht
  | succ n => rfl

theorem addTAux_eq : ∀ (w : List LD) (t : Nat) (acc : List LD),
    addTAux w t acc = (addT w t).map (fun u => acc.reverseAux u)
  | w, 0, acc => by simp [addTAux]
  | [], t + 1, acc => by simp [addTAux, addT_nil]
  | d :: w, t + 1, acc => by
      rw [addTAux_cons d w acc (by omega), addTAux_eq w (carries d (t + 1)) (nextD d (t + 1) :: acc),
        addT_cons d w (by omega : t + 1 ≠ 0)]
      cases addT w (carries d (t + 1)) <;> simp [List.reverseAux]

/-- The tail-recursive implementation of `addT`. -/
def addTImpl (w : List LD) (t : Nat) : Option (List LD) := addTAux w t []

@[csimp] theorem addT_eq_addTImpl : @addT = @addTImpl := by
  funext w t
  rw [addTImpl, addTAux_eq]
  cases addT w t <;> simp [List.reverseAux]

/-- A bulk increment does not change the number of digits. -/
theorem addT_length : ∀ {w w' : List LD} {t : Nat}, addT w t = some w' →
    w'.length = w.length
  | w, w', 0, h => by simp at h; rw [h]
  | [], w', t + 1, h => by rw [addT_nil (by omega)] at h; exact absurd h (by simp)
  | d :: w, w', t + 1, h => by
      rw [addT_cons d w (by omega : t + 1 ≠ 0)] at h
      cases hv : addT w (carries d (t + 1)) with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some v =>
          rw [hv] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]
          simp [addT_length hv]

/-! ## One bulk increment is one `Inc` -/

/-- One increment of the macro model is one bulk increment. -/
theorem inc_addT_one {w w' : List LD} (h : Inc w w') : addT w 1 = some w' := by
  induction h with
  | d0 w =>
      rw [addT_cons _ _ (by omega), show carries LD.d0 1 = 0 from rfl]
      simp [nextD, flipD]
  | @d1 w w' _ ih =>
      rw [addT_cons _ _ (by omega), show carries LD.d1 1 = 1 from rfl, ih]
      simp [nextD, flipD]
  | @dB w w' _ ih =>
      rw [addT_cons _ _ (by omega), show carries LD.dB 1 = 1 from rfl, ih]
      simp [nextD, flipD]
  | @dA w w' w'' h1 h2 ih1 ih2 =>
      rw [addT_cons _ _ (by omega), show carries LD.dA 1 = 1 + 1 from rfl,
        addT_add w 1 1, ih1]
      simp [ih2, nextD, flipD]

/-- **A successful bulk increment of size one is an increment.** -/
theorem addT_one_inc : ∀ {w w' : List LD}, addT w 1 = some w' → Inc w w'
  | [], w', h => by rw [addT_nil (by omega)] at h; exact absurd h (by simp)
  | .d0 :: w, w', h => by
      rw [addT_cons _ _ (by omega), show carries LD.d0 1 = 0 from rfl] at h
      simp only [addT_zero, Option.map_some, Option.some.injEq] at h
      rw [← h]; exact Inc.d0 w
  | .d1 :: w, w', h => by
      rw [addT_cons _ _ (by omega), show carries LD.d1 1 = 1 from rfl] at h
      cases hv : addT w 1 with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some v =>
          rw [hv] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]; exact Inc.d1 (addT_one_inc hv)
  | .dB :: w, w', h => by
      rw [addT_cons _ _ (by omega), show carries LD.dB 1 = 1 from rfl] at h
      cases hv : addT w 1 with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some v =>
          rw [hv] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]; exact Inc.dB (addT_one_inc hv)
  | .dA :: w, w', h => by
      rw [addT_cons _ _ (by omega), show carries LD.dA 1 = 1 + 1 from rfl,
        addT_add w 1 1] at h
      cases hv : addT w 1 with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some v =>
          rw [hv] at h
          simp only [Option.bind_some] at h
          cases hu : addT v 1 with
          | none => rw [hu] at h; exact absurd h (by simp)
          | some u =>
              rw [hu] at h
              simp only [Option.map_some, Option.some.injEq] at h
              have hlen : v.length = w.length := addT_length hv
              rw [← h]
              exact Inc.dA (addT_one_inc hv) (addT_one_inc hu)
  termination_by w => w.length
  decreasing_by
    · simp [List.length_cons]
    · simp [List.length_cons]
    · simp [List.length_cons]
    · simp [List.length_cons, hlen]

/-- A counter that cannot be bulk-incremented has gap `0`. -/
theorem gap_eq_zero_of_addT_none {w : List LD} (h : addT w 1 = none) : gap w = 0 := by
  cases hg : gap w with
  | zero => rfl
  | succ k =>
      obtain ⟨w', hw'⟩ := inc_exists (by omega : 0 < gap w)
      rw [inc_addT_one hw'] at h
      exact absurd h (by simp)

/-- Four bulk increments are four increments. -/
theorem addT_four {w w4 : List LD} (h : addT w 4 = some w4) :
    ∃ w1 w2 w3, Inc w w1 ∧ Inc w1 w2 ∧ Inc w2 w3 ∧ Inc w3 w4 := by
  rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, addT_add, addT_add, addT_add] at h
  cases h1 : addT w 1 with
  | none => rw [h1] at h; simp at h
  | some w1 =>
      rw [h1] at h; simp only [Option.bind_some] at h
      cases h2 : addT w1 1 with
      | none => rw [h2] at h; simp at h
      | some w2 =>
          rw [h2] at h; simp only [Option.bind_some] at h
          cases h3 : addT w2 1 with
          | none => rw [h3] at h; simp at h
          | some w3 =>
              rw [h3] at h; simp only [Option.bind_some] at h
              exact ⟨w1, w2, w3, addT_one_inc h1, addT_one_inc h2, addT_one_inc h3,
                addT_one_inc h⟩

/-! ## The blocks released by an overflow

`ovfF w acc` computes the blocks the overflow of `w` releases, in tape order
(most significant first), in front of the accumulated blocks `acc`.  The digits
are read from the lowest one upwards, which is the order in which the sweep
meets them, so the accumulator is built by prepending.
-/

def ovfF : List LD → List Sym → Option (List Sym)
  | [], acc => some acc
  | .d0 :: _, _ => none
  | .d1 :: w, acc => ovfF w (4 :: acc)
  | .dB :: w, acc => ovfF w (0 :: acc)
  | .dA :: w, acc =>
      match h : addT w 1 with
      | none => ovfF w (2 :: acc)
      | some w' => ovfF w' (1 :: acc)
  termination_by w => w.length
  decreasing_by
    · simp
    · simp
    · simp
    · simp [addT_length h]

/-- **`ovfF` computes the released blocks.** -/
theorem ovfF_spec : ∀ {w : List LD} {acc L : List Sym}, ovfF w acc = some L →
    ∃ L0, L = L0 ++ acc ∧ (∀ x ∈ L0, Label x) ∧ Ovf w (cellsOf L0)
  | [], acc, L, h => by
      refine ⟨[], ?_, by simp, Ovf.nil⟩
      rw [ovfF] at h
      simpa using h.symm
  | .d0 :: w, acc, L, h => by rw [ovfF] at h; exact absurd h (by simp)
  | .d1 :: w, acc, L, h => by
      rw [ovfF] at h
      obtain ⟨L0, rfl, hlab, hovf⟩ := ovfF_spec h
      refine ⟨L0 ++ [4], by simp, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hlab x hx
        · simp at hx; exact Or.inl hx
      · rw [cellsOf_append]; exact Ovf.d1 hovf
  | .dB :: w, acc, L, h => by
      rw [ovfF] at h
      obtain ⟨L0, rfl, hlab, hovf⟩ := ovfF_spec h
      refine ⟨L0 ++ [0], by simp, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hlab x hx
        · simp at hx; exact Or.inr (Or.inl hx)
      · rw [cellsOf_append]; exact Ovf.dB hovf
  | .dA :: w, acc, L, h => by
      rw [ovfF] at h
      cases hone : addT w 1 with
      | none =>
          rw [hone] at h
          simp only at h
          obtain ⟨L0, rfl, hlab, hovf⟩ := ovfF_spec h
          refine ⟨L0 ++ [2], by simp, ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact hlab x hx
            · simp at hx; exact Or.inr (Or.inr (Or.inl hx))
          · rw [cellsOf_append]; exact Ovf.dA1 hovf
      | some w' =>
          rw [hone] at h
          simp only at h
          have hlen : w'.length = w.length := addT_length hone
          obtain ⟨L0, rfl, hlab, hovf⟩ := ovfF_spec h
          refine ⟨L0 ++ [1], by simp, ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact hlab x hx
            · simp at hx; exact Or.inr (Or.inr (Or.inr hx))
          · rw [cellsOf_append]; exact Ovf.dA2 (addT_one_inc hone) hovf
  termination_by w => w.length
  decreasing_by
    · simp
    · simp
    · simp
    · simp [hlen]

/-! ## The reset phase -/

/-- Absorbing the blocks `L` into the counter `w`; `none` if the counter
underflows, or if a block `14` meets a radix-3/2 digit. -/
def resetF : List LD → List Sym → Option (List LD)
  | w, [] => some w
  | w, 4 :: L => resetF (.d0 :: w) L
  | w, 0 :: L => resetF (.d1 :: w) L
  | w, 2 :: L =>
      match addT w 1 with
      | none => none
      | some w' => resetF (.d0 :: w') L
  | .d1 :: v, 1 :: L =>
      match addT v 4 with
      | none => none
      | some v' => resetF (.d0 :: .dA :: v') L
  | .d0 :: v, 1 :: L =>
      match addT v 4 with
      | none => none
      | some v' => resetF (.d0 :: .dB :: v') L
  | _, _ => none

@[simp] theorem resetF_three (w : List LD) (L : List Sym) : resetF w (3 :: L) = none := rfl
@[simp] theorem resetF_one_nil (L : List Sym) : resetF [] (1 :: L) = none := rfl
@[simp] theorem resetF_one_dA (v : List LD) (L : List Sym) :
    resetF (.dA :: v) (1 :: L) = none := rfl
@[simp] theorem resetF_one_dB (v : List LD) (L : List Sym) :
    resetF (.dB :: v) (1 :: L) = none := rfl

/-- **`resetF` computes the reset phase.** -/
theorem resetF_spec : ∀ {w w' : List LD} {L : List Sym}, resetF w L = some w' →
    ∀ r : List Sym, MSteps ⟨w, cellsOf L ++ r⟩ ⟨w', r⟩
  | w, w', [], h, r => by
      rw [resetF] at h
      cases h
      simpa using MSteps.refl _
  | w, w', x :: L, h, r => by
      have key : ∀ (w1 : List LD), MSteps ⟨w, x :: 4 :: (cellsOf L ++ r)⟩ ⟨w1, cellsOf L ++ r⟩ →
          resetF w1 L = some w' → MSteps ⟨w, cellsOf (x :: L) ++ r⟩ ⟨w', r⟩ := by
        intro w1 hstep hrec
        have hrest := resetF_spec hrec r
        simpa using hstep.trans hrest
      match x with
      | 4 => exact key _ (macro_44 w _) (by rw [resetF] at h; exact h)
      | 0 => exact key _ (macro_04 w _) (by rw [resetF] at h; exact h)
      | 2 =>
          rw [resetF] at h
          cases hone : addT w 1 with
          | none => rw [hone] at h; simp at h
          | some w1 =>
              rw [hone] at h; simp only at h
              exact key _ (macro_24 (addT_one_inc hone) _) h
      | 1 =>
          match w with
          | [] => simp at h
          | .dA :: v => simp at h
          | .dB :: v => simp at h
          | .d1 :: v =>
              rw [resetF] at h
              cases hfour : addT v 4 with
              | none => rw [hfour] at h; simp at h
              | some v' =>
                  rw [hfour] at h; simp only at h
                  obtain ⟨v1, v2, v3, e1, e2, e3, e4⟩ := addT_four hfour
                  exact key _ (macro_14_d1 e1 e2 e3 e4 _) h
          | .d0 :: v =>
              rw [resetF] at h
              cases hfour : addT v 4 with
              | none => rw [hfour] at h; simp at h
              | some v' =>
                  rw [hfour] at h; simp only at h
                  obtain ⟨v1, v2, v3, e1, e2, e3, e4⟩ := addT_four hfour
                  exact key _ (macro_14_d0 e1 e2 e3 e4 _) h
      | 3 => simp at h

/-! ## The junction -/

/-- Reading the terminating `1` of the old right-hand material. -/
def junctionF : List LD → Option (List LD)
  | .d1 :: v => (addT v 4).map (fun v' => .dA :: .dA :: v')
  | .d0 :: v => (addT v 4).map (fun v' => .dA :: .dB :: v')
  | _ => none

@[simp] theorem junctionF_nil : junctionF [] = none := rfl
@[simp] theorem junctionF_dA (v : List LD) : junctionF (.dA :: v) = none := rfl
@[simp] theorem junctionF_dB (v : List LD) : junctionF (.dB :: v) = none := rfl

/-- **`junctionF` computes the junction.** -/
theorem junctionF_spec : ∀ {w w' : List LD}, junctionF w = some w' →
    MSteps ⟨w, [1]⟩ ⟨w', []⟩
  | [], w', h => by simp at h
  | .dA :: v, w', h => by simp at h
  | .dB :: v, w', h => by simp at h
  | .d1 :: v, w', h => by
      rw [junctionF] at h
      cases hfour : addT v 4 with
      | none => rw [hfour] at h; simp at h
      | some v' =>
          rw [hfour] at h
          simp only [Option.map_some, Option.some.injEq] at h
          obtain ⟨v1, v2, v3, e1, e2, e3, e4⟩ := addT_four hfour
          subst h
          have s1 : MStep ⟨LD.d1 :: v, [1]⟩ ⟨v, [2, 0, 3]⟩ := MStep.one1 (r := [1]) rfl
          have s2 : MStep ⟨v, [2, 0, 3]⟩ ⟨v1, [4, 0, 3]⟩ := MStep.inc2 (r := [2, 0, 3]) e1 rfl
          have s3 : MStep ⟨v1, [4, 0, 3]⟩ ⟨LD.dA :: v1, [3]⟩ := MStep.a40 (r := [4, 0, 3]) rfl rfl
          have s4 : MStep ⟨LD.dA :: v1, [3]⟩ ⟨LD.dB :: v3, [2]⟩ :=
            MStep.inc3 (r := [3]) (Inc.dA e2 e3) rfl
          have s5 : MStep ⟨LD.dB :: v3, [2]⟩ ⟨LD.dA :: v', [4]⟩ :=
            MStep.inc2 (r := [2]) (Inc.dB e4) rfl
          have s6 : MStep ⟨LD.dA :: v', [4]⟩ ⟨LD.dA :: LD.dA :: v', []⟩ :=
            MStep.a40 (r := [4]) rfl rfl
          exact (((((MSteps.single s1).tail s2).tail s3).tail s4).tail s5).tail s6
  | .d0 :: v, w', h => by
      rw [junctionF] at h
      cases hfour : addT v 4 with
      | none => rw [hfour] at h; simp at h
      | some v' =>
          rw [hfour] at h
          simp only [Option.map_some, Option.some.injEq] at h
          obtain ⟨v1, v2, v3, e1, e2, e3, e4⟩ := addT_four hfour
          subst h
          have s1 : MStep ⟨LD.d0 :: v, [1]⟩ ⟨v, [2, 1, 3]⟩ := MStep.one0 (r := [1]) rfl
          have s2 : MStep ⟨v, [2, 1, 3]⟩ ⟨v1, [4, 1, 3]⟩ := MStep.inc2 (r := [2, 1, 3]) e1 rfl
          have s3 : MStep ⟨v1, [4, 1, 3]⟩ ⟨LD.dB :: v1, [3]⟩ := MStep.a41 (r := [4, 1, 3]) rfl rfl
          have s4 : MStep ⟨LD.dB :: v1, [3]⟩ ⟨LD.dA :: v2, [2]⟩ :=
            MStep.inc3 (r := [3]) (Inc.dB e2) rfl
          have s5 : MStep ⟨LD.dA :: v2, [2]⟩ ⟨LD.dB :: v', [4]⟩ :=
            MStep.inc2 (r := [2]) (Inc.dA e3 e4) rfl
          have s6 : MStep ⟨LD.dB :: v', [4]⟩ ⟨LD.dA :: LD.dB :: v', []⟩ :=
            MStep.a40 (r := [4]) rfl rfl
          exact (((((MSteps.single s1).tail s2).tail s3).tail s4).tail s5).tail s6

/-! ## The normal phase -/

/-- The normal phase: spend the counter one increment at a time, pushing a
radix-3/2 digit `03` per cycle, until it overflows; then release its digits as
the blocks of the next reset phase. -/
def normalF (w : List LD) (acc : List Sym) : Option (List Sym) :=
  match h : addT w 1 with
  | some w' => normalF (.dB :: w') acc
  | none => ovfF w acc
  termination_by gap w
  decreasing_by exact gap_normal_cycle_lt (addT_one_inc h) (addT_one_inc h).gap_pos

/-- **`normalF` computes the normal phase.** -/
theorem normalF_spec : ∀ {w : List LD} {acc L : List Sym}, normalF w acc = some L →
    ∃ L0, L = L0 ++ acc ∧ (∀ x ∈ L0, Label x) ∧
      MSteps ⟨w, []⟩ ⟨[], 4 :: 4 :: (cellsOf L0 ++ [1])⟩
  | w, acc, L, h => by
      rw [normalF] at h
      cases hone : addT w 1 with
      | none =>
          rw [hone] at h
          simp only at h
          obtain ⟨L0, hL, hlab, hovf⟩ := ovfF_spec h
          exact ⟨L0, hL, hlab, normal_overflow hovf⟩
      | some w' =>
          rw [hone] at h
          simp only at h
          have hinc : Inc w w' := addT_one_inc hone
          have hlt : gap (LD.dB :: w') < gap w := gap_normal_cycle_lt hinc hinc.gap_pos
          obtain ⟨L0, hL, hlab, hsteps⟩ := normalF_spec h
          exact ⟨L0, hL, hlab, (normal_cycle hinc).trans hsteps⟩
  termination_by w => gap w

/-! ## One revolution -/

/-- One super-cycle, as a function on block sequences. -/
def revolutionF (L : List Sym) : Option (List Sym) :=
  (resetF [.d0] L).bind (fun w => (junctionF w).bind (fun w' => normalF w' []))

/-- **`revolutionF` computes the super-cycle.** -/
theorem revolutionF_spec {L L' : List Sym} (h : revolutionF L = some L') :
    (∀ x ∈ L', Label x) ∧ MPlus (phaseStart L) (phaseStart L') := by
  rw [revolutionF] at h
  cases hreset : resetF [LD.d0] L with
  | none => rw [hreset] at h; simp at h
  | some w =>
      rw [hreset] at h
      simp only [Option.bind_some] at h
      cases hjunc : junctionF w with
      | none => rw [hjunc] at h; simp at h
      | some w' =>
          rw [hjunc] at h
          simp only [Option.bind_some] at h
          obtain ⟨L0, hL, hlab, hnormal⟩ := normalF_spec h
          rw [List.append_nil] at hL
          subst hL
          refine ⟨hlab, ?_⟩
          have hfirst : MStep (phaseStart L) ⟨[LD.d0], cellsOf L ++ [1]⟩ :=
            MStep.a44 (r := 4 :: 4 :: (cellsOf L ++ [1])) rfl rfl
          exact ⟨_, hfirst, ((resetF_spec hreset [1]).trans (junctionF_spec hjunc)).trans
            hnormal⟩

/-! ## Iterating the revolution -/

/-- The block sequences of the successive reset phases, starting with the one
released by the machine's first overflow. -/
def revIter : Nat → Option (List Sym)
  | 0 => some firstBlocks
  | n + 1 => (revIter n).bind revolutionF

/-- **The machine reaches the start of the `n`-th reset phase** whenever the
computation of the block sequences gets that far. -/
theorem revIter_reaches : ∀ {n : Nat} {L : List Sym}, revIter n = some L →
    init ⟶* enc (phaseStart L)
  | 0, L, h => by
      rw [revIter] at h
      cases h
      exact reaches_of_run run_init_306
  | n + 1, L, h => by
      rw [revIter] at h
      cases hprev : revIter n with
      | none => rw [hprev] at h; simp at h
      | some L0 =>
          rw [hprev] at h
          simp only [Option.bind_some] at h
          obtain ⟨_, hplus⟩ := revolutionF_spec h
          exact (revIter_reaches hprev).trans hplus.sim.reaches

/-- Every sequence in the iteration consists of blocks `44|04|24|14`. -/
theorem revIter_labels : ∀ {n : Nat} {L : List Sym}, revIter n = some L → ∀ x ∈ L, Label x
  | 0, L, h => by
      rw [revIter] at h
      cases h
      exact firstBlocks_labels
  | n + 1, L, h => by
      rw [revIter] at h
      cases hprev : revIter n with
      | none => rw [hprev] at h; simp at h
      | some L0 =>
          rw [hprev] at h
          simp only [Option.bind_some] at h
          exact (revolutionF_spec h).1

end SOC
