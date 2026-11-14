module

public import RequestProject.Levels
public import HaltEngine

/-!
# Correctness of the engine, part 1: letters, states and a single cell step

We relate the byte-level encodings used by `HaltEngine` to the cell transducer
`BCM.cell1`: letters are bits (`false` = `A`, `true` = `B`), cell states are
bytes `2 * c + f`.
-/

@[expose] public section

namespace BCM.Eng

open HaltEngine

/-- Letter of a bit. -/
def ofB : Bool → St
  | false => .A
  | true => .B

/-- Bit of a letter. -/
def toB : St → Bool
  | .A => false
  | .B => true

@[simp] theorem ofB_toB (s : St) : ofB (toB s) = s := by cases s <;> rfl

/-- Decode a byte-encoded cell state. -/
def dec (st : UInt8) : Sym × Bool := (Fin.ofNat 5 (st.toNat / 2), st.toNat % 2 == 1)

/-- Encode a cell state. -/
def enc (c : Sym) (f : Bool) : UInt8 := UInt8.ofNat (2 * c.val + f.toNat)

/-- The bits `0, …, n-1` of `v`. -/
def natBits (v n : Nat) : List Bool := (List.range n).map v.testBit

@[simp] theorem natBits_length (v n : Nat) : (natBits v n).length = n := by simp [natBits]

theorem natBits_zero (v : Nat) : natBits v 0 = [] := rfl

theorem natBits_add (v a b : Nat) : natBits v (a + b) = natBits v a ++ natBits (v >>> a) b := by
  simp only [natBits, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [Nat.testBit_shiftRight]

theorem natBits_or_shift (acc o al c : Nat) (h : acc < 2 ^ al) :
    natBits (acc ||| (o <<< al)) (al + c) = natBits acc al ++ natBits o c := by
  rw [natBits_add]
  congr 1
  · simp only [natBits]
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.not_le.mpr hj]
  · simp only [natBits]
    apply List.map_congr_left
    intro j _
    have h1 : acc.testBit (al + j) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, h1]

theorem natBits_mod (v n m : Nat) (h : n ≤ m) : natBits (v % 2 ^ m) n = natBits v n := by
  simp only [natBits]
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  simp [Nat.testBit_mod_two_pow]
  omega

/-- A single step of `cstep` agrees with `cell1`. -/
def StepOK (st : UInt8) (x : Bool) : Prop :=
  match cell1 (dec st).1 (dec st).2 (ofB x) with
  | none => (cstep st x).1 = 255
  | some (c', f', o) => (cstep st x).1 = enc c' f' ∧ (cstep st x).2.1 = o.length ∧
      natBits (cstep st x).2.2 o.length = o.map toB ∧ (cstep st x).2.2 < 2 ^ o.length

instance (st : UInt8) (x : Bool) : Decidable (StepOK st x) := by
  unfold StepOK
  split <;> infer_instance

theorem stepOK_all : ∀ st : Fin 10, ∀ x : Bool, StepOK (UInt8.ofNat st.val) x := by decide

theorem stepOK (st : UInt8) (h : st.toNat < 10) (x : Bool) : StepOK st x := by
  have := stepOK_all ⟨st.toNat, h⟩ x
  simpa using this

theorem enc_lt (c : Sym) (f : Bool) : (enc c f).toNat < 10 := by
  revert c f; decide

theorem dec_enc (c : Sym) (f : Bool) : dec (enc c f) = (c, f) := by
  revert c f; decide

theorem natBits_add_mul (v1 v2 c1 c2 : Nat) (h : v1 < 2 ^ c1) :
    natBits (v1 + v2 * 2 ^ c1) (c1 + c2) = natBits v1 c1 ++ natBits v2 c2 := by
  rw [natBits_add, ← natBits_mod _ c1 c1 (Nat.le_refl _), Nat.shiftRight_eq_div_pow]
  have h2 : 0 < 2 ^ c1 := Nat.two_pow_pos c1
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h, Nat.add_mul_div_right _ _ h2,
    Nat.div_eq_of_lt h, Nat.zero_add]

theorem add_mul_lt (v1 v2 c1 c2 : Nat) (h1 : v1 < 2 ^ c1) (h2 : v2 < 2 ^ c2) :
    v1 + v2 * 2 ^ c1 < 2 ^ (c1 + c2) := by
  rw [Nat.pow_add]
  have : v2 * 2 ^ c1 + 2 ^ c1 ≤ 2 ^ c1 * 2 ^ c2 := by
    rw [Nat.mul_comm (2 ^ c1)]
    have := Nat.mul_le_mul_right (2 ^ c1) (Nat.succ_le_of_lt h2)
    rw [Nat.succ_mul] at this
    exact this
  omega

theorem enc_dec_all : ∀ st : Fin 10, enc (dec (UInt8.ofNat st.val)).1 (dec (UInt8.ofNat st.val)).2 = UInt8.ofNat st.val := by decide

theorem enc_dec (st : UInt8) (h : st.toNat < 10) : enc (dec st).1 (dec st).2 = st := by
  have := enc_dec_all ⟨st.toNat, h⟩
  simpa using this

/-- The final state byte for a cell run. -/
def endByte (s : Sym × Bool) (w : List St) : UInt8 :=
  match cellEnd s.1 s.2 w with
  | none => 255
  | some (c, f) => enc c f

theorem crun_spec (xs : List Bool) : ∀ (st : UInt8), st.toNat < 10 →
    (crun st xs).1 = endByte (dec st) (xs.map ofB) ∧
    (crun st xs).2.1 = (cellOut (dec st).1 (dec st).2 (xs.map ofB)).length ∧
    natBits (crun st xs).2.2 (crun st xs).2.1 = (cellOut (dec st).1 (dec st).2 (xs.map ofB)).map toB ∧
    (crun st xs).2.2 < 2 ^ (crun st xs).2.1 := by
  induction xs with
  | nil =>
    intro st h
    simp only [crun, endByte, cellEnd, cellOut, List.map_nil, List.length_nil, natBits_zero,
      Nat.pow_zero, true_and]
    refine ⟨(enc_dec st h).symm, by decide⟩
  | cons x xs ih =>
    intro st h
    have hs := stepOK st h x
    unfold StepOK at hs
    simp only [crun, List.map_cons, endByte, cellEnd, cellOut]
    split at hs
    next hc =>
      rw [hc]; simp [hs, natBits_zero]
    next c' f' o hc =>
      rw [hc]
      obtain ⟨h1, h2, h3, h4⟩ := hs
      have hne : (cstep st x).1 ≠ 255 := by
        rw [h1]; intro e; have := enc_lt c' f'; rw [e] at this; simp at this
      obtain ⟨i1, i2, i3, i4⟩ := ih (enc c' f') (enc_lt c' f')
      rw [dec_enc] at i1 i2 i3
      simp only [h1, beq_iff_eq]
      have hne' : enc c' f' ≠ 255 := by rw [← h1]; exact hne
      rw [if_neg hne']
      refine ⟨i1, ?_, ?_, ?_⟩
      · simp only [List.length_append, h2, i2]
      · simp only [h2, List.map_append]
        rw [natBits_add_mul _ _ _ _ h4, h3, i3]
      · simp only [h2]
        exact add_mul_lt _ _ _ _ h4 i4

end BCM.Eng
