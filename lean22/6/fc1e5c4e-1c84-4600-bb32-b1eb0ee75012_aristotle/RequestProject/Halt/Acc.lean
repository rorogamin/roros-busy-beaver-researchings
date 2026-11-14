module

public import RequestProject.Halt.Basic

/-!
# Correctness of the engine, part 2: bit streams and the output accumulator

`rd a i n` is the list of the first `n` letters (bits) stored in the byte array
`a` from byte `i` on, as the engine reads them; `accBits` is the content of an
output accumulator.  `add_spec` shows that appending bits to an accumulator does
what it should.
-/

@[expose] public section

namespace BCM.Eng

open HaltEngine

def rdBytes (a : ByteArray) : Nat → Nat → List Bool
  | _, 0 => []
  | i, n + 1 => byteBits (a.get! i) ++ rdBytes a (i + 1) n

def rd (a : ByteArray) (i n : Nat) : List Bool :=
  rdBytes a i (n / 8) ++ (if n % 8 = 0 then [] else (byteBits (a.get! (i + n / 8))).take (n % 8))

def AccValid (a : Acc) : Prop := a.al < 8 ∧ a.acc.toNat < 2 ^ a.al

def accBits (a : Acc) : List Bool := rdBytes a.out 0 a.out.size ++ natBits a.acc.toNat a.al

theorem byteBits_eq (b : UInt8) : byteBits b = natBits b.toNat 8 := rfl

theorem rdBytes_congr {a a' : ByteArray} : ∀ n i, (∀ j, i ≤ j → j < i + n → a.get! j = a'.get! j) →
    rdBytes a i n = rdBytes a' i n
  | 0, _, _ => rfl
  | n + 1, i, h => by
    simp only [rdBytes]
    rw [h i (Nat.le_refl _) (by omega), rdBytes_congr n (i + 1) (fun j h1 h2 => h j (by omega) (by omega))]

theorem rdBytes_succ_right (a : ByteArray) : ∀ n i,
    rdBytes a i (n + 1) = rdBytes a i n ++ byteBits (a.get! (i + n))
  | 0, i => by simp [rdBytes]
  | n + 1, i => by
    rw [rdBytes, rdBytes_succ_right a n (i + 1), rdBytes, List.append_assoc,
      show i + 1 + n = i + (n + 1) by omega]

theorem rdBytes_add (a : ByteArray) : ∀ m n i,
    rdBytes a i (m + n) = rdBytes a i m ++ rdBytes a (i + m) n
  | 0, n, i => by simp [rdBytes]
  | m + 1, n, i => by
    rw [show m + 1 + n = (m + n) + 1 by omega, rdBytes, rdBytes, rdBytes_add a m n (i + 1),
      List.append_assoc, show i + 1 + m = i + (m + 1) by omega]

@[simp] theorem size_push (a : ByteArray) (b : UInt8) : (a.push b).size = a.size + 1 :=
  Array.size_push _

theorem get!_push_lt (a : ByteArray) (b : UInt8) (j : Nat) (h : j < a.size) :
    (a.push b).get! j = a.get! j := by
  show (a.data.push b)[j]! = a.data[j]!
  have h' : j < a.data.size := h
  have h2 : j < (a.data.push b).size := by rw [Array.size_push]; omega
  rw [getElem!_pos (a.data.push b) j h2, getElem!_pos a.data j h',
    Array.getElem_push_lt]

theorem get!_push_eq (a : ByteArray) (b : UInt8) : (a.push b).get! a.size = b := by
  show (a.data.push b)[a.data.size]! = b
  have h2 : a.data.size < (a.data.push b).size := by rw [Array.size_push]; omega
  rw [getElem!_pos (a.data.push b) a.data.size h2, Array.getElem_push_eq]

theorem rdBytes_push (a : ByteArray) (b : UInt8) :
    rdBytes (a.push b) 0 (a.size + 1) = rdBytes a 0 a.size ++ byteBits b := by
  rw [rdBytes_succ_right, Nat.zero_add, get!_push_eq]
  congr 1
  exact rdBytes_congr _ _ (fun j _ h2 => get!_push_lt a b j (by omega))


theorem byteBits_u64 (A : UInt64) : byteBits A.toUInt8 = natBits A.toNat 8 := by
  rw [byteBits_eq, UInt64.toNat_toUInt8]
  exact natBits_mod _ _ 8 (Nat.le_refl _)

theorem natBits_split8 (v m : Nat) : natBits v (8 + m) = natBits v 8 ++ natBits (v >>> 8) m :=
  natBits_add v 8 m

theorem add_spec (a : Acc) (c : Nat) (o : UInt64) (ha : AccValid a) (hc : c ≤ 24)
    (ho : o.toNat < 2 ^ c) :
    AccValid (a.add c o) ∧ accBits (a.add c o) = accBits a ++ natBits o.toNat c := by
  obtain ⟨h1, h2⟩ := ha
  have hsh : o.toNat <<< a.al < 2 ^ (a.al + c) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm (2 ^ a.al)]
    exact Nat.mul_lt_mul_of_pos_right ho (Nat.two_pow_pos _)
  have hA : (a.acc ||| (o <<< a.al.toUInt64)).toNat = a.acc.toNat ||| (o.toNat <<< a.al) := by
    have e1 : a.al.toUInt64.toNat % 64 = a.al := by simp; omega
    have e2 : 2 ^ (a.al + c) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, e1, Nat.mod_eq_of_lt (by omega)]
  have hAb : (a.acc ||| (o <<< a.al.toUInt64)).toNat < 2 ^ (a.al + c) := by
    rw [hA]
    exact Nat.or_lt_two_pow (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega))) hsh
  have hbits : natBits (a.acc ||| (o <<< a.al.toUInt64)).toNat (a.al + c) =
      natBits a.acc.toNat a.al ++ natBits o.toNat c := by
    rw [hA]; exact natBits_or_shift _ _ _ _ h2
  unfold Acc.add
  simp only [accBits, AccValid]
  generalize a.acc ||| (o <<< a.al.toUInt64) = A at hA hAb hbits ⊢
  have hdiv : ∀ k, A.toNat >>> k < 2 ^ (a.al + c - k) := by
    intro k
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hAb (Nat.pow_le_pow_right (by omega) (by omega))
  have t8 : (A >>> 8).toNat = A.toNat >>> 8 := by simp
  have t16 : (A >>> 16).toNat = A.toNat >>> 8 >>> 8 := by
    simp; rw [show (16 : Nat) = 8 + 8 from rfl, Nat.shiftRight_add]
  have t24 : (A >>> 24).toNat = A.toNat >>> 8 >>> 8 >>> 8 := by
    simp; rw [show (24 : Nat) = 8 + 8 + 8 from rfl, Nat.shiftRight_add, Nat.shiftRight_add]
  split
  · refine ⟨⟨by dsimp only; omega, hAb⟩, ?_⟩
    rw [hbits, List.append_assoc]
  split
  · refine ⟨⟨by dsimp only; omega, t8 ▸ hdiv 8⟩, ?_⟩
    rw [size_push, rdBytes_push, byteBits_u64, t8, List.append_assoc, List.append_assoc, ← hbits,
      show a.al + c = 8 + (a.al + c - 8) by omega, natBits_split8]
    simp only [Nat.add_sub_cancel_left]
  split
  · refine ⟨⟨by dsimp only; omega, ?_⟩, ?_⟩
    · rw [t16, ← Nat.shiftRight_add]; exact hdiv 16
    dsimp only
    rw [size_push, rdBytes_push, size_push, rdBytes_push, byteBits_u64, byteBits_u64, t8, t16,
      List.append_assoc, List.append_assoc, List.append_assoc, ← hbits,
      show a.al + c = 8 + (8 + (a.al + c - 16)) by omega, natBits_split8, natBits_split8]
    rw [show 8 + (8 + (a.al + c - 16)) - 16 = a.al + c - 16 by omega]
  · refine ⟨⟨by dsimp only; omega, ?_⟩, ?_⟩
    · rw [t24, ← Nat.shiftRight_add, ← Nat.shiftRight_add]; exact hdiv 24
    dsimp only
    rw [size_push, rdBytes_push, size_push, rdBytes_push, size_push, rdBytes_push, byteBits_u64,
      byteBits_u64, byteBits_u64, t8, t16, t24,
      List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, ← hbits,
      show a.al + c = 8 + (8 + (8 + (a.al + c - 24))) by omega, natBits_split8, natBits_split8,
      natBits_split8]
    rw [show 8 + (8 + (8 + (a.al + c - 24))) - 24 = a.al + c - 24 by omega]

end BCM.Eng
