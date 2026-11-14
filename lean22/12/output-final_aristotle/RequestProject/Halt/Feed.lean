module

public import RequestProject.Halt.Acc

/-!
# Correctness of the engine, part 3: feeding a cell

`feed_spec`: feeding the letters `rd inp i n` to a cell in byte-encoded state
`st` does exactly what `cellEnd`/`cellOut` prescribe (`FeedOK`); on a halt the
engine's `quiet` flag guarantees that nothing was emitted.
-/

@[expose] public section

namespace TM5.Eng

open HaltEngine

/-- Specification of the outcome `r` of feeding the word `w` to a cell in state
`s`, with output accumulator `a`. -/
def FeedOK (s : Sym × Bool) (w : List St) (a : Acc) : FR → Prop
  | .ok st' a' => st'.toNat < 10 ∧ cellEnd s.1 s.2 w = some (dec st') ∧ AccValid a' ∧
      accBits a' = accBits a ++ (cellOut s.1 s.2 w).map toB
  | .halt q => cellEnd s.1 s.2 w = none ∧ (q = true → accBits a = [] ∧ cellOut s.1 s.2 w = [])

theorem cellEnd_append_none (xs ys : List St) : ∀ c f, cellEnd c f xs = none →
    cellEnd c f (xs ++ ys) = none := by
  induction xs with
  | nil => intro c f h; cases h
  | cons x xs ih =>
    intro c f h
    simp only [cellEnd, List.cons_append] at h ⊢
    cases hc : cell1 c f x with
    | none => rfl
    | some v =>
      obtain ⟨c1, f1, o⟩ := v
      rw [hc] at h
      exact ih c1 f1 h

theorem cellOut_append_none (xs ys : List St) : ∀ c f, cellEnd c f xs = none →
    cellOut c f (xs ++ ys) = cellOut c f xs := by
  induction xs with
  | nil => intro c f h; cases h
  | cons x xs ih =>
    intro c f h
    simp only [cellEnd, cellOut, List.cons_append] at h ⊢
    cases hc : cell1 c f x with
    | none => rfl
    | some v =>
      obtain ⟨c1, f1, o⟩ := v
      rw [hc] at h
      simp only
      rw [ih c1 f1 h]

/-- Number of letters emitted by one cell step. -/
def outLen (c : Sym) (f : Bool) (x : St) : Nat :=
  match cell1 c f x with
  | none => 0
  | some (_, _, o) => o.length

theorem outLen_le_aux : ∀ (c : Sym) (f : Bool) (x : Bool), outLen c f (ofB x) ≤ 3 := by decide

theorem outLen_le (c : Sym) (f : Bool) (x : St) : outLen c f x ≤ 3 := by
  have := outLen_le_aux c f (toB x)
  rwa [ofB_toB] at this

theorem cellOut_length_le (w : List St) : ∀ c f, (cellOut c f w).length ≤ 3 * w.length := by
  induction w with
  | nil => intro c f; simp [cellOut]
  | cons x w ih =>
    intro c f
    have h := outLen_le c f x
    simp only [cellOut]
    split
    · simp
    · next c' f' o hc =>
      simp only [outLen, hc] at h
      simp only [List.length_append, List.length_cons]
      have := ih c' f'
      omega

theorem FeedOK_append {s : Sym × Bool} {u v : List St} {a a' : Acc} {s1 : Sym × Bool}
    (hu : cellEnd s.1 s.2 u = some s1) (ha : accBits a' = accBits a ++ (cellOut s.1 s.2 u).map toB)
    {r : FR} (hr : FeedOK s1 v a' r) : FeedOK s (u ++ v) a r := by
  have e1 := cellEnd_append u v s.1 s.2 s1.1 s1.2 hu
  have e2 := cellOut_append_of_end u v s.1 s.2 s1.1 s1.2 hu
  cases r with
  | ok st' a'' =>
    obtain ⟨h1, h2, h3, h4⟩ := hr
    refine ⟨h1, by rw [e1]; exact h2, h3, ?_⟩
    rw [h4, ha, e2, List.map_append, List.append_assoc]
  | halt q =>
    obtain ⟨h1, h2⟩ := hr
    refine ⟨by rw [e1]; exact h1, fun hq => ?_⟩
    obtain ⟨h3, h4⟩ := h2 hq
    rw [ha] at h3
    have h5 := List.append_eq_nil_iff.mp h3
    have h6 : cellOut s.1 s.2 u = [] := List.map_eq_nil_iff.mp h5.2
    exact ⟨h5.1, by rw [e2, h6, h4]; rfl⟩

theorem FeedOK_halt {s : Sym × Bool} {u v : List St} {a : Acc} {q : Bool}
    (hu : cellEnd s.1 s.2 u = none) (hq : q = true → accBits a = [] ∧ cellOut s.1 s.2 u = []) :
    FeedOK s (u ++ v) a (.halt q) :=
  ⟨cellEnd_append_none u v _ _ hu, fun h => by
    rw [cellOut_append_none u v _ _ hu]; exact hq h⟩

theorem FeedOK_nil (st : UInt8) (a : Acc) (h : st.toNat < 10) (ha : AccValid a) :
    FeedOK (dec st) [] a (.ok st a) :=
  ⟨h, rfl, ha, by simp [cellOut]⟩

theorem accBits_empty (a : Acc) (h1 : a.out.size = 0) (h2 : a.al = 0) : accBits a = [] := by
  simp [accBits, h1, h2, rdBytes, natBits_zero]

/-! ## Tables -/

theorem entry_eq (st b : UInt8) :
    entry (st.toNat * 256 + b.toNat) = crun st (byteBits b) := by
  have hb := b.toNat_lt
  unfold entry
  have e1 : (st.toNat * 256 + b.toNat) / 256 = st.toNat := by omega
  have e2 : (st.toNat * 256 + b.toNat) % 256 = b.toNat := by omega
  rw [e1, e2]
  simp

theorem crun_cnt_le (st : UInt8) (h : st.toNat < 10) (b : UInt8) :
    (crun st (byteBits b)).2.1 ≤ 24 := by
  rw [(crun_spec _ st h).2.1]
  have := cellOut_length_le ((byteBits b).map ofB) (dec st).1 (dec st).2
  rw [List.length_map, show (byteBits b).length = 8 by simp [byteBits]] at this
  omega

theorem nsT_get (k : Nat) (hk : k < 2560) : nsT.get! k = (entry k).1 := by
  show ((Array.range 2560).map (fun k => (entry k).1))[k]! = _
  rw [getElem!_pos _ k (by simp; omega)]
  simp

theorem cntT_get (k : Nat) (hk : k < 2560) : cntT.get! k = UInt8.ofNat (entry k).2.1 := by
  show ((Array.range 2560).map (fun k => UInt8.ofNat (entry k).2.1))[k]! = _
  rw [getElem!_pos _ k (by simp; omega)]
  simp

theorem outT_get (k : Nat) (hk : k < 2560) : outT[k]! = UInt32.ofNat (entry k).2.2 := by
  show ((Array.range 2560).map (fun k => UInt32.ofNat (entry k).2.2))[k]! = _
  rw [getElem!_pos _ k (by simp; omega)]
  simp


theorem endByte_255 {s : Sym × Bool} {w : List St} (h : endByte s w = 255) :
    cellEnd s.1 s.2 w = none := by
  unfold endByte at h
  split at h
  · assumption
  · next c f _ => have := enc_lt c f; rw [h] at this; simp at this

theorem endByte_ne {s : Sym × Bool} {w : List St} (h : endByte s w ≠ 255) :
    cellEnd s.1 s.2 w = some (dec (endByte s w)) := by
  unfold endByte at h ⊢
  split
  · next he => rw [he] at h; exact absurd rfl h
  · next c f he => rw [dec_enc]; exact he

theorem endByte_lt {s : Sym × Bool} {w : List St} (h : endByte s w ≠ 255) :
    (endByte s w).toNat < 10 := by
  unfold endByte at h ⊢
  split
  · next he => rw [he] at h; exact absurd rfl h
  · exact enc_lt _ _

theorem feedBytes_spec (inp : ByteArray) : ∀ nb i st a, st.toNat < 10 → AccValid a →
    FeedOK (dec st) ((rdBytes inp i nb).map ofB) a (feedBytes inp i st a nb) := by
  intro nb
  induction nb with
  | zero => intro i st a hst ha; exact FeedOK_nil st a hst ha
  | succ nb ih =>
    intro i st a hst ha
    simp only [feedBytes, rdBytes, List.map_append]
    generalize inp.get! i = b
    have hb := b.toNat_lt
    have hk : st.toNat * 256 + b.toNat < 2560 := by omega
    obtain ⟨c1, c2, c3, c4⟩ := crun_spec (byteBits b) st hst
    have hle := crun_cnt_le st hst b
    rw [nsT_get _ hk, entry_eq, c1]
    split
    · next h255 =>
      apply FeedOK_halt (endByte_255 (by simpa using h255))
      intro hq
      simp only [Bool.and_eq_true, beq_iff_eq] at hq
      obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hq
      refine ⟨accBits_empty a hq1 hq2, ?_⟩
      rw [c2] at hq3
      exact List.eq_nil_of_length_eq_zero hq3
    · next h255 =>
      have hne : endByte (dec st) ((byteBits b).map ofB) ≠ 255 := by simpa using h255
      have hcnt : (cntT.get! (st.toNat * 256 + b.toNat)).toNat = (crun st (byteBits b)).2.1 := by
        rw [cntT_get _ hk, entry_eq]; simp; omega
      have hout : (outT[st.toNat * 256 + b.toNat]!).toUInt64.toNat = (crun st (byteBits b)).2.2 := by
        rw [outT_get _ hk, entry_eq]
        have : (crun st (byteBits b)).2.2 < 2 ^ 32 :=
          Nat.lt_of_lt_of_le c4 (Nat.pow_le_pow_right (by omega) (by omega))
        simp; omega
      rw [hcnt]
      have hadd := add_spec a (crun st (byteBits b)).2.1
        (outT[st.toNat * 256 + b.toNat]!).toUInt64 ha hle (by rw [hout]; exact c4)
      rw [hout, c3] at hadd
      refine FeedOK_append (endByte_ne hne) hadd.2 ?_
      exact ih (i + 1) _ _ (endByte_lt hne) hadd.1


theorem feedBits_spec : ∀ (xs : List Bool) (st : UInt8) (a : Acc), st.toNat < 10 → AccValid a →
    FeedOK (dec st) (xs.map ofB) a (feedBits st a xs) := by
  intro xs
  induction xs with
  | nil => intro st a hst ha; exact FeedOK_nil st a hst ha
  | cons x xs ih =>
    intro st a hst ha
    have hs := stepOK st hst x
    unfold StepOK at hs
    simp only [feedBits, List.map_cons]
    rw [show ofB x :: xs.map ofB = [ofB x] ++ xs.map ofB from rfl]
    split at hs
    · next hc =>
      rw [hs]
      simp only [beq_self_eq_true, if_true]
      apply FeedOK_halt (by simp [cellEnd, hc])
      intro hq
      simp only [Bool.and_eq_true, beq_iff_eq] at hq
      exact ⟨accBits_empty a hq.1 hq.2, by simp [cellOut, hc]⟩
    · next c' f' o hc =>
      obtain ⟨h1, h2, h3, h4⟩ := hs
      have hne : (cstep st x).1 ≠ 255 := by
        rw [h1]; intro e; have := enc_lt c' f'; rw [e] at this; simp at this
      have hlen : o.length ≤ 3 := by
        have := outLen_le (dec st).1 (dec st).2 (ofB x)
        simp only [outLen, hc] at this; exact this
      have hv : (UInt64.ofNat (cstep st x).2.2).toNat = (cstep st x).2.2 := by
        have : (cstep st x).2.2 < 2 ^ 64 :=
          Nat.lt_of_lt_of_le h4 (Nat.pow_le_pow_right (by omega) (by omega))
        simp; omega
      simp only [hne, beq_iff_eq, if_false]
      rw [h2]
      have hadd := add_spec a o.length (UInt64.ofNat (cstep st x).2.2) ha (by omega)
        (by rw [hv]; exact h4)
      rw [hv, h3] at hadd
      have hu : cellEnd (dec st).1 (dec st).2 [ofB x] = some (c', f') := by simp [cellEnd, hc]
      have hu' : cellOut (dec st).1 (dec st).2 [ofB x] = o := by simp [cellOut, hc]
      refine FeedOK_append hu (by rw [hu']; exact hadd.2) ?_
      have := ih (cstep st x).1 _ (by rw [h1]; exact enc_lt _ _) hadd.1
      rw [h1, dec_enc] at this
      rw [h1]
      exact this

theorem feed_spec (inp : ByteArray) (i n : Nat) (st : UInt8) (a : Acc) (hst : st.toNat < 10)
    (ha : AccValid a) : FeedOK (dec st) ((rd inp i n).map ofB) a (feed inp i n st a) := by
  have hb := feedBytes_spec inp (n / 8) i st a hst ha
  unfold feed rd
  rw [List.map_append]
  revert hb
  cases feedBytes inp i st a (n / 8) with
  | ok st' a' =>
    intro hb
    obtain ⟨h1, h2, h3, h4⟩ := hb
    simp only
    by_cases h8 : n % 8 = 0
    · simp only [h8, beq_self_eq_true, if_true, List.map_nil]
      refine FeedOK_append h2 h4 ?_
      exact FeedOK_nil st' a' h1 h3
    · have h8' : (n % 8 == 0) = false := by simpa using h8
      simp only [h8', h8, if_false, Bool.false_eq_true]
      exact FeedOK_append h2 h4 (feedBits_spec _ st' a' h1 h3)
  | halt q =>
    intro hb
    exact FeedOK_halt hb.1 hb.2


theorem fresh_spec (cap : Nat) : AccValid (Acc.fresh cap) ∧ accBits (Acc.fresh cap) = [] := by
  refine ⟨⟨by simp [Acc.fresh], by simp [Acc.fresh]⟩, ?_⟩
  exact accBits_empty _ rfl rfl

theorem close_spec (a : Acc) (ha : AccValid a) : rd a.close.1 0 a.close.2 = accBits a := by
  obtain ⟨h1, h2⟩ := ha
  unfold Acc.close rd accBits
  by_cases h0 : a.al = 0
  · simp only [h0, beq_self_eq_true, if_true, natBits_zero, List.append_nil]
    rw [show 8 * a.out.size / 8 = a.out.size by omega, show 8 * a.out.size % 8 = 0 by omega]
    simp
  · have h0' : (a.al == 0) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, if_false]
    rw [show (8 * a.out.size + a.al) / 8 = a.out.size by omega,
      show (8 * a.out.size + a.al) % 8 = a.al by omega, if_neg h0, Nat.zero_add, get!_push_eq,
      rdBytes_congr a.out.size 0 (a' := a.out) (fun j _ h => get!_push_lt _ _ j (by omega))]
    congr 1
    rw [byteBits_u64, show 8 = a.al + (8 - a.al) by omega, natBits_add,
      List.take_left' (by simp)]

end TM5.Eng
