/-
# The decoder of a counter stack and the prefix invariant

The left stack of the machine is the project's nearest-first list of blocks
`X = 11` (bit `0`), `Z = 01` (bit `1`) and `W = 03` (a pop), over the bottom
block `L = ^11`.  Writing it *bottom first* — which is the order in which the
overflow deposits it on the tape — a **bottom prefix** of the stack is exactly
a suffix of the nearest-first list.

`pdec s` is the word of digit blocks the stack decodes to: every bit block
deposits `Y`, and a pop deposits `V` or `X` according to the bit it pops (the
parity of the counter below it).  When the counter is exhausted this is
literally the word the overflow deposits (`ofw_eq_pdec`).

`bval s` is the value of that word under the reset arithmetic of `Word.lean`,
and the invariant of the whole development is

```
  Good s :  cval t ≤ bval t   for every bottom prefix t of s
```

together with admissibility `Adm s` (every bottom prefix has at least as many
bit blocks as pops).
-/
import RequestProject.BB25.Prefix.Word
import RequestProject.BB25.Runs

namespace BB25.Prefix

open BB25

/-! ## The decoder -/

/-- The word of digit blocks a counter stack decodes to, in tape order. -/
def pdec : List LB → List RB
  | [] => []
  | .X :: s => pdec s ++ [.Y]
  | .Z :: s => pdec s ++ [.Y]
  | .W :: s => pdec s ++ [if cval s % 2 = 1 then .V else .X]
  | _ :: _ => []

@[simp] theorem pdec_nil : pdec [] = [] := rfl
@[simp] theorem pdec_L (s : List LB) : pdec (.L :: s) = [] := rfl
@[simp] theorem pdec_X (s : List LB) : pdec (.X :: s) = pdec s ++ [.Y] := rfl
@[simp] theorem pdec_Z (s : List LB) : pdec (.Z :: s) = pdec s ++ [.Y] := rfl
@[simp] theorem pdec_W (s : List LB) :
    pdec (.W :: s) = pdec s ++ [if cval s % 2 = 1 then .V else .X] := rfl

theorem pdec_digs (s : List LB) : Digs (pdec s) := by
  induction s with
  | nil => exact Digs.nil
  | cons b s ih =>
      cases b with
      | X => exact ih.append (fun c hc => by simp at hc; subst hc; exact Or.inl rfl)
      | Z => exact ih.append (fun c hc => by simp at hc; subst hc; exact Or.inl rfl)
      | W =>
          refine ih.append (fun c hc => ?_)
          simp only [List.mem_singleton] at hc
          subst hc
          by_cases h : cval s % 2 = 1 <;> simp [h, Dig]
      | _ => exact Digs.nil

/-- The decoded value of a stack: the reset value of the word it decodes to. -/
def bval : List LB → ℤ
  | [] => 0
  | .X :: s => 2 * bval s + 1
  | .Z :: s => 2 * bval s + 1
  | .W :: s => if cval s % 2 = 1 then 2 * bval s else bval s / 2 - 1
  | _ :: _ => 0

@[simp] theorem bval_nil : bval [] = 0 := rfl
@[simp] theorem bval_L (s : List LB) : bval (.L :: s) = 0 := rfl
@[simp] theorem bval_X (s : List LB) : bval (.X :: s) = 2 * bval s + 1 := rfl
@[simp] theorem bval_Z (s : List LB) : bval (.Z :: s) = 2 * bval s + 1 := rfl
@[simp] theorem bval_W (s : List LB) :
    bval (.W :: s) = if cval s % 2 = 1 then 2 * bval s else bval s / 2 - 1 := rfl

/-- `bval` is the reset value of the decoded word. -/
theorem bval_eq_rrun (s : List LB) : bval s = rrun (pdec s) 0 := by
  induction s with
  | nil => rfl
  | cons b s ih =>
      cases b with
      | X => rw [pdec_X, rrun_append, ← ih]; simp
      | Z => rw [pdec_Z, rrun_append, ← ih]; simp
      | W =>
          rw [pdec_W, rrun_append, ← ih]
          by_cases h : cval s % 2 = 1 <;> simp [h]
      | _ => rfl

/-! ## Counts and admissibility -/

/-- The number of bit blocks of a stack (the bottom block `L` ends the count). -/
def nbit : List LB → ℕ
  | [] => 0
  | .X :: s => nbit s + 1
  | .Z :: s => nbit s + 1
  | .W :: s => nbit s
  | _ :: _ => 0

/-- The number of pops of a stack. -/
def nsh : List LB → ℕ
  | [] => 0
  | .X :: s => nsh s
  | .Z :: s => nsh s
  | .W :: s => nsh s + 1
  | _ :: _ => 0

@[simp] theorem nbit_nil : nbit [] = 0 := rfl
@[simp] theorem nbit_L (s : List LB) : nbit (.L :: s) = 0 := rfl
@[simp] theorem nbit_X (s : List LB) : nbit (.X :: s) = nbit s + 1 := rfl
@[simp] theorem nbit_Z (s : List LB) : nbit (.Z :: s) = nbit s + 1 := rfl
@[simp] theorem nbit_W (s : List LB) : nbit (.W :: s) = nbit s := rfl
@[simp] theorem nsh_nil : nsh [] = 0 := rfl
@[simp] theorem nsh_L (s : List LB) : nsh (.L :: s) = 0 := rfl
@[simp] theorem nsh_X (s : List LB) : nsh (.X :: s) = nsh s := rfl
@[simp] theorem nsh_Z (s : List LB) : nsh (.Z :: s) = nsh s := rfl
@[simp] theorem nsh_W (s : List LB) : nsh (.W :: s) = nsh s + 1 := rfl

theorem bal_pdec (s : List LB) : bal (pdec s) = (nbit s : ℤ) - nsh s := by
  induction s with
  | nil => simp
  | cons b s ih =>
      cases b with
      | X => rw [pdec_X, bal_append, ih]; simp; ring
      | Z => rw [pdec_Z, bal_append, ih]; simp; ring
      | W =>
          rw [pdec_W, bal_append, ih]
          by_cases h : cval s % 2 = 1 <;> simp [h] <;> ring
      | _ => simp [pdec, nbit, nsh]

/-- Admissibility: no bottom prefix pops more bits than it has. -/
def Adm (s : List LB) : Prop := ∀ t, t <:+ s → nsh t ≤ nbit t

/-- The prefix invariant. -/
def Good (s : List LB) : Prop := ∀ t, t <:+ s → (cval t : ℤ) ≤ bval t

theorem Adm.suffix {s t : List LB} (h : Adm s) (ht : t <:+ s) : Adm t :=
  fun u hu => h u (hu.trans ht)

theorem Good.suffix {s t : List LB} (h : Good s) (ht : t <:+ s) : Good t :=
  fun u hu => h u (hu.trans ht)

theorem Adm.head {s : List LB} (h : Adm s) : nsh s ≤ nbit s := h s (List.suffix_refl s)

theorem Good.head {s : List LB} (h : Good s) : (cval s : ℤ) ≤ bval s := h s (List.suffix_refl s)

theorem Adm.cons {b : LB} {s : List LB} (h : Adm s) (hb : nsh (b :: s) ≤ nbit (b :: s)) :
    Adm (b :: s) := by
  intro t ht
  rcases List.suffix_cons_iff.mp ht with rfl | ht'
  · exact hb
  · exact h t ht'

theorem Good.cons {b : LB} {s : List LB} (h : Good s) (hb : (cval (b :: s) : ℤ) ≤ bval (b :: s)) :
    Good (b :: s) := by
  intro t ht
  rcases List.suffix_cons_iff.mp ht with rfl | ht'
  · exact hb
  · exact h t ht'

/-- Every prefix of the decoded word is the decoded word of a bottom prefix. -/
theorem pdec_prefix {s : List LB} {p : List RB} (hp : p <+: pdec s) :
    ∃ t, t <:+ s ∧ p = pdec t := by
  induction s with
  | nil => exact ⟨[], List.nil_suffix, by simpa using List.prefix_nil.mp hp⟩
  | cons b s ih =>
      have hcons : ∀ t, t <:+ s → t <:+ b :: s := fun t ht => ht.trans (List.suffix_cons b s)
      cases b with
      | X =>
          rw [pdec_X] at hp
          rcases prefix_append_cases hp with h | ⟨q, rfl, hq⟩
          · obtain ⟨t, ht, rfl⟩ := ih h
            exact ⟨t, hcons t ht, rfl⟩
          · rcases prefix_singleton_cases hq with rfl | rfl
            · exact ⟨s, hcons s (List.suffix_refl s), by simp⟩
            · exact ⟨.X :: s, List.suffix_refl _, rfl⟩
      | Z =>
          rw [pdec_Z] at hp
          rcases prefix_append_cases hp with h | ⟨q, rfl, hq⟩
          · obtain ⟨t, ht, rfl⟩ := ih h
            exact ⟨t, hcons t ht, rfl⟩
          · rcases prefix_singleton_cases hq with rfl | rfl
            · exact ⟨s, hcons s (List.suffix_refl s), by simp⟩
            · exact ⟨.Z :: s, List.suffix_refl _, rfl⟩
      | W =>
          rw [pdec_W] at hp
          rcases prefix_append_cases hp with h | ⟨q, rfl, hq⟩
          · obtain ⟨t, ht, rfl⟩ := ih h
            exact ⟨t, hcons t ht, rfl⟩
          · rcases prefix_singleton_cases hq with rfl | rfl
            · exact ⟨s, hcons s (List.suffix_refl s), by simp⟩
            · exact ⟨.W :: s, List.suffix_refl _, rfl⟩
      | _ =>
          exact ⟨[], List.nil_suffix, by simpa using List.prefix_nil.mp hp⟩

/-- **The decoded word of an admissible stack is a Dyck prefix.** -/
theorem pdec_dyck {s : List LB} (h : Adm s) : DyckPre (pdec s) := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := pdec_prefix hp
  have := h t ht
  rw [bal_pdec]
  omega

/-! ## The size of the counter -/

/-- The counter is carried by the unmatched bits. -/
theorem cval_lt_two_pow {s : List LB} (hst : CStack s) (h : Adm s) :
    cval s < 2 ^ (nbit s - nsh s) := by
  induction hst with
  | base => simp
  | @consW t hst ih =>
      have hadm : Adm t := h.suffix (List.suffix_cons _ _)
      have hle : nsh t + 1 ≤ nbit t := by simpa using h.head
      have hih := ih hadm
      have h1 : nbit (.W :: t) - nsh (.W :: t) = (nbit t - nsh t) - 1 := by simp; omega
      have hk : 1 ≤ nbit t - nsh t := by omega
      rw [h1]
      have : cval t / 2 < 2 ^ (nbit t - nsh t - 1) := by
        have h2 : 2 ^ (nbit t - nsh t) = 2 * 2 ^ (nbit t - nsh t - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        omega
      simpa using this
  | @consX t hst ih =>
      have hadm : Adm t := h.suffix (List.suffix_cons _ _)
      have hih := ih hadm
      have h1 : nbit (.X :: t) - nsh (.X :: t) = (nbit t - nsh t) + 1 := by
        simp
        have := (h.suffix (List.suffix_cons _ _)).head
        omega
      rw [h1, pow_succ]
      simp only [cval_X]
      omega
  | @consZ t hst ih =>
      have hadm : Adm t := h.suffix (List.suffix_cons _ _)
      have hih := ih hadm
      have h1 : nbit (.Z :: t) - nsh (.Z :: t) = (nbit t - nsh t) + 1 := by
        simp
        have := (h.suffix (List.suffix_cons _ _)).head
        omega
      rw [h1, pow_succ]
      simp only [cval_Z]
      omega

theorem one_le_unmatched {s : List LB} (hst : CStack s) (h : Adm s) (hv : 1 ≤ cval s) :
    1 ≤ nbit s - nsh s := by
  by_contra hc
  have h0 : nbit s - nsh s = 0 := by omega
  have := cval_lt_two_pow hst h
  rw [h0] at this
  omega

theorem two_le_unmatched {s : List LB} (hst : CStack s) (h : Adm s) (hv : 2 ≤ cval s) :
    2 ≤ nbit s - nsh s := by
  by_contra hc
  have := cval_lt_two_pow hst h
  interval_cases hk : (nbit s - nsh s) <;> omega

/-! ## The decrement -/

private theorem cdec_CStack_aux : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s →
    CStack (cdec s) := by
  intro n
  induction n with
  | zero =>
      intro s hs hst
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
      simpa using hst
  | succ n ih =>
      intro s hs hst
      have hs' : ∀ t : List LB, (∃ b, s = b :: t) → t.length ≤ n := by
        rintro t ⟨b, rfl⟩
        simp at hs
        omega
      match s with
      | [] => simpa using hst
      | .Z :: t =>
          have hst' : CStack t := by cases hst with | consZ h => exact h
          rw [cdec_Z]; exact hst'.consX
      | .X :: t =>
          have hst' : CStack t := by cases hst with | consX h => exact h
          rw [cdec_X]
          exact (ih t (hs' t ⟨_, rfl⟩) hst').consZ
      | .W :: t =>
          have hst' : CStack t := by cases hst with | consW h => exact h
          have h1 : CStack (cdec t) := ih t (hs' t ⟨_, rfl⟩) hst'
          have h2 : CStack (cdec (cdec t)) :=
            ih (cdec t) (by rw [cdec_length]; exact hs' t ⟨_, rfl⟩) h1
          rw [cdec_W]; exact h2.consW
      | .L :: t => simpa using hst
      | .J :: t => cases hst
      | .J1 :: t => cases hst
      | .J0 :: t => cases hst
      | .K0 :: t => cases hst
      | .K1 :: t => cases hst

/-- `CStack` is preserved by the decrement, whatever the counter value. -/
theorem cdec_CStack_all {s : List LB} (hst : CStack s) : CStack (cdec s) :=
  cdec_CStack_aux s.length s (le_refl _) hst

private theorem shape_cdec_aux : ∀ (n : ℕ) (s : List LB), s.length ≤ n →
    nbit (cdec s) = nbit s ∧ nsh (cdec s) = nsh s := by
  intro n
  induction n with
  | zero =>
      intro s hs
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
      simp
  | succ n ih =>
      intro s hs
      match s with
      | [] => simp
      | .Z :: t => simp
      | .X :: t =>
          have h := ih t (by simpa using hs)
          rw [cdec_X]
          simp [h.1, h.2]
      | .W :: t =>
          have h1 := ih t (by simpa using hs)
          have h2 := ih (cdec t) (by rw [cdec_length]; simpa using hs)
          rw [cdec_W]
          simp [h1.1, h1.2, h2.1, h2.2]
      | .L :: t => simp
      | .J :: t => simp [cdec, cdecF]
      | .J1 :: t => simp [cdec, cdecF]
      | .J0 :: t => simp [cdec, cdecF]
      | .K0 :: t => simp [cdec, cdecF]
      | .K1 :: t => simp [cdec, cdecF]

theorem nbit_cdec (s : List LB) : nbit (cdec s) = nbit s :=
  (shape_cdec_aux s.length s (le_refl _)).1

theorem nsh_cdec (s : List LB) : nsh (cdec s) = nsh s :=
  (shape_cdec_aux s.length s (le_refl _)).2

/-- The decrement does not change the decoded word. -/
private theorem pdec_cdec_aux : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s → 1 ≤ cval s →
    pdec (cdec s) = pdec s := by
  intro n
  induction n with
  | zero =>
      intro s hs _ hv
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
      simp at hv
  | succ n ih =>
      intro s hs hst hv
      match s with
      | [] => simp at hv
      | .Z :: t => simp
      | .X :: t =>
          have hst' : CStack t := by cases hst with | consX h => exact h
          have hvt : 1 ≤ cval t := by simp at hv; omega
          rw [cdec_X, pdec_Z, pdec_X, ih t (by simp at hs; omega) hst' hvt]
      | .W :: t =>
          have hst' : CStack t := by cases hst with | consW h => exact h
          have hvt : 2 ≤ cval t := by
            simp only [cval_W] at hv
            omega
          have hv1 : 1 ≤ cval t := by omega
          have hc1 : cval (cdec t) = cval t - 1 := cdec_cval hst' hv1
          have hst1 : CStack (cdec t) := cdec_CStack_all hst'
          have hv2 : 1 ≤ cval (cdec t) := by omega
          have hc2 : cval (cdec (cdec t)) = cval t - 2 := by
            rw [cdec_cval hst1 hv2, hc1]
            omega
          have e1 : pdec (cdec t) = pdec t := ih t (by simp at hs; omega) hst' hv1
          have hlen : t.length ≤ n := by simp at hs; omega
          have e2 : pdec (cdec (cdec t)) = pdec (cdec t) :=
            ih (cdec t) (by rw [cdec_length]; exact hlen) hst1 hv2
          have hpar : (cval t - 2) % 2 = cval t % 2 := by omega
          rw [cdec_W, pdec_W, pdec_W, e2, e1, hc2, hpar]
      | .L :: t => simp at hv
      | .J :: t => cases hst
      | .J1 :: t => cases hst
      | .J0 :: t => cases hst
      | .K0 :: t => cases hst
      | .K1 :: t => cases hst

theorem pdec_cdec {s : List LB} (hst : CStack s) (hv : 1 ≤ cval s) : pdec (cdec s) = pdec s :=
  pdec_cdec_aux s.length s (le_refl _) hst hv

/-- The decrement does not change the decoded value. -/
theorem bval_cdec {s : List LB} (hst : CStack s) (hv : 1 ≤ cval s) : bval (cdec s) = bval s := by
  rw [bval_eq_rrun, bval_eq_rrun, pdec_cdec hst hv]

/-- **Every bottom prefix of a decremented stack matches one of the original
stack**: with the same shape and decoded value, and a counter value that has
not increased. -/
private theorem cdec_suffix_aux : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s → 1 ≤ cval s →
    ∀ v, v <:+ cdec s → ∃ u, u <:+ s ∧ cval v ≤ cval u ∧ bval v = bval u ∧
      nbit v = nbit u ∧ nsh v = nsh u := by
  intro n
  induction n with
  | zero =>
      intro s hs _ hv
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
      simp at hv
  | succ n ih =>
      intro s hs hst hv v hvs
      match s with
      | [] => simp at hv
      | .Z :: t =>
          rw [cdec_Z] at hvs
          rcases List.suffix_cons_iff.mp hvs with rfl | hvt
          · exact ⟨.Z :: t, List.suffix_refl _, by simp, by simp, by simp, by simp⟩
          · exact ⟨v, hvt.trans (List.suffix_cons _ _), le_refl _, rfl, rfl, rfl⟩
      | .X :: t =>
          have hst' : CStack t := by cases hst with | consX h => exact h
          have hvt : 1 ≤ cval t := by simp at hv; omega
          rw [cdec_X] at hvs
          rcases List.suffix_cons_iff.mp hvs with rfl | hvt'
          · refine ⟨.X :: t, List.suffix_refl _, ?_, ?_, ?_, ?_⟩
            · simp [cdec_cval hst' hvt]; omega
            · simp [bval_cdec hst' hvt]
            · simp [nbit_cdec]
            · simp [nsh_cdec]
          · obtain ⟨u, hu, h1, h2, h3, h4⟩ := ih t (by simp at hs; omega) hst' hvt v hvt'
            exact ⟨u, hu.trans (List.suffix_cons _ _), h1, h2, h3, h4⟩
      | .W :: t =>
          have hst' : CStack t := by cases hst with | consW h => exact h
          have hvt : 2 ≤ cval t := by simp only [cval_W] at hv; omega
          have hv1 : 1 ≤ cval t := by omega
          have hc1 : cval (cdec t) = cval t - 1 := cdec_cval hst' hv1
          have hst1 : CStack (cdec t) := cdec_CStack_all hst'
          have hv2 : 1 ≤ cval (cdec t) := by omega
          have hc2 : cval (cdec (cdec t)) = cval t - 2 := by
            rw [cdec_cval hst1 hv2, hc1]
            omega
          have e1 : bval (cdec t) = bval t := bval_cdec hst' hv1
          have e2 : bval (cdec (cdec t)) = bval (cdec t) := bval_cdec hst1 hv2
          rw [cdec_W] at hvs
          rcases List.suffix_cons_iff.mp hvs with rfl | hvt'
          · refine ⟨.W :: t, List.suffix_refl _, ?_, ?_, ?_, ?_⟩
            · simp only [cval_W, hc2]; omega
            · have hpar : (cval t - 2) % 2 = cval t % 2 := by omega
              simp only [bval_W, hc2, e2, e1, hpar]
            · simp [nbit_cdec]
            · simp [nsh_cdec]
          · have hlen : t.length ≤ n := by simp at hs; omega
            obtain ⟨u1, hu1, h1, h2, h3, h4⟩ :=
              ih (cdec t) (by rw [cdec_length]; exact hlen) hst1 hv2 v hvt'
            obtain ⟨u2, hu2, k1, k2, k3, k4⟩ :=
              ih t hlen hst' hv1 u1 hu1
            exact ⟨u2, hu2.trans (List.suffix_cons _ _), by omega, by omega, by omega, by omega⟩
      | .L :: t => simp at hv
      | .J :: t => cases hst
      | .J1 :: t => cases hst
      | .J0 :: t => cases hst
      | .K0 :: t => cases hst
      | .K1 :: t => cases hst

theorem cdec_suffix {s : List LB} (hst : CStack s) (hv : 1 ≤ cval s) {v : List LB}
    (hvs : v <:+ cdec s) : ∃ u, u <:+ s ∧ cval v ≤ cval u ∧ bval v = bval u ∧
      nbit v = nbit u ∧ nsh v = nsh u :=
  cdec_suffix_aux s.length s (le_refl _) hst hv v hvs

theorem Adm.cdec {s : List LB} (hst : CStack s) (h : Adm s) (hv : 1 ≤ cval s) : Adm (cdec s) := by
  intro v hvs
  obtain ⟨u, hu, _, _, h3, h4⟩ := cdec_suffix hst hv hvs
  have := h u hu
  omega

/-- **The decrement preserves the invariant.** -/
theorem Good.cdec {s : List LB} (hst : CStack s) (hg : Good s) (hv : 1 ≤ cval s) :
    Good (cdec s) := by
  intro v hvs
  obtain ⟨u, hu, h1, h2, _, _⟩ := cdec_suffix hst hv hvs
  have := hg u hu
  omega

/-! ## The overflow deposit -/

private theorem ofw_eq_pdec_aux : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s → cval s = 0 →
    ofw s = pdec s := by
  intro n
  induction n with
  | zero =>
      intro s hs _ _
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
      simp
  | succ n ih =>
      intro s hs hst hv
      match s with
      | [] => simp
      | .L :: t => simp
      | .Z :: t => simp at hv
      | .X :: t =>
          have hst' : CStack t := by cases hst with | consX h => exact h
          have hvt : cval t = 0 := by simpa using hv
          rw [ofw_X, pdec_X, ih t (by simp at hs; omega) hst' hvt]
      | .W :: t =>
          have hst' : CStack t := by cases hst with | consW h => exact h
          have hlen : t.length ≤ n := by simp at hs; omega
          have hle : cval t ≤ 1 := by
            simp only [cval_W] at hv
            omega
          rcases Nat.eq_zero_or_pos (cval t) with h0 | h1
          · rw [ofw_W, if_pos h0, pdec_W, ih t hlen hst' h0]
            simp [h0]
          · have h1' : cval t = 1 := by omega
            have hst1 : CStack (cdec t) := cdec_CStack_all hst'
            have hc : cval (cdec t) = 0 := by rw [cdec_cval hst' (by omega)]; omega
            rw [ofw_W, if_neg (by omega), pdec_W,
              ih (cdec t) (by rw [cdec_length]; exact hlen) hst1 hc,
              pdec_cdec hst' (by omega)]
            simp [h1']
      | .J :: t => cases hst
      | .J1 :: t => cases hst
      | .J0 :: t => cases hst
      | .K0 :: t => cases hst
      | .K1 :: t => cases hst

/-- **At an exhausted counter the decoder is the word the overflow deposits.** -/
theorem ofw_eq_pdec {s : List LB} (hst : CStack s) (hv : cval s = 0) : ofw s = pdec s :=
  ofw_eq_pdec_aux s.length s (le_refl _) hst hv

end BB25.Prefix
