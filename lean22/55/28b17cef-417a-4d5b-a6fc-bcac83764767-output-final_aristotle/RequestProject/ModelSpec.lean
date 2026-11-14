/-
# The counter model is a description of the machine

`RequestProject/DigitModel.lean` defines the counter model: one epoch of
`1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` as a single scan over digits and arrival
counts.  Here that model is *proved* to describe the machine, by composing the
excursion rules of `RequestProject/Excursion.lean`:

> **`scan_spec`.**  If `scan t s = some o`, then `t` successive head visits to
> the word whose token heads are `s` are all returned, and they leave the word
> `o` behind.

and its corollary

> **`epoch_spec`.**  If `epochF L = some L'`, then the head standing on the
> fresh blank cell of an epoch boundary, with the word `2 l₀ 2 l₁ …` to its
> right, comes back out to the left — so the machine does not halt during that
> epoch — and the next epoch boundary shows the word `2 l'₀ 2 l'₁ …`.

Nothing here assumes anything about the machine's behaviour: every step is one
of the seventeen local passages proved in `RequestProject/Transits.lean`.
-/
import RequestProject.Excursion
import RequestProject.DigitModel

namespace ShiftOverflow
namespace Counter

/-! ## Arithmetic of the digit cycle -/

theorem cycE_zero (d : ℕ) : cycE 0 d = 0 := by simp [cycE]

theorem cycE_succ (t d : ℕ) :
    cycE (t + 1) d = (if d % 3 = 0 then 0 else 1) + cycE t ((d + 1) % 3) := by
  have h : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases h with h | h | h <;> simp [cycE, h] <;> omega

theorem cycS_succ (t d : ℕ) : cycS (t + 1) d = cycS t ((d + 1) % 3) := by
  simp [cycS]; omega

theorem stDigit_mod (d : ℕ) : stDigit (d % 3) = stDigit d := by simp [stDigit]

/-- A digit in the passing state `1` passes the first signal it gets. -/
theorem cycE_one_pos (k : ℕ) : 1 ≤ cycE (k + 1) 1 := by
  rw [cycE_succ]; simp

/-! ## Batch passages

Each lemma below says what a whole batch of `t` head visits does to one token,
given what the batch it sends on does to the rest of the word. -/

theorem upd1_apply {p : ℤ} {s : ℤ → ℕ} {a : ℕ} (i : ℤ) :
    upd1 s p a i = if i = p then a else s i := by
  unfold upd1 Function.update
  by_cases h : i = p <;> simp [h]

theorem excN_zero_upd2 {p : ℤ} {T U : ℤ → ℕ} {a b : ℕ} (h0 : T p = a) (h1 : T (p + 1) = b)
    (h : ExcN 0 (p + 2) T U) : ExcN 0 p T (upd2 U p a b) := by
  intro i hi
  rw [upd2_apply]
  by_cases e1 : i = p + 1
  · simp [e1, h1]
  · by_cases e0 : i = p
    · simp [e0, h0]
    · rw [if_neg e1, if_neg e0]; exact h i (by omega)

/-- **The radix-2 position.**  A block `2 2` passes each visit on twice. -/
theorem excN_22 : ∀ (t : ℕ) {p : ℤ} {T U : ℤ → ℕ}, T p = 2 → T (p + 1) = 2 →
    ExcN (2 * t) (p + 2) T U → ExcN t p T (upd2 U p 2 2) := by
  intro t
  induction t with
  | zero =>
      intro p T U h0 h1 h
      exact excN_zero_upd2 h0 h1 h
  | succ k ih =>
      intro p T U h0 h1 h
      rw [show 2 * (k + 1) = 2 + 2 * k from by ring] at h
      obtain ⟨W, hW1, hW2⟩ := ExcN_split 2 (2 * k) h
      obtain ⟨V, hV, hrest⟩ := hW1
      obtain ⟨Z, hZ, hZ0⟩ := hrest
      refine ⟨upd2 Z p 2 2, exc_22 h0 h1 hV hZ, ?_⟩
      refine ih (by rw [upd2_apply]; simp) (by rw [upd2_apply]; simp) ?_
      refine ExcN_congr (fun i hi => ?_) (fun _ _ => rfl) hW2
      rw [upd2_right hi]
      exact (hZ0 i hi).symm

/-- **The radix-3/2 position.**  A digit in state `d` returns `cycE t d` of the
`t` visits it gets, and ends in state `cycS t d`. -/
theorem excN_cyc : ∀ (t : ℕ) {p : ℤ} {T U : ℤ → ℕ} (d : ℕ), T p = 2 → T (p + 1) = stDigit d →
    ExcN (cycE t d) (p + 2) T U → ExcN t p T (upd2 U p 2 (stDigit (cycS t d))) := by
  intro t
  induction t with
  | zero =>
      intro p T U d h0 h1 h
      rw [cycE_zero] at h
      have : stDigit (cycS 0 d) = stDigit d := by
        simp only [cycS, Nat.add_zero]; exact stDigit_mod d
      rw [this]
      exact excN_zero_upd2 h0 h1 h
  | succ k ih =>
      intro p T U d h0 h1 h
      rw [cycE_succ] at h
      rw [cycS_succ]
      have hd : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
      rcases hd with hd | hd | hd
      · -- state `0`, the block `2 0`: the visit is absorbed
        rw [if_pos hd, Nat.zero_add] at h
        have hs : stDigit d = 0 := by simp [stDigit, hd]
        have hm : (d + 1) % 3 = 1 := by omega
        have hs' : stDigit ((d + 1) % 3) = 3 := by simp [stDigit, hm]
        refine ⟨upd2 T p 2 3, exc_20 (by rw [h0]) (by rw [h1, hs]), ?_⟩
        refine ih ((d + 1) % 3) (by rw [upd2_apply]; simp) (by rw [upd2_apply]; simp [hs']) ?_
        exact ExcN_congr (fun i hi => by rw [upd2_right hi]) (fun _ _ => rfl) h
      · -- state `1`, the block `2 3`: the visit is passed on
        rw [if_neg (by omega)] at h
        have hs : stDigit d = 3 := by simp [stDigit, hd]
        have hm : (d + 1) % 3 = 2 := by omega
        have hs' : stDigit ((d + 1) % 3) = 1 := by simp [stDigit, hm]
        obtain ⟨V', hV1, hV2⟩ := ExcN_split 1 (cycE k ((d + 1) % 3)) h
        obtain ⟨V, hV, hV0⟩ := hV1
        refine ⟨upd2 V p 2 1, exc_23 (by rw [h0]) (by rw [h1, hs]) hV, ?_⟩
        refine ih ((d + 1) % 3) (by rw [upd2_apply]; simp) (by rw [upd2_apply]; simp [hs']) ?_
        refine ExcN_congr (fun i hi => ?_) (fun _ _ => rfl) hV2
        rw [upd2_right hi]; exact (hV0 i hi).symm
      · -- state `2`, the block `2 1`: the visit is passed on
        rw [if_neg (by omega)] at h
        have hs : stDigit d = 1 := by simp [stDigit, hd]
        have hm : (d + 1) % 3 = 0 := by omega
        have hs' : stDigit ((d + 1) % 3) = 0 := by simp [stDigit, hm]
        obtain ⟨V', hV1, hV2⟩ := ExcN_split 1 (cycE k ((d + 1) % 3)) h
        obtain ⟨V, hV, hV0⟩ := hV1
        refine ⟨upd2 V p 2 0, exc_21 (by rw [h0]) (by rw [h1, hs]) hV, ?_⟩
        refine ih ((d + 1) % 3) (by rw [upd2_apply]; simp) (by rw [upd2_apply]; simp [hs']) ?_
        refine ExcN_congr (fun i hi => ?_) (fun _ _ => rfl) hV2
        rw [upd2_right hi]; exact (hV0 i hi).symm

/-- **A fresh block joins the counter.**  `0 2` passes the first visit on and
becomes the radix-2 block `2 2`. -/
theorem excN_02 {t : ℕ} {p : ℤ} {T U : ℤ → ℕ} (ht : 1 ≤ t) (h0 : T p = 0) (h1 : T (p + 1) = 2)
    (h : ExcN (2 * t - 1) (p + 2) T U) : ExcN t p T (upd2 U p 2 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 1 + 2 * k from by omega] at h
  obtain ⟨V', hV1, hV2⟩ := ExcN_split 1 (2 * k) h
  obtain ⟨V, hV, hV0⟩ := hV1
  refine ⟨upd2 V p 2 2, exc_02 h0 h1 hV, ?_⟩
  refine excN_22 k (by rw [upd2_apply]; simp) (by rw [upd2_apply]; simp) ?_
  refine ExcN_congr (fun i hi => ?_) (fun _ _ => rfl) hV2
  rw [upd2_right hi]; exact (hV0 i hi).symm

/-- A loose `1` eats one visit and turns into a radix-2 block. -/
theorem excN_12 {t : ℕ} {p : ℤ} {T U : ℤ → ℕ} (ht : 1 ≤ t) (h0 : T p = 1) (h1 : T (p + 1) = 2)
    (h : ExcN (2 * (t - 1)) (p + 2) T U) : ExcN t p T (upd2 U p 2 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  refine ⟨upd1 T p 2, exc_1 h0, ?_⟩
  refine excN_22 k (by rw [upd1_apply]; simp) ?_ ?_
  · rw [upd1_apply, if_neg (by omega)]; exact h1
  · refine ExcN_congr (fun i hi => ?_) (fun _ _ => rfl) h
    rw [upd1_apply, if_neg (by omega)]

/-! ## The tape of a word -/

/-- The cells of the tape whose token heads are `s`: heads alternate with the
`2`s that separate them, and the last head is followed by blank tape. -/
def inCells : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: rest => a :: 2 :: inCells (b :: rest)

/-- The cells of the word a scan leaves behind: every token becomes `2 d`. -/
def outCells (o : List ℕ) : List ℕ := o.flatMap (fun d => [2, d])

theorem outCells_cons (d : ℕ) (o : List ℕ) : outCells (d :: o) = 2 :: d :: outCells o := rfl

/-- `T` shows the cells `cs` from `p` rightwards (and blanks beyond them). -/
def AgreeFrom (T : ℤ → ℕ) (p : ℤ) (cs : List ℕ) : Prop :=
  ∀ i : ℤ, p ≤ i → T i = cs.getD (i - p).toNat 0

theorem AgreeFrom.head {T : ℤ → ℕ} {p : ℤ} {x : ℕ} {cs : List ℕ}
    (h : AgreeFrom T p (x :: cs)) : T p = x := by
  have := h p (le_refl p); simpa using this

theorem AgreeFrom.tail {T : ℤ → ℕ} {p : ℤ} {x : ℕ} {cs : List ℕ}
    (h : AgreeFrom T p (x :: cs)) : AgreeFrom T (p + 1) cs := by
  intro i hi
  have h' := h i (by omega)
  rw [h']
  have : (i - p).toNat = (i - (p + 1)).toNat + 1 := by omega
  rw [this]
  simp

theorem AgreeFrom.nil_of {T : ℤ → ℕ} {p : ℤ} (h : ∀ i, p ≤ i → T i = 0) : AgreeFrom T p [] := by
  intro i hi; simpa using h i hi

theorem AgreeFrom.blank {T : ℤ → ℕ} {p : ℤ} (h : AgreeFrom T p []) :
    ∀ i, p ≤ i → T i = 0 := by
  intro i hi; simpa using h i hi

/-! ## The scan describes the machine -/

/-- The frontier: `t` visits running off the end of the used tape grow the word
`freshW t`. -/
theorem freshW_spec : ∀ (t : ℕ) {p : ℤ} {T U : ℤ → ℕ}, AgreeFrom T p [] →
    AgreeFrom U p (outCells (freshW t)) → ExcN t p T U := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro p T U hT hU
    match t with
    | 0 =>
        intro i hi
        rw [hU i hi]
        have h00 : freshW 0 = [] := by rw [freshW]
        rw [h00]
        simp only [outCells, List.flatMap_nil, List.getD_nil]
        exact (hT.blank i hi).symm
    | (k + 1) =>
        have hfw : freshW (k + 1) = stDigit (cycS k 2) :: freshW (cycE k 2) := by
          rw [freshW]
        rw [hfw, outCells_cons] at hU
        have h0 : T p = 0 := hT.blank p (le_refl p)
        have h1 : T (p + 1) = 0 := hT.blank (p + 1) (by omega)
        have hUp : U p = 2 := hU.head
        have hUp1 : U (p + 1) = stDigit (cycS k 2) := (hU.tail).head
        have hUrest : AgreeFrom U (p + 2) (outCells (freshW (cycE k 2))) := by
          have := (hU.tail).tail
          simpa [add_assoc] using this
        refine ⟨upd2 T p 2 1, exc_00 h0 h1, ?_⟩
        have hcyc := excN_cyc k (p := p) (T := upd2 T p 2 1) (U := U) 2
          (by rw [upd2_apply]; simp) (by rw [upd2_apply]; simp [stDigit]) ?_
        · refine ExcN_congr (fun _ _ => rfl) (fun i hi => ?_) hcyc
          rw [upd2_apply]
          by_cases e1 : i = p + 1
          · simp [e1, hUp1]
          · by_cases e0 : i = p
            · simp [e0, hUp]
            · rw [if_neg e1, if_neg e0]
        · refine ih (cycE k 2) (by have := cycE_le k 2; omega) ?_ hUrest
          refine AgreeFrom.nil_of (fun i hi => ?_)
          rw [upd2_right hi]
          exact hT.blank i (by omega)

/-! ## Reading off the two ends of a word -/

theorem outCells_head {U : ℤ → ℕ} {p : ℤ} {d : ℕ} {o : List ℕ}
    (hU : AgreeFrom U p (outCells (d :: o))) :
    U p = 2 ∧ U (p + 1) = d ∧ AgreeFrom U (p + 2) (outCells o) := by
  rw [outCells_cons] at hU
  refine ⟨hU.head, (hU.tail).head, ?_⟩
  have := (hU.tail).tail
  simpa [add_assoc] using this

/-- The cells behind the head of a word do not depend on that head: this is why
replacing a consumed `3` by a `0` is all the scan has to record. -/
theorem inCells_tail (x : ℕ) (rest : List ℕ) :
    ∃ ts, inCells (x :: rest) = x :: ts ∧ ∀ y, inCells (y :: rest) = y :: ts := by
  match rest with
  | [] => exact ⟨[], rfl, fun _ => rfl⟩
  | c :: r => exact ⟨2 :: inCells (c :: r), rfl, fun _ => rfl⟩

theorem upd2_congr_out {n : ℕ} {p : ℤ} {T U : ℤ → ℕ} {a b : ℕ} (hU0 : U p = a)
    (hU1 : U (p + 1) = b) (h : ExcN n p T (upd2 U p a b)) : ExcN n p T U := by
  refine ExcN_congr (fun _ _ => rfl) (fun i hi => ?_) h
  rw [upd2_apply]
  by_cases e1 : i = p + 1
  · simp [e1, hU1]
  · by_cases e0 : i = p
    · simp [e0, hU0]
    · rw [if_neg e1, if_neg e0]

theorem cyc_step {m d : ℕ} {p : ℤ} {T U : ℤ → ℕ}
    (h0 : T p = 2) (h1 : T (p + 1) = stDigit d)
    (htail : ExcN (cycE m d) (p + 2) T U)
    (hU0 : U p = 2) (hU1 : U (p + 1) = stDigit (cycS m d)) : ExcN m p T U :=
  upd2_congr_out hU0 hU1 (excN_cyc m d h0 h1 htail)

/-- The last token of the word, the block `(a, 0)`: from here the word grows. -/
theorem last_cyc {m d : ℕ} {p : ℤ} {T U : ℤ → ℕ} (h0 : T p = 2) (h1 : T (p + 1) = stDigit d)
    (hb : ∀ i, p + 2 ≤ i → T i = 0)
    (hU : AgreeFrom U p (outCells (stDigit (cycS m d) :: freshW (cycE m d)))) :
    ExcN m p T U := by
  obtain ⟨hU0, hU1, hUr⟩ := outCells_head hU
  exact cyc_step h0 h1 (freshW_spec _ (AgreeFrom.nil_of hb) hUr) hU0 hU1


theorem upd3_apply {p : ℤ} {s : ℤ → ℕ} {a b c : ℕ} (i : ℤ) :
    upd3 s p a b c i = if i = p + 2 then c else if i = p + 1 then b else if i = p then a
      else s i := by
  unfold upd3 Function.update
  by_cases h2 : i = p + 2 <;> by_cases h1 : i = p + 1 <;> by_cases h0 : i = p <;> simp_all

theorem AgreeFrom.cons {T : ℤ → ℕ} {p : ℤ} {x : ℕ} {cs : List ℕ} (h0 : T p = x)
    (h : AgreeFrom T (p + 1) cs) : AgreeFrom T p (x :: cs) := by
  intro i hi
  by_cases e : i = p
  · subst e; simpa using h0
  · have hi' : p + 1 ≤ i := by omega
    rw [h i hi']
    have : (i - p).toNat = (i - (p + 1)).toNat + 1 := by omega
    rw [this]; simp

theorem AgreeFrom.congr {T T' : ℤ → ℕ} {p : ℤ} {cs : List ℕ} (he : ∀ i, p ≤ i → T' i = T i)
    (h : AgreeFrom T p cs) : AgreeFrom T' p cs := fun i hi => by rw [he i hi]; exact h i hi


/-! ## The scan is the machine -/

/-- **The counter model describes the machine.**  If the scan of `t` head
visits into the word whose token heads are `s` succeeds, then those `t` visits
really are made and returned by the machine, and they leave the word `o`
behind.  Every step of the proof is one of the local passages of
`RequestProject/Transits.lean`, so nothing about the machine is assumed. -/
theorem scan_spec : ∀ (n : ℕ) (s : List ℕ), s.length = n → ∀ (t : ℕ) (o : List ℕ),
    scan t s = some o → ∀ (p : ℤ) (T U : ℤ → ℕ), AgreeFrom T p (inCells s) →
    AgreeFrom U p (outCells o) → ExcN t p T U := by
  intro n
  induction n with
  | zero =>
      intro s hs t o h p T U hT hU
      match s with
      | [] =>
          simp only [scan] at h
          have ho : freshW t = o := Option.some.inj h
          subst ho
          exact freshW_spec t (by simpa [inCells] using hT) hU
      | a :: rest => simp at hs
  | succ k ih =>
      intro s hs t o h p T U hT hU
      match s with
      | [] => simp at hs
      | [a] =>
          have hTp : T p = a := hT.head
          have hTb : ∀ i, p + 1 ≤ i → T i = 0 := by
            intro i hi
            have hv := hT i (by omega)
            have hn : (i - p).toNat = ((i - (p + 1)).toNat) + 1 := by omega
            rw [hv, hn]; simp [inCells]
          simp only [scan] at h
          by_cases h0 : t = 0
          · rw [if_pos h0] at h; exact absurd h (by simp)
          rw [if_neg h0] at h
          obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at h
          by_cases ha0 : a = 0
          · rw [if_pos ha0] at h
            have ho := Option.some.inj h; subst ho
            refine ⟨upd2 T p 2 1, exc_00 (by rw [hTp, ha0]) (hTb (p + 1) (by omega)), ?_⟩
            refine last_cyc (d := 2) (by rw [upd2_apply]; simp)
              (by rw [upd2_apply]; simp [stDigit]) (fun i hi => ?_) hU
            rw [upd2_right hi]; exact hTb i (by omega)
          rw [if_neg ha0] at h
          by_cases ha1 : a = 1
          · rw [if_pos ha1] at h
            have ho := Option.some.inj h; subst ho
            refine ⟨upd1 T p 2, exc_1 (by rw [hTp, ha1]), ?_⟩
            refine last_cyc (d := 0) (by rw [upd1_apply]; simp) ?_ (fun i hi => ?_) hU
            · rw [upd1_apply, if_neg (by omega), hTb (p + 1) (by omega)]; simp [stDigit]
            · rw [upd1_apply, if_neg (by omega)]; exact hTb i (by omega)
          rw [if_neg ha1] at h
          by_cases ha2 : a = 2
          · rw [if_pos ha2] at h
            have ho := Option.some.inj h; subst ho
            exact last_cyc (d := 0) (by rw [hTp, ha2])
              (by rw [hTb (p + 1) (by omega)]; simp [stDigit]) (fun i hi => hTb i (by omega)) hU
          · rw [if_neg ha2] at h; exact absurd h (by simp)
      | a :: c :: rest =>
          have e : inCells (a :: c :: rest) = a :: 2 :: inCells (c :: rest) := rfl
          rw [e] at hT
          have hTa : T p = a := hT.head
          have hT1 : T (p + 1) = 2 := (hT.tail).head
          have hTr : AgreeFrom T (p + 2) (inCells (c :: rest)) := by
            have := (hT.tail).tail; simpa [add_assoc] using this
          obtain ⟨ts, hts, hts'⟩ := inCells_tail c rest
          have hTc : T (p + 2) = c := by rw [hts] at hTr; exact hTr.head
          have hTts : AgreeFrom T (p + 3) ts := by
            rw [hts] at hTr
            have := hTr.tail; simpa [show p + 2 + 1 = p + 3 from by ring] using this
          have hlen0 : (0 :: rest).length = k := by simp only [List.length_cons] at hs ⊢; omega
          have hlenc : (c :: rest).length = k := by simp only [List.length_cons] at hs ⊢; omega
          simp only [scan] at h
          by_cases h0 : t = 0
          · rw [if_pos h0] at h; exact absurd h (by simp)
          rw [if_neg h0] at h
          obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at h
          by_cases h3 : c = 3
          · rw [if_pos h3] at h
            by_cases ha2 : a = 2
            · -- `A · 2 2 3 = 2 0 0`: a radix-2 block turns into a radix-3/2 digit
              rw [if_pos ha2] at h
              obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 h
              obtain ⟨hU0, hU1, hUr⟩ := outCells_head hU
              refine ⟨upd3 T p 2 0 0, exc_223 (by rw [hTa, ha2]) hT1 (by rw [hTc, h3]), ?_⟩
              refine cyc_step (d := 0) ?_ ?_ ?_ hU0 hU1
              · rw [upd3_apply, if_neg (by omega), if_neg (by omega), if_pos rfl]
              · rw [upd3_apply, if_neg (by omega), if_pos rfl]; simp [stDigit]
              · refine ih (0 :: rest) hlen0 _ _ ho' (p + 2) _ _ ?_ hUr
                rw [hts' 0]
                refine AgreeFrom.cons (by rw [upd3_apply, if_pos rfl]) ?_
                refine AgreeFrom.congr (fun i hi => ?_)
                  (by simpa [show p + 2 + 1 = p + 3 from by ring] using hTts)
                rw [upd3_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            rw [if_neg ha2] at h
            by_cases ha0 : a = 0
            · -- `A · 0 2 3 = 2 3 4`: the only rule that writes a `4`
              rw [if_pos ha0] at h
              by_cases hlt : m + 1 < 2
              · rw [if_pos hlt] at h; exact absurd h (by simp)
              rw [if_neg hlt] at h
              obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 h
              obtain ⟨hU0, hU1, hUr⟩ := outCells_head hU
              obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              obtain ⟨f, hf⟩ : ∃ f, cycE (m' + 1) 1 = f + 1 :=
                ⟨cycE (m' + 1) 1 - 1, by have := cycE_one_pos m'; omega⟩
              refine ⟨upd3 T p 2 3 4, exc_023 (by rw [hTa, ha0]) hT1 (by rw [hTc, h3]), ?_⟩
              refine cyc_step (d := 1) ?_ ?_ ?_ hU0 hU1
              · rw [upd3_apply, if_neg (by omega), if_neg (by omega), if_pos rfl]
              · rw [upd3_apply, if_neg (by omega), if_pos rfl]; simp [stDigit]
              · rw [hf]
                refine ⟨upd1 (upd3 T p 2 3 4) (p + 2) 0,
                  exc_4 (by rw [upd3_apply, if_pos rfl]), ?_⟩
                have hff : cycE (m' + 1) 1 - 1 = f := by omega
                rw [hff] at ho'
                refine ih (0 :: rest) hlen0 _ _ ho' (p + 2) _ _ ?_ hUr
                rw [hts' 0]
                refine AgreeFrom.cons (by rw [upd1_apply, if_pos rfl]) ?_
                refine AgreeFrom.congr (fun i hi => ?_)
                  (by simpa [show p + 2 + 1 = p + 3 from by ring] using hTts)
                rw [upd1_apply, if_neg (by omega), upd3_apply, if_neg (by omega),
                  if_neg (by omega), if_neg (by omega)]
            rw [if_neg ha0] at h
            by_cases ha1 : a = 1
            · -- a loose `1`, and then `2 2 3`
              rw [if_pos ha1] at h
              by_cases hlt : m + 1 < 2
              · rw [if_pos hlt] at h; exact absurd h (by simp)
              rw [if_neg hlt] at h
              obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 h
              obtain ⟨hU0, hU1, hUr⟩ := outCells_head hU
              obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              simp only [show m' + 1 + 1 - 2 = m' from by omega] at ho' hU1 ⊢
              refine ⟨upd1 T p 2, exc_1 (by rw [hTa, ha1]), ?_⟩
              have h1p : (upd1 T p 2) p = 2 := by rw [upd1_apply, if_pos rfl]
              have h1p1 : (upd1 T p 2) (p + 1) = 2 := by
                rw [upd1_apply, if_neg (by omega)]; exact hT1
              have h1p2 : (upd1 T p 2) (p + 2) = 3 := by
                rw [upd1_apply, if_neg (by omega), hTc, h3]
              refine ⟨upd3 (upd1 T p 2) p 2 0 0, exc_223 h1p h1p1 h1p2, ?_⟩
              refine cyc_step (d := 0) ?_ ?_ ?_ hU0 hU1
              · rw [upd3_apply, if_neg (by omega), if_neg (by omega), if_pos rfl]
              · rw [upd3_apply, if_neg (by omega), if_pos rfl]; simp [stDigit]
              · refine ih (0 :: rest) hlen0 _ _ ho' (p + 2) _ _ ?_ hUr
                rw [hts' 0]
                refine AgreeFrom.cons (by rw [upd3_apply, if_pos rfl]) ?_
                refine AgreeFrom.congr (fun i hi => ?_)
                  (by simpa [show p + 2 + 1 = p + 3 from by ring] using hTts)
                rw [upd3_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega),
                  upd1_apply, if_neg (by omega)]
            · rw [if_neg ha1] at h; exact absurd h (by simp)
          · rw [if_neg h3] at h
            by_cases ha2 : a = 2
            · rw [if_pos ha2] at h
              obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 h
              obtain ⟨hU0, hU1, hUr⟩ := outCells_head hU
              refine upd2_congr_out hU0 hU1 (excN_22 (m + 1) (by rw [hTa, ha2]) hT1 ?_)
              exact ih (c :: rest) hlenc _ _ ho' (p + 2) _ _ hTr hUr
            rw [if_neg ha2] at h
            by_cases ha0 : a = 0
            · rw [if_pos ha0] at h
              obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 h
              obtain ⟨hU0, hU1, hUr⟩ := outCells_head hU
              refine upd2_congr_out hU0 hU1 (excN_02 (by omega) (by rw [hTa, ha0]) hT1 ?_)
              exact ih (c :: rest) hlenc _ _ ho' (p + 2) _ _ hTr hUr
            rw [if_neg ha0] at h
            by_cases ha1 : a = 1
            · rw [if_pos ha1] at h
              obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 h
              obtain ⟨hU0, hU1, hUr⟩ := outCells_head hU
              refine upd2_congr_out hU0 hU1 (excN_12 (by omega) (by rw [hTa, ha1]) hT1 ?_)
              have hre : 2 * (m + 1 - 1) = 2 * (m + 1) - 2 := by omega
              rw [hre]
              exact ih (c :: rest) hlenc _ _ ho' (p + 2) _ _ hTr hUr
            · rw [if_neg ha1] at h; exact absurd h (by simp)

/-! ## From one epoch boundary to the next -/

/-- The cells of a word, read as the tape behind a token head. -/
theorem inCells_cons (y : ℕ) (r : List ℕ) : inCells (y :: r) = y :: outCells r := by
  induction r generalizing y with
  | nil => rfl
  | cons z r ih =>
      show y :: 2 :: inCells (z :: r) = y :: outCells (z :: r)
      rw [ih, outCells_cons]

/-- **An epoch boundary**: the head at `p` in state `A`, nothing but blanks at
`p` and to its left, and the word of `L` from `p + 1` on. -/
def AtBoundary (T : ℤ → ℕ) (p : ℤ) (L : List ℕ) : Prop :=
  (∀ i, i ≤ p → T i = 0) ∧ AgreeFrom T (p + 1) (outCells L)

/-- **One epoch of the machine.**  If the counter model gets from `L` to `L'`,
then the machine gets from the epoch boundary showing `L` to the next epoch
boundary, one cell further left, showing `L'` — in particular it does not halt
in between. -/
theorem boundary_step {L L' : List ℕ} (h : epochF L = some L') {T : ℤ → ℕ} {p : ℤ}
    (hB : AtBoundary T p L) :
    ∃ T', Reaches ⟨T, p, .A⟩ ⟨T', p - 1, .A⟩ ∧ AtBoundary T' (p - 1) L' := by
  obtain ⟨hblank, hword⟩ := hB
  set U : ℤ → ℕ := fun i => if p ≤ i then (outCells L').getD (i - p).toNat 0 else 0 with hUdef
  have hUagree : AgreeFrom U p (outCells L') := by
    intro i hi; simp [hUdef, hi]
  have hTin : AgreeFrom T p (inCells (0 :: L)) := by
    rw [inCells_cons]
    exact AgreeFrom.cons (hblank p (le_refl p)) hword
  have hspec := scan_spec (0 :: L).length (0 :: L) rfl 1 L' h p T U hTin hUagree
  obtain ⟨w, hw, hw0⟩ := hspec
  refine ⟨patch p T w, hw T (fun _ _ => rfl), ?_, ?_⟩
  · intro i hi
    rw [patch_left (by omega)]
    exact hblank i (by omega)
  · intro i hi
    rw [show p - 1 + 1 = p from by ring] at hi ⊢
    rw [patch_right hi, ← hw0 i hi]
    simp [hUdef, hi]

/-! ## Non-halting, reduced to the counter model -/

/-- The blank tape is the machine's first epoch boundary, with the empty word. -/
theorem init_boundary : AtBoundary blank 0 [] :=
  ⟨fun _ _ => rfl, fun i _ => by simp [blank, outCells]⟩

/-- A configuration reached in `k ≥ 1` steps. -/
theorem reaches_pos {T T' : ℤ → ℕ} {p q : ℤ} {st st' : St} (h : Reaches ⟨T, p, st⟩ ⟨T', q, st'⟩)
    (hne : p ≠ q) : ∃ k, 1 ≤ k ∧ steps k ⟨T, p, st⟩ = some ⟨T', q, st'⟩ := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp only [steps, Option.some.injEq] at hk
    exact absurd (congrArg Cfg.pos hk) hne
  · exact hpos

/-- **Non-halting is now a statement about the counter model alone.**  If every
iterate of `epochF` from the empty word succeeds, the machine started on the
blank tape never halts. -/
theorem never_halts_of_model (hall : ∀ n, (epochIter n []).isSome) :
    ∀ n, steps n init ≠ none := by
  have key : ∀ n : ℕ, ∃ (N : ℕ) (T : ℤ → ℕ) (p : ℤ) (L : List ℕ), n ≤ N ∧
      steps N init = some ⟨T, p, .A⟩ ∧ AtBoundary T p L ∧ epochIter n [] = some L := by
    intro n
    induction n with
    | zero => exact ⟨0, blank, 0, [], le_refl _, rfl, init_boundary, rfl⟩
    | succ n ih =>
        obtain ⟨N, T, p, L, hN, hsteps, hB, hL⟩ := ih
        obtain ⟨L', hL'⟩ : ∃ L', epochF L = some L' := by
          have := hall (n + 1)
          rw [epochIter, hL, Option.bind_some] at this
          exact Option.isSome_iff_exists.1 this
        obtain ⟨T', hreach, hB'⟩ := boundary_step hL' hB
        obtain ⟨k, hk1, hk⟩ := reaches_pos hreach (by omega)
        refine ⟨N + k, T', p - 1, L', by omega, ?_, hB', ?_⟩
        · rw [steps_add, hsteps]; simpa using hk
        · rw [epochIter, hL, Option.bind_some, hL']
  intro n hn
  obtain ⟨N, T, p, L, hN, hsteps, _, _⟩ := key n
  exact steps_ne_none_of_le hN (by rw [hsteps]; simp) hn

end Counter
end ShiftOverflow
