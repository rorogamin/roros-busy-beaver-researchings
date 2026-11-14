import RequestProject.Words

/-!
# Chain rules and the general block sweep

This file proves the *general* macro rules of
`1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`, i.e. the rules that hold for a region of **arbitrary**
size.  They are the building blocks of the generalized longitudinal analysis: every long
monotone excursion of the head is a composition of them.

* one-cell rules (`sweepR_A0`, `sweepL_A1`, …), one for each transition;
* run rules: a run of `4`s crossed rightwards in state `B` (`run_fours`), a run of `1`s
  crossed leftwards in state `A` (`run_ones_A`) or `B` (`run_ones_B`), and a run of `3`s
  crossed leftwards (`run_threes`, the state alternating);
* the **block sweep** `blockR`: the word `0 4^j 2` is crossed rightwards in state `A` in
  `j + 2` steps and becomes `1 0^j 3`.  Chaining it (`sweepR_blocks`) shows that *any*
  concatenation of such blocks — with arbitrary, unrelated exponents — is crossed in one
  pass, without halting, and turns into the corresponding concatenation of `1 0^j 3`.
  This is the rigorous form of the empirical observation that the tape of this machine is
  always a sequence of blocks `0 4^j 2` (up to the phase of the sweep), the `j = 1` blocks
  making up the bulk and the `j ≥ 2` blocks being the "walls".
* the left bulk sweep `sweepL_103` and its chain `sweepL_bulk`.
-/

namespace BB25

lemma wr_eq_self {T : ℤ → Sym} {p : ℤ} {v : Sym} (h : T p = v) : wr T p v = T := by
  funext i
  by_cases hi : i = p
  · subst hi; simp [wr, h]
  · simp [wr, hi]

/-! ### One-cell rules -/

lemma sweepR_single (q q' : St) (x y : Sym)
    (h : ∀ (T : ℤ → Sym) (p : ℤ), T p = x → step ⟨q, p, T⟩ = ⟨q', p + 1, wr T p y⟩) :
    SweepR q q' [x] [y] 1 := by
  intro T a hs
  rw [Seg_cons] at hs
  refine ⟨wr T a y, ?_, ?_, ?_⟩
  · simpa using h T a hs.1
  · rw [Seg_cons]; exact ⟨by simp, Seg_nil _ _⟩
  · intro i hi
    refine wr_of_ne _ _ _ ?_
    simp only [List.length_cons, List.length_nil, Nat.cast_one, zero_add] at hi
    omega

lemma sweepL_single (q q' : St) (x y : Sym)
    (h : ∀ (T : ℤ → Sym) (p : ℤ), T p = x → step ⟨q, p, T⟩ = ⟨q', p - 1, wr T p y⟩) :
    SweepL q q' [x] [y] 1 := by
  intro T a hs
  rw [Seg_cons] at hs
  refine ⟨wr T a y, ?_, ?_, ?_⟩
  · simpa using h T a hs.1
  · rw [Seg_cons]; exact ⟨by simp, Seg_nil _ _⟩
  · intro i hi
    refine wr_of_ne _ _ _ ?_
    simp only [List.length_cons, List.length_nil, Nat.cast_one, zero_add] at hi
    omega

lemma sweepR_A0 : SweepR St.A St.B [0] [1] 1 :=
  sweepR_single _ _ _ _ (fun T p h => step_A0 T p h)

lemma sweepR_B2 : SweepR St.B St.A [2] [3] 1 :=
  sweepR_single _ _ _ _ (fun T p h => step_B2 T p h)

lemma sweepR_B4 : SweepR St.B St.B [4] [0] 1 :=
  sweepR_single _ _ _ _ (fun T p h => step_B4 T p h)

lemma sweepL_A1 : SweepL St.A St.A [1] [2] 1 :=
  sweepL_single _ _ _ _ (fun T p h => step_A1 T p h)

lemma sweepL_A2 : SweepL St.A St.B [2] [3] 1 :=
  sweepL_single _ _ _ _ (fun T p h => step_A2 T p h)

lemma sweepL_A3 : SweepL St.A St.B [3] [4] 1 :=
  sweepL_single _ _ _ _ (fun T p h => step_A3 T p h)

lemma sweepL_B0 : SweepL St.B St.A [0] [0] 1 :=
  sweepL_single _ _ _ _ (fun T p h => by rw [step_B0 T p h, wr_eq_self h])

lemma sweepL_B1 : SweepL St.B St.B [1] [4] 1 :=
  sweepL_single _ _ _ _ (fun T p h => step_B1 T p h)

lemma sweepL_B3 : SweepL St.B St.A [3] [4] 1 :=
  sweepL_single _ _ _ _ (fun T p h => step_B3 T p h)

/-! ### Trivial rules and repetition -/

lemma sweepR_nil (q : St) : SweepR q q [] [] 0 := by
  intro T a _
  exact ⟨T, by simp, Seg_nil _ _, fun i _ => rfl⟩

lemma sweepL_nil (q : St) : SweepL q q [] [] 0 := by
  intro T a _
  refine ⟨T, ?_, Seg_nil _ _, fun i _ => rfl⟩
  simp

/-- `rep w k` is the word `w` repeated `k` times. -/
def rep (w : List Sym) (k : ℕ) : List Sym := (List.replicate k w).flatten

@[simp] lemma rep_zero (w : List Sym) : rep w 0 = [] := by simp [rep]

lemma rep_succ (w : List Sym) (k : ℕ) : rep w (k + 1) = w ++ rep w k := by
  simp [rep, List.replicate_succ]

lemma rep_succ' (w : List Sym) (k : ℕ) : rep w (k + 1) = rep w k ++ w := by
  induction k with
  | zero => simp [rep_succ]
  | succ k ih =>
      calc rep w (k + 1 + 1) = w ++ rep w (k + 1) := rep_succ _ _
        _ = w ++ (rep w k ++ w) := by rw [ih]
        _ = (w ++ rep w k) ++ w := by rw [List.append_assoc]
        _ = rep w (k + 1) ++ w := by rw [rep_succ]

@[simp] lemma rep_length (w : List Sym) (k : ℕ) : (rep w k).length = k * w.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

/-- A rule that returns to its starting state can be iterated. -/
theorem sweepR_rep {q : St} {u v : List Sym} {n : ℕ} (h : SweepR q q u v n)
    (hlen : v.length = u.length) (k : ℕ) : SweepR q q (rep u k) (rep v k) (k * n) := by
  induction k with
  | zero => simpa using sweepR_nil q
  | succ k ih =>
      rw [rep_succ, rep_succ]
      have := h.comp ih hlen
      have e : n + k * n = (k + 1) * n := by ring
      rwa [e] at this

theorem sweepL_rep {q : St} {u v : List Sym} {n : ℕ} (h : SweepL q q u v n)
    (hlen : v.length = u.length) (k : ℕ) : SweepL q q (rep u k) (rep v k) (k * n) := by
  induction k with
  | zero => simpa using sweepL_nil q
  | succ k ih =>
      rw [rep_succ', rep_succ']
      have := h.comp ih (by simp [hlen])
      have e : n + k * n = (k + 1) * n := by ring
      rwa [e] at this

/-! ### Run rules

A run of a single symbol is a repetition of a one-cell rule. -/

lemma rep_single (x : Sym) (n : ℕ) : rep [x] n = List.replicate n x := by
  induction n with
  | zero => simp
  | succ n ih => rw [rep_succ, ih, List.replicate_succ]; rfl

/-- A run of `n` `4`s is crossed rightwards in state `B` in `n` steps, becoming `0`s. -/
theorem run_fours (n : ℕ) :
    SweepR St.B St.B (List.replicate n 4) (List.replicate n 0) n := by
  have := sweepR_rep sweepR_B4 (by simp) n
  rw [rep_single, rep_single] at this
  simpa using this

/-- A run of `n` `1`s is crossed leftwards in state `A` in `n` steps, becoming `2`s. -/
theorem run_ones_A (n : ℕ) :
    SweepL St.A St.A (List.replicate n 1) (List.replicate n 2) n := by
  have := sweepL_rep sweepL_A1 (by simp) n
  rw [rep_single, rep_single] at this
  simpa using this

/-- A run of `n` `1`s is crossed leftwards in state `B` in `n` steps, becoming `4`s. -/
theorem run_ones_B (n : ℕ) :
    SweepL St.B St.B (List.replicate n 1) (List.replicate n 4) n := by
  have := sweepL_rep sweepL_B1 (by simp) n
  rw [rep_single, rep_single] at this
  simpa using this

/-- The state after crossing a run of `n` `3`s, starting in state `q`. -/
def altSt (q : St) (n : ℕ) : St :=
  if n % 2 = 0 then q else (match q with | St.A => St.B | St.B => St.A | St.H => St.H)

/-- A run of `n` `3`s is crossed leftwards in `n` steps, becoming `4`s; the state
alternates between `A` and `B`. -/
theorem run_threes (q : St) (hq : q = St.A ∨ q = St.B) (n : ℕ) :
    SweepL q (altSt q n) (List.replicate n 3) (List.replicate n 4) n := by
  induction n generalizing q with
  | zero => simpa [altSt] using sweepL_nil q
  | succ n ih =>
      rcases hq with rfl | rfl
      · have h1 : SweepL St.A St.B [3] [4] 1 := sweepL_A3
        have h2 := ih St.B (Or.inr rfl)
        have := h1.comp h2 (by simp)
        rw [← List.replicate_succ' (a := (3 : Sym)), ← List.replicate_succ' (a := (4 : Sym))]
          at this
        have e : altSt St.B n = altSt St.A (n + 1) := by
          rcases Nat.even_or_odd n with h | h
          · have : n % 2 = 0 := Nat.even_iff.mp h
            simp [altSt, this, Nat.add_mod]
          · have : n % 2 = 1 := Nat.odd_iff.mp h
            simp [altSt, this, Nat.add_mod]
        rw [e] at this
        have e2 : 1 + n = n + 1 := by ring
        rwa [e2] at this
      · have h1 : SweepL St.B St.A [3] [4] 1 := sweepL_B3
        have h2 := ih St.A (Or.inl rfl)
        have := h1.comp h2 (by simp)
        rw [← List.replicate_succ' (a := (3 : Sym)), ← List.replicate_succ' (a := (4 : Sym))]
          at this
        have e : altSt St.A n = altSt St.B (n + 1) := by
          rcases Nat.even_or_odd n with h | h
          · have : n % 2 = 0 := Nat.even_iff.mp h
            simp [altSt, this, Nat.add_mod]
          · have : n % 2 = 1 := Nat.odd_iff.mp h
            simp [altSt, this, Nat.add_mod]
        rw [e] at this
        have e2 : 1 + n = n + 1 := by ring
        rwa [e2] at this

/-! ### The general block sweep -/

/-- The block `0 4^j 2`. -/
def blkIn (j : ℕ) : List Sym := [0] ++ (List.replicate j 4 ++ [2])

/-- What a rightward sweep leaves behind: `1 0^j 3`. -/
def blkOut (j : ℕ) : List Sym := [1] ++ (List.replicate j 0 ++ [3])

@[simp] lemma blkIn_length (j : ℕ) : (blkIn j).length = j + 2 := by
  simp [blkIn]

@[simp] lemma blkOut_length (j : ℕ) : (blkOut j).length = j + 2 := by
  simp [blkOut]

/-- **Block rule.**  In state `A`, the block `0 4^j 2` is crossed rightwards in exactly
`j + 2` steps and becomes `1 0^j 3`; the head emerges in state `A`. -/
theorem blockR (j : ℕ) : SweepR St.A St.A (blkIn j) (blkOut j) (j + 2) := by
  have h := sweepR_A0.comp ((run_fours j).comp sweepR_B2 (by simp)) (by simp)
  have e : 1 + (j + 1) = j + 2 := by ring
  rwa [e] at h

/-- The tape word of a list of blocks. -/
def wordIn (js : List ℕ) : List Sym := (js.map blkIn).flatten

/-- The tape word the sweep leaves behind. -/
def wordOut (js : List ℕ) : List Sym := (js.map blkOut).flatten

/-- The number of steps the sweep takes. -/
def cost (js : List ℕ) : ℕ := (js.map (· + 2)).sum

@[simp] lemma wordIn_nil : wordIn [] = [] := rfl
@[simp] lemma wordOut_nil : wordOut [] = [] := rfl
@[simp] lemma cost_nil : cost [] = 0 := rfl

lemma wordIn_cons (j : ℕ) (js : List ℕ) : wordIn (j :: js) = blkIn j ++ wordIn js := rfl
lemma wordOut_cons (j : ℕ) (js : List ℕ) : wordOut (j :: js) = blkOut j ++ wordOut js := rfl
lemma cost_cons (j : ℕ) (js : List ℕ) : cost (j :: js) = (j + 2) + cost js := rfl

/-- **Generalized longitudinal sweep.**  A concatenation of blocks `0 4^{j₁} 2 … 0 4^{jₘ} 2`
with *arbitrary* exponents is crossed rightwards in state `A`, in one pass, in
`∑ (jᵢ + 2)` steps; it becomes `1 0^{j₁} 3 … 1 0^{jₘ} 3` and nothing outside changes.
In particular the machine does not halt during such a pass. -/
theorem sweepR_blocks (js : List ℕ) : SweepR St.A St.A (wordIn js) (wordOut js) (cost js) := by
  induction js with
  | nil => simpa using sweepR_nil St.A
  | cons j js ih =>
      rw [wordIn_cons, wordOut_cons, cost_cons]
      exact (blockR j).comp ih (by simp)

/-! ### The left bulk sweep -/

/-- **Left bulk rule.**  In state `A`, the block `1 0 3` is crossed leftwards in `3`
steps and becomes `2 0 4`. -/
theorem sweepL_103 : SweepL St.A St.A [1, 0, 3] [2, 0, 4] 3 := by
  have h := sweepL_A3.comp (sweepL_B0.comp sweepL_A1 (by simp)) (by simp)
  norm_num at h
  exact h

/-- A bulk of `k` blocks `1 0 3` is crossed leftwards in state `A` in `3k` steps. -/
theorem sweepL_bulk (k : ℕ) :
    SweepL St.A St.A (rep [1, 0, 3] k) (rep [2, 0, 4] k) (k * 3) :=
  sweepL_rep sweepL_103 (by simp) k

end BB25
