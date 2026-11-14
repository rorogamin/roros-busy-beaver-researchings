import RequestProject.Start
import RequestProject.Fractal
import RequestProject.NonHalting

/-!
# Reducing non-halting to a closed family of tape words

Every macro rule of this development is a `Win` rule of one and the same shape:

```
Win St.B St.B 3 0 ([0, 0, 0] ++ W) W' k
```

i.e. *the head starts in state `B` on the leftmost non-blank cell, with (at least) three
blank cells to its left, and after `k` steps it is again in state `B`, three cells further
left, on what is now the leftmost non-blank cell, the tape word having become `W'`.*  All
these rules conserve cells: `W'.length = W.length + 3`, the three extra cells being the
three blank cells the rule consumes on the left, so the right edge of the word never
moves.

This file turns that observation into a **reduction**: to prove that the machine never
halts it suffices to exhibit a family `P` of tape words which

* contains the word the machine actually reaches (at step `3099`, see `Start.lean`), and
* is closed under one macro step in the above sense.

No analysis of the machine is needed beyond that; in particular the family may be
infinite, and the individual macro steps may be given by different rules.  Everything that
`ANALYSIS.md` still lists as missing — the fractal recursion — is exactly the task of
producing such a `P`.

The two ingredients are `AtWord` (the machine, run from the blank tape, is at a
synchronisation moment with tape word `W`) and `AtWord.macro` (a macro rule carries one
synchronisation moment to the next).
-/

namespace BB25

/-! ### Synchronisation moments of the blank-tape orbit -/

/-- `AtWord n a W`: after `n` steps from the blank tape the machine is in state `B` with
its head on cell `a`, the tape carries the word `W` on the cells `a, …, a + |W| - 1`, and
every other cell is blank.  This is the exact form of a *synchronisation moment* (a
`B`-event at a new leftmost cell) used throughout `ANALYSIS.md`. -/
def AtWord (n : ℕ) (a : ℤ) (W : List Sym) : Prop :=
  (run n).st = St.B ∧ (run n).pos = a ∧ Seg (run n).tape a W ∧
    ∀ i : ℤ, i < a ∨ a + (W.length : ℤ) ≤ i → (run n).tape i = 0

/-- At a synchronisation moment the machine has not halted. -/
theorem AtWord.not_halted {n : ℕ} {a : ℤ} {W : List Sym} (h : AtWord n a W) :
    ¬ Halted (run n) := by
  rw [Halted, h.1]
  exact fun hc => St.noConfusion hc

/-! ### One macro step -/

/-- **A macro rule carries one synchronisation moment to the next.**  If the machine is at
a synchronisation moment with tape word `W`, and a window rule takes `[0,0,0] ++ W` to a
word `W'` of length `|W| + 3` — returning to state `B` three cells further left — then
`k` steps later the machine is at the next synchronisation moment, with word `W'`. -/
theorem AtWord.macro {n k : ℕ} {a : ℤ} {W W' : List Sym}
    (h : AtWord n a W) (hlen : W'.length = W.length + 3)
    (hw : Win St.B St.B 3 0 ([0, 0, 0] ++ W) W' k) :
    AtWord (n + k) (a - 3) W' := by
  obtain ⟨hst, hpos, hseg, hout⟩ := h
  set T := (run n).tape with hT
  -- the window `[0,0,0] ++ W` starting three cells to the left of the head
  have hz : Seg T (a - 3) [0, 0, 0] := by
    refine Seg_cons.mpr ⟨hout _ (Or.inl (by omega)), Seg_cons.mpr ⟨?_, Seg_cons.mpr ⟨?_, ?_⟩⟩⟩
    · exact hout _ (Or.inl (by omega))
    · exact hout _ (Or.inl (by omega))
    · simp
  have hseg3 : Seg T (a - 3) ([0, 0, 0] ++ W) := by
    refine Seg_append.mpr ⟨hz, ?_⟩
    have e : a - 3 + (([0, 0, 0] : List Sym).length : ℤ) = a := by simp
    rw [e]; exact hseg
  obtain ⟨T', hstep, hseg', hout'⟩ := hw T (a - 3) hseg3
  have hpos3 : a - 3 + ((3 : ℕ) : ℤ) = a := by push_cast; ring
  have hpos0 : a - 3 + ((0 : ℕ) : ℤ) = a - 3 := by push_cast; ring
  rw [hpos3, hpos0] at hstep
  have hrun : run n = ⟨St.B, a, T⟩ := by
    rw [hT, ← hst, ← hpos]
  have hrunk : run (n + k) = ⟨St.B, a - 3, T'⟩ := by
    have : run (n + k) = step^[k] (run n) := by
      rw [run, run, show n + k = k + n from by ring, Function.iterate_add_apply]
    rw [this, hrun, hstep]
  refine ⟨by rw [hrunk], by rw [hrunk], by rw [hrunk]; exact hseg', ?_⟩
  intro i hi
  rw [hrunk]
  show T' i = 0
  have hi' : i < a - 3 ∨ a - 3 + ((([0, 0, 0] ++ W : List Sym)).length : ℤ) ≤ i := by
    rcases hi with hi | hi
    · left; exact hi
    · right
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      rw [hlen] at hi
      push_cast at hi ⊢
      omega
  rw [hout' i hi']
  refine hout i ?_
  rcases hi with hi | hi
  · left; omega
  · right
    rw [hlen] at hi
    push_cast at hi ⊢
    omega

/-! ### Families of tape words closed under one macro step -/

/-- `MacroClosed P`: every word of the family `P` admits a macro rule — a window rule
taking `[0,0,0] ++ W` in state `B` at offset `3` to a word `W'` of length `|W| + 3` in
state `B` at offset `0`, in a positive number of steps — whose result `W'` is again in
`P`.  This is the shape of every left-end rule of the development. -/
def MacroClosed (P : List Sym → Prop) : Prop :=
  ∀ W, P W → ∃ (W' : List Sym) (k : ℕ), 0 < k ∧ W'.length = W.length + 3 ∧
    Win St.B St.B 3 0 ([0, 0, 0] ++ W) W' k ∧ P W'

/-- **A macro rule applies to a word with an arbitrary right context.**  The rules of the
development are stated for the shortest window they need; this adapter appends an
arbitrary tail `S`, which the rule leaves untouched.  It is what turns a catalogue entry
into a step of a `MacroClosed` family. -/
theorem Win.macro_append {L L' : List Sym} {k : ℕ}
    (h : Win St.B St.B 3 0 ([0, 0, 0] ++ L) L' k) (hlen : L'.length = L.length + 3)
    (S : List Sym) :
    Win St.B St.B 3 0 ([0, 0, 0] ++ (L ++ S)) (L' ++ S) k := by
  have h' := h.embed (by simp; omega) [] S
  exact h'.cast (by simp) (by simp) (by simp) (by simp) rfl

/-- The `P2` rule, as a step of a `MacroClosed` family: it applies to any word beginning
with the token `U(2,2)` followed by a blank cell. -/
theorem macro_step_P2 (S : List Sym) :
    Win St.B St.B 3 0 ([0, 0, 0] ++ (tokU 2 2 ++ [0] ++ S))
      (tokU 2 2 ++ tokV 1 ++ [0] ++ S) 31 := by
  have h : Win St.B St.B 3 0 ([0, 0, 0] ++ (tokU 2 2 ++ [0]))
      (tokU 2 2 ++ tokV 1 ++ [0]) 31 := by
    simpa [List.append_assoc] using rule_P2
  simpa [List.append_assoc] using h.macro_append (by simp [tokU, tokV]) S

/-! ### The reduction -/

/-- **Non-halting follows from a closed family of tape words.**  Suppose `P` is any family
of tape words such that every `W` in `P` admits a macro rule — a window rule taking
`[0,0,0] ++ W` in state `B` at offset `3` to a word `W'` of length `|W| + 3` in state `B`
at offset `0`, in a positive number of steps — whose result `W'` is again in `P`.  If the
machine, started on the blank tape, ever reaches a synchronisation moment whose tape word
lies in `P`, then it never halts.

This is the precise sense in which the remaining gap is combinatorial: the analysis of the
machine is complete once such a family is exhibited. -/
theorem never_halts_of_closed (P : List Sym → Prop) (hclosed : MacroClosed P)
    {n₀ : ℕ} {a₀ : ℤ} {W₀ : List Sym} (h0 : AtWord n₀ a₀ W₀) (hP : P W₀) :
    ∀ n : ℕ, ¬ Halted (run n) := by
  have key : ∀ j : ℕ, ∃ (n : ℕ) (a : ℤ) (W : List Sym), n₀ + j ≤ n ∧ AtWord n a W ∧ P W := by
    intro j
    induction j with
    | zero => exact ⟨n₀, a₀, W₀, by omega, h0, hP⟩
    | succ j ih =>
        obtain ⟨n, a, W, hn, hA, hPW⟩ := ih
        obtain ⟨W', k, hk, hlen, hwin, hP'⟩ := hclosed W hPW
        exact ⟨n + k, a - 3, W', by omega, hA.macro hlen hwin, hP'⟩
  refine never_halts_of_unbounded ?_
  intro N
  obtain ⟨n, a, W, hn, hA, -⟩ := key N
  exact ⟨n, by omega, hA.not_halted⟩

/-! ### The synchronisation moment the machine actually reaches -/

/-- The tape word at step `3099`: `U(2,1) U(4,1) u u U(2,2) V(1) u U(1,18) u^12`, with the
trailing blank cells of the computed window. -/
def orbitWord : List Sym :=
  tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 2 2 ++ tokV 1 ++
    tokU 1 1 ++ tokU 1 18 ++ [0] ++
    ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0])))

/-- Cells inside a run of `0`s are blank. -/
lemma Seg_replicate_zero {T : ℤ → Sym} {a : ℤ} {k : ℕ}
    (h : Seg T a (List.replicate k 0)) {i : ℤ} (h1 : a ≤ i) (h2 : i < a + (k : ℤ)) :
    T i = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = a + (j : ℤ) := ⟨(i - a).toNat, by omega⟩
  have hj : j < (List.replicate k (0 : Sym)).length := by
    simp only [List.length_replicate]
    omega
  have := h j hj
  simpa [List.getD_eq_getElem?_getD] using this

/-- **The machine reaches a synchronisation moment with word `orbitWord` at step `3099`.**
This is `orbit_prefix_3099` of `Start.lean`, restated in the form the reduction needs. -/
theorem orbit_atWord : AtWord 3099 (-65) orbitWord := by
  obtain ⟨T, hstep, hseg, hout⟩ := orbit_prefix_3099 (fun _ => (0 : Sym)) (-71)
    (Seg_blank _ _)
  have h0 : ((-71 : ℤ) + ((71 : ℕ) : ℤ)) = 0 := by norm_num
  have hrun : run 3099 = ⟨St.B, -65, T⟩ := by
    have : run 3099 = step^[3099] ⟨St.A, (-71 : ℤ) + ((71 : ℕ) : ℤ), fun _ => (0 : Sym)⟩ := by
      rw [h0]; rfl
    rw [this, hstep]
    norm_num
  -- split the computed window word into its blank prefix and `orbitWord`
  have hsplit : (List.replicate 6 0 ++
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 2 2 ++ tokV 1 ++
        tokU 1 1 ++ tokU 1 18 ++ [0]) ++
      ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0]))) : List Sym)
      = List.replicate 6 0 ++ orbitWord := by
    simp [orbitWord, List.append_assoc]
  rw [hsplit] at hseg
  obtain ⟨hz, hw⟩ := Seg_append.mp hseg
  have hpos : (-71 : ℤ) + ((List.replicate 6 (0 : Sym)).length : ℤ) = -65 := by
    simp
  rw [hpos] at hw
  have hlen : (orbitWord.length : ℤ) = 90 := by simp [orbitWord]
  refine ⟨by rw [hrun], by rw [hrun], by rw [hrun]; exact hw, ?_⟩
  intro i hi
  rw [hrun]
  show T i = 0
  rcases hi with hi | hi
  · rcases lt_or_ge i (-71 : ℤ) with h | h
    · rw [hout i (Or.inl h)]
    · exact Seg_replicate_zero hz h (by simp; omega)
  · rw [hlen] at hi
    refine hout i (Or.inr ?_)
    simp only [List.length_replicate]
    push_cast
    omega

/-- **The reduction, applied to the real orbit.**  If some family of tape words contains
`orbitWord` — the word the machine reaches at step `3099` — and is closed under one macro
step, then the machine never halts. -/
theorem never_halts_of_closed_orbit (P : List Sym → Prop) (hclosed : MacroClosed P)
    (hP : P orbitWord) :
    ∀ n : ℕ, ¬ Halted (run n) :=
  never_halts_of_closed P hclosed orbit_atWord hP

/-! ### The fractal mechanism, in general form

A run of `3j` blank cells in the middle of the tape hosts `j` macro steps of the
machine's own computation: this is the content of `ANALYSIS.md` §24 — a rightward sweep
turns a token `U(a,1) = 0 4^a 2` into `1 0^a 3` (`four_run_to_zero_run`), so a `4`-run
becomes a piece of *virtual blank tape*, on which the left-end rules apply verbatim
(`Win.in_zero_run`), each consuming three of its cells.

The theorem below says this for a whole closed family at once, and for every `j`
simultaneously, by induction on `j`: it is the inductive engine of the self-similarity. -/

/-- **A closed family runs `j` macro steps inside a run of `3j` extra blank cells.**  If
`P` is closed under one macro step and `P W`, then for every `j` the machine, entering the
window `0^(3j) · 0 0 0 · W` at the leftmost cell of `W` in state `B`, performs exactly `j`
macro steps inside it and ends in state `B` on the leftmost non-blank cell, which is `3j`
cells further left, with a word `W'` of the family, of length `|W| + 3j` — and three blank
cells still to its left.

The `Win` conclusion also certifies that the head never leaves the window during those
steps, so the computation really is confined to the run: this is why a `4`-run of length
`3j+1` reproduces the machine's own first `j` tape words. -/
theorem MacroClosed.in_zero_run {P : List Sym → Prop} (hP : MacroClosed P) :
    ∀ (j : ℕ) (W : List Sym), P W → ∃ (W' : List Sym) (n : ℕ), P W' ∧
      W'.length = W.length + 3 * j ∧
      Win St.B St.B (3 * j + 3) 3
        (List.replicate (3 * j) 0 ++ ([0, 0, 0] ++ W)) ([0, 0, 0] ++ W') n := by
  intro j
  induction j with
  | zero =>
      intro W hW
      refine ⟨W, 0, hW, by simp, ?_⟩
      have h := Win.refl St.B 3 ([0, 0, 0] ++ W)
      simpa using h
  | succ j ih =>
      intro W hW
      obtain ⟨W₁, k₁, -, hlen₁, hwin₁, hP₁⟩ := hP W hW
      obtain ⟨W₂, n, hP₂, hlen₂, hwin₂⟩ := ih W₁ hP₁
      -- the first macro step, performed `3j+3` cells inside the run
      have hstep := hwin₁.in_zero_run (by omega) (3 * j + 3)
      have hzeros : (List.replicate (3 * j + 3) 0 ++ W₁ : List Sym)
          = List.replicate (3 * j) 0 ++ ([0, 0, 0] ++ W₁) := by
        rw [replicate_split (0 : Sym) (3 * j) 3]
        simp
      have hstep' : Win St.B St.B (3 * j + 3 + 3) (3 * j + 3)
          (List.replicate (3 * j + 3) 0 ++ ([0, 0, 0] ++ W))
          (List.replicate (3 * j) 0 ++ ([0, 0, 0] ++ W₁)) k₁ :=
        hstep.cast (by ring) (by ring) (by simp) hzeros rfl
      have hcomp := hstep'.trans hwin₂ (by simp; omega)
      refine ⟨W₂, k₁ + n, hP₂, by omega, ?_⟩
      refine hcomp.cast (by ring) rfl ?_ rfl rfl
      congr 2

end BB25
