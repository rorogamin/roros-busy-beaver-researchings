import RequestProject.RoundTrip

/-!
# The second counter: the region is a binary counter, two cells per digit

`Counter.lean` describes the base-3 counter that sits immediately to the right
of the frontier `1`.  This file identifies the *other* counter, the one living
in the region to the right of it, and proves its increment rule.

The digits of that counter are **pairs of cells**:

* `4 2` is the digit `0`,
* `4 4` is the digit `1`,

least significant digit first (nearest to the ternary counter).  A digit string
is incremented by the following event, which is the commonest event in the whole
computation:

> the head, sweeping back to the left in state `B`, meets a cell holding `3` — a
> *marker* left behind by an earlier outward pass.  It rewrites the marker, runs
> out over the digits to the right of it, and comes back.

`marker_increment` proves that this takes exactly `4k + 13` steps, where `k` is
the length of the carry chain, and that its effect is exactly

```
  3  b₀ 1 1 … 1 0 …   ↦   2  b₀ 0 0 … 0 1 …
```

— the marker becomes a `2` (so the returning sweep passes over it: the marker is
consumed), the lowest digit `b₀` is left untouched, and the digit string *above*
`b₀` is incremented by one.  In terms of the value of the region counter
(`binValue`, least significant digit first) the event adds exactly `2`:
`binValue_marker_increment`.

This is the mechanism behind the empirical law recorded in `ANALYSIS.md` §5.6
(`gap = 2·log₂ v + c`, cascades at `v ≈ C·4^k`): the region really is a binary
counter at two cells per digit, and it is driven by the markers that the outward
passes leave behind.
-/

namespace TM2x5

/-- A binary digit as a pair of tape cells: `4 4` is `1`, `4 2` is `0`. -/
def binPair (b : Bool) : List Sym :=
  if b then [(4 : Sym), (4 : Sym)] else [(4 : Sym), (2 : Sym)]

/-- A binary word, least significant digit first, written on the tape at two
cells per digit. -/
def binWord (bs : List Bool) : List Sym := (bs.map binPair).flatten

@[simp] theorem binWord_nil : binWord [] = [] := rfl

@[simp] theorem binWord_cons (b : Bool) (bs : List Bool) :
    binWord (b :: bs) = binPair b ++ binWord bs := by
  simp [binWord]

@[simp] theorem binWord_append (bs cs : List Bool) :
    binWord (bs ++ cs) = binWord bs ++ binWord cs := by
  simp [binWord]

/-- The value of a binary word, least significant digit first. -/
def binValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * binValue bs

/-- A block of `k` digits `0` on the tape is unchanged by moving one of its
pairs from one end to the other. -/
theorem binWord_zeros_snoc : ∀ k : ℕ,
    binWord (List.replicate k false) ++ [(4 : Sym), (2 : Sym)] =
      (4 : Sym) :: (2 : Sym) :: binWord (List.replicate k false) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : binWord (List.replicate (k + 1) false) =
        (4 : Sym) :: (2 : Sym) :: binWord (List.replicate k false) := by
      simp [List.replicate_succ, binPair]
    rw [h]
    simp only [List.cons_append, ih]

/-! ## The two auxiliary words

`twoZeros k` is what the outward pass writes over `k` digit pairs (`2 0` for
each of them); `zeroTwos k` is the same word reversed, i.e. the way it looks in
the left context of the head. -/

def twoZeros : ℕ → List Sym
  | 0 => []
  | k + 1 => (2 : Sym) :: (0 : Sym) :: twoZeros k

def zeroTwos : ℕ → List Sym
  | 0 => []
  | k + 1 => (0 : Sym) :: (2 : Sym) :: zeroTwos k

theorem zeroTwos_snoc : ∀ k : ℕ,
    zeroTwos k ++ [(0 : Sym), (2 : Sym)] = zeroTwos (k + 1) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simpa [zeroTwos] using congrArg (fun u => (0 : Sym) :: (2 : Sym) :: u) ih

theorem reverse_twoZeros : ∀ k : ℕ, (twoZeros k).reverse = zeroTwos k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((2 : Sym) :: (0 : Sym) :: twoZeros k).reverse = zeroTwos (k + 1)
    simp only [List.reverse_cons, List.append_assoc, ih]
    simpa using zeroTwos_snoc k

theorem length_zeroTwos : ∀ k : ℕ, (zeroTwos k).length = 2 * k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [zeroTwos, ih]; omega

theorem zeroTwos_mem : ∀ (k : ℕ), ∀ s ∈ zeroTwos k, s = 0 ∨ s = 2 := by
  intro k
  induction k with
  | zero => simp [zeroTwos]
  | succ k ih =>
    intro s hs
    rcases List.mem_cons.mp hs with h | hs'
    · exact Or.inl h
    · rcases List.mem_cons.mp hs' with h | hs''
      · exact Or.inr h
      · exact ih s hs''

/-- The return sweep turns the word the pass wrote over a block of digits back
into a block of digits `0`. -/
theorem map_sweepSym_zeroTwos : ∀ k : ℕ,
    ((zeroTwos k).map sweepSym).reverse = binWord (List.replicate k false) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs0 : sweepSym 0 = (2 : Sym) := rfl
    have hs2 : sweepSym 2 = (4 : Sym) := rfl
    show (((0 : Sym) :: (2 : Sym) :: zeroTwos k).map sweepSym).reverse = _
    simp only [List.map_cons, hs0, hs2, List.reverse_cons, List.append_assoc, ih]
    have h : binWord (List.replicate (k + 1) false) =
        (4 : Sym) :: (2 : Sym) :: binWord (List.replicate k false) := by
      simp [List.replicate_succ, binPair]
    rw [h]
    simpa using binWord_zeros_snoc k

/-! ## The outward half of the event -/

/-- The pass over a block of `1` digits: each pair `4 4` is rewritten as `2 0`
and the phase stays `0`, two steps per digit. -/
theorem out_ones : ∀ k : ℕ,
    Out 0 (binWord (List.replicate k true)) 0 (twoZeros k) (2 * k) := by
  intro k
  induction k with
  | zero => exact Out.nil 0
  | succ k ih =>
    have h : Out 0 ((4 : Sym) :: (4 : Sym) :: binWord (List.replicate k true)) 0
        ((2 : Sym) :: (0 : Sym) :: twoZeros k) (2 * k + 2) := Out.four_four ih
    have hw : binWord (List.replicate (k + 1) true) =
        (4 : Sym) :: (4 : Sym) :: binWord (List.replicate k true) := by
      simp [List.replicate_succ, binPair]
    rw [hw, show 2 * (k + 1) = 2 * k + 2 by ring]
    exact h

/-- The pass over the lowest digit and the carry chain above it.  A `0` in the
lowest position is crossed by a bounce, which rewrites the marker `4` on its
left as a `0`; a `1` is crossed by the plain rule `4 4 ↦ 2 0`, which leaves the
marker alone. -/
theorem out_low_false (k : ℕ) :
    Out 4 (binWord (false :: List.replicate k true)) 0 (twoZeros (k + 1)) (2 * k + 6) := by
  have h : Out 4 ((4 : Sym) :: (2 : Sym) :: binWord (List.replicate k true)) 0
      ((2 : Sym) :: (0 : Sym) :: twoZeros k) (2 * k + 6) :=
    Out.four_two_of_four (out_ones k)
  simpa [binPair, twoZeros] using h

/-- The same for a lowest digit `1`: the pair `4 4` is crossed by the plain
rule, which leaves the marker alone. -/
theorem out_low_true (k : ℕ) :
    Out 4 (binWord (true :: List.replicate k true)) 4 (twoZeros (k + 1)) (2 * k + 2) := by
  have h : Out 4 ((4 : Sym) :: (4 : Sym) :: binWord (List.replicate k true)) 4
      ((2 : Sym) :: (0 : Sym) :: twoZeros k) (2 * k + 2) :=
    Out.four_four (out_ones k)
  simpa [binPair, twoZeros] using h

/-! ## The whole event -/

/-- Chaining two runs: the cheap way to compose the macroscopic rules without
rewriting inside the goal. -/
theorem iter_trans {m n : ℕ} {x y z : Option Cfg} (h1 : iter m x = y) (h2 : iter n y = z) :
    iter (m + n) x = z := by rw [iter_add, h1, h2]

/-- **The binary increment.**  The head, sweeping left in state `B`, meets a
marker `3`; to the right of the marker stands the region counter, whose lowest
digit is `b₀`, followed by a carry chain of `k` digits `1` and then a digit `0`.

After exactly `4k + 13` steps the head is back in state `B` on the cell to the
left of the marker, the marker has become a `2`, the lowest digit is unchanged,
the `k` digits `1` have become `0` and the digit `0` above them has become `1`:
the region counter has been incremented above its lowest digit, and everything
further right is untouched. -/
theorem marker_increment (b0 : Bool) (k : ℕ) (a : Sym) (l r : List Sym) :
    iter (4 * k + 13)
        (some ⟨St.B, a :: l, 3,
          binWord (b0 :: (List.replicate k true ++ [false])) ++ r⟩) =
      some ⟨St.B, l, a,
        (2 : Sym) :: binWord (b0 :: (List.replicate k false ++ [true])) ++ r⟩ := by
  have hs0 : sweepSym 0 = (2 : Sym) := rfl
  have hs2 : sweepSym 2 = (4 : Sym) := rfl
  have hz : zeroTwos (k + 1) = (0 : Sym) :: (2 : Sym) :: zeroTwos k := rfl
  have hsnoc := binWord_zeros_snoc k
  cases b0 with
  | false =>
    -- the tape to the right of the marker, split at the stopping digit
    have hsplit : binWord (false :: (List.replicate k true ++ [false])) ++ r =
        binWord (false :: List.replicate k true) ++ (4 : Sym) :: (2 : Sym) :: r := by
      simp [binPair]
    -- step 1: the marker is rewritten as a `4` and the head goes right
    have h1 : iter 1 (some (⟨St.B, a :: l, 3,
          binWord (false :: List.replicate k true) ++ (4 : Sym) :: (2 : Sym) :: r⟩ : Cfg)) =
        some (onFirst St.A ((4 : Sym) :: a :: l)
          (binWord (false :: List.replicate k true) ++ (4 : Sym) :: (2 : Sym) :: r)) := by
      cases hb : binWord (false :: List.replicate k true) with
      | nil => simp [binPair] at hb
      | cons x xs => rfl
    -- step 2: the outward pass, which rewrites the marker as a `0`
    have h2 := out_cross (out_low_false k) (a :: l) ((4 : Sym) :: (2 : Sym) :: r)
    rw [reverse_twoZeros, hz] at h2
    simp only [List.cons_append, onFirst_cons] at h2
    -- step 3: the turn at the stopping digit
    have h3 := A_turn (0 : Sym) (Or.inl rfl) (2 : Sym) (zeroTwos k ++ (0 : Sym) :: a :: l) r
    -- step 4: the return sweep back to the marker
    have h4 := B_sweep (zeroTwos k) (zeroTwos_mem k) (2 : Sym) (Or.inr rfl) (0 : Sym) (a :: l)
      (sweepSym 0 :: (4 : Sym) :: (4 : Sym) :: r)
    rw [map_sweepSym_zeroTwos, length_zeroTwos] at h4
    -- step 5: the marker, now a `0`, is swept over as well, and the head is home
    have h5 : iter 1 (some (⟨St.B, a :: l, 0,
          binWord (List.replicate k false) ++ sweepSym 2 :: sweepSym 0 ::
            (4 : Sym) :: (4 : Sym) :: r⟩ : Cfg)) =
        some ⟨St.B, l, a, (2 : Sym) :: (binWord (List.replicate k false) ++
          sweepSym 2 :: sweepSym 0 :: (4 : Sym) :: (4 : Sym) :: r)⟩ := rfl
    have hcost : 4 * k + 13 = 1 + ((2 * k + 6) + (4 + ((2 * k + 1) + 1))) := by ring
    have hout : binWord (List.replicate k false) ++ (4 : Sym) :: (2 : Sym) ::
        (4 : Sym) :: (4 : Sym) :: r =
        binWord (false :: (List.replicate k false ++ [true])) ++ r := by
      calc binWord (List.replicate k false) ++ (4 : Sym) :: (2 : Sym) ::
            (4 : Sym) :: (4 : Sym) :: r
          = (binWord (List.replicate k false) ++ [(4 : Sym), (2 : Sym)]) ++
              (4 : Sym) :: (4 : Sym) :: r := by simp
        _ = ((4 : Sym) :: (2 : Sym) :: binWord (List.replicate k false)) ++
              (4 : Sym) :: (4 : Sym) :: r := by rw [hsnoc]
        _ = _ := by simp [binPair]
    have hall := iter_trans h1 (iter_trans h2 (iter_trans h3 (iter_trans h4 h5)))
    rw [← hcost, ← hsplit, hs0, hs2, hout] at hall
    exact hall
  | true =>
    have hsplit : binWord (true :: (List.replicate k true ++ [false])) ++ r =
        binWord (true :: List.replicate k true) ++ (4 : Sym) :: (2 : Sym) :: r := by
      simp [binPair]
    have h1 : iter 1 (some (⟨St.B, a :: l, 3,
          binWord (true :: List.replicate k true) ++ (4 : Sym) :: (2 : Sym) :: r⟩ : Cfg)) =
        some (onFirst St.A ((4 : Sym) :: a :: l)
          (binWord (true :: List.replicate k true) ++ (4 : Sym) :: (2 : Sym) :: r)) := by
      cases hb : binWord (true :: List.replicate k true) with
      | nil => simp [binPair] at hb
      | cons x xs => rfl
    -- this time the pass leaves the marker holding a `4`
    have h2 := out_cross (out_low_true k) (a :: l) ((4 : Sym) :: (2 : Sym) :: r)
    rw [reverse_twoZeros, hz] at h2
    simp only [List.cons_append, onFirst_cons] at h2
    have h3 := A_turn (0 : Sym) (Or.inl rfl) (2 : Sym) (zeroTwos k ++ (4 : Sym) :: a :: l) r
    have h4 := B_sweep (zeroTwos k) (zeroTwos_mem k) (2 : Sym) (Or.inr rfl) (4 : Sym) (a :: l)
      (sweepSym 0 :: (4 : Sym) :: (4 : Sym) :: r)
    rw [map_sweepSym_zeroTwos, length_zeroTwos] at h4
    -- the lowest digit, seen again from the left, is moved to the front
    have hmove : binWord (List.replicate k false) ++ (4 : Sym) :: (2 : Sym) ::
        (4 : Sym) :: (4 : Sym) :: r =
        (4 : Sym) :: (2 : Sym) :: (binWord (List.replicate k false) ++
          (4 : Sym) :: (4 : Sym) :: r) := by
      calc binWord (List.replicate k false) ++ (4 : Sym) :: (2 : Sym) ::
            (4 : Sym) :: (4 : Sym) :: r
          = (binWord (List.replicate k false) ++ [(4 : Sym), (2 : Sym)]) ++
              (4 : Sym) :: (4 : Sym) :: r := by simp
        _ = ((4 : Sym) :: (2 : Sym) :: binWord (List.replicate k false)) ++
              (4 : Sym) :: (4 : Sym) :: r := by rw [hsnoc]
        _ = _ := by simp
    rw [hs0, hs2, hmove] at h4
    -- step 5: the sweep stops on the marker, which still holds a `4`, so the
    -- head turns round once more
    have h5 : iter 1 (some (⟨St.B, a :: l, 4, (4 : Sym) :: (2 : Sym) ::
          (binWord (List.replicate k false) ++ (4 : Sym) :: (4 : Sym) :: r)⟩ : Cfg)) =
        some ⟨St.A, (0 : Sym) :: a :: l, 4, (2 : Sym) ::
          (binWord (List.replicate k false) ++ (4 : Sym) :: (4 : Sym) :: r)⟩ := rfl
    -- step 6: it flips the lowest digit back to `1` and comes home
    have h6 := A_turn (0 : Sym) (Or.inl rfl) a l
      (binWord (List.replicate k false) ++ (4 : Sym) :: (4 : Sym) :: r)
    have hcost : 4 * k + 13 = 1 + ((2 * k + 2) + (4 + ((2 * k + 1) + (1 + 4)))) := by ring
    have hout : (4 : Sym) :: (4 : Sym) :: (binWord (List.replicate k false) ++
        (4 : Sym) :: (4 : Sym) :: r) =
        binWord (true :: (List.replicate k false ++ [true])) ++ r := by
      simp [binPair]
    have hall := iter_trans h1 (iter_trans h2 (iter_trans h3
      (iter_trans h4 (iter_trans h5 h6))))
    rw [← hcost, ← hsplit, hs0, hout] at hall
    exact hall

/-- **The marker shift.**  The other thing that can happen at a marker: if the
cell to its right holds a `2` rather than the start of a digit pair, then two
steps (`B3 → 4RA`, `A2 → 3RA`) leave a `4` where the marker was, put a new
marker one cell further right, and send the head on as an outward pass in phase
`3`.

Together with `marker_increment` this covers every marker event: the sweep
either increments the region counter or shifts the marker one cell to the right.
The shift also leaves a cascade-killing `4` behind: a `4` stops a cascade dead
(`cascade_P_four_stops`), so every marker that sits on a `2` contributes one of
the `4`s that a returning cascade can run into. -/
theorem marker_shift (a : Sym) (l xs : List Sym) :
    iter 2 (some ⟨St.B, a :: l, 3, (2 : Sym) :: xs⟩) =
      some (onFirst St.A ((3 : Sym) :: (4 : Sym) :: a :: l) xs) := by
  cases xs <;> rfl

/-- The arithmetic content of `marker_increment`: the event adds exactly `2` to
the value of the region counter (the lowest digit is untouched and the digits
above it go up by one). -/
theorem binValue_marker_increment (b0 : Bool) (k : ℕ) (bs : List Bool) :
    binValue (b0 :: (List.replicate k false ++ true :: bs)) =
      binValue (b0 :: (List.replicate k true ++ false :: bs)) + 2 := by
  have key : ∀ k : ℕ, binValue (List.replicate k false ++ true :: bs) =
      binValue (List.replicate k true ++ false :: bs) + 1 := by
    intro k
    induction k with
    | zero => simp [binValue]; omega
    | succ k ih =>
      simp [List.replicate_succ, binValue, ih]
      omega
  cases b0 <;> simp [binValue, key] <;> omega

/-- The tape form of the increment with an arbitrary further digit string `bs`
above the carry chain: the digits above the carry chain, and everything to the
right of them, are untouched. -/
theorem marker_increment_words (b0 : Bool) (k : ℕ) (bs : List Bool) (a : Sym)
    (l r : List Sym) :
    iter (4 * k + 13)
        (some ⟨St.B, a :: l, 3,
          binWord (b0 :: (List.replicate k true ++ false :: bs)) ++ r⟩) =
      some ⟨St.B, l, a,
        (2 : Sym) :: binWord (b0 :: (List.replicate k false ++ true :: bs)) ++ r⟩ := by
  have h := marker_increment b0 k a l (binWord bs ++ r)
  have e1 : binWord (b0 :: (List.replicate k true ++ [false])) ++ (binWord bs ++ r) =
      binWord (b0 :: (List.replicate k true ++ false :: bs)) ++ r := by
    simp [List.append_assoc]
  have e2 : binWord (b0 :: (List.replicate k false ++ [true])) ++ (binWord bs ++ r) =
      binWord (b0 :: (List.replicate k false ++ true :: bs)) ++ r := by
    simp [List.append_assoc]
  rw [e1] at h
  rw [h]
  simp [List.append_assoc]

end TM2x5
