import RequestProject.Machine

/-!
# Binary counter, ternary digits and the basic moves of a cycle

Bits are stored in cell pairs, least significant pair next to the right end of the binary
counter.  Reading a pair from the right (as the leftward-moving head does), bit `0` is the
pair `0,1` and bit `1` is the pair `1,1`.  Ternary digits are cell pairs read left to
right: `0 ↦ 24`, `1 ↦ 11`, `2 ↦ 21`.
-/

namespace TM25

/-! ### Encodings -/

/-- Encoding of a bit list (least significant bit first) as seen from the right,
nearest cell first. -/
def encBits (bs : List Bool) : List Sym :=
  bs.flatMap (fun b => [if b then 1 else 0, 1])

@[simp] theorem encBits_cons (b : Bool) (bs : List Bool) :
    encBits (b :: bs) = (if b then 1 else 0) :: 1 :: encBits bs := rfl

theorem encBits_append (a b : List Bool) : encBits (a ++ b) = encBits a ++ encBits b := by
  simp [encBits]

theorem encBits_replicate_true (k : Nat) :
    encBits (List.replicate k true) = List.replicate (2 * k) 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, encBits_cons, ih, replicate_two_mul_succ]; rfl

theorem encBits_replicate_false (k : Nat) :
    encBits (List.replicate k false) = (List.replicate k [(0 : Sym), 1]).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, encBits_cons, ih]; simp [List.replicate_succ]

/-- Encoding of one ternary digit as a pair of cells (left to right). -/
def encDigit : Fin 3 → List Sym
  | 0 => [2, 4]
  | 1 => [1, 1]
  | 2 => [2, 1]

/-- Encoding of a ternary counter, least significant digit first (leftmost). -/
def encT (ds : List (Fin 3)) : List Sym := ds.flatMap encDigit

@[simp] theorem encT_cons (d : Fin 3) (ds : List (Fin 3)) :
    encT (d :: ds) = encDigit d ++ encT ds := rfl

/-! ### Configurations -/

/-- The "event" configuration: head in state `A` on a blank cell at the left end of the
used tape, followed by `m` cells `2` and then the list `R`. -/
def event (m : Nat) (R : List Sym) : Cfg := ⟨.A, [], 0 :: List.replicate m 2 ++ R⟩

/-- The binary counter with bits `bs`, head (state `A`) on a blocking `4`. -/
def blockedCfg (bs : List Bool) (X : List Sym) : Cfg :=
  ⟨.A, 1 :: encBits bs ++ [1], 4 :: X⟩

/-- Aligned configuration: binary counter `bs` (least significant bit first), head in
state `B` (moving right) on the lowest ternary cell `d0`, followed by `T`. -/
def alignedCfg (bs : List Bool) (d0 : Sym) (T : List Sym) : Cfg :=
  ⟨.B, encBits bs ++ [1], d0 :: T⟩

/-- Head in state `A` moving right, just past the lone last cell of a counter region. -/
def midCfg (bs : List Bool) (R : List Sym) : Cfg := ⟨.A, 1 :: encBits bs ++ [1], R⟩

/-- Head in state `B` moving right, just past the lowest pair of the counter region. -/
def bCfg (bs : List Bool) (R : List Sym) : Cfg := ⟨.B, encBits bs ++ [1], R⟩

/-- `Carry X Y`: a carry (state `A`, moving right) entering the tape segment `X` turns it
into `Y` and comes back (state `A`, moving left). -/
def Carry (X Y : List Sym) : Prop :=
  ∀ (x : Sym) (L : List Sym), Reaches ⟨.A, x :: L, X⟩ ⟨.A, L, x :: Y⟩

/-! ### Blocked counting -/

theorem blocked_inc (k : Nat) (rest : List Bool) (X : List Sym) :
    Reaches (blockedCfg (List.replicate k true ++ false :: rest) X)
      (blockedCfg (List.replicate k false ++ true :: rest) X) := by
  unfold blockedCfg
  refine Reaches.head (b := ⟨.A, encBits (List.replicate k true ++ false :: rest) ++ [1],
    1 :: 4 :: X⟩) (by simp [step, delta]) ?_
  rw [encBits_append, encBits_replicate_true, encBits_cons]
  simp only [List.append_assoc, List.cons_append, Bool.false_eq_true, if_false]
  refine (sweep_left_ones (2 * k) 0 _ _).trans ?_
  refine Reaches.head (b := ⟨.B, 1 :: 1 :: (encBits rest ++ [1]),
    List.replicate (2 * k + 1) 2 ++ 4 :: X⟩) (by simp [step, delta]) ?_
  rw [List.replicate_succ', List.append_assoc]
  refine (sweep_right k _ _).trans ?_
  refine Reaches.single ?_
  simp [step, delta, encBits_append, encBits_replicate_false]

/-- A full count of the low `n` bits (the higher bits `h` are untouched). -/
theorem blocked_count (n : Nat) (h : List Bool) (X : List Sym) :
    Reaches (blockedCfg (List.replicate n false ++ h) X)
      (blockedCfg (List.replicate n true ++ h) X) := by
  induction n generalizing h with
  | zero => exact Reaches.refl _
  | succ n ih =>
    rw [List.replicate_succ', List.append_assoc]
    refine (ih _).trans ?_
    refine (blocked_inc n h X).trans ?_
    refine (ih _).trans (Reaches.of_eq ?_)
    rw [List.replicate_succ', List.append_assoc]; rfl

theorem blocked_overflow (p : Nat) (X : List Sym) :
    Reaches (blockedCfg (List.replicate p true) X) (event (2 * p + 2) (4 :: X)) := by
  unfold event blockedCfg
  refine Reaches.head (b := ⟨.A, encBits (List.replicate p true) ++ [1], 1 :: 4 :: X⟩)
    (by simp [step, delta]) ?_
  rw [encBits_replicate_true]
  refine (sweep_left_ones (2 * p) 1 [] _).trans ?_
  refine Reaches.single ?_
  simp [step, delta, List.replicate_succ]

/-- Counting the binary counter up to all ones, starting from any value. -/
theorem blocked_to_top (X : List Sym) : ∀ (lo : List Bool) (n : Nat) (hi : List Bool),
    Reaches (blockedCfg (List.replicate n true ++ lo ++ hi) X)
      (blockedCfg (List.replicate n true ++ List.replicate lo.length true ++ hi) X)
  | [], n, hi => by simpa using Reaches.refl _
  | true :: lo, n, hi => by
    have := blocked_to_top X lo (n + 1) hi
    refine (Reaches.of_eq ?_).trans (this.trans (Reaches.of_eq ?_))
    · simp [List.replicate_succ', List.append_assoc]
    · simp only [List.length_cons, List.replicate_succ', List.append_assoc]
      simp [replicate_append_cons]
  | false :: lo, n, hi => by
    refine (Reaches.of_eq ?_).trans ((blocked_inc n (lo ++ hi) X).trans ?_)
    · simp
    refine (blocked_count n (true :: lo ++ hi) X).trans ?_
    have := blocked_to_top X lo (n + 1) hi
    refine (Reaches.of_eq ?_).trans (this.trans (Reaches.of_eq ?_))
    · simp [List.replicate_succ', List.append_assoc]
    · simp only [List.length_cons, List.replicate_succ', List.append_assoc]
      simp [replicate_append_cons]

/-! ### Misaligned reading: absorbing a `1` -/

theorem mis_start (p : Nat) (R : List Sym) :
    Reaches (event (2 * p + 1) R) (midCfg (List.replicate p false) R) := by
  unfold event midCfg
  tm_step
  rw [List.replicate_succ', List.append_assoc]
  refine (sweep_right p _ _).trans ?_
  tm_step
  refine Reaches.of_eq ?_
  simp [encBits_replicate_false]

/-- A `1` met by `A` right after the counter region is absorbed: it becomes the second
cell of a new lowest bit pair, and the counter (now one bit longer) is incremented. -/
theorem absorb_one (j : Nat) (rest : List Bool) (X : List Sym) :
    Reaches (midCfg (List.replicate j true ++ false :: rest) (1 :: X))
      (bCfg (false :: List.replicate j false ++ true :: rest) X) := by
  unfold midCfg bCfg
  simp only [encBits_append, encBits_replicate_true, encBits_cons, Bool.false_eq_true,
    if_false, List.append_assoc, List.cons_append]
  have e := sweep_left_ones (2 * j + 1) 0 (1 :: (encBits rest ++ [1])) X
  simp only [List.replicate_succ, List.cons_append] at e
  refine e.trans ?_
  tm_step
  have e2 := sweep_right (j + 1) (1 :: 1 :: (encBits rest ++ [1])) X
  simp only [replicate_two_mul_succ, List.cons_append] at e2
  refine (Reaches.of_eq ?_).trans (e2.trans (Reaches.of_eq ?_))
  · simp
  · simp [encBits_replicate_false, List.replicate_succ]

/-! ### Aligned rounds -/

/-- `d0 = 4`, second lowest bit `0`: the counter gains `4`, `d0` becomes `1`. -/
theorem aligned_step4a (k : Nat) (rest : List Bool) (T : List Sym) :
    Reaches (alignedCfg (false :: false :: List.replicate k true ++ false :: rest) 4 T)
      (alignedCfg (List.replicate (k + 2) false ++ true :: rest) 1 T) := by
  unfold alignedCfg
  simp only [encBits_cons, encBits_append, encBits_replicate_true, Bool.false_eq_true,
    if_false, List.cons_append, List.append_assoc]
  tm_step; tm_step; tm_step; tm_step; tm_step; tm_step
  have e := sweep_left_ones (2 * k + 2) 0 (1 :: (encBits rest ++ [1])) (2 :: 1 :: T)
  simp only [List.replicate_succ, List.cons_append] at e
  refine e.trans ?_
  tm_step
  have e2 := sweep_right (k + 2) (1 :: 1 :: (encBits rest ++ [1])) (1 :: T)
  simp only [replicate_two_mul_succ, List.cons_append] at e2
  refine (Reaches.of_eq ?_).trans (e2.trans (Reaches.of_eq ?_))
  · simp [replicate_append_cons]
  · simp [encBits_replicate_false, List.replicate_succ]

/-- `d0 = 4`, second lowest bit `1`: the counter gains `4`, `d0` becomes `1`. -/
theorem aligned_step4b (k : Nat) (rest : List Bool) (T : List Sym) :
    Reaches (alignedCfg (false :: true :: List.replicate k true ++ false :: rest) 4 T)
      (alignedCfg (false :: true :: List.replicate k false ++ true :: rest) 1 T) := by
  unfold alignedCfg
  simp only [encBits_cons, encBits_append, encBits_replicate_true, Bool.false_eq_true,
    if_false, if_true, List.cons_append, List.append_assoc]
  tm_step; tm_step; tm_step
  have e := sweep_left_ones (2 * k + 1) 0 (1 :: (encBits rest ++ [1])) (2 :: 1 :: 1 :: T)
  simp only [List.replicate_succ, List.cons_append] at e
  refine e.trans ?_
  tm_step
  have e2 := sweep_right (k + 1) (1 :: 1 :: (encBits rest ++ [1])) (2 :: 1 :: 1 :: T)
  simp only [replicate_two_mul_succ, List.cons_append, List.replicate_succ,
    List.flatten_cons, List.nil_append] at e2
  refine (Reaches.of_eq ?_).trans (e2.trans ?_)
  · simp [replicate_append_cons]
  tm_step; tm_step; tm_step; tm_step; tm_step; tm_step
  refine Reaches.of_eq ?_
  simp [encBits_replicate_false]

theorem aligned_ovf4a (k : Nat) (T : List Sym) :
    Reaches (alignedCfg (false :: false :: List.replicate k true) 4 T)
      (event (2 * k + 5) (1 :: T)) := by
  unfold alignedCfg event
  simp only [encBits_cons, encBits_replicate_true, Bool.false_eq_true,
    if_false, List.cons_append]
  tm_step; tm_step; tm_step; tm_step; tm_step; tm_step
  have e := sweep_left_ones (2 * k + 2) 1 [] (2 :: 1 :: T)
  simp only [List.replicate_succ, List.cons_append] at e
  refine (Reaches.of_eq ?_).trans (e.trans ?_)
  · simp [replicate_append_cons]
  tm_step
  refine Reaches.of_eq ?_
  simp [List.replicate_succ, replicate_append_cons]

theorem aligned_ovf4b (k : Nat) (T : List Sym) :
    Reaches (alignedCfg (false :: true :: List.replicate k true) 4 T)
      (event (2 * k + 4) (1 :: 1 :: T)) := by
  unfold alignedCfg event
  simp only [encBits_cons, encBits_replicate_true, Bool.false_eq_true,
    if_false, if_true, List.cons_append]
  tm_step; tm_step; tm_step
  have e := sweep_left_ones (2 * k + 1) 1 [] (2 :: 1 :: 1 :: T)
  simp only [List.replicate_succ, List.cons_append] at e
  refine (Reaches.of_eq ?_).trans (e.trans ?_)
  · simp [replicate_append_cons]
  tm_step
  refine Reaches.of_eq ?_
  simp [List.replicate_succ, replicate_append_cons]

/-- `d0 = 1`: the lowest cell becomes `4` and one carry is sent into the segment `T`. -/
theorem aligned_step1_gen (k : Nat) (rest : List Bool) {T T' : List Sym} (hc : Carry T T') :
    Reaches (alignedCfg (false :: List.replicate k true ++ false :: rest) 1 T)
      (alignedCfg (List.replicate (k + 1) false ++ true :: rest) 4 T') := by
  unfold alignedCfg
  simp only [encBits_cons, encBits_append, encBits_replicate_true, Bool.false_eq_true,
    if_false, List.cons_append, List.append_assoc]
  tm_step; tm_step; tm_step
  refine (hc 4 _).trans ?_
  tm_step
  have e := sweep_left_ones (2 * k + 1) 0 (1 :: (encBits rest ++ [1])) (4 :: T')
  simp only [List.replicate_succ, List.cons_append] at e
  refine e.trans ?_
  tm_step
  have e2 := sweep_right (k + 1) (1 :: 1 :: (encBits rest ++ [1])) (4 :: T')
  rw [replicate_two_mul_succ] at e2
  refine (by simpa using e2 : Reaches _ _).trans (Reaches.of_eq ?_)
  simp [encBits_replicate_false]

/-- Overflow during a `d0 = 1` step: the lowest cell becomes `4`, one last carry is sent. -/
theorem aligned_ovf1_gen (q : Nat) {T T' : List Sym} (hc : Carry T T') :
    Reaches (alignedCfg (false :: List.replicate q true) 1 T) (event (2 * q + 3) (4 :: T')) := by
  unfold alignedCfg event
  simp only [encBits_cons, encBits_replicate_true, Bool.false_eq_true, if_false,
    List.cons_append]
  tm_step; tm_step; tm_step
  refine (hc 4 _).trans ?_
  tm_step
  have e := sweep_left_ones (2 * q + 1) 1 [] (4 :: T')
  simp only [List.replicate_succ, List.cons_append] at e
  refine (Reaches.of_eq ?_).trans (e.trans ?_)
  · simp [replicate_append_cons]
  tm_step
  refine Reaches.of_eq ?_
  simp [List.replicate_succ]

/-! ### Counter values as natural numbers -/

/-- The `q`-bit binary expansion of `n`, least significant bit first. -/
def bitsOf : Nat → Nat → List Bool
  | 0, _ => []
  | q + 1, n => (n % 2 == 1) :: bitsOf q (n / 2)

theorem bitsOf_even {q n : Nat} (h : n % 2 = 0) :
    bitsOf (q + 1) n = false :: bitsOf q (n / 2) := by
  simp [bitsOf, h]

theorem bitsOf_odd {q n : Nat} (h : n % 2 = 1) :
    bitsOf (q + 1) n = true :: bitsOf q (n / 2) := by
  simp [bitsOf, h]

theorem bitsOf_zero (q : Nat) : bitsOf q 0 = List.replicate q false := by
  induction q with
  | zero => rfl
  | succ q ih => simp [bitsOf, ih, List.replicate_succ]

theorem bitsOf_all (q : Nat) : bitsOf q (2 ^ q - 1) = List.replicate q true := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have := Nat.one_le_two_pow (n := q)
    have e : 2 ^ (q + 1) = 2 ^ q * 2 := Nat.pow_succ ..
    rw [bitsOf_odd (by omega), show (2 ^ (q + 1) - 1) / 2 = 2 ^ q - 1 by omega, ih,
      List.replicate_succ]

theorem length_bitsOf : ∀ n v, (bitsOf n v).length = n
  | 0, _ => rfl
  | n + 1, v => by simp [bitsOf, length_bitsOf n]

/-- Binary increment in terms of bit lists. -/
theorem bitsOf_shape : ∀ (q n : Nat), n + 1 < 2 ^ q →
    ∃ k rest, bitsOf q n = List.replicate k true ++ false :: rest ∧
      bitsOf q (n + 1) = List.replicate k false ++ true :: rest
  | 0, n, h => by simp at h
  | q + 1, n, h => by
    have e : 2 ^ (q + 1) = 2 ^ q * 2 := Nat.pow_succ ..
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · refine ⟨0, bitsOf q (n / 2), ?_, ?_⟩
      · simp [bitsOf_even hn]
      · simp [bitsOf_odd (show (n + 1) % 2 = 1 by omega), show (n + 1) / 2 = n / 2 by omega]
    · obtain ⟨k, rest, e1, e2⟩ := bitsOf_shape q (n / 2) (by omega)
      refine ⟨k + 1, rest, ?_, ?_⟩
      · rw [bitsOf_odd hn, e1]; simp [List.replicate_succ]
      · rw [bitsOf_even (show (n + 1) % 2 = 0 by omega), show (n + 1) / 2 = n / 2 + 1 by omega,
          e2]
        simp [List.replicate_succ]

theorem bitsOf_top_minus_two (q : Nat) :
    bitsOf (q + 2) (2 ^ (q + 2) - 2) = false :: List.replicate (q + 1) true := by
  have e : 2 ^ (q + 2) = 2 ^ (q + 1) * 2 := Nat.pow_succ ..
  have := Nat.one_le_two_pow (n := q + 1)
  rw [bitsOf_even (by omega), show (2 ^ (q + 2) - 2) / 2 = 2 ^ (q + 1) - 1 by omega, bitsOf_all]

theorem bitsOf_top_minus_four (q : Nat) :
    bitsOf (q + 2) (2 ^ (q + 2) - 4) = false :: false :: List.replicate q true := by
  have e : 2 ^ (q + 2) = 2 ^ q * 4 := by rw [Nat.pow_add]
  have := Nat.one_le_two_pow (n := q)
  rw [bitsOf_even (by omega), bitsOf_even (by omega),
    show (2 ^ (q + 2) - 4) / 2 / 2 = 2 ^ q - 1 by omega, bitsOf_all]

/-- `d0 = 4` step with natural-number bookkeeping. -/
theorem aligned_step4_nat {q n : Nat} (T : List Sym) (hn : n % 2 = 0)
    (hlt : n + 4 < 2 ^ (q + 2)) :
    Reaches (alignedCfg (bitsOf (q + 2) n) 4 T)
      (alignedCfg (bitsOf (q + 2) (n + 4)) 1 T) := by
  have hp : 2 ^ (q + 2) = 2 ^ q * 4 := by rw [Nat.pow_add]
  rw [hp] at hlt
  rw [bitsOf_even hn, bitsOf_even (show (n + 4) % 2 = 0 by omega)]
  rcases Nat.mod_two_eq_zero_or_one (n / 2) with ha | ha
  · obtain ⟨k, rest, e1, e2⟩ := bitsOf_shape q (n / 2 / 2) (by omega)
    rw [bitsOf_even ha, bitsOf_even (show (n + 4) / 2 % 2 = 0 by omega),
      show (n + 4) / 2 / 2 = n / 2 / 2 + 1 by omega, e1, e2]
    refine (aligned_step4a k rest T).trans (Reaches.of_eq ?_)
    simp [List.replicate_succ]
  · obtain ⟨k, rest, e1, e2⟩ := bitsOf_shape q (n / 2 / 2) (by omega)
    rw [bitsOf_odd ha, bitsOf_odd (show (n + 4) / 2 % 2 = 1 by omega),
      show (n + 4) / 2 / 2 = n / 2 / 2 + 1 by omega, e1, e2]
    exact aligned_step4b k rest T

/-- `d0 = 1` step with natural-number bookkeeping. -/
theorem aligned_step1_gen_nat {q n : Nat} {T T' : List Sym} (hc : Carry T T') (hn : n % 2 = 0)
    (hlt : n + 2 < 2 ^ (q + 1)) :
    Reaches (alignedCfg (bitsOf (q + 1) n) 1 T)
      (alignedCfg (bitsOf (q + 1) (n + 2)) 4 T') := by
  have e : 2 ^ (q + 1) = 2 ^ q * 2 := Nat.pow_succ ..
  obtain ⟨k, rest, e1, e2⟩ := bitsOf_shape q (n / 2) (by omega)
  rw [bitsOf_even hn, bitsOf_even (show (n + 2) % 2 = 0 by omega),
    show (n + 2) / 2 = n / 2 + 1 by omega, e1, e2]
  refine (aligned_step1_gen k rest hc).trans (Reaches.of_eq ?_)
  simp [List.replicate_succ]

/-- The end of an aligned cycle in which the lowest cell is `4` at counter value `2^n - 6`:
one `d0 = 4` step, then the overflowing `d0 = 1` step with a last carry. -/
theorem aligned_finish (q : Nat) {T T' : List Sym} (hc : Carry T T') :
    Reaches (alignedCfg (bitsOf (q + 3) (2 ^ (q + 3) - 6)) 4 T)
      (event (2 * (q + 3) + 1) (4 :: T')) := by
  have e : 2 ^ (q + 3) = 2 ^ q * 8 := by rw [Nat.pow_add]
  have e2 : 2 ^ (q + 1 + 2) = 2 ^ q * 8 := by rw [Nat.pow_add, Nat.pow_add, Nat.mul_assoc]
  have := Nat.one_le_two_pow (n := q)
  refine (aligned_step4_nat (q := q + 1) (n := 2 ^ (q + 3) - 6) T (by omega)
    (by omega)).trans ?_
  rw [show 2 ^ (q + 3) - 6 + 4 = 2 ^ (q + 1 + 2) - 2 by omega, bitsOf_top_minus_two (q + 1)]
  refine (aligned_ovf1_gen (q + 2) hc).trans (Reaches.of_eq ?_)
  congr 1

end TM25
