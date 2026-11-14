import RequestProject.Cycles

/-!
# Pair-digit counters, multiple carries and a verified macro step

The part of the tape that receives carries during an aligned cycle is read in cell pairs.
The possible pairs (left to right) and their reaction to one carry are:

* `24` → `11`, `11` → `21`, `21` → `24` plus a carry to the right: an ordinary ternary digit
  (`24 = 0`, `11 = 1`, `21 = 2`);
* `12` → `22` (a one-shot pair);
* `22` → `22`, passing **two** carries to the right (a doubler);
* a pair starting with `4` is a wall: carries bounce off it;
* the blank tape behaves like infinitely many digits `1`;
* `14` → `24` (and then acts as a digit `0`).

`carryF T N` computes the effect of `N` carries arithmetically; `carryF_sound` proves it
agrees with the machine.  `macroStep` jumps from one event to the next, and
`macroStep_sound` proves that the machine really gets there.
-/

namespace TM25

/-! ### Single carries -/

theorem carry_wall (Z : List Sym) : Carry (4 :: Z) (4 :: Z) := by
  intro x L; tm_step; exact Reaches.refl _

theorem carry_a (X : List Sym) : Carry (1 :: 2 :: X) (2 :: 2 :: X) := by
  intro x L; tm_step; exact Reaches.refl _

theorem carry_b {X Y W : List Sym} (hX : Carry X Y) (hY : Carry Y W) :
    Carry (2 :: 2 :: X) (2 :: 2 :: W) := by
  intro x L
  tm_step; tm_step
  refine (hX 1 _).trans ?_
  tm_step; tm_step; tm_step
  refine (hY 1 _).trans ?_
  tm_step; tm_step
  exact Reaches.refl _

theorem carry_dig0 (Z : List Sym) : Carry (2 :: 4 :: Z) (1 :: 1 :: Z) := by
  intro x L; tm_step; tm_step; tm_step; exact Reaches.refl _

theorem carry_dig1 (Z : List Sym) : Carry (1 :: 1 :: Z) (2 :: 1 :: Z) := by
  intro x L; tm_step; exact Reaches.refl _

theorem carry_dig2 {Z Z' : List Sym} (h : Carry Z Z') : Carry (2 :: 1 :: Z) (2 :: 4 :: Z') := by
  intro x L
  tm_step; tm_step; tm_step; tm_step
  refine (h 4 _).trans ?_
  tm_step; tm_step
  exact Reaches.refl _

theorem carry_blank : Carry [] [2, 1] := by
  intro x L; tm_step; tm_step; tm_step; exact Reaches.refl _

/-! ### Multiple carries -/

/-- `MC n X Y`: `n` successive carries turn the segment `X` into `Y`. -/
def MC : Nat → List Sym → List Sym → Prop
  | 0, X, Y => X = Y
  | n + 1, X, Y => ∃ U, Carry X U ∧ MC n U Y

theorem MC.one {X Y : List Sym} (h : Carry X Y) : MC 1 X Y := ⟨Y, h, rfl⟩

theorem MC.add : ∀ {a b : Nat} {X U Y : List Sym}, MC a X U → MC b U Y → MC (a + b) X Y
  | 0, b, X, U, Y, h1, h2 => by
    change X = U at h1; subst h1; simpa using h2
  | a + 1, b, X, U, Y, ⟨V, hV, h1⟩, h2 => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    exact ⟨V, hV, MC.add h1 h2⟩

theorem MC.split : ∀ {a b : Nat} {X Y : List Sym}, MC (a + b) X Y → ∃ U, MC a X U ∧ MC b U Y
  | 0, b, X, Y, h => ⟨X, rfl, by simpa using h⟩
  | a + 1, b, X, Y, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega] at h
    obtain ⟨V, hV, h1⟩ := h
    obtain ⟨U, hU1, hU2⟩ := MC.split h1
    exact ⟨U, ⟨V, hV, hU1⟩, hU2⟩

/-- A chain of carries as a sequence. -/
theorem MC.seq : ∀ {n : Nat} {X Y : List Sym}, MC n X Y →
    ∃ f : Nat → List Sym, f 0 = X ∧ f n = Y ∧ ∀ j < n, Carry (f j) (f (j + 1))
  | 0, X, Y, h => ⟨fun _ => X, rfl, h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, X, Y, ⟨U, hU, h⟩ => by
    obtain ⟨f, h0, hn, hf⟩ := MC.seq h
    refine ⟨fun j => if j = 0 then X else f (j - 1), by simp, by simpa using hn, ?_⟩
    intro j hj
    rcases j with _ | j
    · simpa [h0] using hU
    · simpa using hf j (by omega)

/-- The cells of a ternary digit (`0 ↦ 24`, `1 ↦ 11`, otherwise `21`). -/
def dig : Nat → List Sym
  | 0 => [2, 4]
  | 1 => [1, 1]
  | _ => [2, 1]

theorem MC.digit : ∀ (N d : Nat), d < 3 → ∀ {Z Z' : List Sym}, MC ((d + N) / 3) Z Z' →
    MC N (dig d ++ Z) (dig ((d + N) % 3) ++ Z')
  | 0, d, hd, Z, Z', h => by
    rw [Nat.div_eq_of_lt (by omega)] at h
    change Z = Z' at h; subst h
    rw [Nat.add_zero, Nat.mod_eq_of_lt hd]; rfl
  | N + 1, d, hd, Z, Z', h => by
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
    · refine ⟨dig 1 ++ Z, carry_dig0 Z, ?_⟩
      have := MC.digit N 1 (by omega) (Z := Z) (Z' := Z') (by
        rw [show (1 + N) = 0 + (N + 1) by omega]; exact h)
      rwa [show 1 + N = 0 + (N + 1) by omega] at this
    · refine ⟨dig 2 ++ Z, carry_dig1 Z, ?_⟩
      have := MC.digit N 2 (by omega) (Z := Z) (Z' := Z') (by
        rw [show (2 + N) = 1 + (N + 1) by omega]; exact h)
      rwa [show 2 + N = 1 + (N + 1) by omega] at this
    · rw [show (2 + (N + 1)) / 3 = 1 + (0 + N) / 3 by omega] at h
      obtain ⟨U, ⟨V, hV, hVU⟩, hU⟩ := MC.split h
      change V = U at hVU; subst hVU
      refine ⟨dig 0 ++ V, carry_dig2 hV, ?_⟩
      have := MC.digit N 0 (by omega) hU
      rwa [show (0 + N) % 3 = (2 + (N + 1)) % 3 by omega] at this

theorem MC.wall (Z : List Sym) : ∀ N, MC N (4 :: Z) (4 :: Z)
  | 0 => rfl
  | N + 1 => ⟨_, carry_wall Z, MC.wall Z N⟩

theorem MC.dbl : ∀ (N : Nat) {Z Z' : List Sym}, MC (2 * N) Z Z' → MC N (2 :: 2 :: Z) (2 :: 2 :: Z')
  | 0, Z, Z', h => by change Z = Z' at h; subst h; rfl
  | N + 1, Z, Z', h => by
    rw [show 2 * (N + 1) = 2 + 2 * N by omega] at h
    obtain ⟨U, ⟨V, hV, W, hW, hWU⟩, hU⟩ := MC.split h
    change W = U at hWU; subst hWU
    exact ⟨2 :: 2 :: W, carry_b hV hW, MC.dbl N hU⟩

theorem MC.oneTwo (N : Nat) {Z Z' : List Sym} (h : MC (2 * N) Z Z') :
    MC (N + 1) (1 :: 2 :: Z) (2 :: 2 :: Z') := by
  rw [Nat.add_comm]
  exact MC.add (MC.one (carry_a Z)) (MC.dbl N h)

theorem MC.oneFour (N : Nat) {Z Z' : List Sym} (h : MC (N / 3) Z Z') :
    MC (N + 1) (1 :: 4 :: Z) (dig (N % 3) ++ Z') := by
  rw [Nat.add_comm]
  have h2 := MC.digit N 0 (by omega) (Z := Z) (Z' := Z') (by simpa using h)
  rw [Nat.zero_add] at h2
  refine MC.add (MC.one (fun x L => ?_)) h2
  tm_step; exact Reaches.refl _

/-- The blank tape after `N` carries (with fuel `f ≥ N`). -/
def blankF : Nat → Nat → List Sym
  | 0, _ => []
  | f + 1, N => if N = 0 then [] else dig ((N + 1) % 3) ++ blankF f ((N + 1) / 3)

theorem blankF_zero : ∀ f, blankF f 0 = []
  | 0 => rfl
  | _ + 1 => by simp [blankF]

theorem MC.blank : ∀ (f N : Nat), N ≤ f → MC N [] (blankF f N)
  | f, 0, _ => by rw [blankF_zero]; rfl
  | 0, N + 1, h => absurd h (by omega)
  | f + 1, M + 1, h => by
    simp only [blankF, Nat.add_one_ne_zero, if_false]
    refine ⟨[2, 1], carry_blank, ?_⟩
    have := MC.digit M 2 (by omega) (Z := []) (MC.blank f ((2 + M) / 3) (by omega))
    rwa [show 2 + M = M + 1 + 1 by omega] at this

/-- `N` carries into the segment `T`, computed arithmetically (`none` if the segment has a
shape not covered above, e.g. a lone last cell). -/
def carryF : List Sym → Nat → Option (List Sym)
  | T, 0 => some T
  | [], N + 1 => some (blankF (N + 1) (N + 1))
  | 4 :: Z, _ + 1 => some (4 :: Z)
  | 1 :: 1 :: Z, N + 1 => (carryF Z ((1 + (N + 1)) / 3)).map (dig ((1 + (N + 1)) % 3) ++ ·)
  | 1 :: 2 :: Z, N + 1 => (carryF Z (2 * N)).map (fun Z' => 2 :: 2 :: Z')
  | 1 :: 4 :: Z, N + 1 => (carryF Z (N / 3)).map (dig (N % 3) ++ ·)
  | 2 :: 4 :: Z, N + 1 => (carryF Z ((N + 1) / 3)).map (dig ((N + 1) % 3) ++ ·)
  | 2 :: 1 :: Z, N + 1 => (carryF Z ((2 + (N + 1)) / 3)).map (dig ((2 + (N + 1)) % 3) ++ ·)
  | 2 :: 2 :: Z, N + 1 => (carryF Z (2 * (N + 1))).map (fun Z' => 2 :: 2 :: Z')
  | _, _ => none

theorem carryF_sound : ∀ (T : List Sym) (N : Nat) (T' : List Sym), carryF T N = some T' →
    MC N T T' := by
  intro T N T' h
  induction T, N using carryF.induct generalizing T' with
  | case1 T => simp [carryF] at h; subst h; rfl
  | case2 N => simp [carryF] at h; subst h; exact MC.blank _ _ (Nat.le_refl _)
  | case3 Z N => simp [carryF] at h; subst h; exact MC.wall Z _
  | case4 Z N ih =>
    simp only [carryF, Option.map_eq_some_iff] at h
    obtain ⟨Z', hZ, rfl⟩ := h
    exact MC.digit (N + 1) 1 (by omega) (ih Z' hZ)
  | case5 Z N ih =>
    simp only [carryF, Option.map_eq_some_iff] at h
    obtain ⟨Z', hZ, rfl⟩ := h
    exact MC.oneTwo N (ih Z' hZ)
  | case6 Z N ih =>
    simp only [carryF, Option.map_eq_some_iff] at h
    obtain ⟨Z', hZ, rfl⟩ := h
    exact MC.oneFour N (ih Z' hZ)
  | case7 Z N ih =>
    simp only [carryF, Option.map_eq_some_iff] at h
    obtain ⟨Z', hZ, rfl⟩ := h
    have := MC.digit (N + 1) 0 (by omega) (by simpa using ih Z' hZ)
    simpa using this
  | case8 Z N ih =>
    simp only [carryF, Option.map_eq_some_iff] at h
    obtain ⟨Z', hZ, rfl⟩ := h
    exact MC.digit (N + 1) 2 (by omega) (ih Z' hZ)
  | case9 Z N ih =>
    simp only [carryF, Option.map_eq_some_iff] at h
    obtain ⟨Z', hZ, rfl⟩ := h
    exact MC.dbl (N + 1) (ih Z' hZ)
  | case10 T N h1 h2 h3 h4 h5 h6 h7 h8 h9 => simp_all [carryF]

/-! ### Reader moves -/

theorem event_even_to_b (p : Nat) (R : List Sym) :
    Reaches (event (2 * p) R) (bCfg (bitsOf p 0) R) := by
  unfold event bCfg
  tm_step
  refine (sweep_right p _ _).trans (Reaches.of_eq ?_)
  simp [bitsOf_zero, encBits_replicate_false]

theorem event_odd_to_m (p : Nat) (R : List Sym) :
    Reaches (event (2 * p + 1) R) (midCfg (bitsOf p 0) R) := by
  rw [bitsOf_zero]; exact mis_start p R

theorem b_two (bs : List Bool) (X : List Sym) : Reaches (bCfg bs (2 :: X)) (midCfg bs X) := by
  unfold bCfg midCfg; tm_step; exact Reaches.refl _

theorem m_two (bs : List Bool) (X : List Sym) :
    Reaches (midCfg bs (2 :: X)) (bCfg (false :: bs) X) := by
  unfold bCfg midCfg; tm_step; exact Reaches.refl _

theorem m_one (n v : Nat) (X : List Sym) (h : v + 1 < 2 ^ n) :
    Reaches (midCfg (bitsOf n v) (1 :: X)) (bCfg (bitsOf (n + 1) (2 * (v + 1))) X) := by
  obtain ⟨k, rest, e1, e2⟩ := bitsOf_shape n v h
  rw [e1, bitsOf_even (by omega), show 2 * (v + 1) / 2 = v + 1 by omega, e2]
  exact absorb_one k rest X

theorem m_four (n v : Nat) (X : List Sym) :
    Reaches (midCfg (bitsOf n v) (4 :: X)) (event (2 * n + 2) (4 :: X)) := by
  have h := blocked_to_top X (bitsOf n v) 0 []
  simp only [List.replicate_zero, List.nil_append, List.append_nil, length_bitsOf] at h
  exact h.trans (blocked_overflow n X)

/-! ### Aligned cycles, bounded version -/

theorem aligned_rounds_b (q v0 J : Nat) (f : Nat → List Sym)
    (hf : ∀ j < J, Carry (f j) (f (j + 1))) (hv : v0 % 2 = 0) :
    ∀ j ≤ J, v0 + 6 * j < 2 ^ (q + 2) →
      Reaches (alignedCfg (bitsOf (q + 2) v0) 4 (f 0))
        (alignedCfg (bitsOf (q + 2) (v0 + 6 * j)) 4 (f j))
  | 0, _, _ => Reaches.refl _
  | j + 1, hj, h => by
    have e : 2 ^ (q + 1 + 1) = 2 ^ (q + 2) := rfl
    refine (aligned_rounds_b q v0 J f hf hv j (by omega) (by omega)).trans ?_
    refine (aligned_step4_nat (q := q) (n := v0 + 6 * j) _ (by omega) (by omega)).trans ?_
    have := aligned_step1_gen_nat (q := q + 1) (n := v0 + 6 * j + 4) (hf j (by omega))
      (by omega) (by omega)
    exact (by simpa [show v0 + 6 * j + 4 + 2 = v0 + 6 * (j + 1) by omega] using this)

/-- The end of an aligned cycle with lowest cell `4`, after all complete rounds. -/
def alignedOut4 (n v c0 : Nat) (T : List Sym) : Option (Nat × List Sym) :=
  if 2 ^ n - (v + 6 * ((2 ^ n - 1 - v) / 6)) = 6 then
    (carryF T (c0 + (2 ^ n - 1 - v) / 6 + 1)).map (fun T' => (2 * n + 1, 4 :: T'))
  else if 2 ^ n - (v + 6 * ((2 ^ n - 1 - v) / 6)) = 4 then
    (carryF T (c0 + (2 ^ n - 1 - v) / 6)).map (fun T' => (2 * n + 1, 1 :: T'))
  else
    (carryF T (c0 + (2 ^ n - 1 - v) / 6)).map (fun T' => (2 * n, 1 :: 1 :: T'))

/-- The whole aligned cycle, from the moment `B` reaches the lowest cell `d0`. -/
def alignedOut (n v : Nat) (d0 : Sym) (T : List Sym) : Option (Nat × List Sym) :=
  if n < 2 then none
  else if d0 = 4 then alignedOut4 n v 0 T
  else if d0 = 1 then
    (if v + 2 < 2 ^ n then alignedOut4 n (v + 2) 1 T
     else (carryF T 1).map (fun T' => (2 * n + 1, 4 :: T')))
  else none

theorem alignedOut4_sound (n v c0 : Nat) (T : List Sym) (m' : Nat) (R' : List Sym)
    (hn : 2 ≤ n) (hv : v % 2 = 0) (hlt : v < 2 ^ n)
    (h : alignedOut4 n v c0 T = some (m', R')) :
    ∃ (C : Nat) (f : Nat → List Sym), f 0 = T ∧ c0 ≤ C ∧ (∀ j < C, Carry (f j) (f (j + 1))) ∧
      Reaches (alignedCfg (bitsOf n v) 4 (f c0)) (event m' R') := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 2 := ⟨n - 2, by omega⟩
  have e : 2 ^ (q + 2) = 2 ^ q * 4 := by rw [Nat.pow_add]
  have hq := Nat.one_le_two_pow (n := q)
  generalize hr : (2 ^ (q + 2) - 1 - v) / 6 = r
  have hr1 : v + 6 * r ≤ 2 ^ (q + 2) - 1 := by omega
  have hr2 : 2 ^ (q + 2) - 1 < v + 6 * r + 6 := by omega
  unfold alignedOut4 at h
  rw [hr] at h
  by_cases h6 : 2 ^ (q + 2) - (v + 6 * r) = 6
  · rw [if_pos h6, Option.map_eq_some_iff] at h
    obtain ⟨T', hT, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨f, hf0, hfC, hf⟩ := MC.seq (carryF_sound _ _ _ hT)
    refine ⟨_, f, hf0, by omega, hf, ?_⟩
    have hrd := aligned_rounds_b q v r (fun j => f (c0 + j))
      (fun j hj => by simpa [Nat.add_assoc] using hf (c0 + j) (by omega)) hv r
      (Nat.le_refl _) (by omega)
    simp only [Nat.add_zero] at hrd
    refine hrd.trans ?_
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by
      rcases q with _ | q
      · simp at e; omega
      · omega⟩
    rw [show v + 6 * r = 2 ^ (q' + 1 + 2) - 6 by omega]
    change Reaches (alignedCfg (bitsOf (q' + 3) (2 ^ (q' + 3) - 6)) 4 (f (c0 + r)))
      (event (2 * (q' + 3) + 1) (4 :: T'))
    have := aligned_finish q' (hf (c0 + r) (by omega))
    rw [hfC] at this
    simpa using this
  rw [if_neg h6] at h
  by_cases h4 : 2 ^ (q + 2) - (v + 6 * r) = 4
  · rw [if_pos h4, Option.map_eq_some_iff] at h
    obtain ⟨T', hT, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨f, hf0, hfC, hf⟩ := MC.seq (carryF_sound _ _ _ hT)
    refine ⟨_, f, hf0, by omega, hf, ?_⟩
    have hrd := aligned_rounds_b q v r (fun j => f (c0 + j))
      (fun j hj => by simpa [Nat.add_assoc] using hf (c0 + j) (by omega)) hv r
      (Nat.le_refl _) (by omega)
    simp only [Nat.add_zero] at hrd
    refine hrd.trans ?_
    rw [show v + 6 * r = 2 ^ (q + 2) - 4 by omega, bitsOf_top_minus_four, hfC]
    refine (aligned_ovf4a q _).trans (Reaches.of_eq ?_)
    congr 1
  · rw [if_neg h4, Option.map_eq_some_iff] at h
    obtain ⟨T', hT, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨f, hf0, hfC, hf⟩ := MC.seq (carryF_sound _ _ _ hT)
    refine ⟨_, f, hf0, by omega, hf, ?_⟩
    have hrd := aligned_rounds_b q v r (fun j => f (c0 + j))
      (fun j hj => by simpa [Nat.add_assoc] using hf (c0 + j) (by omega)) hv r
      (Nat.le_refl _) (by omega)
    simp only [Nat.add_zero] at hrd
    refine hrd.trans ?_
    rw [show v + 6 * r = 2 ^ (q + 2) - 2 by omega, bitsOf_top_minus_two, hfC]
    refine (aligned_ovf4b q _).trans (Reaches.of_eq ?_)
    congr 1

theorem alignedOut_sound (n v : Nat) (d0 : Sym) (T : List Sym) (m' : Nat) (R' : List Sym)
    (hv : v % 2 = 0) (hlt : v < 2 ^ n) (h : alignedOut n v d0 T = some (m', R')) :
    Reaches (alignedCfg (bitsOf n v) d0 T) (event m' R') := by
  unfold alignedOut at h
  by_cases h1 : n < 2
  · simp [h1] at h
  rw [if_neg h1] at h
  by_cases h2 : d0 = 4
  · subst h2
    rw [if_pos rfl] at h
    obtain ⟨C, f, hf0, -, -, hr⟩ := alignedOut4_sound n v 0 T m' R' (by omega) hv hlt h
    rwa [hf0] at hr
  rw [if_neg h2] at h
  by_cases h3 : d0 = 1
  · subst h3
    rw [if_pos rfl] at h
    by_cases h4 : v + 2 < 2 ^ n
    · rw [if_pos h4] at h
      obtain ⟨C, f, hf0, hC, hf, hr⟩ := alignedOut4_sound n (v + 2) 1 T m' R' (by omega)
        (by omega) h4 h
      obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
      have hs := aligned_step1_gen_nat (q := q) (n := v) (hf 0 (by omega)) hv h4
      rw [hf0] at hs
      exact hs.trans hr
    · rw [if_neg h4, Option.map_eq_some_iff] at h
      obtain ⟨T', hT, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨U, hU, hUT⟩ := carryF_sound _ _ _ hT
      change U = T' at hUT; subst hUT
      obtain ⟨q, rfl⟩ : ∃ q, n = q + 2 := ⟨n - 2, by omega⟩
      have e : 2 ^ (q + 2) = 2 ^ q * 4 := by rw [Nat.pow_add]
      have := Nat.one_le_two_pow (n := q)
      rw [show v = 2 ^ (q + 2) - 2 by omega, bitsOf_top_minus_two]
      refine (aligned_ovf1_gen (q + 1) hU).trans (Reaches.of_eq ?_)
      congr 1
  · simp [h3] at h

/-! ### The reader and the macro step -/

/-- The reader: `b = true` means state `B` after a complete pair, `false` means state `A`
after a lone cell; `n` bits with value `v`. -/
def readR : Bool → Nat → Nat → List Sym → Option (Nat × List Sym)
  | true, n, v, 2 :: X => readR false n v X
  | true, n, v, d0 :: T => alignedOut n v d0 T
  | false, n, v, 2 :: X => readR true (n + 1) (2 * v) X
  | false, n, v, 1 :: X => if v + 1 < 2 ^ n then readR true (n + 1) (2 * (v + 1)) X else none
  | false, n, _, 4 :: X => some (2 * n + 2, 4 :: X)
  | _, _, _, _ => none

/-- Reader configuration. -/
def readCfg (b : Bool) (n v : Nat) (R : List Sym) : Cfg :=
  if b then bCfg (bitsOf n v) R else midCfg (bitsOf n v) R

theorem readR_sound : ∀ (b : Bool) (n v : Nat) (R : List Sym) (m' : Nat) (R' : List Sym),
    v < 2 ^ n → (b = true → v % 2 = 0) → readR b n v R = some (m', R') →
    Reaches (readCfg b n v R) (event m' R') := by
  intro b n v R m' R' hlt hv h
  induction b, n, v, R using readR.induct generalizing m' R' with
  | case1 n v X ih =>
    simp only [readR] at h
    exact (b_two _ X).trans (ih m' R' hlt (by simp) h)
  | case2 n v d0 T hd0 =>
    have h' : alignedOut n v d0 T = some (m', R') := by
      have hd : d0 = 0 ∨ d0 = 1 ∨ d0 = 3 ∨ d0 = 4 := by
        clear h; revert hd0; revert d0; decide
      rcases hd with rfl | rfl | rfl | rfl <;> simpa [readR] using h
    exact alignedOut_sound n v d0 T m' R' (hv rfl) hlt h'
  | case3 n v X ih =>
    simp only [readR] at h
    refine (m_two _ X).trans ?_
    have := ih m' R' (by rw [Nat.pow_succ]; omega) (by intro; omega) h
    simpa [readCfg, bitsOf_even (show 2 * v % 2 = 0 by omega)] using this
  | case4 n v X h1 ih =>
    simp only [readR, h1, if_true] at h
    exact (m_one n v X h1).trans (ih m' R' (by rw [Nat.pow_succ]; omega) (by intro; omega) h)
  | case5 n v X h1 =>
    simp [readR, h1] at h
  | case6 n v X =>
    simp only [readR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact m_four n v X
  | case7 R b n v h1 h2 h3 h4 h5 =>
    exfalso
    rcases b with _ | _ <;> rcases R with _ | ⟨c, X⟩ <;> simp_all [readR]

/-- One macro step: from `event m R` to the next event. -/
def macroStep (s : Nat × List Sym) : Option (Nat × List Sym) :=
  readR (s.1 % 2 == 0) (s.1 / 2) 0 s.2

theorem macroStep_sound (m : Nat) (R : List Sym) (m' : Nat) (R' : List Sym)
    (h : macroStep (m, R) = some (m', R')) : Reaches (event m R) (event m' R') := by
  unfold macroStep at h
  have hp := Nat.one_le_two_pow (n := m / 2)
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have e : m = 2 * (m / 2) := by omega
    have := readR_sound true (m / 2) 0 R m' R' (by omega) (by simp) (by simpa [hm] using h)
    rw [e]; exact (event_even_to_b _ R).trans (by simpa [readCfg] using this)
  · have e : m = 2 * (m / 2) + 1 := by omega
    have := readR_sound false (m / 2) 0 R m' R' (by omega) (by simp) (by simpa [hm] using h)
    rw [e]; exact (event_odd_to_m _ R).trans (by simpa [readCfg] using this)

/-- Iterated macro steps. -/
def macroRun : Nat → Nat × List Sym → Option (Nat × List Sym)
  | 0, s => some s
  | k + 1, s => (macroStep s).bind (macroRun k)

theorem macroRun_sound : ∀ (k : Nat) (m : Nat) (R : List Sym) (m' : Nat) (R' : List Sym),
    macroRun k (m, R) = some (m', R') → Reaches (event m R) (event m' R')
  | 0, m, R, m', R', h => by
    simp only [macroRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact Reaches.refl _
  | k + 1, m, R, m', R', h => by
    simp only [macroRun, Option.bind_eq_some_iff] at h
    obtain ⟨⟨m1, R1⟩, h1, h2⟩ := h
    exact (macroStep_sound m R m1 R1 h1).trans (macroRun_sound k m1 R1 m' R' h2)

end TM25
