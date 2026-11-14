import RequestProject.Macro

/-!
# The machine does not halt from the blank tape

After 681 steps the machine is at `event 13 (4 | 24 21 21)` (`run_681`).  Forty-one verified
macro steps later (`run_macro41`, both checked by kernel computation) it is at

    event 100 (1 1 2^4 4 | Z)          (Z an ordinary ternary counter)

i.e. an aligned configuration with `n = 50` bits whose lowest cell is `1`, followed by the
offset counter `1 2^a 4 Z`.  For `n ≡ 2 (mod 6)` such a configuration is a loop
(`loop_step`): the aligned cycle sends `1 + (2^n-4)/6` carries into `1 2^a 4 Z`; the first
turns the leading `1` into `2`, the others pass the doublers `22` and reach either a wall
`4…` (when `a` is odd) or the digit `24` (when `a` is even), which receives a multiple of
`3` of them and therefore stays `24`.  The binary counter overflows exactly as before, and
the next event is `event 100 (1 1 2^(a+1) 4 | Z')`.  The run of `2`s grows forever and the
binary counter never grows, so the machine never halts.
-/

namespace TM25

/-! ### Carries into offset counters, symbolically -/

theorem carryF_zero (T : List Sym) : carryF T 0 = some T := by
  cases T with
  | nil => rfl
  | cons c X => rfl

theorem carryF_wall (Z : List Sym) (M : Nat) : carryF (4 :: Z) M = some (4 :: Z) := by
  cases M <;> rfl

theorem carryF_twotwo (Y : List Sym) (M : Nat) :
    carryF (2 :: 2 :: Y) M = (carryF Y (2 * M)).map (fun Y' => 2 :: 2 :: Y') := by
  cases M with
  | zero => simp [carryF_zero]
  | succ M => rfl

theorem carryF_twos_wall (Z : List Sym) : ∀ (b M : Nat),
    carryF (List.replicate (2 * b) 2 ++ 4 :: Z) M = some (List.replicate (2 * b) 2 ++ 4 :: Z)
  | 0, M => by simpa using carryF_wall Z M
  | b + 1, M => by
    rw [replicate_two_mul_succ, List.cons_append, List.cons_append, carryF_twotwo,
      carryF_twos_wall Z b]
    rfl

theorem carryF_twofour (Z : List Sym) (M : Nat) :
    carryF (2 :: 4 :: Z) M = (carryF Z (M / 3)).map (dig (M % 3) ++ ·) := by
  cases M with
  | zero => simp [carryF_zero, dig]
  | succ M => rfl

theorem carryF_twos_digit (Z : List Sym) : ∀ (c M : Nat),
    carryF (List.replicate (2 * c) 2 ++ 2 :: 4 :: Z) M =
      (carryF Z (2 ^ c * M / 3)).map (fun Z' => List.replicate (2 * c) 2 ++ dig (2 ^ c * M % 3) ++ Z')
  | 0, M => by simp [carryF_twofour]
  | c + 1, M => by
    rw [replicate_two_mul_succ, List.cons_append, List.cons_append, carryF_twotwo,
      carryF_twos_digit Z c, show 2 ^ c * (2 * M) = 2 ^ (c + 1) * M by
        rw [Nat.pow_succ, Nat.mul_assoc]]
    simp [Option.map_map, Function.comp_def]

theorem dig_eq_lt : ∀ (x : Nat) (hx : x < 3), dig x = encDigit ⟨x, hx⟩
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

theorem dig_mod_eq (k : Nat) : dig (k % 3) = encDigit ⟨k % 3, Nat.mod_lt _ (by decide)⟩ :=
  dig_eq_lt _ _

theorem blankF_encT : ∀ (f N : Nat), ∃ zs, blankF f N = encT zs
  | 0, _ => ⟨[], rfl⟩
  | f + 1, N => by
    by_cases hN : N = 0
    · exact ⟨[], by simp [blankF, hN, encT]⟩
    · obtain ⟨zs, hzs⟩ := blankF_encT f ((N + 1) / 3)
      exact ⟨⟨(N + 1) % 3, Nat.mod_lt _ (by decide)⟩ :: zs, by
        simp [blankF, hN, hzs, dig_mod_eq]⟩

/-- Any number of carries into an ordinary ternary counter gives an ordinary ternary
counter. -/
theorem carryF_encT : ∀ (zs : List (Fin 3)) (M : Nat), ∃ zs', carryF (encT zs) M = some (encT zs')
  | zs, 0 => ⟨zs, carryF_zero _⟩
  | [], M + 1 => by
    obtain ⟨zs', h⟩ := blankF_encT (M + 1) (M + 1)
    exact ⟨zs', by simp [encT, carryF, h]⟩
  | ⟨0, _⟩ :: zs, M + 1 => by
    obtain ⟨zs', h⟩ := carryF_encT zs ((M + 1) / 3)
    refine ⟨⟨(M + 1) % 3, Nat.mod_lt _ (by decide)⟩ :: zs', ?_⟩
    simp [encDigit, carryF, h, dig_mod_eq]
  | ⟨1, _⟩ :: zs, M + 1 => by
    obtain ⟨zs', h⟩ := carryF_encT zs ((1 + (M + 1)) / 3)
    refine ⟨⟨(1 + (M + 1)) % 3, Nat.mod_lt _ (by decide)⟩ :: zs', ?_⟩
    simp [encDigit, carryF, h, dig_mod_eq]
  | ⟨2, _⟩ :: zs, M + 1 => by
    obtain ⟨zs', h⟩ := carryF_encT zs ((2 + (M + 1)) / 3)
    refine ⟨⟨(2 + (M + 1)) % 3, Nat.mod_lt _ (by decide)⟩ :: zs', ?_⟩
    simp [encDigit, carryF, h, dig_mod_eq]

/-- `1 + 3t` carries into the offset counter `1 2^a 4 Z`. -/
theorem carryF_loop (a t : Nat) (zs : List (Fin 3)) : ∃ zs',
    carryF (1 :: (List.replicate a 2 ++ 4 :: encT zs)) (3 * t + 1) =
      some (List.replicate (a + 1) 2 ++ 4 :: encT zs') := by
  obtain ⟨b, rfl | rfl⟩ : ∃ b, a = 2 * b ∨ a = 2 * b + 1 := ⟨a / 2, by omega⟩
  · rcases b with _ | c
    · obtain ⟨zs', h⟩ := carryF_encT zs t
      refine ⟨zs', ?_⟩
      simp [carryF, h, dig, show 3 * t / 3 = t by omega, show 3 * t % 3 = 0 by omega]
    · obtain ⟨zs', h⟩ := carryF_encT zs (2 ^ c * (2 * (3 * t)) / 3)
      refine ⟨zs', ?_⟩
      have e : List.replicate (2 * (c + 1)) (2 : Sym) ++ 4 :: encT zs =
          2 :: (List.replicate (2 * c) 2 ++ 2 :: 4 :: encT zs) := by
        rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega, List.replicate_succ',
          List.replicate_succ]
        simp
      rw [e]
      have hm : 2 ^ c * (2 * (3 * t)) % 3 = 0 := by
        rw [show 2 ^ c * (2 * (3 * t)) = 3 * (2 ^ c * 2 * t) by
          rw [Nat.mul_left_comm 2, Nat.mul_left_comm (2 ^ c), Nat.mul_assoc]]
        exact Nat.mul_mod_right 3 _
      simp only [carryF, carryF_twos_digit, h, hm, Option.map_some]
      simp [dig, List.replicate_succ', show 2 * (c + 1) + 1 = 2 * c + 1 + 1 + 1 by omega,
        replicate_append_cons]
  · refine ⟨zs, ?_⟩
    rw [List.replicate_succ, List.cons_append]
    simp only [carryF]
    rw [carryF_twos_wall]
    simp [List.replicate_succ]

theorem two_pow_loop_mod (s : Nat) : 2 ^ (6 * s + 2) % 18 = 4 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [show 6 * (s + 1) + 2 = 6 * s + 2 + 6 by omega, Nat.pow_add]; omega

/-- **The loop.**  With `n = 6s+2` bits, `event (2n) (1 1 2^a 4 | Z)` leads to
`event (2n) (1 1 2^(a+1) 4 | Z')` for an ordinary ternary counter `Z'`. -/
theorem loop_step (s a : Nat) (zs : List (Fin 3)) : ∃ zs',
    Reaches (event (2 * (6 * s + 2)) (1 :: 1 :: (List.replicate a 2 ++ 4 :: encT zs)))
      (event (2 * (6 * s + 2)) (1 :: 1 :: (List.replicate (a + 1) 2 ++ 4 :: encT zs'))) := by
  have hmod := two_pow_loop_mod s
  generalize hn : 6 * s + 2 = n at hmod ⊢
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = 18 * t + 4 := ⟨2 ^ n / 18, by omega⟩
  obtain ⟨zs', hc⟩ := carryF_loop a t zs
  refine ⟨zs', macroStep_sound _ _ _ _ ?_⟩
  have hr : (2 ^ n - 1 - (0 + 2)) / 6 = 3 * t := by omega
  simp only [macroStep]
  simp only [show 2 * n % 2 = 0 by omega, show 2 * n / 2 = n by omega, beq_self_eq_true]
  change alignedOut n 0 1 _ = _
  unfold alignedOut alignedOut4
  simp only [show ¬ n < 2 by omega, if_false, show ((1 : Sym) = 4) = False by decide,
    if_true, show (0 + 2 < 2 ^ n) = True by simp; omega]
  simp only [Nat.zero_add] at hr
  rw [hr, show 2 ^ n - (2 + 6 * (3 * t)) = 2 by omega, Nat.add_comm 1 (3 * t), hc]
  simp

/-! ### Determinism and non-halting -/

theorem reaches_of_run : ∀ (n : Nat) (c c' : Cfg), run n c = some c' → Reaches c c'
  | 0, c, c', h => by simp [run] at h; subst h; exact Reaches.refl _
  | n + 1, c, c', h => by
    simp only [run] at h
    cases hs : step c with
    | none => simp [hs] at h
    | some b => rw [hs] at h; exact Reaches.head hs (reaches_of_run n b c' h)

theorem run_add : ∀ (a b : Nat) (c : Cfg), run (a + b) c = (run a c).bind (run b)
  | 0, b, c => by simp [run]
  | a + 1, b, c => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [run]
    cases step c with
    | none => rfl
    | some d => simp [run_add a b d]

theorem run_of_reaches {a b : Cfg} (h : Reaches a b) : ∃ n, run (n + 1) a = some b ∨ a = b := by
  induction h with
  | refl => exact ⟨0, Or.inr rfl⟩
  | @head a b c hs _ ih =>
    obtain ⟨n, hn | rfl⟩ := ih
    · exact ⟨n + 1, Or.inl (by simp [run, hs] at hn ⊢; exact hn)⟩
    · exact ⟨0, Or.inl (by simp [run, hs])⟩

theorem run_of_reaches' {a b : Cfg} (h : Reaches a b) : ∃ n, run n a = some b := by
  obtain ⟨n, hn | rfl⟩ := run_of_reaches h
  · exact ⟨n + 1, hn⟩
  · exact ⟨0, rfl⟩

theorem run_none_of_halt {h : Cfg} (hs : step h = none) : ∀ k, run (k + 1) h = none := by
  intro k; simp [run, hs]

/-- If every configuration satisfying `P` makes progress to another one satisfying `P`,
none of them halts. -/
theorem not_halts_of_progress (P : Cfg → Prop)
    (hP : ∀ c, P c → ∃ c', P c' ∧ ∃ k, run (k + 1) c = some c') :
    ∀ c, P c → ¬ Halts c := by
  rintro c hc ⟨h, hr, hs⟩
  obtain ⟨n, hn⟩ := run_of_reaches' hr
  clear hr
  induction n using Nat.strongRecOn generalizing c with
  | _ n ih =>
    obtain ⟨c', hc', k, hk⟩ := hP c hc
    by_cases hkn : k + 1 ≤ n
    · have e := run_add (k + 1) (n - (k + 1)) c
      rw [show k + 1 + (n - (k + 1)) = n by omega, hn, hk] at e
      exact ih (n - (k + 1)) (by omega) c' hc' e.symm
    · have e := run_add n (k + 1 - n) c
      rw [show n + (k + 1 - n) = k + 1 by omega, hk, hn] at e
      obtain ⟨j, hj⟩ : ∃ j, k + 1 - n = j + 1 := ⟨k - n, by omega⟩
      rw [hj] at e
      simp [run_none_of_halt hs j] at e

theorem halts_of_reaches {a b : Cfg} (hab : Reaches a b) (ha : Halts a) : Halts b := by
  obtain ⟨h, hr, hs⟩ := ha
  obtain ⟨n, hn⟩ := run_of_reaches' hr
  obtain ⟨m, hm⟩ := run_of_reaches' hab
  by_cases hmn : m ≤ n
  · have e := run_add m (n - m) a
    rw [show m + (n - m) = n by omega, hn, hm] at e
    exact ⟨h, reaches_of_run _ _ _ e.symm, hs⟩
  · have e := run_add n (m - n) a
    rw [show n + (m - n) = m by omega, hm, hn] at e
    obtain ⟨j, hj⟩ : ∃ j, m - n = j + 1 := ⟨m - n - 1, by omega⟩
    rw [hj] at e
    simp [run_none_of_halt hs j] at e

theorem loop_event_ne (m a : Nat) (X Y : List Sym) :
    event m (1 :: 1 :: (List.replicate a 2 ++ 4 :: X)) ≠
      event m (1 :: 1 :: (List.replicate (a + 1) 2 ++ 4 :: Y)) := by
  intro h
  simp only [event, Cfg.mk.injEq, true_and, List.cons.injEq, List.append_cancel_left_eq] at h
  rw [List.replicate_succ', List.append_assoc] at h
  have h3 := List.append_cancel_left h
  simp at h3

/-- No configuration of the loop halts. -/
theorem loop_not_halts (s a : Nat) (zs : List (Fin 3)) :
    ¬ Halts (event (2 * (6 * s + 2)) (1 :: 1 :: (List.replicate a 2 ++ 4 :: encT zs))) := by
  refine not_halts_of_progress
    (fun c => ∃ a zs, c = event (2 * (6 * s + 2)) (1 :: 1 :: (List.replicate a 2 ++ 4 :: encT zs)))
    ?_ _ ⟨a, zs, rfl⟩
  rintro c ⟨a, zs, rfl⟩
  obtain ⟨zs', h⟩ := loop_step s a zs
  obtain ⟨n, hn | he⟩ := run_of_reaches h
  · exact ⟨_, ⟨a + 1, zs', rfl⟩, n, hn⟩
  · exact absurd he (loop_event_ne _ _ _ _)

/-! ### The actual run -/

set_option maxRecDepth 100000 in
/-- After 681 steps from the blank tape: 13 cells `2`, then the ternary counter
`4 | 24 21 21` (lowest cell `4`, digits `0, 2, 2`). -/
theorem run_681 : run 681 init = some (event 13 (4 :: encT [0, 2, 2])) := by decide +kernel

set_option maxRecDepth 100000 in
/-- Forty-one macro steps from `event 13 (4 | 24 21 21)` (kernel computation). -/
theorem run_macro41 : macroRun 41 (13, 4 :: encT [0, 2, 2]) =
    some (100, 1 :: 1 :: (List.replicate 4 2 ++ 4 :: encT [1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 2, 0,
      1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 2, 0, 2])) := by
  decide +kernel

/-- From the blank tape the machine reaches the loop configuration with `n = 50`. -/
theorem init_reaches_loop : Reaches init (event (2 * (6 * 8 + 2))
    (1 :: 1 :: (List.replicate 4 2 ++ 4 :: encT [1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 2, 0,
      1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 2, 0, 2]))) :=
  (reaches_of_run 681 _ _ run_681).trans (macroRun_sound 41 _ _ _ _ run_macro41)

/-- **Main theorem: `1RB2LA0RB---4LA_1LA3LA1RA4RA1LB` does not halt from the blank tape.** -/
theorem not_halts_init : ¬ Halts init := fun h =>
  loop_not_halts 8 4 _ (halts_of_reaches init_reaches_loop h)

end TM25
