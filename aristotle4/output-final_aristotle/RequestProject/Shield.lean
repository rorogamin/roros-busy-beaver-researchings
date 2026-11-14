import RequestProject.Pass

/-!
# A `4` between the frontier and a cascade saves the machine

A halt can only be caused by a left-moving cascade reaching the frontier `1`
(`Machine.pre_halt_shape`).  A cascade is stopped by a `4` in either mode
(`cascade_P_four_stops`, `cascade_Q_four_stops`), so a single cell holding `4`
between the frontier and a newborn cascade is enough to make that cascade
harmless — whatever the cells in between look like.

This file proves exactly that, with no assumption on the intervening cells other
than that none of them is the frontier symbol `1`:

> `cascade_dies_before_four` — a cascade whose left context contains a `4`
> reaches, in finitely many steps and without the machine halting, one of the
> four configurations in which a cascade can come to an end (`CascadeOver`).

The argument is now run against an abstract *stopper* (`StopsCascade`), so the
same induction also covers the second way a cascade can be blocked — two
consecutive counter digits `2`, i.e. two consecutive cells holding `0`.  Those
two blockers are exactly the negation of the Cantor criterion of
`Counter.cross_digits_iff`, so `cascade_dies_of_not_cantor` says: *whenever the
counter is not Cantor-compatible, the cascade dies harmlessly.*

It generalises `Counter.no_halt_of_cascade_into_four`, which assumed the
intervening cells to be counter digits, and `Pass.passRev_dies_at_four`, which
assumed them to be the output of a four-free pass.

*Measurement* (`tools/fours.c`, unverified, `2·10^10` steps): there were `299`
cascade births, and **at every one of them at least one cell between the
frontier and the head held a `4`** (the minimum over all births is `1`).  So
this theorem covers every cascade the machine has been observed to produce; what
is missing for a non-halting proof is the invariant that this is always so.
-/

namespace TM2x5

/-- The four ways a cascade comes to an end: it meets a `4` in mode `P` (and
turns into a left-moving `B`), a `4` in mode `Q`, a `2` in mode `P`, or a `0` in
mode `Q` (in the last three cases it turns into a right-moving `A`). -/
def CascadeOver (d : Cfg) : Prop :=
  (∃ l c r, d = ⟨St.B, l, c, (4 : Sym) :: (4 : Sym) :: r⟩) ∨
  (∃ l x r, d = ⟨St.A, (4 : Sym) :: (2 : Sym) :: l, x, r⟩) ∨
  (∃ l r, d = ⟨St.A, (3 : Sym) :: l, 2, r⟩) ∨
  (∃ l x r, d = ⟨St.A, (4 : Sym) :: (1 : Sym) :: l, x, r⟩)

/-! ## The local rules, in the form the induction needs -/

/-- A cascade crossing a `3` keeps going and arrives in mode `P`. -/
theorem casc_three (a : Sym) (mo : Mode) (L r : List Sym) :
    iter 1 (some (⟨St.A, a :: L, 3, mo.sym :: r⟩ : Cfg)) =
      some ⟨St.A, L, a, (2 : Sym) :: mo.sym :: r⟩ := by
  cases mo <;> rfl

/-- A cascade crossing a `0` in mode `P` keeps going and arrives in mode `Q`. -/
theorem casc_zero_P (a : Sym) (L r : List Sym) :
    iter 3 (some (⟨St.A, a :: L, 0, Mode.P.sym :: r⟩ : Cfg)) =
      some ⟨St.A, L, a, Mode.Q.sym :: (4 : Sym) :: r⟩ := rfl

/-- A cascade crossing a `2` in mode `Q` keeps going and arrives in mode `P`. -/
theorem casc_two_Q (a : Sym) (L r : List Sym) :
    iter 3 (some (⟨St.A, a :: L, 2, Mode.Q.sym :: r⟩ : Cfg)) =
      some ⟨St.A, L, a, Mode.P.sym :: (2 : Sym) :: r⟩ := rfl

/-- A `2` in mode `P` stops the cascade. -/
theorem casc_stop_two_P (L r : List Sym) :
    iter 1 (some (⟨St.A, L, 2, Mode.P.sym :: r⟩ : Cfg)) =
      some ⟨St.A, (3 : Sym) :: L, 2, r⟩ := rfl

/-- A `0` in mode `Q` stops the cascade; the cell beyond may be fresh tape. -/
theorem casc_stop_zero_Q (L rr : List Sym) :
    iter 2 (some (⟨St.A, L, 0, Mode.Q.sym :: rr⟩ : Cfg)) =
      some (onFirst St.A ((4 : Sym) :: (1 : Sym) :: L) rr) := by
  cases rr <;> rfl

/-- A `4` in mode `P` stops the cascade. -/
theorem casc_stop_four_P (a : Sym) (L r : List Sym) :
    iter 3 (some (⟨St.A, a :: L, 4, Mode.P.sym :: r⟩ : Cfg)) =
      some ⟨St.B, L, a, (4 : Sym) :: (4 : Sym) :: r⟩ := rfl

/-- A `4` in mode `Q` stops the cascade. -/
theorem casc_stop_four_Q (L rr : List Sym) :
    iter 2 (some (⟨St.A, L, 4, Mode.Q.sym :: rr⟩ : Cfg)) =
      some (onFirst St.A ((4 : Sym) :: (2 : Sym) :: L) rr) := by
  cases rr <;> rfl

/-- Arriving on a `4`, in either mode, the cascade is over. -/
theorem cascade_hits_four (mo : Mode) (a : Sym) (L r : List Sym) :
    ∃ (N : ℕ) (d : Cfg), iter N (some (⟨St.A, a :: L, 4, mo.sym :: r⟩ : Cfg)) = some d ∧
      CascadeOver d := by
  cases mo with
  | P =>
    exact ⟨3, _, casc_stop_four_P a L r, Or.inl ⟨L, a, r, rfl⟩⟩
  | Q =>
    refine ⟨2, _, casc_stop_four_Q (a :: L) r, Or.inr (Or.inl ?_)⟩
    cases r with
    | nil => exact ⟨a :: L, 0, [], rfl⟩
    | cons x r' => exact ⟨a :: L, x, r', rfl⟩

/-- The five symbols, minus the frontier symbol. -/
theorem sym_cases (c : Sym) (hc : c ≠ 1) : c = 0 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  cases c
  · exact Or.inl rfl
  · exact absurd rfl hc
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-! ## Crossing one cell -/

/-- **One cell of a cascade.**  Arriving on a cell `c` other than the frontier
symbol, in either mode, the cascade either comes to an end there or crosses the
cell and arrives on the next one to the left, in some mode. -/
theorem casc_cross (c : Sym) (hc : c ≠ 1) (mo : Mode) (a : Sym) (L r : List Sym) :
    (∃ (N : ℕ) (d : Cfg),
        iter N (some (⟨St.A, a :: L, c, mo.sym :: r⟩ : Cfg)) = some d ∧ CascadeOver d) ∨
    (∃ (N : ℕ) (mo' : Mode) (r' : List Sym),
        iter N (some (⟨St.A, a :: L, c, mo.sym :: r⟩ : Cfg)) =
          some (cfgAt St.A (a :: L) (mo'.sym :: r'))) := by
  rcases sym_cases c hc with h | h | h | h <;> subst h
  · cases mo with
    | P => exact Or.inr ⟨3, Mode.Q, (4 : Sym) :: r, casc_zero_P a L r⟩
    | Q =>
      refine Or.inl ⟨2, _, casc_stop_zero_Q (a :: L) r, Or.inr (Or.inr (Or.inr ?_))⟩
      cases r with
      | nil => exact ⟨a :: L, 0, [], rfl⟩
      | cons x r' => exact ⟨a :: L, x, r', rfl⟩
  · cases mo with
    | P =>
      exact Or.inl ⟨1, _, casc_stop_two_P (a :: L) r,
        Or.inr (Or.inr (Or.inl ⟨a :: L, r, rfl⟩))⟩
    | Q => exact Or.inr ⟨3, Mode.P, (2 : Sym) :: r, casc_two_Q a L r⟩
  · exact Or.inr ⟨1, Mode.P, mo.sym :: r, casc_three a mo L r⟩
  · exact Or.inl (cascade_hits_four mo a L r)

/-! ## The shield -/

/-- A block of cells `v` **stops every cascade**: whichever mode the head
arrives in on the first cell of `v`, and whatever the tape to its right, the
cascade comes to an end in finitely many steps. -/
def StopsCascade (v : List Sym) : Prop :=
  ∀ (mo : Mode) (r : List Sym), ∃ (N : ℕ) (d : Cfg),
    iter N (some (cfgAt St.A v (mo.sym :: r))) = some d ∧ CascadeOver d

/-- A cell holding `4` stops every cascade — this is the digit `1` of the
base-3 counter. -/
theorem stopsCascade_four (zc : Sym) (zs : List Sym) :
    StopsCascade ((4 : Sym) :: zc :: zs) :=
  fun mo r => cascade_hits_four mo zc zs r

/-- Two consecutive cells holding `0` stop every cascade — these are two
consecutive digits `2` of the base-3 counter. -/
theorem stopsCascade_zero_zero (z : List Sym) :
    StopsCascade ((0 : Sym) :: (0 : Sym) :: z) := by
  intro mo r
  cases mo with
  | P =>
    refine ⟨3 + 2, _, ?_, Or.inr (Or.inr (Or.inr ⟨z, 4, r, rfl⟩))⟩
    rw [iter_add]
    show iter 2 (iter 3 (some (⟨St.A, (0 : Sym) :: z, 0, Mode.P.sym :: r⟩ : Cfg))) = _
    rw [casc_zero_P, casc_stop_zero_Q z ((4 : Sym) :: r)]
    rfl
  | Q =>
    refine ⟨2, _, casc_stop_zero_Q ((0 : Sym) :: z) r, Or.inr (Or.inr (Or.inr ?_))⟩
    cases r with
    | nil => exact ⟨(0 : Sym) :: z, 0, [], rfl⟩
    | cons x r' => exact ⟨(0 : Sym) :: z, x, r', rfl⟩

/-- **A cascade facing a stopper dies before reaching it.**  Whatever the cells
`u` between the head and the stopping block `v` are — as long as none of them is
the frontier symbol `1`, and the cell under the head is not a `1` either — the
cascade comes to an end in finitely many steps, in one of the four ways of
`CascadeOver`. -/
theorem cascade_dies_before_stopper : ∀ (u : List Sym), (∀ s ∈ u, s ≠ 1) →
    ∀ (a : Sym) (v : List Sym), StopsCascade (a :: v) →
    ∀ (c : Sym), c ≠ 1 → ∀ (mo : Mode) (r : List Sym),
    ∃ (N : ℕ) (d : Cfg),
      iter N (some (⟨St.A, u ++ a :: v, c, mo.sym :: r⟩ : Cfg)) = some d ∧ CascadeOver d := by
  intro u
  induction u with
  | nil =>
    intro _ a v hv c hc mo r
    have hL : ([] : List Sym) ++ a :: v = a :: v := rfl
    rw [hL]
    rcases casc_cross c hc mo a v r with h | ⟨N, mo', r', hN⟩
    · exact h
    · obtain ⟨M, d, hM, hd⟩ := hv mo' r'
      exact ⟨N + M, d, by rw [iter_add, hN]; exact hM, hd⟩
  | cons b u ih =>
    intro hu a v hv c hc mo r
    have hb : b ≠ 1 := hu b (List.mem_cons_self ..)
    have hu' : ∀ s ∈ u, s ≠ 1 := fun s hs => hu s (List.mem_cons_of_mem _ hs)
    have hsplit : (b :: u) ++ a :: v = b :: (u ++ a :: v) := rfl
    rw [hsplit]
    rcases casc_cross c hc mo b (u ++ a :: v) r with h | ⟨N, mo', r', hN⟩
    · exact h
    · obtain ⟨M, d, hM, hd⟩ := ih hu' a v hv b hb mo' r'
      exact ⟨N + M, d, by rw [iter_add, hN]; exact hM, hd⟩

/-- **A cascade facing a `4` dies before reaching it.**  Whatever the cells `u`
between the head and the `4` are — as long as none of them is the frontier
symbol `1`, and the cell under the head is not a `1` either — the cascade comes
to an end in finitely many steps, in one of the four ways of `CascadeOver`. -/
theorem cascade_reaches_stop (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (zc : Sym) (zs r : List Sym) :
    ∃ (N : ℕ) (d : Cfg),
      iter N (some (⟨St.A, u ++ (4 : Sym) :: zc :: zs, c, mo.sym :: r⟩ : Cfg)) = some d ∧
        CascadeOver d :=
  cascade_dies_before_stopper u hu 4 (zc :: zs) (stopsCascade_four zc zs) c hc mo r

/-- **The negation of the Cantor criterion kills the cascade.**  A cascade
reaches the frontier only if every counter digit ahead of it is a `0` or a `2`
and no two consecutive digits are `2` (`cross_digits_iff`).  Here is the
complementary statement, in the form the tape provides it: if somewhere ahead of
the cascade there is a digit `1` (a cell holding `4`) or two consecutive digits
`2` (two cells holding `0`), then the cascade dies harmlessly, whatever the
cells before it are. -/
theorem cascade_dies_of_not_cantor (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (v : List Sym) (hv : (∃ zc zs, v = (4 : Sym) :: zc :: zs) ∨ (∃ z, v = (0 : Sym) :: 0 :: z))
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (r : List Sym) :
    ∃ (N : ℕ) (d : Cfg),
      iter N (some (⟨St.A, u ++ v, c, mo.sym :: r⟩ : Cfg)) = some d ∧ CascadeOver d := by
  rcases hv with ⟨zc, zs, rfl⟩ | ⟨z, rfl⟩
  · exact cascade_dies_before_stopper u hu 4 (zc :: zs) (stopsCascade_four zc zs) c hc mo r
  · exact cascade_dies_before_stopper u hu 0 (0 :: z) (stopsCascade_zero_zero z) c hc mo r

/-- **The machine survives a cascade blocked by the counter.**  Same hypotheses
as `cascade_dies_of_not_cantor`: the machine does not halt at any step up to the
moment the cascade dies. -/
theorem no_halt_before_stopper (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (v : List Sym) (hv : (∃ zc zs, v = (4 : Sym) :: zc :: zs) ∨ (∃ z, v = (0 : Sym) :: 0 :: z))
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (r : List Sym) :
    ∃ (N : ℕ) (d : Cfg),
      (∀ k ≤ N, iter k (some (⟨St.A, u ++ v, c, mo.sym :: r⟩ : Cfg)) ≠ none) ∧
      iter N (some (⟨St.A, u ++ v, c, mo.sym :: r⟩ : Cfg)) = some d ∧ CascadeOver d := by
  obtain ⟨N, d, hN, hd⟩ := cascade_dies_of_not_cantor u hu v hv c hc mo r
  exact ⟨N, d, fun k hk => iter_isSome_of_le hN hk, hN, hd⟩

/-- **The machine survives such a cascade.**  Same hypotheses as
`cascade_reaches_stop`: the machine does not halt at any step up to the moment
the cascade dies. -/
theorem cascade_dies_before_four (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (zc : Sym) (zs r : List Sym) :
    ∃ (N : ℕ) (d : Cfg),
      (∀ k ≤ N, iter k (some (⟨St.A, u ++ (4 : Sym) :: zc :: zs, c, mo.sym :: r⟩ : Cfg))
        ≠ none) ∧
      iter N (some (⟨St.A, u ++ (4 : Sym) :: zc :: zs, c, mo.sym :: r⟩ : Cfg)) = some d ∧
        CascadeOver d := by
  obtain ⟨N, d, hN, hd⟩ := cascade_reaches_stop u hu c hc mo zc zs r
  exact ⟨N, d, fun k hk => iter_isSome_of_le hN hk, hN, hd⟩

/-- The same statement for the machine started on the blank tape: a reachable
cascade with a `4` between it and the frontier cannot be the one that halts the
machine. -/
theorem reachable_cascade_over (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (zc : Sym) (zs r : List Sym)
    (hreach : Reachable ⟨St.A, u ++ (4 : Sym) :: zc :: zs, c, mo.sym :: r⟩) :
    ∃ d, Reachable d ∧ CascadeOver d := by
  obtain ⟨N, d, hN, hd⟩ := cascade_reaches_stop u hu c hc mo zc zs r
  exact ⟨d, hreach.iter hN, hd⟩

end TM2x5
