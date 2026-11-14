module

public import RequestProject.Levels

/-!
# The chaotic counter: digit encoding and structural laws

After the bouncer has been removed, every cell of the right half-tape is a copy
of the transducer `cell1`.  A cell that has already sent the head into its
right neighbour (flag `true`) holds `1`, `2` or `3` forever and never halts
(`cellDies_emitted`).  In this *emitted* regime a cell is one digit of a binary
counter whose `1`-digits carry a colour:

| content | digit          |
|---------|----------------|
| `2`     | `0`            |
| `1`     | `1`, colour a  |
| `3`     | `1`, colour b  |

An arriving `A` is an increment, an arriving `B` is a second kind of signal.

* `phase_law`: the digit (`0` iff the content is `2`) after reading a word `w`
  is the starting digit plus the number of `A`s in `w`, modulo 2.  The `B`s and
  the colours never change the digit.
* `token_zero`: a `0`-digit turns the token `B^r A` into `(B A)^r` and becomes
  a `1`-digit of colour a;
* `token_one`: a `1`-digit of colour a turns the token `B^s A` into
  `A^(s/2)` followed by `A` (`s` even) or `B` (`s` odd), and becomes a `0`-digit.

So in the emitted regime the input is cut at its `A`s into tokens `B^r A`,
which are read alternately by a `0`-digit and by a `1`-digit.

* `BABA_preimage`: a blank cell emits a word beginning with `B A B A` (the
  word on which its right neighbour halts, `cellDies_blank_iff`) iff its own
  input begins with `ABBAAA`, `ABBAABB`, `BBBBAAA` or `BBBBAABB`.
-/

@[expose] public section

namespace BCM

/-- The counter digit of a cell content in the emitted regime: `2 ↦ 0`,
`1, 3 ↦ 1`. -/
def isZeroDigit (c : Sym) : Bool := c == 2

/-- **Phase law.**  Started from a content `c ∈ {1, 2, 3}` with flag `true`,
a cell reading any word `w` ends in a content `c' ∈ {1, 2, 3}` with flag
`true`, and `c'` is the zero digit `2` iff (`c` is `2`) xor (`w` has an odd
number of `A`s). -/
theorem phase_law (w : List St) : ∀ c : Sym, (c = 1 ∨ c = 2 ∨ c = 3) →
    ∃ c' : Sym, cellEnd c true w = some (c', true) ∧ (c' = 1 ∨ c' = 2 ∨ c' = 3) ∧
      isZeroDigit c' = (isZeroDigit c ^^ (w.count .A % 2 == 1)) := by
  induction w with
  | nil =>
      intro c hc
      exact ⟨c, rfl, hc, by simp⟩
  | cons x w ih =>
      intro c hc
      have par : ∀ (a b : Bool) (x : St), (b = (a ^^ (x == .A))) →
          ∀ bw : Bool, (b ^^ bw) = (a ^^ ((x :: w).count .A % 2 == 1)) ↔
            bw = (w.count .A % 2 == 1) := by
        intro a b x hb bw
        subst hb
        rcases Nat.mod_two_eq_zero_or_one (List.count St.A w) with h | h <;> cases x <;>
          cases a <;> cases bw <;> simp [h, Nat.add_mod]
      rcases hc with rfl | rfl | rfl <;> cases x
      all_goals first
        | (obtain ⟨c', h1, h2, h3⟩ := ih 1 (by decide)
           exact ⟨c', by simpa [cellEnd, cell1] using h1, h2,
             by rw [h3]; exact (par _ _ _ (by decide) _).mpr rfl⟩)
        | (obtain ⟨c', h1, h2, h3⟩ := ih 2 (by decide)
           exact ⟨c', by simpa [cellEnd, cell1] using h1, h2,
             by rw [h3]; exact (par _ _ _ (by decide) _).mpr rfl⟩)
        | (obtain ⟨c', h1, h2, h3⟩ := ih 3 (by decide)
           exact ⟨c', by simpa [cellEnd, cell1] using h1, h2,
             by rw [h3]; exact (par _ _ _ (by decide) _).mpr rfl⟩)

/-- `r` copies of the letter `B`. -/
def bs (r : Nat) : List St := List.replicate r .B

/-- **Token law for a `0`-digit.**  A cell holding `2` (in the emitted regime)
turns the token `B^r A` into `(B A)^r` and ends holding `1`. -/
theorem token_zero (r : Nat) :
    cellOut 2 true (bs r ++ [.A]) = (List.replicate r [St.B, .A]).flatten ∧
      cellEnd 2 true (bs r ++ [.A]) = some (1, true) := by
  induction r with
  | zero => exact ⟨rfl, rfl⟩
  | succ r ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [bs, List.replicate_succ, List.cons_append, List.flatten_cons] at h1 h2 ⊢
      refine ⟨?_, ?_⟩
      · simp only [cellOut, cell1]
        rw [h1]; rfl
      · simp only [cellEnd, cell1]
        exact h2

/-- **Token law for a `1`-digit.**  A cell holding `1` (in the emitted regime)
turns the token `B^s A` into `A^(s/2)` followed by `A` if `s` is even and by
`B` if `s` is odd, and ends holding `2`. -/
theorem token_one : ∀ s : Nat,
    cellOut 1 true (bs s ++ [.A]) =
        List.replicate (s / 2) St.A ++ [if s % 2 = 0 then St.A else St.B] ∧
      cellEnd 1 true (bs s ++ [.A]) = some (2, true)
  | 0 => ⟨rfl, rfl⟩
  | 1 => ⟨rfl, rfl⟩
  | s + 2 => by
      obtain ⟨h1, h2⟩ := token_one s
      simp only [bs, List.replicate_succ, List.cons_append] at h1 h2 ⊢
      refine ⟨?_, ?_⟩
      · simp only [cellOut, cell1]
        rw [h1, show (s + 2) / 2 = s / 2 + 1 by omega, show (s + 2) % 2 = s % 2 by omega,
          List.replicate_succ]
        rfl
      · simp only [cellEnd, cell1]
        exact h2

/-- **The dangerous prefixes.**  A blank cell emits a word beginning with
`B A B A` — the input on which the next (blank) cell halts — if and only if its
own input begins with `ABBAAA`, `ABBAABB`, `BBBBAAA` or `BBBBAABB`. -/
theorem BABA_preimage (w : List St) :
    [St.B, .A, .B, .A] <+: cellOut 0 false w ↔
      ([St.A, .B, .B, .A, .A, .A] <+: w ∨ [St.A, .B, .B, .A, .A, .B, .B] <+: w ∨
        [St.B, .B, .B, .B, .A, .A, .A] <+: w ∨ [St.B, .B, .B, .B, .A, .A, .B, .B] <+: w) := by
  rcases w with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8, w⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    (try cases x1) <;> (try cases x2) <;> (try cases x3) <;> (try cases x4) <;>
    (try cases x5) <;> (try cases x6) <;> (try cases x7) <;> (try cases x8) <;>
    simp [cellOut, cell1]

end BCM
