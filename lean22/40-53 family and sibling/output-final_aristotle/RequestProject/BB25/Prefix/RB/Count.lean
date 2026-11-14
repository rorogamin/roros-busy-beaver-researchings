/-
# The counter phase above a marker, and the exact marker return of `0RB`

The member `0RB` has the `A> 241` rule

```
  A> 241  ⟶  300 A>        (three base steps)
```

so the `241` block becomes the marker block `J0 = 300` and the head carries on
to the right.  When the head comes back to the marker,

```
  J0 <A  ⟶  <B1 22        (nine base steps)
```

the marker *disappears* and the head is back in the `<B1` sweep, with one more
`22` block in front of it.  So the sweep of `0RB` continues after a pop, like
the sweep of `1LA`, but the word in front of the head is no longer a run of
`22` blocks: the local counter the head builds above the marker drains against
it and deposits its decoded word.

This file proves the exact form of that deposit (`marker_return_word`): if the
head starts at `A>` in front of a word `w` of digit blocks which is a colored
Dyck prefix of height `h`, and the marker is directly below it, then the head
comes back to the marker with the word

```
  w X^h V
```

in front of it, where `X = 11` and `V = 21`.  Combining this with the two rules
above gives the whole pop episode of the `0RB` sweep (`rb_pop_episode`).

The ingredients are the *counter phase* `cfold` — `22` pushes a one bit, `21` a
pop, and `11` a decrement followed by a pop — and a version of the drain of
`Bottom.lean` that does not need the stack to be good (`drain_plain`), because
the local counter above a marker is *not* good in general: its decoded value
can be smaller than its counter.
-/
import RequestProject.BB25.Prefix.LA.Final

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## Colored Dyck words, with the heights carried along -/

/-- `DyckRun h w h'`: reading the word `w` of digit blocks from height `h`,
every close finds an open, and the final height is `h'`. -/
inductive DyckRun : ℕ → List RB → ℕ → Prop
  | nil (h : ℕ) : DyckRun h [] h
  | consY {h h' : ℕ} {w : List RB} : DyckRun (h + 1) w h' → DyckRun h (.Y :: w) h'
  | consV {h h' : ℕ} {w : List RB} : DyckRun h w h' → DyckRun (h + 1) (.V :: w) h'
  | consX {h h' : ℕ} {w : List RB} : DyckRun h w h' → DyckRun (h + 1) (.X :: w) h'

theorem DyckRun.digs : ∀ {h h' : ℕ} {w : List RB}, DyckRun h w h' → Digs w := by
  intro h h' w hd
  induction hd with
  | nil => exact Digs.nil
  | consY _ ih => exact Digs.cons (Or.inl rfl) ih
  | consV _ ih => exact Digs.cons (Or.inr (Or.inl rfl)) ih
  | consX _ ih => exact Digs.cons (Or.inr (Or.inr rfl)) ih

theorem DyckRun.append : ∀ {h h₁ h₂ : ℕ} {w v : List RB}, DyckRun h w h₁ → DyckRun h₁ v h₂ →
    DyckRun h (w ++ v) h₂ := by
  intro h h₁ h₂ w v hw hv
  induction hw with
  | nil => simpa using hv
  | consY _ ih => exact DyckRun.consY (ih hv)
  | consV _ ih => exact DyckRun.consV (ih hv)
  | consX _ ih => exact DyckRun.consX (ih hv)

/-- A Dyck run still fits when the whole stack is raised. -/
theorem DyckRun.shift : ∀ {h h' : ℕ} {w : List RB}, DyckRun h w h' → ∀ j : ℕ,
    DyckRun (h + j) w (h' + j) := by
  intro h h' w hd
  induction hd with
  | nil h => intro j; exact DyckRun.nil _
  | @consY h h' w _ ih =>
      intro j
      exact DyckRun.consY (by simpa [show h + 1 + j = h + j + 1 by omega] using ih j)
  | @consV h h' w _ ih =>
      intro j
      rw [show h + 1 + j = (h + j) + 1 by omega]
      exact DyckRun.consV (ih j)
  | @consX h h' w _ ih =>
      intro j
      rw [show h + 1 + j = (h + j) + 1 by omega]
      exact DyckRun.consX (ih j)

/-- A run of `h` closes from height `h`. -/
theorem dyckRun_Xrun : ∀ (h : ℕ), DyckRun h (List.replicate h .X) 0 := by
  intro h
  induction h with
  | zero => exact DyckRun.nil 0
  | succ h ih =>
      rw [List.replicate_succ]
      exact DyckRun.consX ih

theorem dyckRun_Yrun : ∀ (r h : ℕ), DyckRun h (List.replicate r .Y) (h + r) := by
  intro r
  induction r with
  | zero => intro h; simpa using DyckRun.nil h
  | succ r ih =>
      intro h
      rw [List.replicate_succ]
      have hh := ih (h + 1)
      rw [show h + 1 + r = h + (r + 1) by omega] at hh
      exact DyckRun.consY hh

/-! ## The counter phase -/

/-- One digit block of the counter phase, as an operation on the stack: `22`
pushes a one bit, `21` a pop, and `11` costs a decrement and then pops. -/
def cstep (σ : List LB) : RB → List LB
  | .Y => .Z :: σ
  | .V => .W :: σ
  | .X => .W :: cdec σ
  | _ => σ

@[simp] theorem cstep_Y (σ : List LB) : cstep σ .Y = .Z :: σ := rfl
@[simp] theorem cstep_V (σ : List LB) : cstep σ .V = .W :: σ := rfl
@[simp] theorem cstep_X (σ : List LB) : cstep σ .X = .W :: cdec σ := rfl

/-- The stack the counter phase builds from a whole word. -/
def cfold (σ : List LB) : List RB → List LB
  | [] => σ
  | b :: w => cfold (cstep σ b) w

@[simp] theorem cfold_nil (σ : List LB) : cfold σ [] = σ := rfl
@[simp] theorem cfold_cons (σ : List LB) (b : RB) (w : List RB) :
    cfold σ (b :: w) = cfold (cstep σ b) w := rfl

/-- **The counter phase over a foreign bottom.**  The head reads a colored
Dyck word above a marker: the local counter it builds is the all-ones numeral
of the current height, and its decoded word is the word just read. -/
theorem cfold_props (β : List LB) : ∀ {h h' : ℕ} {w : List RB}, DyckRun h w h' →
    ∀ {σ : List LB}, CStack σ → cval σ = 2 ^ h - 1 → ∀ rest : List RB,
      CStack (cfold σ w) ∧ cval (cfold σ w) = 2 ^ h' - 1 ∧ pdec (cfold σ w) = pdec σ ++ w ∧
        ∃ k, BRun (b4 := b4) ⟨rep β σ, .Rt, w ++ rest⟩ ⟨rep β (cfold σ w), .Rt, rest⟩ k := by
  intro h h' w hd
  induction hd with
  | nil h =>
      intro σ hst hcv rest
      exact ⟨hst, hcv, by simp, 0, by simpa using BRun.refl (b4 := b4) _⟩
  | @consY h h' w hd ih =>
      intro σ hst hcv rest
      have hpow : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      have hcv' : cval (.Z :: σ) = 2 ^ (h + 1) - 1 := by
        simp only [cval_Z, hcv, pow_succ]
        omega
      obtain ⟨g1, g2, g3, k, hrun⟩ := ih (σ := .Z :: σ) hst.consZ hcv' rest
      refine ⟨by simpa using g1, by simpa using g2, ?_, 2 + k, ?_⟩
      · rw [cfold_cons, cstep_Y, g3, pdec_Z]
        simp
      · refine BRun.head (show bstep b4 ⟨rep β σ, .Rt, (RB.Y :: w) ++ rest⟩
          = some (⟨.Z :: rep β σ, .Rt, w ++ rest⟩, 2) from rfl) ?_
        rw [← rep_Z]
        simpa using hrun
  | @consV h h' w hd ih =>
      intro σ hst hcv rest
      have hpow : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      have hodd : cval σ % 2 = 1 := by
        rw [hcv, pow_succ]
        omega
      have hcv' : cval (.W :: σ) = 2 ^ h - 1 := by
        simp only [cval_W, hcv, pow_succ]
        omega
      obtain ⟨g1, g2, g3, k, hrun⟩ := ih (σ := .W :: σ) hst.consW hcv' rest
      refine ⟨by simpa using g1, by simpa using g2, ?_, 2 + k, ?_⟩
      · rw [cfold_cons, cstep_V, g3, pdec_W, if_pos hodd]
        simp
      · refine BRun.head (show bstep b4 ⟨rep β σ, .Rt, (RB.V :: w) ++ rest⟩
          = some (⟨.W :: rep β σ, .Rt, w ++ rest⟩, 2) from rfl) ?_
        rw [← rep_W]
        simpa using hrun
  | @consX h h' w hd ih =>
      intro σ hst hcv rest
      have hpow : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      have h1cv : 1 ≤ cval σ := by
        rw [hcv, pow_succ]
        omega
      have hstd : CStack (cdec σ) := cdec_CStack_all hst
      have hcvd : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1cv
      have heven : cval (cdec σ) % 2 = 0 := by
        rw [hcvd, hcv, pow_succ]
        omega
      have hcv' : cval (.W :: cdec σ) = 2 ^ h - 1 := by
        simp only [cval_W, hcvd, hcv, pow_succ]
        omega
      obtain ⟨g1, g2, g3, k, hrun⟩ := ih (σ := .W :: cdec σ) hstd.consW hcv' rest
      obtain ⟨kd, hrund⟩ := brun_cdec_rep_of (b4 := b4) (β := β) hst h1cv (.V :: (w ++ rest))
      refine ⟨by simpa using g1, by simpa using g2, ?_, 1 + (kd + (2 + k)), ?_⟩
      · rw [cfold_cons, cstep_X, g3, pdec_W, if_neg (by omega), pdec_cdec hst h1cv]
        simp
      · refine BRun.head (show bstep b4 ⟨rep β σ, .Rt, (RB.X :: w) ++ rest⟩
          = some (⟨rep β σ, .Lt, .V :: (w ++ rest)⟩, 1) from rfl) ?_
        refine hrund.trans (BRun.head (show bstep b4 ⟨rep β (cdec σ), .Rt, RB.V :: (w ++ rest)⟩
          = some (⟨.W :: rep β (cdec σ), .Rt, w ++ rest⟩, 2) from rfl) ?_)
        rw [← rep_W]
        simpa using hrun

/-! ## The drain, without goodness -/

/-- The drain of an all-ones counter deposits a run of `11` blocks. -/
theorem dword_ones : ∀ h : ℕ, dword (2 ^ h - 1) = List.replicate h .X := by
  intro h
  induction h with
  | zero => simpa using dword_zero
  | succ h ih =>
      have hpow : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      have hp : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
      have he : 2 ^ (h + 1) - 1 = (2 ^ (h + 1) - 2) + 1 := by omega
      rw [he, dword_succ]
      have h3 : (2 ^ (h + 1) - 2) / 2 = 2 ^ h - 1 := by omega
      rw [if_neg (by omega), h3, ih, List.replicate_succ]

/-- **The drain over a foreign bottom, with its word and without goodness.**
This is `drain_rep_word` of `DrainWord.lean` with the goodness of the stack
dropped: the local counter above a marker need not be good, and none of the
steps of the drain uses it. -/
theorem drain_plain (β : List LB) : ∀ (n : ℕ) (σ : List LB), cval σ ≤ n → CStack σ →
    ∃ σ' k, CStack σ' ∧ cval σ' = 0 ∧ pdec σ' = pdec σ ++ dword (cval σ) ∧
      BRun (b4 := b4) ⟨rep β σ, .Rt, [.R]⟩ ⟨β, .Lt, pdec σ' ++ [.V, .R]⟩ k := by
  intro n
  induction n with
  | zero =>
      intro σ hn hst
      have hv : cval σ = 0 := by omega
      obtain ⟨k, hrun⟩ := brun_overflow_rep_of (b4 := b4) (β := β) hst hv [.V, .R]
      rw [ofw_eq_pdec hst hv] at hrun
      exact ⟨σ, 3 + k, hst, hv, by rw [hv]; simp [dword_zero], BRun.head
        (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl) hrun⟩
  | succ n ih =>
      intro σ hn hst
      rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
      · obtain ⟨k, hrun⟩ := brun_overflow_rep_of (b4 := b4) (β := β) hst h0 [.V, .R]
        rw [ofw_eq_pdec hst h0] at hrun
        exact ⟨σ, 3 + k, hst, h0, by rw [h0]; simp [dword_zero], BRun.head
          (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl) hrun⟩
      · have hstd : CStack (cdec σ) := cdec_CStack_all hst
        have hcvd : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
        have hpd : pdec (cdec σ) = pdec σ := pdec_cdec hst h1
        have hcv1 : cval (.W :: cdec σ) = (cval σ - 1) / 2 := by rw [cval_W, hcvd]
        obtain ⟨k₁, hrun₁⟩ := brun_cdec_rep_of (b4 := b4) (β := β) hst h1 [.V, .R]
        obtain ⟨σ', k, hst', hv', hw', hrun'⟩ := ih (.W :: cdec σ) (by omega) hstd.consW
        have hstep : pdec (.W :: cdec σ) = pdec σ ++ [if cval σ % 2 = 0 then RB.V else RB.X] := by
          rw [pdec_W, hpd, hcvd]
          by_cases hpar : cval σ % 2 = 0
          · rw [if_pos hpar, if_pos (by omega)]
          · rw [if_neg hpar, if_neg (by omega)]
        have hword : pdec σ' = pdec σ ++ dword (cval σ) := by
          rw [hw', hstep, hcv1, List.append_assoc]
          congr 1
          obtain ⟨u, hu⟩ : ∃ u, cval σ = u + 1 := ⟨cval σ - 1, by omega⟩
          rw [hu, dword_succ]
          have hh : (u + 1 - 1) / 2 = u / 2 := by omega
          rw [hh]
          by_cases hpar : (u + 1) % 2 = 0
          · rw [if_pos hpar]; rfl
          · rw [if_neg hpar]; rfl
        refine ⟨σ', 3 + (k₁ + (2 + k)), hst', hv', hword, ?_⟩
        refine BRun.head
          (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl)
          (hrun₁.trans (BRun.head (show bstep b4 ⟨rep β (cdec σ), .Rt, [RB.V, .R]⟩
            = some (⟨.W :: rep β (cdec σ), .Rt, [.R]⟩, 2) from rfl) ?_))
        rwa [← rep_W]

/-! ## The exact marker return -/

/-- **The first return of the head to an untouched marker.**  The head starts
at `A>` in front of a colored Dyck word `w` of height `h` and the bare right
end; it comes back to the marker in state `<A` with the word `w X^h V` in front
of it.  The marker itself has not been touched. -/
theorem marker_return_word {β : List LB} {h : ℕ} {w : List RB} (hd : DyckRun 0 w h) :
    ∃ k, BRun (b4 := b4) ⟨β, .Rt, w ++ [.R]⟩
      ⟨β, .Lt, (w ++ List.replicate h .X ++ [.V]) ++ [.R]⟩ k := by
  have hrepL : rep β ([.L] : List LB) = β := rfl
  obtain ⟨hst1, hcv1, hpd1, k1, hrun1⟩ :=
    cfold_props (b4 := b4) β hd (σ := [LB.L]) CStack.base (by simp) [.R]
  set σ : List LB := cfold [LB.L] w with hσ
  obtain ⟨σ', k2, hst2, hv2, hw2, hrun2⟩ := drain_plain (b4 := b4) β (cval σ) σ (le_refl _) hst1
  refine ⟨k1 + k2, ?_⟩
  have hw : pdec σ' = w ++ List.replicate h .X := by
    rw [hw2, hpd1, hcv1, dword_ones]
    simp
  rw [hrepL] at hrun1
  have hrun : BRun (b4 := b4) ⟨β, .Rt, w ++ [.R]⟩ ⟨β, .Lt, pdec σ' ++ [.V, .R]⟩ (k1 + k2) :=
    hrun1.trans hrun2
  rw [hw] at hrun
  simpa using hrun

/-- The marker rule of `0RB`: the marker disappears and the head is back in the
`<B1` sweep with one more `22` block. -/
theorem j0_step (c : List LB) (rt : List RB) :
    bstep b4 ⟨.J0 :: c, .Lt, rt⟩ = some (⟨c, .Bt, .Y :: rt⟩, 9) := rfl

/-- **One pop of the `0RB` sweep.**  The head meets a pop with a colored Dyck
word `w` of height `h` in front of it and at least two decrements below; it
comes back to the sweep two decrements lower, with the word `Y w X^h V`. -/
theorem rb_pop_episode {c : List LB} (hst : CStack c) (h2 : 2 ≤ cval c)
    {h : ℕ} {w : List RB} (hd : DyckRun 0 w h) :
    ∃ k, BRun (b4 := b4_0RB) ⟨.W :: c, .Bt, w ++ [.R]⟩
      ⟨cdec (cdec c), .Bt, (.Y :: (w ++ List.replicate h .X ++ [.V])) ++ [.R]⟩ k := by
  have h1 : 1 ≤ cval c := by omega
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hcvd : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  set tail : List RB := w ++ [RB.R] with htail
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4_0RB) hst h1 (.F :: tail)
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_0RB) hstd h1' (.G :: tail)
  obtain ⟨k3, hr3⟩ := marker_return_word (b4 := b4_0RB) (β := .J0 :: cdec (cdec c)) hd
  refine ⟨2 + (k1 + (1 + (k2 + (3 + (k3 + 9))))), ?_⟩
  refine BRun.head (show bstep b4_0RB ⟨.W :: c, .Bt, tail⟩
      = some (⟨c, .Lt, .F :: tail⟩, 2) from rfl) ?_
  refine hr1.trans (BRun.head (show bstep b4_0RB ⟨cdec c, .Rt, .F :: tail⟩
      = some (⟨cdec c, .Lt, .G :: tail⟩, 1) from rfl) ?_)
  refine hr2.trans (BRun.head (show bstep b4_0RB ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨.J0 :: cdec (cdec c), .Rt, tail⟩, 3) from rfl) ?_)
  exact hr3.trans (BRun.of_step (j0_step _ _))

end BB25.Prefix
