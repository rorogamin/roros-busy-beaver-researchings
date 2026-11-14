/-
# Counter stacks over a foreign bottom

Four of the five members treated in `Marker.lean` push a *marker block* onto
the left stack when they consume the `241` block.  The counter that the machine
then builds sits on top of that marker, and until the head reaches it the
marker is inert: every rule of the block simulator that fires looks only at the
topmost left block.

`rep β s` is the stack `s` with its bottom block `^11` replaced by an arbitrary
list `β` — the *foreign bottom*.  Because `cval`, `bval`, `pdec`, `nbit`, `nsh`
and `cdec` all stop at the first block that is not `03`/`11`/`01`, all the
arithmetic of such a stack is the arithmetic of its **shadow** `s`, an ordinary
counter stack over `^11`; only the machine runs have to be redone, and they are
redone here:

* `brun_cdec_rep` — one excursion decrements the shadow;
* `brun_overflow_rep` — an exhausted shadow deposits its decoded word and
  leaves the head *at the foreign bottom* `β`, in state `<A`;
* `drain_rep` — the protected drain at the right end of the tape, ending in
  that same overflow.

`returns_reset_end` is the other half of the story and needs no foreign bottom:
the reset of a clean word over an arbitrary good base stack, ending at the
right end of the tape, reaches a safe checkpoint.
-/
import RequestProject.BB25.Prefix.Drain

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## Replacing the bottom of a counter stack -/

/-- `rep β s`: the stack `s` with everything from its bottom block on replaced
by `β`. -/
def rep (β : List LB) : List LB → List LB
  | .W :: s => .W :: rep β s
  | .X :: s => .X :: rep β s
  | .Z :: s => .Z :: rep β s
  | _ => β

@[simp] theorem rep_W (β s : List LB) : rep β (.W :: s) = .W :: rep β s := rfl
@[simp] theorem rep_X (β s : List LB) : rep β (.X :: s) = .X :: rep β s := rfl
@[simp] theorem rep_Z (β s : List LB) : rep β (.Z :: s) = .Z :: rep β s := rfl
@[simp] theorem rep_L (β s : List LB) : rep β (.L :: s) = β := rfl

theorem rep_Zrun (β : List LB) (n : ℕ) (s : List LB) :
    rep β (List.replicate n .Z ++ s) = List.replicate n .Z ++ rep β s := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

/-! ## The machine over a foreign bottom -/

/-- **The decrement, over a foreign bottom.**  The head enters a nonzero
counter in state `<A` and comes back out in state `A>`; it never reaches the
bottom, so the block list below is irrelevant. -/
theorem brun_cdec_rep (β : List LB) : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s →
    1 ≤ cval s → ∀ rt : List RB,
      ∃ k, BRun (b4 := b4) ⟨rep β s, .Lt, rt⟩ ⟨rep β (cdec s), .Rt, rt⟩ k := by
  intro n
  induction n with
  | zero =>
      intro s hlen hst _ _
      exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hst.ne_nil
  | succ n ih =>
      intro s hlen hst hv rt
      cases hst with
      | base => exact absurd hv (by simp)
      | @consX s hs =>
          have hlen' : s.length ≤ n := by simpa using hlen
          have hs1 : 1 ≤ cval s := by simp at hv; omega
          obtain ⟨k, hrun⟩ := ih s hlen' hs hs1 (.Y :: rt)
          refine ⟨2 + (k + 2), ?_⟩
          rw [cdec_X, rep_X, rep_Z]
          exact BRun.head
            (show bstep b4 ⟨.X :: rep β s, .Lt, rt⟩ = some (⟨rep β s, .Lt, .Y :: rt⟩, 2) from rfl)
            (hrun.trans (BRun.of_step (show bstep b4 ⟨rep β (cdec s), .Rt, .Y :: rt⟩
              = some (⟨.Z :: rep β (cdec s), .Rt, rt⟩, 2) from rfl)))
      | @consZ s hs =>
          refine ⟨3, ?_⟩
          rw [cdec_Z, rep_Z, rep_X]
          exact BRun.of_step
            (show bstep b4 ⟨.Z :: rep β s, .Lt, rt⟩ = some (⟨.X :: rep β s, .Rt, rt⟩, 3) from rfl)
      | @consW s hs =>
          have hlen' : s.length ≤ n := by simpa using hlen
          have hs2 : 2 ≤ cval s := by simp at hv; omega
          obtain ⟨k₁, hrun₁⟩ := ih s hlen' hs (by omega) (.X :: rt)
          have hv' : cval (cdec s) = cval s - 1 := cdec_cval hs (by omega)
          have hlen'' : (cdec s).length ≤ n := by rw [cdec_length]; exact hlen'
          obtain ⟨k₂, hrun₂⟩ :=
            ih (cdec s) hlen'' (cdec_CStack hs (by omega)) (by omega) (.V :: rt)
          refine ⟨2 + (k₁ + (1 + (k₂ + 2))), ?_⟩
          rw [cdec_W, rep_W, rep_W]
          exact BRun.head
            (show bstep b4 ⟨.W :: rep β s, .Lt, rt⟩ = some (⟨rep β s, .Lt, .X :: rt⟩, 2) from rfl)
            (hrun₁.trans (BRun.head (show bstep b4 ⟨rep β (cdec s), .Rt, .X :: rt⟩
                = some (⟨rep β (cdec s), .Lt, .V :: rt⟩, 1) from rfl)
              (hrun₂.trans (BRun.of_step (show bstep b4 ⟨rep β (cdec (cdec s)), .Rt, .V :: rt⟩
                = some (⟨.W :: rep β (cdec (cdec s)), .Rt, rt⟩, 2) from rfl)))))

theorem brun_cdec_rep_of {β s : List LB} (hst : CStack s) (hv : 1 ≤ cval s) (rt : List RB) :
    ∃ k, BRun (b4 := b4) ⟨rep β s, .Lt, rt⟩ ⟨rep β (cdec s), .Rt, rt⟩ k :=
  brun_cdec_rep β s.length s (le_refl _) hst hv rt

/-- **The overflow, over a foreign bottom.**  The head walks off the bottom of
an exhausted counter, depositing its decoded word, and arrives at the foreign
bottom in state `<A`. -/
theorem brun_overflow_rep (β : List LB) : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s →
    cval s = 0 → ∀ rt : List RB,
      ∃ k, BRun (b4 := b4) ⟨rep β s, .Lt, rt⟩ ⟨β, .Lt, ofw s ++ rt⟩ k := by
  intro n
  induction n with
  | zero =>
      intro s hlen hst _ _
      exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hst.ne_nil
  | succ n ih =>
      intro s hlen hst hv rt
      cases hst with
      | base => exact ⟨0, by simpa using BRun.refl (b4 := b4) _⟩
      | @consZ s hs => exact absurd hv (by simp)
      | @consX s hs =>
          have hlen' : s.length ≤ n := by simpa using hlen
          have h0 : cval s = 0 := by simp at hv; omega
          obtain ⟨k, hrun⟩ := ih s hlen' hs h0 (.Y :: rt)
          refine ⟨2 + k, ?_⟩
          rw [ofw_X, rep_X]
          simpa using BRun.head
            (show bstep b4 ⟨.X :: rep β s, .Lt, rt⟩ = some (⟨rep β s, .Lt, .Y :: rt⟩, 2) from rfl)
            hrun
      | @consW s hs =>
          have hlen' : s.length ≤ n := by simpa using hlen
          have h1 : cval s ≤ 1 := by simp at hv; omega
          rw [rep_W]
          rcases Nat.eq_zero_or_pos (cval s) with h0 | h0
          · obtain ⟨k, hrun⟩ := ih s hlen' hs h0 (.X :: rt)
            refine ⟨2 + k, ?_⟩
            rw [ofw_W, if_pos h0]
            simpa using BRun.head
              (show bstep b4 ⟨.W :: rep β s, .Lt, rt⟩ = some (⟨rep β s, .Lt, .X :: rt⟩, 2) from rfl)
              hrun
          · obtain ⟨k₁, hrun₁⟩ := brun_cdec_rep_of (b4 := b4) (β := β) hs h0 (.X :: rt)
            have hlen'' : (cdec s).length ≤ n := by rw [cdec_length]; exact hlen'
            have hv' : cval (cdec s) = 0 := by rw [cdec_cval hs (by omega)]; omega
            obtain ⟨k₂, hrun₂⟩ := ih (cdec s) hlen'' (cdec_CStack hs (by omega)) hv' (.V :: rt)
            refine ⟨2 + (k₁ + (1 + k₂)), ?_⟩
            rw [ofw_W, if_neg (by omega)]
            have hrun : BRun (b4 := b4) ⟨.W :: rep β s, .Lt, rt⟩
                ⟨β, .Lt, ofw (cdec s) ++ (.V :: rt)⟩ (2 + (k₁ + (1 + k₂))) :=
              BRun.head
                (show bstep b4 ⟨.W :: rep β s, .Lt, rt⟩
                  = some (⟨rep β s, .Lt, .X :: rt⟩, 2) from rfl)
                (hrun₁.trans (BRun.head (show bstep b4 ⟨rep β (cdec s), .Rt, .X :: rt⟩
                    = some (⟨rep β (cdec s), .Lt, .V :: rt⟩, 1) from rfl) hrun₂))
            simpa using hrun

theorem brun_overflow_rep_of {β s : List LB} (hst : CStack s) (hv : cval s = 0) (rt : List RB) :
    ∃ k, BRun (b4 := b4) ⟨rep β s, .Lt, rt⟩ ⟨β, .Lt, ofw s ++ rt⟩ k :=
  brun_overflow_rep β s.length s (le_refl _) hst hv rt

/-! ## The protected drain over a foreign bottom -/

/-- A protected right end that is also good.  Goodness survives the drain
because the drain bound is much stronger than goodness at every positive
counter value. -/
structure StrongG (σ : List LB) : Prop where
  st : CStack σ
  adm : Adm σ
  good : Good σ
  bound : 3 * ((cval σ : ℤ) + 1) ≤ bval σ + 2

/-- One round of the drain at the right end of the tape. -/
theorem strongG_round {σ : List LB} (h : StrongG σ) (hv : 1 ≤ cval σ) :
    StrongG (.W :: cdec σ) ∧ cval (.W :: cdec σ) < cval σ := by
  have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval h.st hv
  have hbv : bval (cdec σ) = bval σ := bval_cdec h.st hv
  have hstd : CStack (cdec σ) := cdec_CStack_all h.st
  have hadmd : Adm (cdec σ) := Adm.cdec h.st h.adm hv
  have hgd : Good (cdec σ) := Good.cdec h.st h.good hv
  have hcount : 1 ≤ nbit σ - nsh σ := one_le_unmatched h.st h.adm hv
  have hadmh := h.adm.head
  have hB := h.bound
  refine ⟨⟨hstd.consW, adm_consW hadmd ?_, good_consW hgd ?_, ?_⟩, ?_⟩
  · rw [nbit_cdec, nsh_cdec]; omega
  · rw [hcv, hbv]
    have : (0 : ℤ) ≤ cval σ := Int.natCast_nonneg _
    have hcast : ((cval σ - 1 : ℕ) : ℤ) = (cval σ : ℤ) - 1 := by
      have : 1 ≤ (cval σ : ℤ) := by exact_mod_cast hv
      omega
    rw [hcast]
    omega
  · simp only [cval_W, bval_W, hcv, hbv]
    have hcast : ((cval σ - 1 : ℕ) : ℤ) = (cval σ : ℤ) - 1 := by
      have : 1 ≤ (cval σ : ℤ) := by exact_mod_cast hv
      omega
    by_cases hodd : (cval σ - 1) % 2 = 1
    · simp only [hodd, if_pos]
      have h2 : ((cval σ - 1) / 2 : ℕ) ≤ cval σ - 1 := Nat.div_le_self _ _
      have h2' : (((cval σ - 1) / 2 : ℕ) : ℤ) ≤ (cval σ : ℤ) - 1 := by
        have : (((cval σ - 1) / 2 : ℕ) : ℤ) ≤ ((cval σ - 1 : ℕ) : ℤ) := by exact_mod_cast h2
        omega
      omega
    · simp only [hodd, if_false]
      have h2 : 2 * ((cval σ - 1) / 2 : ℕ) ≤ cval σ - 1 := Nat.mul_div_le _ _ |>.trans (le_refl _)
      have h2' : 2 * (((cval σ - 1) / 2 : ℕ) : ℤ) ≤ (cval σ : ℤ) - 1 := by
        have : (2 * ((cval σ - 1) / 2 : ℕ) : ℤ) ≤ ((cval σ - 1 : ℕ) : ℤ) := by exact_mod_cast h2
        push_cast at this ⊢
        omega
      have hdiv : 2 * (bval σ / 2) ≤ bval σ := Int.mul_ediv_add_emod (bval σ) 2 ▸ by
        have := Int.emod_nonneg (bval σ) (by norm_num : (2:ℤ) ≠ 0)
        omega
      omega
  · simp only [cval_W, hcv]
    have : (cval σ - 1) / 2 ≤ cval σ - 1 := Nat.div_le_self _ _
    omega

/-- **The protected drain, over a foreign bottom.**  The counter is drained to
zero and then overflows; the head arrives at the foreign bottom with the
decoded word of the exhausted stack, followed by the `21` block the right end
created. -/
theorem drain_rep (β : List LB) : ∀ (n : ℕ) (σ : List LB), cval σ ≤ n → StrongG σ →
    ∃ σ' k, StrongG σ' ∧ cval σ' = 0 ∧ (1 : ℤ) ≤ bval σ' ∧
      BRun (b4 := b4) ⟨rep β σ, .Rt, [.R]⟩ ⟨β, .Lt, pdec σ' ++ [.V, .R]⟩ k := by
  intro n
  induction n with
  | zero =>
      intro σ hn h
      have hv : cval σ = 0 := by omega
      have hb : (1 : ℤ) ≤ bval σ := by
        have := h.bound; rw [hv] at this; simpa using by omega
      obtain ⟨k, hrun⟩ := brun_overflow_rep_of (b4 := b4) (β := β) h.st hv [.V, .R]
      rw [ofw_eq_pdec h.st hv] at hrun
      exact ⟨σ, 3 + k, h, hv, hb, BRun.head
        (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl) hrun⟩
  | succ n ih =>
      intro σ hn h
      rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
      · have hb : (1 : ℤ) ≤ bval σ := by
          have := h.bound; rw [h0] at this; simpa using by omega
        obtain ⟨k, hrun⟩ := brun_overflow_rep_of (b4 := b4) (β := β) h.st h0 [.V, .R]
        rw [ofw_eq_pdec h.st h0] at hrun
        exact ⟨σ, 3 + k, h, h0, hb, BRun.head
          (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl) hrun⟩
      · obtain ⟨hS, hlt⟩ := strongG_round h h1
        obtain ⟨k₁, hrun₁⟩ := brun_cdec_rep_of (b4 := b4) (β := β) h.st h1 [.V, .R]
        obtain ⟨σ', k, hS', hv', hb', hrun'⟩ := ih (.W :: cdec σ) (by omega) hS
        refine ⟨σ', 3 + (k₁ + (2 + k)), hS', hv', hb', ?_⟩
        refine BRun.head
          (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl)
          (hrun₁.trans (BRun.head (show bstep b4 ⟨rep β (cdec σ), .Rt, [RB.V, .R]⟩
            = some (⟨.W :: rep β (cdec σ), .Rt, [.R]⟩, 2) from rfl) ?_))
        rwa [← rep_W]

theorem drain_rep_of {β σ : List LB} (h : StrongG σ) :
    ∃ σ' k, StrongG σ' ∧ cval σ' = 0 ∧ (1 : ℤ) ≤ bval σ' ∧
      BRun (b4 := b4) ⟨rep β σ, .Rt, [.R]⟩ ⟨β, .Lt, pdec σ' ++ [.V, .R]⟩ k :=
  drain_rep β (cval σ) σ (le_refl _) h

/-! ## The entry into the drain -/

/-- Two decrements, a pop and the pending-`2>` tail `2> 22 22 1$` bring a good
stack to a protected right end. -/
theorem strongG_entry {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ)
    (h2 : 2 ≤ cval σ) : StrongG (.W :: .Z :: .Z :: .W :: cdec (cdec σ)) := by
  have h1 : 1 ≤ cval σ := by omega
  have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
  have hbv : bval (cdec σ) = bval σ := bval_cdec hst h1
  have hstd : CStack (cdec σ) := cdec_CStack_all hst
  have hadmd : Adm (cdec σ) := Adm.cdec hst hadm h1
  have hgd : Good (cdec σ) := Good.cdec hst hg h1
  have h1' : 1 ≤ cval (cdec σ) := by omega
  have hcv2 : cval (cdec (cdec σ)) = cval σ - 2 := by
    rw [cdec_cval hstd h1', hcv]; omega
  have hbv2 : bval (cdec (cdec σ)) = bval σ := by rw [bval_cdec hstd h1', hbv]
  have hstd2 : CStack (cdec (cdec σ)) := cdec_CStack_all hstd
  have hadmd2 : Adm (cdec (cdec σ)) := Adm.cdec hstd hadmd h1'
  have hgd2 : Good (cdec (cdec σ)) := Good.cdec hstd hgd h1'
  have hcount : 1 ≤ nbit σ - nsh σ := one_le_unmatched hst hadm h1
  have hgh : (cval σ : ℤ) ≤ bval σ := hg.head
  have hcast : ((cval σ - 2 : ℕ) : ℤ) = (cval σ : ℤ) - 2 := by
    have : 2 ≤ (cval σ : ℤ) := by exact_mod_cast h2
    omega
  -- the pop
  set τ : List LB := .W :: cdec (cdec σ) with hτ
  have hstτ : CStack τ := hstd2.consW
  have hadmτ : Adm τ := adm_consW hadmd2 (by rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]; omega)
  have hgτ : Good τ := good_consW hgd2 (by rw [hcv2, hbv2, hcast]; omega)
  have hheadτ : (cval τ : ℤ) ≤ bval τ := hgτ.head
  -- two bits
  set ρ : List LB := .Z :: .Z :: τ with hρ
  have hstρ : CStack ρ := hstτ.consZ.consZ
  have hadmρ : Adm ρ := adm_consZ (adm_consZ hadmτ)
  have hgρ : Good ρ := good_consZ (good_consZ hgτ)
  have hcvρ : cval ρ = 4 * cval τ + 3 := by simp [hρ]; ring
  have hbvρ : bval ρ = 4 * bval τ + 3 := by simp [hρ]; ring
  refine ⟨hstρ.consW, adm_consW hadmρ ?_, hgρ.cons ?_, ?_⟩
  · simp only [hρ, hτ, nbit_Z, nsh_Z, nbit_W, nsh_W, nbit_cdec, nsh_cdec]
    have := hadm.head
    omega
  · simp only [cval_W, bval_W, hcvρ, hbvρ]
    have : ((4 * cval τ + 3) / 2 : ℕ) = 2 * cval τ + 1 := by omega
    rw [this]
    push_cast
    omega
  · simp only [cval_W, bval_W, hcvρ, hbvρ]
    have : ((4 * cval τ + 3) / 2 : ℕ) = 2 * cval τ + 1 := by omega
    rw [this]
    push_cast
    omega

/-! ## The reset of a clean word at the right end -/

/-- **The reset of a clean word over a good base stack.**  The word is
re-parsed on top of `π`, the right end of the tape turns the head around and
the machine reaches a safe checkpoint — provided the word ends in a `21` block,
so that the checkpoint ends in a zero bit. -/
theorem returns_reset_end {π : List LB} (hst : CStack π) (hadm : Adm π) (hg : Good π)
    {w w' : List RB} (hw : Digs w) (hend : w = w' ++ [.V])
    (hpos : 1 ≤ rrun w (cval π)) :
    Returns b4 ⟨π, .Rt, .P2 :: (w ++ [.R])⟩ := by
  have hcl : 0 ≤ rrun w (cval (paid true π)) := by simpa using by omega
  obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
    brun_paid (b4 := b4) w hw true π hst (by simp) hcl [.R]
  obtain ⟨hst', hadm', hg', hcv', -, -⟩ :=
    tfold_props w hw (σ := π) hst hadm hg (by simpa using by omega)
  set ν : List LB := tfold π w with hν
  have hpaid' : paid p' phys = ν := by simpa using hpaid
  have hcvν : (cval ν : ℤ) = rrun w (cval π) := hcv'
  have hposν : 1 ≤ cval ν := by
    have : (1 : ℤ) ≤ (cval ν : ℤ) := by rw [hcvν]; exact hpos
    exact_mod_cast this
  have hendX : ∃ t, ν = .X :: t := ⟨tfold π w', by rw [hν, hend, tfold_append]; rfl⟩
  obtain ⟨k₂, hr₂⟩ := brun_end (b4 := b4) p' phys hstp (by
    intro hpf
    have := hcvp hpf
    omega)
  rw [hpaid'] at hr₂
  exact Returns.of_run (hrun.trans hr₂) (Returns.cp ⟨hst', hadm', hg', hposν, hendX⟩)

end BB25.Prefix
