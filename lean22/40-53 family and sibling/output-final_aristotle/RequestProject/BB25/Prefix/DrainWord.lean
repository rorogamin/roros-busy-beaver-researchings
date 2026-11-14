/-
# The word the drain deposits

The protected drain of `Bottom.lean` ends with the head at the foreign bottom
and the decoded word of the exhausted stack on the tape.  For the member `2RA`
that word has to be known *explicitly*, because the marker `K0` turns the head
around without creating a pending digit and the machine then re-reads the word
in the counter phase, where the usual reset arithmetic does not apply.

Fortunately the word is easy to follow: one round of the drain replaces the
stack `σ` by `03 ⌜σ-1⌝`, and

```
  pdec (W :: cdec σ) = pdec σ ++ [if cval σ is even then V else X]
```

because the decrement does not change the decoded word.  So the drain simply
*appends* one digit per round, chosen by the parity of the counter, and the
counter itself follows `v ↦ (v - 1) / 2`.  `dword v` is the word of those
digits and `drain_rep_word` is the drain of `Bottom.lean` with that extra
conclusion.

The file also collects the runs of equal blocks used by the explicit
calculations: a run of `21` blocks read in the counter phase (`brun_Vrun`),
and the counter, the decoded word and the reset value of such runs.
-/
import RequestProject.BB25.Prefix.Bottom

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## Runs of equal blocks -/

theorem pdec_Zrun (r : ℕ) (σ : List LB) :
    pdec (List.replicate r .Z ++ σ) = pdec σ ++ List.replicate r .Y := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append, pdec_Z, ih, List.replicate_succ']
      simp

theorem cval_Wrun (k : ℕ) (σ : List LB) :
    cval (List.replicate k .W ++ σ) = cval σ / 2 ^ k := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, cval_W, ih, Nat.div_div_eq_div_mul, pow_succ]

theorem rep_Wrun (β : List LB) (k : ℕ) (s : List LB) :
    rep β (List.replicate k .W ++ s) = List.replicate k .W ++ rep β s := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

theorem CStack_Wrun {σ : List LB} (k : ℕ) (h : CStack σ) :
    CStack (List.replicate k .W ++ σ) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [List.replicate_succ, List.cons_append]; exact ih.consW

/-- A tower of pops over an all-ones counter: every pop closes a one bit, so
every deposited digit is a `21` block. -/
theorem pdec_Wrun_ones : ∀ (k : ℕ) (σ : List LB), cval σ = 2 ^ k - 1 →
    pdec (List.replicate k .W ++ σ) = pdec σ ++ List.replicate k .V := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro σ hσ
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hodd : cval σ % 2 = 1 := by
        rw [hσ]
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      have hcv : cval (.W :: σ) = 2 ^ k - 1 := by
        rw [cval_W, hσ]
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      have := ih (.W :: σ) hcv
      rw [List.replicate_succ', List.append_assoc]
      simp only [List.singleton_append]
      rw [this, pdec_W, if_pos hodd, List.append_assoc]
      rfl

/-- **A run of `21` blocks read in the counter phase.**  Each one pushes a
pop. -/
theorem brun_Vrun (k : ℕ) (σ : List LB) (rest : List RB) :
    BRun b4 ⟨σ, .Rt, List.replicate k .V ++ rest⟩
      ⟨List.replicate k .W ++ σ, .Rt, rest⟩ (2 * k) := by
  induction k generalizing σ with
  | zero => simpa using BRun.refl (b4 := b4) _
  | succ k ih =>
      have h1 : bstep b4 ⟨σ, .Rt, RB.V :: (List.replicate k RB.V ++ rest)⟩
          = some (⟨.W :: σ, .Rt, List.replicate k .V ++ rest⟩, 2) := rfl
      have hrun := BRun.head (b4 := b4) h1 (ih (.W :: σ))
      have he : List.replicate k LB.W ++ (LB.W :: σ) = List.replicate (k + 1) LB.W ++ σ := by
        simp [List.replicate_succ', List.append_assoc]
      rw [he] at hrun
      rw [List.replicate_succ, List.cons_append]
      have hk : 2 + 2 * k = 2 * (k + 1) := by ring
      rwa [hk] at hrun

/-- A word of `21` blocks doubles the reset value. -/
theorem rrun_replicate_V (k : ℕ) (a : ℤ) :
    rrun (List.replicate k RB.V) a = 2 ^ k * a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, rrun_cons, ih, rstep_V, pow_succ]
      ring

theorem digs_replicate_V (k : ℕ) : Digs (List.replicate k RB.V) := by
  intro b hb
  rw [List.eq_of_mem_replicate hb]
  exact Or.inr (Or.inl rfl)

theorem digs_replicate_Y (k : ℕ) : Digs (List.replicate k RB.Y) := by
  intro b hb
  rw [List.eq_of_mem_replicate hb]
  exact Or.inl rfl

/-! ## The word of the drain -/

/-- The digits the drain appends, one per round: `21` when the counter is even
and `11` when it is odd. -/
def dword : ℕ → List RB
  | 0 => []
  | (v + 1) => (if (v + 1) % 2 = 0 then RB.V else RB.X) :: dword (v / 2)

theorem dword_zero : dword 0 = [] := by rw [dword]

theorem dword_succ (v : ℕ) :
    dword (v + 1) = (if (v + 1) % 2 = 0 then RB.V else RB.X) :: dword (v / 2) := by
  rw [dword]

/-- The drain of a counter `2^k - 2` deposits `k - 1` `21` blocks. -/
theorem dword_ones_even : ∀ k : ℕ, dword (2 ^ (k + 1) - 2) = List.replicate k .V := by
  intro k
  induction k with
  | zero => norm_num [dword]
  | succ k ih =>
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hp2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
      have he : 2 ^ (k + 2) - 2 = (2 ^ (k + 2) - 3) + 1 := by omega
      rw [he, dword_succ]
      have h2 : (2 ^ (k + 2) - 3 + 1) % 2 = 0 := by omega
      have h3 : (2 ^ (k + 2) - 3) / 2 = 2 ^ (k + 1) - 2 := by omega
      rw [if_pos h2, h3, ih, List.replicate_succ]

/-- The drain of the marker episode: the entry counter is `2^n - 3`. -/
theorem dword_entry (n : ℕ) (hn : 2 ≤ n) :
    dword (2 ^ n - 3) = .X :: List.replicate (n - 2) .V := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hp2 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
  have he : 2 ^ (m + 2) - 3 = (2 ^ (m + 2) - 4) + 1 := by omega
  rw [he, dword_succ]
  have h2 : (2 ^ (m + 2) - 4 + 1) % 2 = 1 := by omega
  have h3 : (2 ^ (m + 2) - 4) / 2 = 2 ^ (m + 1) - 2 := by omega
  rw [if_neg (by omega), h3, dword_ones_even]
  congr 1

/-! ## The drain, with its deposited word -/

/-- **The protected drain over a foreign bottom, with its word.**  This is
`drain_rep` of `Bottom.lean` together with the exact word the drain leaves on
the tape. -/
theorem drain_rep_word (β : List LB) : ∀ (n : ℕ) (σ : List LB), cval σ ≤ n → StrongG σ →
    ∃ σ' k, StrongG σ' ∧ cval σ' = 0 ∧ (1 : ℤ) ≤ bval σ' ∧
      pdec σ' = pdec σ ++ dword (cval σ) ∧
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
      refine ⟨σ, 3 + k, h, hv, hb, by rw [hv]; simp [dword], BRun.head
        (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl) hrun⟩
  | succ n ih =>
      intro σ hn h
      rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
      · have hb : (1 : ℤ) ≤ bval σ := by
          have := h.bound; rw [h0] at this; simpa using by omega
        obtain ⟨k, hrun⟩ := brun_overflow_rep_of (b4 := b4) (β := β) h.st h0 [.V, .R]
        rw [ofw_eq_pdec h.st h0] at hrun
        exact ⟨σ, 3 + k, h, h0, hb, by rw [h0]; simp [dword], BRun.head
          (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl) hrun⟩
      · obtain ⟨hS, hlt⟩ := strongG_round h h1
        obtain ⟨k₁, hrun₁⟩ := brun_cdec_rep_of (b4 := b4) (β := β) h.st h1 [.V, .R]
        obtain ⟨σ', k, hS', hv', hb', hw', hrun'⟩ := ih (.W :: cdec σ) (by omega) hS
        -- the word of one round
        have hcvd : cval (cdec σ) = cval σ - 1 := cdec_cval h.st h1
        have hpd : pdec (cdec σ) = pdec σ := pdec_cdec h.st h1
        have hstep : pdec (.W :: cdec σ) = pdec σ
            ++ [if cval σ % 2 = 0 then RB.V else RB.X] := by
          rw [pdec_W, hpd, hcvd]
          by_cases hpar : cval σ % 2 = 0
          · rw [if_pos hpar, if_pos (by omega)]
          · rw [if_neg hpar, if_neg (by omega)]
        have hcv1 : cval (.W :: cdec σ) = (cval σ - 1) / 2 := by rw [cval_W, hcvd]
        have hword : pdec σ' = pdec σ ++ dword (cval σ) := by
          rw [hw', hstep, hcv1, List.append_assoc]
          congr 1
          obtain ⟨u, hu⟩ : ∃ u, cval σ = u + 1 := ⟨cval σ - 1, by omega⟩
          rw [hu, dword_succ]
          have : (u + 1 - 1) / 2 = u / 2 := by omega
          rw [this]
          by_cases hpar : (u + 1) % 2 = 0
          · rw [if_pos hpar]; rfl
          · rw [if_neg hpar]; rfl
        refine ⟨σ', 3 + (k₁ + (2 + k)), hS', hv', hb', hword, ?_⟩
        refine BRun.head
          (show bstep b4 ⟨rep β σ, .Rt, [.R]⟩ = some (⟨rep β σ, .Lt, [.V, .R]⟩, 3) from rfl)
          (hrun₁.trans (BRun.head (show bstep b4 ⟨rep β (cdec σ), .Rt, [RB.V, .R]⟩
            = some (⟨.W :: rep β (cdec σ), .Rt, [.R]⟩, 2) from rfl) ?_))
        rwa [← rep_W]

theorem drain_rep_word_of {β σ : List LB} (h : StrongG σ) :
    ∃ σ' k, StrongG σ' ∧ cval σ' = 0 ∧ (1 : ℤ) ≤ bval σ' ∧
      pdec σ' = pdec σ ++ dword (cval σ) ∧
      BRun (b4 := b4) ⟨rep β σ, .Rt, [.R]⟩ ⟨β, .Lt, pdec σ' ++ [.V, .R]⟩ k :=
  drain_rep_word β (cval σ) σ (le_refl _) h

/-! ## The word of a marker episode -/

/-- The word the counter above a marker deposits on it: `n` is the number of
one bits the sweep left there. -/
def kword (n : ℕ) : List RB :=
  List.replicate n .Y ++ [.V, .Y, .Y, .V, .X] ++ List.replicate (n - 1) .V

theorem digs_kword (n : ℕ) : Digs (kword n) := by
  refine ((digs_replicate_Y n).append ?_).append (digs_replicate_V _)
  intro b hb
  fin_cases hb <;> simp [Dig]

/-- Its reset value from zero is `2^(2n+2) - 3 * 2^n`. -/
theorem rrun_kword (n : ℕ) (hn : 1 ≤ n) :
    rrun (kword n) 0 = 2 ^ (2 * n + 2) - 3 * 2 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdiv : ∀ a : ℤ, (2 * a) / 2 = a := fun a => by omega
  rw [kword]
  simp only [Nat.add_sub_cancel]
  rw [rrun_append, rrun_append, rrun_replicate_Y, rrun_replicate_V]
  simp only [rrun_cons, rrun_nil, rstep_V, rstep_Y, rstep_X]
  have hQ : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have key : 2 * (2 * (2 * (2 * ((2 : ℤ) ^ (m + 1) * (0 + 1) - 1)) + 1) + 1)
      = 2 * (8 * 2 ^ (m + 1) - 5) := by ring
  rw [key, hdiv]
  have h1 : (2 : ℤ) ^ (2 * (m + 1) + 2) = 16 * (2 ^ m * 2 ^ m) := by
    rw [show 2 * (m + 1) + 2 = m + m + 4 by ring, pow_add, pow_add]
    ring
  rw [h1, hQ]
  ring

theorem rrun_kword_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ rrun (kword n) 0 := by
  rw [rrun_kword n hn]
  have h1 : (2 : ℤ) ^ (2 * n + 2) = 2 ^ n * (2 ^ n * 4) := by
    rw [show 2 * n + 2 = n + n + 2 by ring, pow_add, pow_add]
    ring
  have h2 : (2 : ℤ) ≤ 2 ^ n := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h3 : (0 : ℤ) < 2 ^ n := by positivity
  rw [h1]
  nlinarith

/-- **The local counter above a marker drains onto it.**  Whatever the marker
block `β` begins with, the sweep's `n ≥ 2` one bits above it become a counter
that drains and overflows, leaving the word `kword n` in front of the right
end.  Until the head reaches the marker this is independent of the marker
rule. -/
theorem marker_drain_gen {β : List LB} (k : ℕ) {P : BCfg → Prop}
    (hP : ∀ {c c' : BCfg} {k : ℕ}, BRun b4 c c' k → P c' → P c)
    (hcont : P ⟨β, .Lt, kword (k + 2) ++ [.R]⟩) :
    P ⟨List.replicate (k + 2) .Z ++ β, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  set n : ℕ := k + 2 with hn
  set p : List LB := List.replicate n .Z ++ [.L] with hp
  have hpow : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowk : 2 ≤ 2 ^ (k + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnk : 2 ^ n = 2 * 2 ^ (k + 1) := by rw [hn, pow_succ]; ring
  have hstp : CStack p := CStack_Zrun _ CStack.base
  have hadmp : Adm p := Adm_Zrun _ adm_L
  have hgp : Good p := Good_Zrun _ good_L
  have hcvp : cval p = 2 ^ n - 1 := by rw [hp, cval_Zrun]; simp
  have hpdp : pdec p = List.replicate n .Y := by rw [hp, pdec_Zrun]; simp
  have hrep : rep β p = List.replicate n .Z ++ β := by rw [hp, rep_Zrun, rep_L]
  rw [← hrep]
  -- two decrements, a pop and the `22` tail bring the head to the right end
  have h1 : 1 ≤ cval p := by omega
  have hstd : CStack (cdec p) := cdec_CStack_all hstp
  have hcvd : cval (cdec p) = 2 ^ n - 2 := by rw [cdec_cval hstp h1, hcvp]; omega
  have hpdd : pdec (cdec p) = List.replicate n .Y := by rw [pdec_cdec hstp h1, hpdp]
  have h1' : 1 ≤ cval (cdec p) := by omega
  have hstd2 : CStack (cdec (cdec p)) := cdec_CStack_all hstd
  have hcvd2 : cval (cdec (cdec p)) = 2 ^ n - 3 := by rw [cdec_cval hstd h1', hcvd]; omega
  have hpdd2 : pdec (cdec (cdec p)) = List.replicate n .Y := by
    rw [pdec_cdec hstd h1', hpdd]
  obtain ⟨k₁, hr₁⟩ := brun_cdec_rep_of (b4 := b4) (β := β) hstp h1 [.X, .P2, .Y, .Y, .R1]
  obtain ⟨k₂, hr₂⟩ := brun_cdec_rep_of (b4 := b4) (β := β) hstd h1' [.V, .P2, .Y, .Y, .R1]
  refine hP hr₁ ?_
  refine hP (c' := ⟨rep β (cdec p), .Lt, [.V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine hP hr₂ ?_
  refine hP (c' := ⟨.W :: rep β (cdec (cdec p)), .Rt, [.P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine hP (c' := ⟨.W :: rep β (cdec (cdec p)), .Rt, [.Y, .P2, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine hP (c' := ⟨.Z :: .W :: rep β (cdec (cdec p)), .Rt, [.P2, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine hP (c' := ⟨.Z :: .W :: rep β (cdec (cdec p)), .Rt, [.Y, .P2, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine hP
    (c' := ⟨.Z :: .Z :: .W :: rep β (cdec (cdec p)), .Rt, [.P2, .R1]⟩) (BRun.of_step rfl) ?_
  refine hP
    (c' := ⟨.Z :: .Z :: .W :: rep β (cdec (cdec p)), .Rt, [.V, .R]⟩) (BRun.of_step rfl) ?_
  refine hP
    (c' := ⟨.W :: .Z :: .Z :: .W :: rep β (cdec (cdec p)), .Rt, [.R]⟩) (BRun.of_step rfl) ?_
  -- the entry of the drain, and its counter and decoded word
  set E : List LB := .W :: .Z :: .Z :: .W :: cdec (cdec p) with hE
  have hrwE : (.W :: .Z :: .Z :: .W :: rep β (cdec (cdec p)) : List LB) = rep β E := rfl
  rw [hrwE]
  have hcvE : cval E = 2 ^ n - 3 := by
    rw [hE]
    simp only [cval_W, cval_Z, hcvd2]
    omega
  have hpdE : pdec E = List.replicate n .Y ++ [.V, .Y, .Y, .V] := by
    rw [hE]
    rw [pdec_W, pdec_Z, pdec_Z, pdec_W, hpdd2, hcvd2, if_pos (by omega)]
    simp only [cval_Z, cval_W, hcvd2]
    rw [if_pos (by omega)]
    simp
  -- the drain
  obtain ⟨σ', k₃, hS', hcv', hb', hword', hr₃⟩ :=
    drain_rep_word_of (b4 := b4) (β := β) (strongG_entry hstp hadmp hgp (by omega))
  refine hP hr₃ ?_
  -- the word it deposited is the word of the episode
  have hw : pdec σ' ++ [RB.V, RB.R] = kword n ++ [RB.R] := by
    rw [hword', hcvE, hpdE, dword_entry n (by omega), kword]
    simp only [hn, Nat.add_sub_cancel]
    simp [List.replicate_succ']
  rw [hw]
  exact hcont

/-- **The local counter above a marker drains onto it**, in the form used by
the members whose marker rule ends the sweep. -/
theorem marker_drain {β : List LB} (k : ℕ)
    (hcont : Returns b4 ⟨β, .Lt, kword (k + 2) ++ [.R]⟩) :
    Returns b4 ⟨List.replicate (k + 2) .Z ++ β, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ :=
  marker_drain_gen k Returns.of_run hcont

end BB25.Prefix
