/-
# Plumbing for the early cases of the `0RB` branch

Four small pieces used by Sections 8.3 and 8.4 of the argument.

* `scan_append_stops`: a reverse scan that stops inside a suffix stops inside
  the whole word — the suffix only has to be read over the value the prefix
  leaves behind.
* `rep_L_self`: replacing the bottom `^11` of a counter stack by itself changes
  nothing, so the theorems proved over a foreign bottom apply to a genuine
  counter stack.
* `cfold_props_gen`: the counter phase over a stack whose counter is *not*
  exhausted.  A colored Dyck word read in the counter phase multiplies
  `counter + 1` by `2^height` and appends itself to the decoded word — this is
  the step of Section 8.3 that re-emits the word `w` into the decoder.
* `dword_eq_chi`: the word a drain deposits is the binary tail of `counter + 1`,
  i.e. the digits `chi` of `LA/Chi.lean`.
-/
import RequestProject.BB25.Prefix.RB.LemmaA
import RequestProject.BB25.Prefix.RB.Sweep

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## Generated words end in a zero-bit block -/

/-- Every generated word ends in a `21` block, so the checkpoint its reset
builds ends in a zero bit. -/
theorem gen_end_V : ∀ {w : List RB} {h : ℕ}, Gen w h → ∃ u, w = u ++ [RB.V] := by
  intro w h hg
  induction hg with
  | @base r hr =>
      match r, hr with
      | 2, _ => exact ⟨[.Y, .X, .Y, .Y], rfl⟩
      | 3, _ => exact ⟨[.Y, .Y, .V, .Y, .Y], rfl⟩
      | (k + 4), _ =>
          refine ⟨.Y :: (List.replicate (k + 2) .Y ++ [.V, .Y, .Y, .V, .X]
            ++ List.replicate k .V), ?_⟩
          have hk : k + 2 - 1 = k + 1 := rfl
          have hv : List.replicate (k + 1) RB.V = List.replicate k RB.V ++ [RB.V] :=
            List.replicate_succ'
          rw [w0_big, kword, hk, hv]
          simp only [List.cons_append, List.append_assoc]
  | pre _ ih =>
      obtain ⟨u, hu⟩ := ih
      exact ⟨.Y :: u, by rw [hu]; rfl⟩
  | @mark w h _ _ =>
      exact ⟨.Y :: (w ++ List.replicate h .X), by simp⟩

/-! ## The reset of a word at the bare right end -/

/-- **The reset of a word at the bare right end.**  The pending `2>` re-parses
the word over the stack `π`; the right end turns the head around and the
machine is at a `0RB` checkpoint, provided the word is clean and positive, ends
in a `21` block, and the paid stack it builds is ready. -/
theorem sret0_reset_end {π : List LB} (hst : CStack π) (hadm : Adm π) (hg : Good π)
    (hstr : Strict π) {w u : List RB} (hw : Digs w) (hend : w = u ++ [.V])
    (hpos : 1 ≤ rrun w (cval π)) (hready : Ready (tfold π w)) :
    SRet b4 ⟨π, .Rt, .P2 :: (w ++ [.R])⟩ := by
  have hcl0 : 0 ≤ rrun w (cval π) := by omega
  have hcl : 0 ≤ rrun w (cval (paid true π)) := by simpa using hcl0
  obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
    brun_paid (b4 := b4) w hw true π hst (by simp) hcl [.R]
  obtain ⟨hst', hadm', hg', hcv', -, -⟩ := tfold_props w hw (σ := π) hst hadm hg hcl0
  set ν : List LB := tfold π w with hν
  have hpaid' : paid p' phys = ν := by simpa using hpaid
  have hcvν : (cval ν : ℤ) = rrun w (cval π) := hcv'
  have hposν : 1 ≤ cval ν := by
    have : (1 : ℤ) ≤ (cval ν : ℤ) := by rw [hcvν]; exact hpos
    exact_mod_cast this
  have hendX : ∃ t, ν = .X :: t := ⟨tfold π u, by rw [hν, hend, tfold_append]; rfl⟩
  have hstrict : Strict ν := Strict.tfold w hw hst hadm hg hstr hcl0
  obtain ⟨k₂, hr₂⟩ := brun_end (b4 := b4) p' phys hstp (by
    intro hpf
    have := hcvp hpf
    omega)
  rw [hpaid'] at hr₂
  exact SRet.of_run (hrun.trans hr₂) (SRet.cp ⟨⟨hst', hadm', hg', hposν, hendX⟩, hready, hstrict⟩)

/-! ## The bottom of a genuine counter stack -/

/-- Replacing the bottom of a counter stack by the bottom block changes
nothing. -/
theorem rep_L_self : ∀ {s : List LB}, CStack s → rep [LB.L] s = s := by
  intro s hst
  induction hst with
  | base => rfl
  | consW _ ih => rw [rep_W, ih]
  | consX _ ih => rw [rep_X, ih]
  | consZ _ ih => rw [rep_Z, ih]

/-! ## The counter phase over a nonempty counter -/

/-- **The counter phase over an arbitrary counter.**  Reading a colored Dyck
word in the counter phase multiplies `counter + 1` by `2^height` and appends
the word itself to the decoded word. -/
theorem cfold_props_gen (A : ℕ) : ∀ {h h' : ℕ} {w : List RB}, DyckRun h w h' →
    ∀ {σ : List LB}, CStack σ → cval σ + 1 = 2 ^ h * (A + 1) → ∀ rest : List RB,
      CStack (cfold σ w) ∧ cval (cfold σ w) + 1 = 2 ^ h' * (A + 1) ∧
        pdec (cfold σ w) = pdec σ ++ w ∧
        ∃ k, BRun (b4 := b4) ⟨σ, .Rt, w ++ rest⟩ ⟨cfold σ w, .Rt, rest⟩ k := by
  intro h h' w hd
  induction hd with
  | nil h =>
      intro σ hst hcv rest
      exact ⟨hst, hcv, by simp, 0, by simpa using BRun.refl (b4 := b4) _⟩
  | @consY h h' w hd ih =>
      intro σ hst hcv rest
      have hp : (2:ℕ) ^ (h + 1) * (A + 1) = 2 * (2 ^ h * (A + 1)) := by ring
      have hcv' : cval (.Z :: σ) + 1 = 2 ^ (h + 1) * (A + 1) := by
        simp only [cval_Z]; omega
      obtain ⟨g1, g2, g3, k, hrun⟩ := ih (σ := .Z :: σ) hst.consZ hcv' rest
      refine ⟨by simpa using g1, by simpa using g2, ?_, 2 + k, ?_⟩
      · rw [cfold_cons, cstep_Y, g3, pdec_Z]
        simp
      · refine BRun.head (show bstep b4 ⟨σ, .Rt, (RB.Y :: w) ++ rest⟩
          = some (⟨.Z :: σ, .Rt, w ++ rest⟩, 2) from rfl) ?_
        simpa using hrun
  | @consV h h' w hd ih =>
      intro σ hst hcv rest
      have hpow : 1 ≤ 2 ^ h * (A + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hp : (2:ℕ) ^ (h + 1) * (A + 1) = 2 * (2 ^ h * (A + 1)) := by ring
      have hodd : cval σ % 2 = 1 := by omega
      have hcv' : cval (.W :: σ) + 1 = 2 ^ h * (A + 1) := by
        simp only [cval_W]; omega
      obtain ⟨g1, g2, g3, k, hrun⟩ := ih (σ := .W :: σ) hst.consW hcv' rest
      refine ⟨by simpa using g1, by simpa using g2, ?_, 2 + k, ?_⟩
      · rw [cfold_cons, cstep_V, g3, pdec_W, if_pos hodd]
        simp
      · refine BRun.head (show bstep b4 ⟨σ, .Rt, (RB.V :: w) ++ rest⟩
          = some (⟨.W :: σ, .Rt, w ++ rest⟩, 2) from rfl) ?_
        simpa using hrun
  | @consX h h' w hd ih =>
      intro σ hst hcv rest
      have hpow : 1 ≤ 2 ^ h * (A + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hp : (2:ℕ) ^ (h + 1) * (A + 1) = 2 * (2 ^ h * (A + 1)) := by ring
      have h1cv : 1 ≤ cval σ := by omega
      have hstd : CStack (cdec σ) := cdec_CStack_all hst
      have hcvd : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1cv
      have heven : cval (cdec σ) % 2 = 0 := by omega
      have hcv' : cval (.W :: cdec σ) + 1 = 2 ^ h * (A + 1) := by
        simp only [cval_W]; omega
      obtain ⟨g1, g2, g3, k, hrun⟩ := ih (σ := .W :: cdec σ) hstd.consW hcv' rest
      obtain ⟨kd, hrund⟩ := brun_cdec_of (b4 := b4) hst h1cv (.V :: (w ++ rest))
      refine ⟨by simpa using g1, by simpa using g2, ?_, 1 + (kd + (2 + k)), ?_⟩
      · rw [cfold_cons, cstep_X, g3, pdec_W, if_neg (by omega), pdec_cdec hst h1cv]
        simp
      · refine BRun.head (show bstep b4 ⟨σ, .Rt, (RB.X :: w) ++ rest⟩
          = some (⟨σ, .Lt, .V :: (w ++ rest)⟩, 1) from rfl) ?_
        refine hrund.trans (BRun.head (show bstep b4 ⟨cdec σ, .Rt, RB.V :: (w ++ rest)⟩
          = some (⟨.W :: cdec σ, .Rt, w ++ rest⟩, 2) from rfl) ?_)
        simpa using hrun

/-! ## The word of a drain -/

/-- The word a drain deposits is the binary tail of `counter + 1`. -/
theorem dword_eq_chi : ∀ v : ℕ, dword v = chi (v + 1) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
      match v with
      | 0 => rw [dword_zero, chi_of_lt (by omega)]
      | (u + 1) =>
          rw [dword_succ, chi_of_le (by omega), ih (u / 2) (by omega)]
          have h1 : u / 2 + 1 = (u + 1 + 1) / 2 := by omega
          have h2 : (if (u + 1) % 2 = 0 then RB.V else RB.X)
              = (if (u + 1 + 1) % 2 = 0 then RB.X else RB.V) := by
            by_cases he : (u + 1) % 2 = 0
            · rw [if_pos he, if_neg (by omega)]
            · rw [if_neg he, if_pos (by omega)]
          rw [h1, h2]

/-! ## The reset word of a counter phase followed by a drain -/

/-- The reset word the machine rebuilds after reading `v` in the counter phase
over the stack `.Z :: t` and draining the right end. -/
def wordCD (t : List LB) (v : List RB) (h : ℕ) : List RB :=
  pdec t ++ [RB.Y] ++ v ++ chi (2 ^ (h + 1) * (cval t + 1)) ++ [RB.V]

theorem digs_chi : ∀ m : ℕ, Digs (chi m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      rcases lt_or_ge m 2 with hm | hm
      · rw [chi_of_lt hm]; exact Digs.nil
      · rw [chi_of_le hm]
        refine Digs.cons ?_ (ih (m / 2) (by omega))
        by_cases he : m % 2 = 0
        · rw [if_pos he]; exact Or.inr (Or.inr rfl)
        · rw [if_neg he]; exact Or.inr (Or.inl rfl)

theorem digs_singleton {b : RB} (hb : Dig b) : Digs [b] := by
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact hb

theorem digs_wordCD {t : List LB} {v : List RB} {h : ℕ} (hv : Digs v) :
    Digs (wordCD t v h) :=
  ((((pdec_digs t).append (digs_singleton (Or.inl rfl))).append hv).append
    (digs_chi _)).append (digs_singleton (Or.inr (Or.inl rfl)))

/-! ## Starting letter of a generated word -/

/-- Every generated word starts with a `22` block. -/
theorem gen_start_Y : ∀ {w : List RB} {h : ℕ}, Gen w h → ∃ v, w = .Y :: v := by
  intro w h hg
  induction hg with
  | @base r hr =>
      match r, hr with
      | 2, _ => exact ⟨[.X, .Y, .Y, .V], rfl⟩
      | 3, _ => exact ⟨[.Y, .V, .Y, .Y, .V], rfl⟩
      | (k + 4), _ => exact ⟨kword (k + 2), w0_big k⟩
  | pre _ _ => exact ⟨_, rfl⟩
  | mark _ _ => exact ⟨_, rfl⟩

end BB25.Prefix
