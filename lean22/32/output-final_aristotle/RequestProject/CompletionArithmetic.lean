import RequestProject.Shape
import RequestProject.Success

/-!
# Completion of the non-halting proof — arithmetic layer

This file, together with `RequestProject.CompletionSaturation` and
`RequestProject.Completion`, completes the non-halting proof of the machine
`1LB3RB0LB---2RB_2RA3LA4LB2LB0RA`.  The mathematical argument it formalises was
supplied with the task (`nonhalting_completion.zip`,
`nonhalting_completion/NONHALTING_PROOF.md`) as an uncompiled candidate; the
source here is that candidate with the proof repairs needed to make it
elaborate, and it is now machine-checked.

`xnext` is the **exact** reset gap after a block, provided the block is
affordable, and the word created by a normal phase is a
function of the gap alone rather than an arbitrary word.  That is what removes
the density hypotheses that earlier attempts at this proof needed.
-/

namespace SOC.Completion

/-- Exact reset gap. The branch for `3` is immaterial for labelled words. -/
def xnext (g : Nat) (b : Sym) : Nat :=
  match b with
  | 0 => 2 * g
  | 1 => 2 * ((g - 8) / 3) + 1
  | 2 => 2 * g - 1
  | _ => 2 * g + 1

@[simp] theorem xnext_zero (g : Nat) : xnext g 0 = 2 * g := rfl
@[simp] theorem xnext_one (g : Nat) : xnext g 1 = 2 * ((g - 8) / 3) + 1 := rfl
@[simp] theorem xnext_two (g : Nat) : xnext g 2 = 2 * g - 1 := rfl
@[simp] theorem xnext_three (g : Nat) : xnext g 3 = 2 * g + 1 := rfl
@[simp] theorem xnext_four (g : Nat) : xnext g 4 = 2 * g + 1 := rfl

def XSafe : Nat → List Sym → Prop
  | _, [] => True
  | g, b :: L => (b = 1 → 8 ≤ g) ∧ (b = 2 → 1 ≤ g) ∧ XSafe (xnext g b) L

def xfold : Nat → List Sym → Nat
  | g, [] => g
  | g, b :: L => xfold (xnext g b) L

instance decXSafe : (g : Nat) → (L : List Sym) → Decidable (XSafe g L)
  | _, [] => isTrue trivial
  | g, b :: L =>
      letI : Decidable (XSafe (xnext g b) L) := decXSafe (xnext g b) L
      inferInstanceAs
        (Decidable ((b = 1 → 8 ≤ g) ∧ (b = 2 → 1 ≤ g) ∧ XSafe (xnext g b) L))

theorem xnext_mono {g G : Nat} (h : g ≤ G) (b : Sym) : xnext g b ≤ xnext G b := by
  rcases sym_cases b with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

theorem xnext_le_four (g : Nat) (b : Sym) : xnext g b ≤ xnext g 4 := by
  rcases sym_cases b with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

theorem xnext_one_le {g : Nat} (hg : 8 ≤ g) (b : Sym) : xnext g 1 ≤ xnext g b := by
  rcases sym_cases b with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

theorem xfold_append (g : Nat) (L M : List Sym) :
    xfold g (L ++ M) = xfold (xfold g L) M := by
  induction L generalizing g with
  | nil => rfl
  | cons b L ih => simpa [xfold] using ih (xnext g b)

theorem xsafe_append {g : Nat} {L M : List Sym} (hL : XSafe g L)
    (hM : XSafe (xfold g L) M) : XSafe g (L ++ M) := by
  induction L generalizing g with
  | nil => exact hM
  | cons b L ih =>
      exact ⟨hL.1, hL.2.1, ih hL.2.2 hM⟩

/-- The least starting gap that safely reads a block and leaves at least `T`. -/
def inv (b : Sym) (T : Nat) : Nat :=
  match b with
  | 0 => (T + 1) / 2
  | 1 => 8 + 3 * (T / 2)
  | 2 => (T + 2) / 2
  | _ => T / 2

theorem inv_sound {b : Sym} {T G : Nat} (h : inv b T ≤ G) :
    (b = 1 → 8 ≤ G) ∧ (b = 2 → 1 ≤ G) ∧ T ≤ xnext G b := by
  rcases sym_cases b with rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;> simp_all [inv, xnext] <;> omega

theorem inv_twice_bound (b : Sym) (T : Nat) : 2 * inv b T ≤ 3 * T + 16 := by
  rcases sym_cases b with rfl | rfl | rfl | rfl | rfl <;> simp only [inv] <;> omega

/-- The saturation labels of a digit `03`, respectively `23`, above gap `h`. -/
def beta (h : Nat) : Sym := if h % 3 = 0 then 0 else if h % 3 = 1 then 2 else 1

def alpha (h : Nat) : Sym := if h % 3 = 0 then 2 else if h % 3 = 1 then 1 else 0

/-- One normal cycle, including the pushed `03`. -/
def descend (g : Nat) : Nat := (2 * g - 1) / 3

/-- The digit released by the `03` that this cycle pushes. -/
def freshDigit (g : Nat) : Sym :=
  if g % 3 = 0 then 1 else if g % 3 = 1 then 0 else 2

theorem descend_lt {g : Nat} (hg : 0 < g) : descend g < g := by
  unfold descend
  omega

theorem freshDigit_succ (h : Nat) : freshDigit (h + 1) = beta h := by
  have h3 : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2 := by omega
  have e : (h + 1) % 3 = if h % 3 = 0 then 1 else if h % 3 = 1 then 2 else 0 := by
    rcases h3 with h3 | h3 | h3 <;> simp [h3] <;> omega
  rcases h3 with h3 | h3 | h3 <;> simp [freshDigit, beta, e, h3]

def fresh : Nat → List Sym
  | 0 => []
  | g + 1 => freshDigit (g + 1) :: fresh (descend (g + 1))
termination_by g => g
decreasing_by exact descend_lt (Nat.succ_pos g)

@[simp] theorem fresh_zero : fresh 0 = [] := by rw [fresh]

theorem fresh_pos {g : Nat} (hg : 0 < g) :
    fresh g = freshDigit g :: fresh (descend g) := by
  cases g with
  | zero => omega
  | succ n => rw [fresh]

/-- Required starting gap for the normal fresh word, with final gap at least 62. -/
def need : Nat → Nat
  | 0 => 62
  | g + 1 => inv (freshDigit (g + 1)) (need (descend (g + 1)))
termination_by g => g
decreasing_by exact descend_lt (Nat.succ_pos g)

@[simp] theorem need_zero : need 0 = 62 := by rw [need]

theorem need_pos {g : Nat} (hg : 0 < g) :
    need g = inv (freshDigit g) (need (descend g)) := by
  cases g with
  | zero => omega
  | succ n => rw [need]

theorem need_safe (g : Nat) :
    ∀ G : Nat, need g ≤ G → XSafe G (fresh g) ∧ 62 ≤ xfold G (fresh g) := by
  induction g using Nat.strongRecOn with
  | ind g ih =>
      intro G hG
      by_cases hz : g = 0
      · subst g
        simp only [fresh_zero, need_zero, XSafe, xfold] at *
        exact ⟨trivial, hG⟩
      · have hg : 0 < g := by omega
        rw [need_pos hg] at hG
        obtain ⟨h1, h2, hn⟩ := inv_sound hG
        obtain ⟨hs, he⟩ := ih (descend g) (descend_lt hg) (xnext G (freshDigit g)) hn
        rw [fresh_pos hg]
        exact ⟨⟨h1, h2, hs⟩, he⟩

/-- Certificate A: 67 cases, not a trajectory simulation. -/
theorem normal_small_certificate :
    ∀ g : Fin 200, 133 ≤ g.val → need g.val + 30 ≤ 2 * g.val := by
  native_decide

/-- The unbounded part is strong induction; only the small base is evaluated. -/
theorem need_bound (g : Nat) (hg : 133 ≤ g) : need g + 30 ≤ 2 * g := by
  revert hg
  induction g using Nat.strongRecOn with
  | ind g ih =>
      intro hg
      by_cases hsmall : g < 200
      · exact normal_small_certificate ⟨g, hsmall⟩ hg
      · have hd : 133 ≤ descend g := by unfold descend; omega
        have hp : 0 < g := by omega
        have hi := ih (descend g) (descend_lt hp) hd
        rw [need_pos hp]
        rcases (show g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 by omega) with h3 | h3 | h3
        · have hf : freshDigit g = 1 := by simp [freshDigit, h3]
          rw [hf]; simp only [inv]; unfold descend at *; omega
        · have hf : freshDigit g = 0 := by simp [freshDigit, h3]
          rw [hf]; simp only [inv]; unfold descend at *; omega
        · have hf : freshDigit g = 2 := by simp [freshDigit, h3]
          rw [hf]; simp only [inv]; unfold descend at *; omega

/-- Every nonempty normal fresh word ends in `04`. -/
theorem fresh_ends_zero (g : Nat) (hg : 0 < g) :
    ∃ P : List Sym, fresh g = P ++ [0] := by
  revert hg
  induction g using Nat.strongRecOn with
  | ind g ih =>
      intro hg
      by_cases hd : descend g = 0
      · have hg1 : g = 1 := by unfold descend at hd; omega
        subst g
        exact ⟨[], by rw [fresh_pos (by decide)]; simp [descend, freshDigit]⟩
      · obtain ⟨P, hP⟩ := ih (descend g) (descend_lt hg) (by omega)
        refine ⟨freshDigit g :: P, ?_⟩
        rw [fresh_pos hg, hP]
        rfl

def junctionTop (g : Nat) : Nat := (g - 8) / 3

def junctionGap (g : Nat) : Nat := (2 * junctionTop g) / 3

def junctionFirst (g : Nat) : Sym :=
  if g % 3 = 0 then 0 else if g % 3 = 1 then 1 else 2

def suffix (g : Nat) : List Sym :=
  junctionFirst g :: alpha (junctionTop g) :: fresh (junctionGap g)

def suffixNeed (g : Nat) : Nat :=
  inv (junctionFirst g) (inv (alpha (junctionTop g)) (need (junctionGap g)))

/-- Certificate B: 273 even gaps, 62,64,...,606. -/
theorem junction_small_certificate :
    ∀ g : Fin 608, 62 ≤ g.val → g.val % 2 = 0 → suffixNeed g.val ≤ g.val := by
  native_decide

theorem suffix_need_bound (g : Nat) (hg : 62 ≤ g) (heven : g % 2 = 0) :
    suffixNeed g ≤ g := by
  by_cases hsmall : g < 608
  · exact junction_small_certificate ⟨g, hsmall⟩ hg heven
  · have hj : 133 ≤ junctionGap g := by
      unfold junctionGap junctionTop
      omega
    have hN := need_bound (junctionGap g) hj
    have hI2 := inv_twice_bound (alpha (junctionTop g)) (need (junctionGap g))
    have hI1 := inv_twice_bound (junctionFirst g)
      (inv (alpha (junctionTop g)) (need (junctionGap g)))
    have hJ : 9 * junctionGap g ≤ 2 * g := by
      unfold junctionGap junctionTop
      omega
    unfold suffixNeed
    omega

/-- The scalar closure lemma, independent of any upgrade-count hypothesis. -/
theorem suffix_safe {g G : Nat} (hg : 62 ≤ g) (heven : g % 2 = 0) (hG : g ≤ G) :
    XSafe G (suffix g) ∧ 62 ≤ xfold G (suffix g) ∧ xfold G (suffix g) % 2 = 0 := by
  have hN : suffixNeed g ≤ G := Nat.le_trans (suffix_need_bound g hg heven) hG
  obtain ⟨h11, h12, h1⟩ := inv_sound hN
  obtain ⟨h21, h22, h2⟩ := inv_sound h1
  obtain ⟨hs, he⟩ := need_safe (junctionGap g) _ h2
  have hsafe : XSafe G (suffix g) := ⟨h11, h12, h21, h22, hs⟩
  have hend : 62 ≤ xfold G (suffix g) := he
  have hjpos : 0 < junctionGap g := by unfold junctionGap junctionTop; omega
  obtain ⟨P, hP⟩ := fresh_ends_zero (junctionGap g) hjpos
  have hsuffix : suffix g = (junctionFirst g :: alpha (junctionTop g) :: P) ++ [0] := by
    simp [suffix, hP]
  refine ⟨hsafe, hend, ?_⟩
  rw [hsuffix, xfold_append]
  simp [xfold]

end SOC.Completion
