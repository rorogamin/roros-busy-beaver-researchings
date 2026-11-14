/-
# Which generated words the leading-run criterion misses

`scan_leading_run` settles a reset word `w` as soon as `nxw w + 2 ≤ lead w`,
where `lead w` is the length of the leading run of one bits.  Write

```
  D(w, h) = lead w - nxw w - h - 2
```

for the *deficit* of a generated word of Dyck height `h`.  Prepending a one bit
raises both `lead` and `h` by one and leaves `D` alone; a marker step raises
`lead` by one, raises `nxw` by `h` and resets the height to zero, so it raises
`D` by one.  On the base words `D` is `-3, -2, -1, r-5` for `r = 2, 3, 4` and
`r ≥ 5`.  The criterion is `D + h ≥ 0`, so it misses exactly the words with a
deficit that its height cannot pay for, and tracking the three negative values
of `D` through the two constructors shows those are six explicit families.

`gen_classify` is that statement: every generated word either satisfies the
leading-run criterion or is one of `Exc`.
-/
import RequestProject.BB25.Prefix.RB.Credit

namespace BB25.Prefix

open BB25

/-! ## The leading run of one bits -/

/-- The length of the leading run of one bits. -/
def lead : List RB → ℕ
  | .Y :: t => lead t + 1
  | _ => 0

@[simp] theorem lead_Y (t : List RB) : lead (.Y :: t) = lead t + 1 := rfl
@[simp] theorem lead_nil : lead [] = 0 := rfl

/-- If `u` is not a run of one bits, appending to it does not change its
leading run. -/
theorem lead_append_of_lt : ∀ (u : List RB), lead u < u.length → ∀ (v : List RB),
    lead (u ++ v) = lead u := by
  intro u
  induction u with
  | nil => intro h; simp at h
  | cons b t ih =>
      intro h v
      cases b <;> simp only [lead, List.cons_append]
      simp only [lead_Y, List.length_cons] at h
      rw [ih (by omega) v]

theorem lead_Yrun_append (L : ℕ) (s : List RB) :
    lead (List.replicate L .Y ++ s) = L + lead s := by
  induction L with
  | zero => simp
  | succ L ih => rw [List.replicate_succ, List.cons_append, lead_Y, ih]; omega

theorem nxw_Yrun_append (L : ℕ) (s : List RB) :
    nxw (List.replicate L .Y ++ s) = nxw s := by
  rw [nxw_append, nxw_Yrun, Nat.zero_add]

@[simp] theorem nxw_Xrun (c : ℕ) : nxw (List.replicate c .X) = c := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.replicate_succ, nxw_X, ih]

/-! ## The six exceptional families -/

/-- The core `X Y Y V` of the base word `w0 2`. -/
def cX : List RB := [.X, .Y, .Y, .V]

/-- The core `V Y Y V` of the base word `w0 3`. -/
def cV : List RB := [.V, .Y, .Y, .V]

/-- Deficit `-3`: the unextended `w0 2` with some one bits in front. -/
def E3 (w : List RB) (h : ℕ) : Prop :=
  ∃ k, w = List.replicate (k + 1) .Y ++ cX ∧ h = k + 1

/-- Deficit `-2`, first shape: the unextended `w0 3` with some one bits in
front. -/
def E2a (w : List RB) (h : ℕ) : Prop :=
  ∃ k, w = List.replicate (k + 2) .Y ++ cV ∧ h = k + 2

/-- Deficit `-2`, second shape: one marker step on a deficit `-3` word. -/
def E2b (w : List RB) (h : ℕ) : Prop :=
  ∃ j k, w = List.replicate (j + k + 2) .Y ++ (cX ++ List.replicate (k + 1) .X ++ [.V])
    ∧ h = j

/-- Deficit `-1` and height zero, first shape. -/
def F5 (w : List RB) : Prop :=
  ∃ k, w = List.replicate (k + 3) .Y ++ (cV ++ List.replicate (k + 2) .X ++ [.V])

/-- Deficit `-1` and height zero, second shape. -/
def F6 (w : List RB) : Prop :=
  ∃ j k, w = List.replicate (j + k + 3) .Y ++
    (cX ++ List.replicate (k + 1) .X ++ [.V] ++ List.replicate j .X ++ [.V])

/-- **The words the leading-run criterion misses.** -/
def Exc (w : List RB) : Prop :=
  (∃ k, k ≤ 1 ∧ w = List.replicate (k + 1) .Y ++ cX)
  ∨ ((∃ j k, j ≤ 1 ∧ w = List.replicate (j + k + 2) .Y ++
      (cX ++ List.replicate (k + 1) .X ++ [.V]))
  ∨ (F5 w ∨ F6 w))

/-! ## The classification invariant -/

/-- The four deficit classes of a generated word. -/
def Cls (w : List RB) (h : ℕ) : Prop :=
  (nxw w + h + 2 ≤ lead w)
  ∨ (nxw w + h + 2 = lead w + 1 ∧ (h = 0 → F5 w ∨ F6 w))
  ∨ (nxw w + h + 2 = lead w + 2 ∧ (E2a w h ∨ E2b w h))
  ∨ (nxw w + h + 2 = lead w + 3 ∧ E3 w h)

/-! ## The classification -/

theorem nxw_Vrun (c : ℕ) : nxw (List.replicate c .V) = 0 := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.replicate_succ, nxw_V, ih]

theorem gen_classify : ∀ {w : List RB} {h : ℕ}, Gen w h → Cls w h ∧ lead w < w.length := by
  intro w h hg
  induction hg with
  | @base r hr =>
      match r, hr with
      | 2, _ =>
          exact ⟨Or.inr (Or.inr (Or.inr ⟨by decide, ⟨0, rfl, rfl⟩⟩)), by decide⟩
      | 3, _ =>
          exact ⟨Or.inr (Or.inr (Or.inl ⟨by decide, Or.inl ⟨0, rfl, rfl⟩⟩)), by decide⟩
      | 4, _ =>
          exact ⟨Or.inr (Or.inl ⟨by decide, fun hc => absurd hc (by decide)⟩), by decide⟩
      | (k + 5), _ =>
          have hw : w0 (k + 5) = List.replicate (k + 4) .Y ++
              ([.V, .Y, .Y, .V, .X] ++ List.replicate (k + 2) .V) := by
            rw [show k + 5 = (k + 1) + 4 by omega, w0_big, kword,
              show k + 1 + 2 = k + 3 by omega, show k + 3 - 1 = k + 2 by omega,
              show List.replicate (k + 4) RB.Y = RB.Y :: List.replicate (k + 3) RB.Y by
                rw [List.replicate_succ]]
            simp [List.append_assoc]
          have hnx : nxw (w0 (k + 5)) = 1 := by
            rw [hw, nxw_Yrun_append, nxw_append, nxw_Vrun]
            rfl
          have hld : lead (w0 (k + 5)) = k + 4 := by
            rw [hw, lead_Yrun_append]
            rfl
          have hh0 : h0 (k + 5) = 1 := by rw [h0, if_neg (by omega)]
          refine ⟨Or.inl ?_, ?_⟩
          · rw [hnx, hld, hh0]; omega
          · rw [hld, hw]
            simp only [List.length_append, List.length_replicate]
            simp
  | @pre w h hgw ih =>
      obtain ⟨hcls, hlen⟩ := ih
      refine ⟨?_, by simpa using hlen⟩
      have hn : nxw (RB.Y :: w) = nxw w := rfl
      have hl : lead (RB.Y :: w) = lead w + 1 := rfl
      rcases hcls with hgood | ⟨he, hsh⟩ | ⟨he, hsh⟩ | ⟨he, hsh⟩
      · exact Or.inl (by rw [hn, hl]; omega)
      · exact Or.inr (Or.inl ⟨by rw [hn, hl]; omega, fun hc => absurd hc (by omega)⟩)
      · refine Or.inr (Or.inr (Or.inl ⟨by rw [hn, hl]; omega, ?_⟩))
        rcases hsh with ⟨k, hw, hh⟩ | ⟨j, k, hw, hh⟩
        · refine Or.inl ⟨k + 1, ?_, by omega⟩
          rw [hw, show k + 1 + 2 = (k + 2) + 1 by omega, List.replicate_succ]
          rfl
        · refine Or.inr ⟨j + 1, k, ?_, by omega⟩
          rw [hw, show j + 1 + k + 2 = (j + k + 2) + 1 by omega, List.replicate_succ]
          rfl
      · refine Or.inr (Or.inr (Or.inr ⟨by rw [hn, hl]; omega, ?_⟩))
        obtain ⟨k, hw, hh⟩ := hsh
        refine ⟨k + 1, ?_, by omega⟩
        rw [hw, show k + 1 + 1 = (k + 1) + 1 by omega, List.replicate_succ]
        rfl
  | @mark w h hgw ih =>
      obtain ⟨hcls, hlen⟩ := ih
      have hn : nxw (RB.Y :: (w ++ List.replicate h .X ++ [.V])) = nxw w + h := by
        show nxw (w ++ List.replicate h .X ++ [RB.V]) = nxw w + h
        rw [nxw_append, nxw_append, nxw_Xrun]
        rfl
      have hl : lead (RB.Y :: (w ++ List.replicate h .X ++ [.V])) = lead w + 1 := by
        show lead (w ++ List.replicate h .X ++ [RB.V]) + 1 = lead w + 1
        rw [List.append_assoc, lead_append_of_lt w hlen]
      have hlen' : lead (RB.Y :: (w ++ List.replicate h .X ++ [.V]))
          < (RB.Y :: (w ++ List.replicate h .X ++ [.V])).length := by
        rw [hl]
        simp only [List.length_cons, List.length_append]
        omega
      refine ⟨?_, hlen'⟩
      rcases hcls with hgood | ⟨he, hsh⟩ | ⟨he, hsh⟩ | ⟨he, hsh⟩
      · exact Or.inl (by rw [hn, hl]; omega)
      · exact Or.inl (by rw [hn, hl]; omega)
      · refine Or.inr (Or.inl ⟨by rw [hn, hl]; omega, ?_⟩)
        intro _
        rcases hsh with ⟨k, hw, hh⟩ | ⟨j, k, hw, hh⟩
        · refine Or.inl ⟨k, ?_⟩
          rw [hw, hh]
          simp [List.replicate_succ, List.append_assoc]
        · refine Or.inr ⟨j, k, ?_⟩
          rw [hw, hh]
          simp [List.replicate_succ, List.append_assoc]
      · refine Or.inr (Or.inr (Or.inl ⟨by rw [hn, hl]; omega, ?_⟩))
        obtain ⟨k, hw, hh⟩ := hsh
        refine Or.inr ⟨0, k, ?_, rfl⟩
        rw [hw, hh, show 0 + k + 2 = (k + 1) + 1 by omega]
        simp [List.replicate_succ, List.append_assoc]

/-- **Every generated word either satisfies the leading-run criterion or is one
of the six exceptional families.** -/
theorem gen_lead_or_exc {w : List RB} {h : ℕ} (hg : Gen w h) :
    nxw w + 2 ≤ lead w ∨ Exc w := by
  obtain ⟨hcls, -⟩ := gen_classify hg
  rcases hcls with hgood | ⟨he, hsh⟩ | ⟨he, hsh⟩ | ⟨he, hsh⟩
  · exact Or.inl (by omega)
  · rcases Nat.eq_zero_or_pos h with rfl | hpos
    · rcases hsh rfl with h5 | h6
      · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))
    · exact Or.inl (by omega)
  · rcases hsh with ⟨k, hw, hh⟩ | ⟨j, k, hw, hh⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · exact Or.inr (Or.inr (Or.inl ⟨j, k, by omega, hw⟩))
      · exact Or.inl (by omega)
  · obtain ⟨k, hw, hh⟩ := hsh
    rcases Nat.lt_or_ge k 2 with hk | hk
    · exact Or.inr (Or.inl ⟨k, by omega, hw⟩)
    · exact Or.inl (by omega)

end BB25.Prefix
