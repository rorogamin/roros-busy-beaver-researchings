import RequestProject.CompletionSaturation

/-!
# Completion of the non-halting proof

`SOC.Completion.neverHalts : SOC.NeverHalts` — the machine
`1LB3RB0LB---2RB_2RA3LA4LB2LB0RA` never halts from the blank tape.

The proof keeps the invariant "the released block sequence is safely resettable
and its exact reset gap is even and at least 62" along the revolutions of
`revIter`, using the exact reset maps of `RequestProject.CompletionArithmetic`
and the saturation bridge of `RequestProject.CompletionSaturation`; the machine
enters the invariant at the second released sequence (`seed`).  No density,
upgrade-count, or infinite-trajectory hypothesis is used.  The two
arithmetic base certificates and the seed are finite `native_decide` checks.

The argument was supplied with the task as an uncompiled candidate
(`nonhalting_completion.zip`); it is repaired where needed and machine-checked
here.
-/

namespace SOC.Completion

/-- The executable reset computes the exact scalar gap. -/
theorem reset_exact : ∀ {w : List LD}, BinHead w → ∀ {L : List Sym},
    (∀ b, b ∈ L → Label b) → XSafe (gap w) L ->
      ∃ w', resetF w L = some w' ∧ BinHead w' ∧ gap w' = xfold (gap w) L
  | w, hb, [], _, _ => ⟨w, rfl, hb, rfl⟩
  | w, hb, x :: L, hlab, hs => by
      obtain ⟨p1, p2, p3⟩ := hs
      have hx : Label x := hlab x (by simp)
      have hlab' : ∀ y, y ∈ L → Label y := fun y hy => hlab y (by simp [hy])
      have key : ∀ w1 : List LD, resetF w (x :: L) = resetF w1 L → BinHead w1 ->
          gap w1 = xnext (gap w) x ->
          ∃ w', resetF w (x :: L) = some w' ∧ BinHead w' ∧
            gap w' = xfold (gap w) (x :: L) := by
        intro w1 heq hb1 hg1
        have hs1 : XSafe (gap w1) L := by rw [hg1]; exact p3
        obtain ⟨w', hw', hb', hg'⟩ := reset_exact hb1 hlab' hs1
        refine ⟨w', by rw [heq, hw'], hb', ?_⟩
        rw [hg', hg1]
        rfl
      rcases hx with rfl | rfl | rfl | rfl
      · exact key (.d0 :: w) rfl trivial rfl
      · exact key (.d1 :: w) rfl trivial rfl
      · have hp : 1 ≤ gap w := p2 rfl
        obtain ⟨w1, hw1, hg1⟩ := addT_of_le_gap 1 hp
        refine key (.d0 :: w1) ?_ trivial ?_
        · rw [resetF, hw1]
        · simp only [gap_d0, xnext_two]
          omega
      · have h8 : 8 ≤ gap w := p1 rfl
        match w, hb with
        | .d0 :: v, _ =>
            have hv : 4 ≤ gap v := by simp only [gap_d0] at h8; omega
            obtain ⟨v', hv', hgv⟩ := addT_of_le_gap 4 hv
            refine key (.d0 :: .dB :: v') ?_ trivial ?_
            · rw [resetF, hv']
            · simp only [gap_d0, gap_dB, xnext_one]
              omega
        | .d1 :: v, _ =>
            have hv : 4 ≤ gap v := by simp only [gap_d1] at h8; omega
            obtain ⟨v', hv', hgv⟩ := addT_of_le_gap 4 hv
            refine key (.d0 :: .dA :: v') ?_ trivial ?_
            · rw [resetF, hv']
            · simp only [gap_d0, gap_dA, gap_d1, xnext_one]
              omega

/-- Exact inherited domination, using the already established shape relation. -/
theorem inherited_exact : ∀ {S L : List Sym} {g G : Nat},
    S.map is4 = L.map notOne → XSafe g L → g ≤ G ->
      XSafe G S ∧ xfold g L ≤ xfold G S
  | [], [], g, G, _, _, h => ⟨trivial, h⟩
  | [], x :: L, _, _, h, _, _ => by simp at h
  | y :: S, [], _, _, h, _, _ => by simp at h
  | y :: S, x :: L, g, G, h, hs, hG => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hhead, htail⟩ := h
      obtain ⟨h1, h2, hrest⟩ := hs
      by_cases hx : x = 1
      · subst x
        have hg8 : 8 ≤ g := h1 rfl
        have hG8 : 8 ≤ G := by omega
        have hstep : xnext g 1 ≤ xnext G y :=
          Nat.le_trans (xnext_mono hG 1) (xnext_one_le hG8 y)
        obtain ⟨hS, he⟩ := inherited_exact htail hrest hstep
        exact ⟨⟨fun _ => hG8, fun _ => by omega, hS⟩, he⟩
      · have hy : y = 4 := is4_eq_true.1 (by rw [hhead]; simp [notOne, hx])
        subst y
        have hstep : xnext g x ≤ xnext G 4 :=
          Nat.le_trans (xnext_mono hG x) (xnext_le_four G x)
        obtain ⟨hS, he⟩ := inherited_exact htail hrest hstep
        exact ⟨⟨fun hc => absurd hc (by decide), fun hc => absurd hc (by decide), hS⟩, he⟩

def Invariant (L : List Sym) : Prop :=
  XSafe 1 L ∧ 62 ≤ xfold 1 L ∧ xfold 1 L % 2 = 0

/-- Every sequence satisfying the invariant has a successor satisfying it. -/
theorem invariant_step {L : List Sym} (hlab : ∀ x, x ∈ L → Label x)
    (hInv : Invariant L) :
    ∃ L', revolutionF L = some L' ∧ Invariant L' := by
  obtain ⟨hSafe, h62, hEven⟩ := hInv
  obtain ⟨w, hreset, hb, hgap⟩ :=
    reset_exact (w := [LD.d0]) trivial hlab (by simpa [gap] using hSafe)
  have hwgap : gap w = xfold 1 L := by simpa [gap] using hgap
  have hw62 : 62 ≤ gap w := by omega
  have hwEven : gap w % 2 = 0 := by omega
  have hjSome := junctionF_isSome hb (by omega : 9 ≤ gap w)
  cases hj : junctionF w with
  | none => rw [hj] at hjSome; simp at hjSome
  | some wj =>
      let L' : List Sym := sat wj ++ fresh (gap wj)
      have hrev : revolutionF L = some L' := by
        rw [revolutionF, hreset, Option.bind_some, hj, Option.bind_some, normal_exact]
        simp [L']
      obtain ⟨S, hS, hshape⟩ := revolution_suffix hreset hrev
      obtain ⟨hsInherited, hdom⟩ := inherited_exact hshape hSafe (Nat.le_refl 1)
      have hstart : gap w ≤ xfold 1 S := by omega
      obtain ⟨hsFresh, heFresh, hpFresh⟩ := suffix_safe hw62 hwEven hstart
      refine ⟨L', hrev, ?_⟩
      unfold Invariant
      rw [hS]
      refine ⟨xsafe_append hsInherited hsFresh, ?_, ?_⟩
      · rw [xfold_append]
        exact heFresh
      · rw [xfold_append]
        exact hpFresh

/-- The second released sequence; the first has the exceptional odd gap 243. -/
def seed : List Sym := [4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 0, 0, 2, 1, 2, 1, 0]

theorem seed_reached : revIter 1 = some seed := by native_decide

theorem seed_safe : XSafe 1 seed := by native_decide

theorem seed_gap : xfold 1 seed = 28958 := by native_decide

theorem seed_invariant : Invariant seed := by
  exact ⟨seed_safe, by rw [seed_gap]; omega, by rw [seed_gap]⟩

/-- A successor exists at every subsequent revolution. -/
theorem all_later_iterations : ∀ n : Nat,
    ∃ L, revIter (n + 1) = some L ∧ Invariant L
  | 0 => ⟨seed, seed_reached, seed_invariant⟩
  | n + 1 => by
      obtain ⟨L, hL, hInv⟩ := all_later_iterations n
      obtain ⟨L', hrev, hInv'⟩ := invariant_step (revIter_labels hL) hInv
      refine ⟨L', ?_, hInv'⟩
      change (revIter (n + 1)).bind revolutionF = some L'
      rw [hL, Option.bind_some, hrev]

/-- **The machine never halts from the blank tape.** -/
theorem neverHalts : SOC.NeverHalts := by
  apply neverHalts_of_revIter
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      obtain ⟨L, hL, _⟩ := all_later_iterations n
      rw [hL]
      rfl

end SOC.Completion
