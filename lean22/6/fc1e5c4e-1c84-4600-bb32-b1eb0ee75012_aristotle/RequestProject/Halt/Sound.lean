module

public import RequestProject.Halt.Stream

/-!
# Correctness of the engine, part 6: soundness

`halts_of_check`: if the executable check `HaltEngine.check q k M c` returns
`true` (for any chunk size `c > 0`), then the Turing machine halts.  The proof
uses only the specifications proved in the previous parts and the halting
criterion `BCM.halts_of_haltsAt`; no computation is involved.
-/

@[expose] public section

namespace BCM.Eng

open HaltEngine

theorem streamPW_spec (q : Nat) (w : PW) (c : Nat) (hc : 0 < c) (sts : Array UInt8)
    (hI : Inv q [] sts) : ∀ k, StreamOK q [] (pwX w ++ rep (pwY w) k) sts (streamPW w c sts k) := by
  intro k
  induction k with
  | zero =>
    have := streamArr_spec q w.x c hc (w.nx + 1) sts 0 w.nx [] (by omega) hI
    simp only [streamPW, rep, List.append_nil]
    exact this
  | succ k ih =>
    simp only [streamPW]
    revert ih
    cases streamPW w c sts k with
    | done sts' =>
      intro ih
      dsimp only
      obtain ⟨h1, h2⟩ := ih
      have := streamArr_spec q w.y c hc (w.ny + 1) sts' 0 w.ny _ (by omega) h2
      revert this
      cases streamArr w.y c sts' 0 w.ny (w.ny + 1) with
      | done s'' =>
        intro h
        dsimp only [StreamOK] at h ⊢
        refine ⟨by rw [h.1, h1], ?_⟩
        have := h.2
        rw [List.nil_append] at this ⊢
        rw [rep_succ', ← List.append_assoc]
        exact this
      | halt l b =>
        intro h
        dsimp only [StreamOK] at h ⊢
        intro hb
        obtain ⟨U, hU, hH⟩ := h hb
        refine ⟨[] ++ (pwX w ++ rep (pwY w) k) ++ U, ?_, by rw [List.nil_append]; exact hH⟩
        have := (List.prefix_append_right_inj (pwX w ++ rep (pwY w) k)).mpr hU
        rw [rep_succ', List.nil_append]
        simpa [List.append_assoc, pwY] using this
      | overflow => intro _; trivial
    | halt l b =>
      intro ih
      dsimp only [StreamOK] at ih ⊢
      intro hb
      obtain ⟨U, hU, hH⟩ := ih hb
      refine ⟨U, ?_, hH⟩
      rw [rep_succ', ← List.append_assoc]
      exact hU.trans (List.prefix_append _ _)
    | overflow => intro _; trivial

theorem chain_nil (q : Nat) : ∀ j, chain q [] j = []
  | 0 => rfl
  | j + 1 => by simp only [chain]; rw [chain_nil q j]; rfl

theorem inv_init (q M : Nat) : Inv q [] ((Array.range M).map (fun j => initSt (q + j))) := by
  intro j hj
  simp only [Array.size_map, Array.size_range] at hj
  have e : ((Array.range M).map (fun j => initSt (q + j)))[j]! = initSt (q + j) := by
    rw [getElem!_pos _ j (by simp; omega)]; simp
  rw [e]
  refine ⟨initSt_lt _, ?_⟩
  rw [chain_nil]
  rfl

theorem chain_mono (q : Nat) {S S' : List St} (h : S <+: S') : ∀ j, chain q S j <+: chain q S' j
  | 0 => h
  | j + 1 => cellOut_mono (chain_mono q h j) _ _

theorem cellDies_of_cellEnd : ∀ (w : List St) (c : Sym) (f : Bool), cellEnd c f w = none →
    cellDies c f w = true
  | [], _, _, h => by cases h
  | x :: w, c, f, h => by
    simp only [cellEnd] at h
    simp only [cellDies]
    revert h
    cases cell1 c f x with
    | none => intro _; rfl
    | some v =>
      obtain ⟨c1, f1, o⟩ := v
      intro h
      exact cellDies_of_cellEnd w c1 f1 h

/-- **The engine is sound**: if `check q k M c` succeeds (with `c > 0`), the
machine halts. -/
theorem halts_of_check (q k M c : Nat) (hc : 0 < c) (h : check q k M c = true) : Halts := by
  unfold check at h
  split at h
  · cases h
  next w hw =>
  have hG := pwUpTo_spec q w hw
  have hS := streamPW_spec q w c hc _ (inv_init q M) k
  generalize streamPW w c ((Array.range M).map (fun j => initSt (q + j))) k = r at hS h
  cases r with
  | halt l b =>
    dsimp only [StreamOK] at hS h
    obtain ⟨U, hU, hH1, hH2⟩ := hS h
    rw [List.nil_append] at hH1 hH2
    have hF := hG k
    generalize 1 + 5 * (w.a + w.b * k) = N at hF
    rw [← hF] at hU
    have hm := chain_mono q hU l
    rw [← lev_chain] at hm
    obtain ⟨rest, hrest⟩ := hm
    apply halts_of_haltsAt (N := N) (p := q + l) (q := q + l + 1)
    · unfold haltsAt
      apply cellDies_of_cellEnd
      have e1 : hdz (([] : List Sym).drop (q + l)) = (dec (initSt (q + l))).1 := by rw [initD_eq]
      have e2 : nbr (([] : List Sym).drop (q + l)) = (dec (initSt (q + l))).2 := by rw [initD_eq]
      rw [e1, e2, ← hrest]
      exact cellEnd_append_none _ _ _ _ hH1
    · rw [lev_step, ← hrest, cellOut_append_none _ _ _ _ hH1]
      exact hH2
  | done _ => cases h
  | overflow => cases h

end BCM.Eng
