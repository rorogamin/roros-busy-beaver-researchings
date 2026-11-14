import RequestProject.CarryU21V
import RequestProject.U2bV

/-!
# From the blank tape into the token world

Every macro rule of this development is a *window* rule: it says what happens when the
tape already carries a word of the token alphabet.  This file connects those rules to the
actual machine by computing the beginning of the blank-tape run.

Two things are proved.

* `blank_prefix`: the first `2016` steps of the machine, started on the blank tape, are a
  window computation on `96` blank cells, at the end of which the head is in state `B` on
  the leftmost non-blank cell and the tape carries the token word
  `U(2,2) u U(2,8) u^3 U(1,2) u^13`.  This is checked by the list-level simulator of
  `Local.lean`, so it is a kernel computation, not a hand proof.
* `orbit_prefix`: continuing from there, four of the proved macro rules apply in turn —
  `rule_P2`, `rule_P3_U2b`, `rule_P1_V`, `rule_P2` — and carry the machine to step `2516`.

Two consequences are worth stating.  First, `not_halted_le_2516`: the machine does not
halt in its first `2516` steps.  Second, and the reason for choosing `2016` as the cut:
`ANALYSIS.md` §31 lists five macro steps in which the carry runs off the right end of the
tape, and all five of them happen before step `1741`.  They are therefore *inside* the
computed prefix, and that census row needs no parametric rule: from step `2016` on, every
macro step of the orbit belongs to one of the recurring rows.
-/

namespace BB25

/-- The blank tape carries a run of `0`s on every window. -/
lemma Seg_blank (a : ℤ) (n : ℕ) : Seg (fun _ => (0 : Sym)) a (List.replicate n 0) := by
  intro i hi
  simp [List.getD_eq_getElem?_getD]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The first `2016` steps.**  Started in state `A` on cell `71` of a window of `96`
blank cells, the machine is, after exactly `2016` steps, in state `B` on cell `21`, and
the window carries `18` blank cells, the token word `U(2,2) u U(2,8) u^3 U(1,2) u^13` and
three more blank cells.  The head never leaves the window. -/
theorem blank_prefix :
    Win St.A St.B 71 21 (List.replicate 96 0)
      (List.replicate 18 0 ++
        ([0, 0, 0] ++ tokU 2 2 ++ tokU 1 1 ++ tokU 2 8 ++ rep (tokU 1 1) 3 ++ tokU 1 2 ++
          rep (tokU 1 1) 13 ++ [0]) ++ [0, 0, 0]) 2016 :=
  Win.of_lrun (by decide)

/-- **The orbit from the blank tape to step `2516`.**  The first `2016` steps are the
computation of `blank_prefix`; the next four macro steps are `rule_P2` (`31` steps),
`rule_P3_U2b` with `r = 0, m = 2, s = 3, m' = 0` (`191` steps), `rule_P1_V` with
`m = 1, c = 0, s = 3, m' = 1` (`247` steps) and `rule_P2` again (`31` steps).  Each of
them is one of the census rows of `ANALYSIS.md` §39, and each is applied here to the
configuration the previous one produces. -/
theorem orbit_prefix :
    Win St.A St.B 71 9 (List.replicate 96 0)
      (List.replicate 9 0 ++
        (tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 8 ++ tokV 1 ++ rep (tokU 1 1) 3 ++
          tokU 1 8 ++ rep (tokU 1 1) 13 ++ [0]) ++ [0, 0, 0]) 2516 := by
  -- the four macro steps, embedded in the `96`-cell window
  have H2 := rule_P2.embed (by simp) (List.replicate 18 0)
    ([4, 2] ++ (tokU 2 8 ++ (rep (tokU 1 1) 3 ++ (tokU 1 2 ++ (rep (tokU 1 1) 13 ++
      ([0] ++ [0, 0, 0]))))))
  have H3 := (rule_P3_U2b 0 2 3 0).embed (by simp) (List.replicate 15 0)
    ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0])))
  have H4 := (rule_P1_V 1 0 3 1).embed (by simp) (List.replicate 12 0)
    ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0])))
  have H5 := rule_P2.embed (by simp) (List.replicate 9 0)
    ([4, 2] ++ (tokU 2 8 ++ (tokV 1 ++ (rep (tokU 1 1) 3 ++ (tokU 1 8 ++
      (rep (tokU 1 1) 13 ++ ([0] ++ [0, 0, 0])))))))
  -- the words the four steps pass through
  have E1 : (List.replicate 18 0 ++
        ([0, 0, 0] ++ tokU 2 2 ++ tokU 1 1 ++ tokU 2 8 ++ rep (tokU 1 1) 3 ++ tokU 1 2 ++
          rep (tokU 1 1) 13 ++ [0]) ++ [0, 0, 0] : List Sym)
      = List.replicate 18 0 ++ ([0, 0, 0] ++ tokU 2 2 ++ [0]) ++
        ([4, 2] ++ (tokU 2 8 ++ (rep (tokU 1 1) 3 ++ (tokU 1 2 ++ (rep (tokU 1 1) 13 ++
          ([0] ++ [0, 0, 0])))))) := by
    decide
  have E2 : (List.replicate 18 0 ++ (tokU 2 2 ++ tokV 1 ++ [0]) ++
        ([4, 2] ++ (tokU 2 8 ++ (rep (tokU 1 1) 3 ++ (tokU 1 2 ++ (rep (tokU 1 1) 13 ++
          ([0] ++ [0, 0, 0])))))) : List Sym)
      = List.replicate 15 0 ++
        ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (0 + 1) ++
          tokU 2 (2 * 2 + 4) ++ rep (tokU 1 1) 3 ++ tokU 1 (2 * 0 + 2) ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0]))) := by
    decide
  have E3 : (List.replicate 15 0 ++
        (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) 0 ++ tokU 1 4 ++ tokV (2 * 2 + 1) ++
          rep (tokU 1 1) 3 ++ tokU 1 (2 * 0 + 4) ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0]))) : List Sym)
      = List.replicate 12 0 ++
        ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * 1 + 2) ++ tokV (2 * 0 + 5) ++
          rep (tokU 1 1) 3 ++ tokU 1 (2 * 1 + 2) ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0]))) := by
    decide
  have E4 : (List.replicate 12 0 ++
        (tokU 2 2 ++ tokU 1 1 ++ tokU 2 (2 * 1 + 6) ++ tokV (2 * 0 + 1) ++
          rep (tokU 1 1) 3 ++ tokU 1 (2 * 1 + 6) ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0]))) : List Sym)
      = List.replicate 9 0 ++ ([0, 0, 0] ++ tokU 2 2 ++ [0]) ++
        ([4, 2] ++ (tokU 2 8 ++ (tokV 1 ++ (rep (tokU 1 1) 3 ++ (tokU 1 8 ++
          (rep (tokU 1 1) 13 ++ ([0] ++ [0, 0, 0]))))))) := by
    decide
  have E5 : (List.replicate 9 0 ++ (tokU 2 2 ++ tokV 1 ++ [0]) ++
        ([4, 2] ++ (tokU 2 8 ++ (tokV 1 ++ (rep (tokU 1 1) 3 ++ (tokU 1 8 ++
          (rep (tokU 1 1) 13 ++ ([0] ++ [0, 0, 0])))))) : List Sym))
      = List.replicate 9 0 ++
        (tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 8 ++ tokV 1 ++ rep (tokU 1 1) 3 ++
          tokU 1 8 ++ rep (tokU 1 1) 13 ++ [0]) ++ [0, 0, 0] := by
    decide
  -- chain them
  have S2 : Win St.B St.B 21 18 _ _ 31 := H2.cast (by simp) (by simp) E1 rfl rfl
  have S3 : Win St.B St.B 18 15 _ _ 191 := H3.cast (by simp) (by simp) E2 rfl (by norm_num)
  have S4 : Win St.B St.B 15 12 _ _ 247 := H4.cast (by simp) (by simp) E3 rfl (by norm_num)
  have S5 : Win St.B St.B 12 9 _ _ 31 := H5.cast (by simp) (by simp) E4 E5 rfl
  have T1 := blank_prefix.trans S2 (by simp)
  have T2 := T1.trans S3 (by simp)
  have T3 := T2.trans S4 (by simp)
  exact (T3.trans S5 (by simp)).cast rfl rfl rfl rfl (by norm_num)

/-- **The configuration at step `2516`.**  The machine started on the blank tape is, after
`2516` steps, in state `B` on cell `-62`, and the tape carries the token word
`U(2,2) V(1) u U(2,8) V(1) u^3 U(1,8) u^13` beginning at that cell, with blanks to its
left. -/
theorem run_2516 :
    ∃ T : ℤ → Sym, run 2516 = ⟨St.B, -62, T⟩ ∧
      Seg T (-71) (List.replicate 9 0 ++
        (tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 8 ++ tokV 1 ++ rep (tokU 1 1) 3 ++
          tokU 1 8 ++ rep (tokU 1 1) 13 ++ [0]) ++ [0, 0, 0]) := by
  obtain ⟨T, hstep, hseg, -⟩ := orbit_prefix (fun _ => (0 : Sym)) (-71) (Seg_blank _ _)
  refine ⟨T, ?_, hseg⟩
  have h0 : ((-71 : ℤ) + (71 : ℕ)) = 0 := by norm_num
  have : run 2516 = step^[2516] ⟨St.A, (-71 : ℤ) + (71 : ℕ), fun _ => (0 : Sym)⟩ := by
    rw [h0]; rfl
  rw [this, hstep]
  norm_num

/-- The machine does not halt during its first `2516` steps. -/
theorem not_halted_le_2516 : ∀ m ≤ 2516, ¬ Halted (run m) := by
  have h := orbit_prefix.no_halt (by exact fun h => St.noConfusion h) (fun _ => (0 : Sym))
    (-71) (Seg_blank _ _)
  intro m hm
  have h0 : ((-71 : ℤ) + (71 : ℕ)) = 0 := by norm_num
  have : run m = step^[m] ⟨St.A, (-71 : ℤ) + (71 : ℕ), fun _ => (0 : Sym)⟩ := by
    rw [h0]; rfl
  rw [this]
  exact h m hm

/-- **The orbit continued to step `3099`.**  The configuration `orbit_prefix` reaches at
step `2516` is exactly the left-hand side of `rule_P3_U2b_V` with `t = 0` and `m = 3`, so
that rule carries the machine `583` steps further, to state `B` on the leftmost non-blank
cell three cells further left again. -/
theorem orbit_prefix_3099 :
    Win St.A St.B 71 6 (List.replicate 96 0)
      (List.replicate 6 0 ++
        (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 2 2 ++ tokV 1 ++
          tokU 1 1 ++ tokU 1 18 ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0])))) 3099 := by
  have H := (rule_P3_U2b_V 0 3).embed (by simp) (List.replicate 6 0)
    ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0])))
  have E1 : (List.replicate 6 0 ++
        ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 8 ++ tokV 1 ++
          rep (tokU 1 1) (0 + 3) ++ tokU 1 (2 * 3 + 2) ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0]))) : List Sym)
      = List.replicate 9 0 ++
        (tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 8 ++ tokV 1 ++ rep (tokU 1 1) 3 ++
          tokU 1 8 ++ rep (tokU 1 1) 13 ++ [0]) ++ [0, 0, 0] := by
    decide
  have E2 : (List.replicate 6 0 ++
        (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 2 2 ++ tokV 1 ++
          rep (tokU 1 1) (0 + 1) ++ tokU 1 (2 * 3 + 12) ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0]))) : List Sym)
      = List.replicate 6 0 ++
        (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 2 2 ++ tokV 1 ++
          tokU 1 1 ++ tokU 1 18 ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0]))) := by
    decide
  have S : Win St.B St.B 9 6 _ _ 583 := H.cast (by simp) (by simp) E1 E2 (by norm_num)
  exact (orbit_prefix.trans S (by decide)).cast rfl rfl rfl rfl (by norm_num)

/-- **The configuration at step `3099`.**  The machine started on the blank tape is, after
`3099` steps, in state `B` on cell `-65`, and the tape carries the token word
`U(2,1) U(4,1) u u U(2,2) V(1) u U(1,18) u^12` beginning at that cell, with blanks to its
left. -/
theorem run_3099 :
    ∃ T : ℤ → Sym, run 3099 = ⟨St.B, -65, T⟩ ∧
      Seg T (-71) (List.replicate 6 0 ++
        (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 2 2 ++ tokV 1 ++
          tokU 1 1 ++ tokU 1 18 ++ [0]) ++
        ([4, 2] ++ (rep (tokU 1 1) 12 ++ ([0] ++ [0, 0, 0])))) := by
  obtain ⟨T, hstep, hseg, -⟩ := orbit_prefix_3099 (fun _ => (0 : Sym)) (-71) (Seg_blank _ _)
  refine ⟨T, ?_, hseg⟩
  have h0 : ((-71 : ℤ) + (71 : ℕ)) = 0 := by norm_num
  have : run 3099 = step^[3099] ⟨St.A, (-71 : ℤ) + (71 : ℕ), fun _ => (0 : Sym)⟩ := by
    rw [h0]; rfl
  rw [this, hstep]
  norm_num

/-- The machine does not halt during its first `3099` steps. -/
theorem not_halted_le_3099 : ∀ m ≤ 3099, ¬ Halted (run m) := by
  have h := orbit_prefix_3099.no_halt (by exact fun h => St.noConfusion h)
    (fun _ => (0 : Sym)) (-71) (Seg_blank _ _)
  intro m hm
  have h0 : ((-71 : ℤ) + (71 : ℕ)) = 0 := by norm_num
  have : run m = step^[m] ⟨St.A, (-71 : ℤ) + (71 : ℕ), fun _ => (0 : Sym)⟩ := by
    rw [h0]; rfl
  rw [this]
  exact h m hm

end BB25
