module

public import RequestProject.Levels

/-!
# A sufficient criterion for halting, in terms of level words

A halt of some cell of the level cascade (`RequestProject/Levels.lean`) is a
halt of the machine, under the (necessary) proviso that the cascade on the
prefix in question dies out:

* `lvl_lev`: after the depth-first processing of `xs` has finished with
  half-tape `T`, every level word for `xs ++ ys` is a word already consumed by
  that cell for `xs`, followed by the level word for `ys` on `T`.
* `not_haltsAt_of_ok`: if the depth-first processing of `xs` finishes, no cell
  halts on its level word.
* `seqO_ne_oof`: if the level words of `xs` are empty from level `q` on, the
  depth-first processing with recursion depth `q` does not run out of fuel.
* **`halts_of_haltsAt`**: if some cell halts on its level word for the prefix
  `word N` of the wall stream, and the cascade on `word N` dies out at some
  level `q`, then the machine halts.
-/

@[expose] public section

namespace TM5

theorem cellEnd_append (xs ys : List St) : ∀ c f c' f', cellEnd c f xs = some (c', f') →
    cellEnd c f (xs ++ ys) = cellEnd c' f' ys := by
  induction xs with
  | nil => intro c f c' f' h; cases h; rfl
  | cons x xs ih =>
      intro c f c' f' h
      simp only [cellEnd, List.cons_append] at h ⊢
      cases hc : cell1 c f x with
      | none => rw [hc] at h; cases h
      | some v =>
          obtain ⟨c1, f1, o⟩ := v
          rw [hc] at h
          exact ih c1 f1 c' f' h

theorem cellOut_append_of_end (xs ys : List St) : ∀ c f c' f', cellEnd c f xs = some (c', f') →
    cellOut c f (xs ++ ys) = cellOut c f xs ++ cellOut c' f' ys := by
  induction xs with
  | nil => intro c f c' f' h; cases h; rfl
  | cons x xs ih =>
      intro c f c' f' h
      simp only [cellEnd, cellOut, List.cons_append] at h ⊢
      cases hc : cell1 c f x with
      | none => rw [hc] at h; cases h
      | some v =>
          obtain ⟨c1, f1, o⟩ := v
          rw [hc] at h
          simp only [ih c1 f1 c' f' h, List.append_assoc]

theorem cellDies_append_of_end (xs ys : List St) : ∀ c f c' f', cellEnd c f xs = some (c', f') →
    cellDies c f (xs ++ ys) = cellDies c' f' ys := by
  induction xs with
  | nil => intro c f c' f' h; cases h; rfl
  | cons x xs ih =>
      intro c f c' f' h
      simp only [cellEnd, cellDies, List.cons_append] at h ⊢
      cases hc : cell1 c f x with
      | none => rw [hc] at h; cases h
      | some v =>
          obtain ⟨c1, f1, o⟩ := v
          rw [hc] at h
          exact ih c1 f1 c' f' h

theorem lev_nil : ∀ (p : Nat) (R : List Sym), lev R [] p = []
  | 0, _ => rfl
  | p + 1, R => lev_nil p (tlz R)

/-- Level commutation for a single arrival. -/
theorem lvl_lev_one (n : Nat)
    (IH : ∀ xs R T, seqO (lvl n) xs R = .ok T → ∀ ys p, ∃ pre,
      lev R (xs ++ ys) p = pre ++ lev T ys p ∧
      cellEnd (hdz (R.drop p)) (nbr (R.drop p)) pre = some (hdz (T.drop p), nbr (T.drop p))) :
    ∀ x R T, lvl (n + 1) x R = .ok T → ∀ ys p, ∃ pre,
      lev R (x :: ys) p = pre ++ lev T ys p ∧
      cellEnd (hdz (R.drop p)) (nbr (R.drop p)) pre = some (hdz (T.drop p), nbr (T.drop p)) := by
  intro x R T h ys p
  simp only [lvl, step1] at h
  cases hc : cell1 (hdz R) (nbr R) x with
  | none => rw [hc] at h; cases h
  | some v =>
      obtain ⟨c1, f1, o1⟩ := v
      rw [hc] at h
      dsimp only at h
      cases hs : seqO (lvl n) o1 (tlz R) with
      | halt => rw [hs] at h; cases h
      | oof => rw [hs] at h; cases h
      | ok R1' =>
          rw [hs] at h
          cases h
          have hf : nbr (c1 :: R1') = f1 := by
            have h1 := cell1_flag hc
            have h2 := seqO_lvl_isEmpty o1 hs
            show (!R1'.isEmpty) = f1
            rw [h1, h2]
            unfold nbr
            cases (tlz R).isEmpty <;> cases o1.isEmpty <;> rfl
          cases p with
          | zero =>
              refine ⟨[x], rfl, ?_⟩
              simp only [List.drop_zero, cellEnd, hc, hdz_cons, hf]
          | succ p =>
              obtain ⟨pre, h1, h2⟩ := IH o1 (tlz R) R1' hs (cellOut c1 f1 ys) p
              refine ⟨pre, ?_, ?_⟩
              · show lev (tlz R) (cellOut (hdz R) (nbr R) (x :: ys)) p =
                  pre ++ lev (tlz (c1 :: R1')) (cellOut (hdz (c1 :: R1')) (nbr (c1 :: R1')) ys) p
                simp only [cellOut, hc, tlz_cons, hdz_cons, hf]
                exact h1
              · rw [drop_succ_tlz, drop_succ_tlz, tlz_cons]
                exact h2

/-- **Level commutation.** After the depth-first processing of `xs` on `R` has
finished with half-tape `T`, the level word of cell `p` for `xs ++ ys` is a word
`pre` that cell `p` has already consumed (going from its state in `R` to its
state in `T` without halting), followed by the level word for `ys` on `T`. -/
theorem lvl_lev (n : Nat) : ∀ xs R T, seqO (lvl n) xs R = .ok T → ∀ ys p, ∃ pre,
    lev R (xs ++ ys) p = pre ++ lev T ys p ∧
    cellEnd (hdz (R.drop p)) (nbr (R.drop p)) pre = some (hdz (T.drop p), nbr (T.drop p)) := by
  induction n with
  | zero =>
      intro xs R T h ys p
      cases xs with
      | nil => cases h; exact ⟨[], rfl, rfl⟩
      | cons x xs => simp [seqO, lvl, bindO] at h
  | succ n IH =>
      have hone := lvl_lev_one n IH
      intro xs
      induction xs with
      | nil => intro R T h ys p; cases h; exact ⟨[], rfl, rfl⟩
      | cons x xs ihx =>
          intro R T h ys p
          simp only [seqO] at h
          cases hx : lvl (n + 1) x R with
          | halt => rw [hx] at h; cases h
          | oof => rw [hx] at h; cases h
          | ok R1 =>
              rw [hx, bindO_ok] at h
              obtain ⟨pre1, h1, e1⟩ := hone x R R1 hx (xs ++ ys) p
              obtain ⟨pre2, h2, e2⟩ := ihx R1 T h ys p
              refine ⟨pre1 ++ pre2, ?_, ?_⟩
              · rw [List.cons_append, h1, h2, List.append_assoc]
              · rw [cellEnd_append pre1 pre2 _ _ _ _ e1]
                exact e2

/-- If the depth-first processing of `xs` finishes, no cell halts on its level
word for `xs`. -/
theorem not_haltsAt_of_ok {n : Nat} {xs : List St} {R T : List Sym}
    (h : seqO (lvl n) xs R = .ok T) (p : Nat) : ¬ haltsAt R xs p := by
  obtain ⟨pre, h1, e⟩ := lvl_lev n xs R T h [] p
  rw [List.append_nil, lev_nil, List.append_nil] at h1
  unfold haltsAt
  rw [h1]
  have := cellDies_append_of_end pre [] _ _ _ _ e
  rw [List.append_nil] at this
  rw [this]
  simp [cellDies]

/-- Fuel suffices: if all level words of `xs` from level `q` on are empty, the
depth-first processing with recursion depth `n ≥ q` does not run out of fuel. -/
theorem seqO_ne_oof (q : Nat) : ∀ n, q ≤ n → ∀ (xs : List St) (R : List Sym),
    lev R xs q = [] → seqO (lvl n) xs R ≠ .oof := by
  induction q with
  | zero =>
      intro n _ xs R h
      cases h
      simp [seqO]
  | succ q IH =>
      intro n hn xs
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      induction xs with
      | nil => intro R _; simp [seqO]
      | cons x xs ihx =>
          intro R h
          simp only [seqO]
          cases hx : lvl (n' + 1) x R with
          | halt => simp [bindO]
          | ok R1 =>
              rw [bindO_ok]
              apply ihx R1
              obtain ⟨pre, h1, _⟩ := lvl_lev (n' + 1) [x] R R1 (by simp [seqO, hx, bindO]) xs (q + 1)
              rw [List.singleton_append, h] at h1
              exact (List.append_eq_nil_iff.mp h1.symm).2
          | oof =>
              exfalso
              simp only [lvl, step1] at hx
              cases hc : cell1 (hdz R) (nbr R) x with
              | none => rw [hc] at hx; cases hx
              | some v =>
                  obtain ⟨c1, f1, o1⟩ := v
                  rw [hc] at hx
                  dsimp only at hx
                  have hq : lev (tlz R) o1 q = [] := by
                    have h' : lev (tlz R) (cellOut (hdz R) (nbr R) (x :: xs)) q = [] := h
                    simp only [cellOut, hc] at h'
                    have hm := lev_mono q (tlz R) (List.prefix_append o1 (cellOut c1 f1 xs))
                    rw [h'] at hm
                    exact List.eq_nil_of_prefix_nil hm
                  have := IH n' (by omega) o1 (tlz R) hq
                  cases hs : seqO (lvl n') o1 (tlz R) with
                  | oof => exact this hs
                  | halt => rw [hs] at hx; cases hx
                  | ok R' => rw [hs] at hx; cases hx

/-- **Sufficient criterion for halting.** If some cell `p` halts on its level
word for the prefix `word N` of the wall stream, and the cascade on `word N`
dies out (the level word of some cell `q` is empty), then the machine halts. -/
theorem halts_of_haltsAt {N p q : Nat} (h : haltsAt R0 (word N) p)
    (hq : lev R0 (word N) q = []) : Halts := by
  apply halts_iff.mpr
  refine ⟨N, q, ?_⟩
  have hne := seqO_ne_oof q q (Nat.le_refl _) (word N) R0 hq
  cases hs : seqO (lvl q) (word N) R0 with
  | halt => rfl
  | oof => exact absurd hs hne
  | ok T => exact absurd h (not_haltsAt_of_ok hs p)

end TM5
