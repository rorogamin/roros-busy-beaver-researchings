module

public import RequestProject.Cascade

/-!
# The level words of the cascade (longitudinal view)

`RequestProject/Cascade.lean` describes the machine as a cascade of cell
transducers processed in the machine's own (depth-first) order.  Here we pass
to the *level* (breadth-first) picture of the longitudinal analysis: the
input word of cell `0` is the arrival stream, and the input word of cell `p+1`
is the output word of cell `p`.

* `cellOut c f xs`: the word emitted by a cell started in `(c, f)` on the input
  word `xs` (up to the moment it halts, if it does).
* `cellDies c f xs`: whether the cell halts while reading `xs`.
* `cellEnd c f xs`: the final state of such a cell (`none` if it halts).
* `lev R xs p`: the input word of cell `p` when cell `0` is fed `xs` and the
  initial half-tape is `R`.
* `haltsAt R xs p`: cell `p` halts on its level word.
-/

@[expose] public section

namespace BCM

/-- The output word of a cell started in `(c, f)` on the input word `xs`
(truncated when the cell halts). -/
def cellOut : Sym → Bool → List St → List St
  | _, _, [] => []
  | c, f, x :: xs =>
    match cell1 c f x with
    | none => []
    | some (c', f', o) => o ++ cellOut c' f' xs

/-- Does a cell started in `(c, f)` halt while reading `xs`? -/
def cellDies : Sym → Bool → List St → Bool
  | _, _, [] => false
  | c, f, x :: xs =>
    match cell1 c f x with
    | none => true
    | some (c', f', _) => cellDies c' f' xs

/-- The input word of cell `p`, when cell `0` receives `xs` and the initial
half-tape is `R`. -/
def lev : List Sym → List St → Nat → List St
  | _, xs, 0 => xs
  | R, xs, p + 1 => lev (tlz R) (cellOut (hdz R) (nbr R) xs) p

/-- Cell `p` of the level cascade halts on its input word. -/
def haltsAt (R : List Sym) (xs : List St) (p : Nat) : Prop :=
  cellDies (hdz (R.drop p)) (nbr (R.drop p)) (lev R xs p) = true

/-! ## Basic properties of the level words -/

theorem cellOut_append (xs ys : List St) : ∀ c f, ∃ ws, cellOut c f (xs ++ ys) = cellOut c f xs ++ ws := by
  induction xs with
  | nil => intro c f; exact ⟨cellOut c f ys, rfl⟩
  | cons x xs ih =>
      intro c f
      simp only [List.cons_append, cellOut]
      cases cell1 c f x with
      | none => exact ⟨[], rfl⟩
      | some v =>
          obtain ⟨c', f', o⟩ := v
          obtain ⟨ws, hws⟩ := ih c' f'
          exact ⟨ws, by simp only [hws, List.append_assoc]⟩

theorem drop_succ_tlz (R : List Sym) (p : Nat) : R.drop (p + 1) = (tlz R).drop p := by
  cases R <;> simp [tlz]

/-- The flag update rule of `cell1`, as a boolean check. -/
def flagOK (c : Sym) (f : Bool) (x : St) : Bool :=
  match cell1 c f x with
  | none => true
  | some (_, f', o) => f' == (f || !o.isEmpty)

theorem flagOK_all : ∀ c f x, flagOK c f x = true := by
  intro c f x; cases f <;> cases x <;> revert c <;> decide

theorem cell1_flag {c : Sym} {f : Bool} {x : St} {c' : Sym} {f' : Bool} {o : List St}
    (h : cell1 c f x = some (c', f', o)) : f' = (f || !o.isEmpty) := by
  have := flagOK_all c f x
  simp only [flagOK, h] at this
  simpa using this

theorem seqO_lvl_isEmpty {n : Nat} (o : List St) : ∀ {T T' : List Sym},
    seqO (lvl n) o T = .ok T' → T'.isEmpty = (T.isEmpty && o.isEmpty) := by
  induction o with
  | nil => intro T T' h; cases h; simp
  | cons x o ih =>
      intro T T' h
      simp only [seqO] at h
      cases hx : lvl n x T with
      | ok T1 =>
          rw [hx, bindO_ok] at h
          have h1 := ih h
          have h2 := lvl_ok_ne_nil hx
          rw [h1]
          cases T1 with
          | nil => exact absurd rfl h2
          | cons _ _ => simp
      | halt => rw [hx] at h; cases h
      | oof => rw [hx] at h; cases h

/-! ## Level words one level down -/

theorem lev_succ' (p : Nat) : ∀ (R : List Sym) (xs : List St),
    lev R xs (p + 1) = cellOut (hdz (R.drop p)) (nbr (R.drop p)) (lev R xs p) := by
  induction p with
  | zero => intro R xs; rfl
  | succ p ih =>
      intro R xs
      show lev (tlz R) (cellOut (hdz R) (nbr R) xs) (p + 1) = _
      rw [ih, drop_succ_tlz]
      rfl

/-! ## Prefix monotonicity -/

theorem cellOut_mono {xs ys : List St} (h : xs <+: ys) (c : Sym) (f : Bool) :
    cellOut c f xs <+: cellOut c f ys := by
  obtain ⟨zs, rfl⟩ := h
  obtain ⟨ws, hws⟩ := cellOut_append xs zs c f
  rw [hws]
  exact List.prefix_append _ _

theorem lev_mono (p : Nat) : ∀ (R : List Sym) {xs ys : List St}, xs <+: ys →
    lev R xs p <+: lev R ys p := by
  induction p with
  | zero => intro R xs ys h; exact h
  | succ p ih => intro R xs ys h; exact ih _ (cellOut_mono h _ _)

/-- The final state (content, flag) of a cell after reading a word, `none` if it
halts. -/
def cellEnd : Sym → Bool → List St → Option (Sym × Bool)
  | c, f, [] => some (c, f)
  | c, f, x :: xs =>
    match cell1 c f x with
    | none => none
    | some (c', f', _) => cellEnd c' f' xs

/-! ## Level commutation -/

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

/-! ## Halts of the machine are halts of single cells -/

theorem cellDies_append_true : ∀ (w v : List St) (c : Sym) (f : Bool),
    cellDies c f w = true → cellDies c f (w ++ v) = true := by
  intro w
  induction w with
  | nil => intro v c f h; simp [cellDies] at h
  | cons x w ih =>
      intro v c f h
      simp only [cellDies, List.cons_append] at h ⊢
      cases hc : cell1 c f x with
      | none => rfl
      | some u =>
          obtain ⟨c1, f1, o⟩ := u
          rw [hc] at h
          exact ih v c1 f1 h

theorem cellDies_prefix {w w' : List St} (hw : w <+: w') {c : Sym} {f : Bool}
    (h : cellDies c f w = true) : cellDies c f w' = true := by
  obtain ⟨v, rfl⟩ := hw
  exact cellDies_append_true w v c f h

/-- If the depth-first processing halts, then some cell halts on its level
word. -/
theorem haltsAt_of_seqO_halt (n : Nat) : ∀ (xs : List St) (R : List Sym),
    seqO (lvl n) xs R = .halt → ∃ p, haltsAt R xs p := by
  induction n with
  | zero =>
      intro xs R h
      cases xs with
      | nil => simp [seqO] at h
      | cons x xs => simp [seqO, lvl, bindO] at h
  | succ n IH =>
      intro xs
      induction xs with
      | nil => intro R h; simp [seqO] at h
      | cons x xs ihx =>
          intro R h
          simp only [seqO] at h
          cases hx : lvl (n + 1) x R with
          | oof => rw [hx] at h; cases h
          | ok R1 =>
              rw [hx, bindO_ok] at h
              obtain ⟨p, hp⟩ := ihx R1 h
              obtain ⟨pre, h1, e1⟩ := lvl_lev (n + 1) [x] R R1 (by simp [seqO, hx, bindO]) xs p
              refine ⟨p, ?_⟩
              unfold haltsAt at hp ⊢
              rw [List.singleton_append] at h1
              rw [h1, cellDies_append_of_end pre _ _ _ _ _ e1]
              exact hp
          | halt =>
              simp only [lvl, step1] at hx
              cases hc : cell1 (hdz R) (nbr R) x with
              | none =>
                  refine ⟨0, ?_⟩
                  simp [haltsAt, lev, cellDies, hc]
              | some u =>
                  obtain ⟨c1, f1, o1⟩ := u
                  rw [hc] at hx
                  dsimp only at hx
                  cases hs : seqO (lvl n) o1 (tlz R) with
                  | ok R' => rw [hs] at hx; cases hx
                  | oof => rw [hs] at hx; cases hx
                  | halt =>
                      obtain ⟨p, hp⟩ := IH o1 (tlz R) hs
                      refine ⟨p + 1, ?_⟩
                      unfold haltsAt at hp ⊢
                      rw [drop_succ_tlz]
                      have e : lev R (x :: xs) (p + 1)
                          = lev (tlz R) (o1 ++ cellOut c1 f1 xs) p := by
                        show lev (tlz R) (cellOut (hdz R) (nbr R) (x :: xs)) p = _
                        simp only [cellOut, hc]
                      rw [e]
                      exact cellDies_prefix (lev_mono p (tlz R) (List.prefix_append _ _)) hp

/-- Fuel suffices: a finished level cascade gives a successful or halting
depth-first processing. -/
theorem halts_of_haltsAt {N p q : Nat} (h : haltsAt [] (word N) p)
    (hq : lev [] (word N) q = []) : Halts := by
  apply halts_iff.mpr
  refine ⟨N, q, ?_⟩
  have hne := seqO_ne_oof q q (Nat.le_refl _) (word N) [] hq
  cases hs : seqO (lvl q) (word N) [] with
  | halt => rfl
  | oof => exact absurd hs hne
  | ok T => exact absurd h (not_haltsAt_of_ok hs p)

/-- **Level form of the reduction, halting direction.**  If the machine halts,
some cell `p` halts on its level word for some prefix `word N` of the arrival
stream. -/
theorem exists_haltsAt_of_halts (h : Halts) : ∃ N p, haltsAt [] (word N) p := by
  obtain ⟨N, n, hN⟩ := halts_iff.mp h
  obtain ⟨p, hp⟩ := haltsAt_of_seqO_halt n (word N) [] hN
  exact ⟨N, p, hp⟩

/-! ## When does a blank cell halt? -/

/-- Once a cell has sent the head into its right neighbour and holds `1`, `2`
or `3`, it can never halt (this is the "counter digit" regime). -/
theorem cellDies_emitted : ∀ (w : List St) (c : Sym), (c = 1 ∨ c = 2 ∨ c = 3) →
    cellDies c true w = false := by
  intro w
  induction w with
  | nil => intro c _; rfl
  | cons x w ih =>
      intro c hc
      rcases hc with rfl | rfl | rfl <;> cases x <;> simp only [cellDies, cell1] <;>
        exact ih _ (by decide)

/-- **Halting criterion for a blank cell.**  A cell that starts blank (with a
blank right neighbour) halts on the input word `w` if and only if `w` begins
with `B A B A`. -/
theorem cellDies_blank_iff (w : List St) :
    cellDies 0 false w = true ↔ [St.B, .A, .B, .A] <+: w := by
  rcases w with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, w⟩⟩⟩⟩
  · simp [cellDies]
  · cases x1 <;> simp [cellDies, cell1]
  · cases x1 <;> cases x2 <;> simp [cellDies, cell1]
  · cases x1 <;> cases x2 <;> cases x3 <;> simp [cellDies, cell1]
  · cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;>
      simp [cellDies, cell1, cellDies_emitted]

/-- On the initially blank half-tape, cell `p` halts on its level word iff the
level word begins with `B A B A`. -/
theorem haltsAt_nil_iff (xs : List St) (p : Nat) :
    haltsAt [] xs p ↔ [St.B, .A, .B, .A] <+: lev [] xs p := by
  unfold haltsAt
  simp only [List.drop_nil, hdz_nil, nbr, tlz_nil, List.isEmpty_nil, Bool.not_true]
  exact cellDies_blank_iff _

/-- **Non-halting reduction.**  If no level word of the cascade (for any prefix
of the arrival stream) begins with `B A B A`, the machine never halts. -/
theorem not_halts_of_no_BABA (h : ∀ N p, ¬ [St.B, .A, .B, .A] <+: lev [] (word N) p) :
    ¬ Halts := by
  intro hH
  obtain ⟨N, p, hp⟩ := exists_haltsAt_of_halts hH
  exact h N p ((haltsAt_nil_iff _ _).mp hp)

/-- **Halting criterion.**  If the level word of some cell begins with
`B A B A` and the cascade on the same prefix of the arrival stream dies out,
the machine halts. -/
theorem halts_of_BABA {N p q : Nat} (h : [St.B, .A, .B, .A] <+: lev [] (word N) p)
    (hq : lev [] (word N) q = []) : Halts :=
  halts_of_haltsAt ((haltsAt_nil_iff _ _).mpr h) hq

end BCM
