module

public import RequestProject.Cascade

/-!
# The level words of the cascade (longitudinal view)

`RequestProject/Cascade.lean` describes the machine as a cascade of cell
transducers processed in the machine's own (depth-first) order.  Here we pass
to the *level* (breadth-first) picture of the longitudinal analysis: the
input word of cell `0` is the wall stream, and the input word of cell `p+1` is
the output word of cell `p`.

* `cellOut c f xs`: the word emitted by a cell started in `(c, f)` on the input
  word `xs` (up to the moment it halts, if it does).
* `cellDies c f xs`: whether the cell halts while reading `xs`.
* `lev R xs p`: the input word of cell `p` when cell `0` is fed `xs` and the
  initial half-tape is `R`.

* `cellEnd c f xs`: the final state of such a cell (`none` if it halts).

Only the basic facts needed by the halting proof are kept here: the link
between the depth-first processing and the level words (`lvl`), prefix
monotonicity, and the fact that cells `p ≥ 9` start blank.
-/

@[expose] public section

namespace TM5

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

theorem lvl_ok_ne_nil {n : Nat} {x : St} {R T : List Sym} (h : lvl n x R = .ok T) : T ≠ [] := by
  cases n with
  | zero => cases h
  | succ n =>
      simp only [lvl, step1] at h
      split at h
      · cases h
      · cases hs : seqO (lvl n) _ (tlz R) with
        | ok R' => rw [hs] at h; cases h; exact List.cons_ne_nil _ _
        | halt => rw [hs] at h; cases h
        | oof => rw [hs] at h; cases h

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

theorem R0_drop_ge9 (p : Nat) (hp : 9 ≤ p) : R0.drop p = [] := by
  simp [R0]; omega

/-- The final state (content, flag) of a cell after reading a word, `none` if it
halts. -/
def cellEnd : Sym → Bool → List St → Option (Sym × Bool)
  | c, f, [] => some (c, f)
  | c, f, x :: xs =>
    match cell1 c f x with
    | none => none
    | some (c', f', _) => cellEnd c' f' xs

end TM5
