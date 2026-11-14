module

public import RequestProject.Wall

/-!
# The right half-tape as a cascade of cell transducers

After the wall (bouncer) has been eliminated (`RequestProject/Wall.lean`), what
remains of the machine is its behaviour on the right half-tape (cells `≥ 0`),
driven by the stream of states in which the head arrives at cell `0`: first the
initial `A` (the machine starts on cell `0` in state `A`), then the return
states of the wall, `B A B A B B A B A B …`.

This file makes the longitudinal (crossing-sequence) picture precise.

* `cell1 c f x` is the finite transducer describing one tape cell: a cell with
  content `c`, whose right neighbour is non-blank iff `f = true`, entered from
  the left in state `x`, gets the new content `c'`, the new flag `f'`, and sends
  the list `o` of states into its right neighbour (each followed by a return of
  the head), before the head leaves it to the left again.  `none` means that
  the machine halts during this visit.
* `lvl n x R` processes one arrival in state `x` on the half-tape `R` in the
  exact depth-first order of the machine (with a recursion depth bound `n`;
  `oof` means the bound was exceeded).
* `Sound`: the machine really does what `lvl` says (`sound_lvl`).
* `halts_iff`: the machine halts iff the cascade halts on some finite prefix of
  the arrival stream `A B A B A B B A B A B …`.
* `not_halts_of_cascade_ok`: if every finite prefix of the arrival stream is
  processed successfully, the machine never halts.
-/

@[expose] public section

namespace BCM

/-! ## Basic facts on `run` -/

theorem run_add (a b : Nat) (c : Cfg) : run (a + b) c = (run a c).bind (run b) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ n ih =>
      rw [show n + 1 + b = (n + b) + 1 from by omega, run_succ, run_succ]
      cases step c with
      | none => rfl
      | some c' => exact ih c'

theorem run_comp_none {a b : Nat} {c d : Cfg} (h1 : run a c = some d) (h2 : run b d = none) :
    run (a + b) c = none := by
  rw [run_add, h1]; exact h2

theorem run_comp_ne_none {a b : Nat} {c d : Cfg} (h1 : run a c = some d) (h2 : run b d ≠ none) :
    run (a + b) c ≠ none := by
  rw [run_add, h1]; exact h2

/-! ## The cell transducer -/

/-- One cell as a finite transducer.  Input: the content `c` of the cell, the
flag `f` (`true` iff the right neighbour is non-blank) and the state `x` in
which the head arrives from the left.  Output (`some (c', f', o)`): the new
content, the new flag, and the list `o` of states in which the head is sent
into the right neighbour during this visit.  `none`: the machine halts. -/
def cell1 : Sym → Bool → St → Option (Sym × Bool × List St)
  | 0, _, .A => some (3, true, [.B])
  | 0, f, .B => some (2, f, [])
  | 1, _, .A => some (2, true, [.A])
  | 1, f, .B => some (3, f, [])
  | 2, f, .A => some (1, f, [])
  | 2, false, .B => some (3, true, [.B])
  | 2, true, .B => some (2, true, [.B, .A])
  | 3, false, .A => none
  | 3, true, .A => some (2, true, [.B])
  | 3, _, .B => some (1, true, [.A])
  | 4, f, .A => some (2, f, [])
  | 4, _, .B => none

/-- Outcome of processing: the machine halts, the recursion bound is exceeded,
or the head leaves the half-tape to the left with the new half-tape `R`. -/
inductive Out
  | halt
  | oof
  | ok (R : List Sym)
deriving DecidableEq, Repr

/-- Monadic bind for `Out`. -/
def bindO (o : Out) (k : List Sym → Out) : Out :=
  match o with
  | .ok R => k R
  | .halt => .halt
  | .oof => .oof

/-- The flag of the first cell of the half-tape `R`: is its right neighbour
non-blank? -/
def nbr (R : List Sym) : Bool := !(tlz R).isEmpty

/-- Process one arrival in state `x` at the first cell of `R`, given a
procedure `sub` for processing a list of arrivals at the second cell. -/
def step1 (sub : List St → List Sym → Out) (x : St) (R : List Sym) : Out :=
  match cell1 (hdz R) (nbr R) x with
  | none => .halt
  | some (c', _, o) => bindO (sub o (tlz R)) (fun R' => .ok (c' :: R'))

/-- Process a list of arrivals one after the other. -/
def seqO (g : St → List Sym → Out) : List St → List Sym → Out
  | [], R => .ok R
  | x :: xs, R => bindO (g x R) (seqO g xs)

/-- Depth-first processing of one arrival, with recursion depth bound `n`. -/
def lvl : Nat → St → List Sym → Out
  | 0 => fun _ _ => .oof
  | n + 1 => step1 (seqO (lvl n))

/-- The state in which the head leaves the half-tape `R` to the left after an
arrival in state `x`: it is `B` only for an arrival in state `B` on a blank
half-tape. -/
def retSt : St → List Sym → St
  | .B, [] => .B
  | _, _ => .A

/-- The three possible outcomes, and what they mean for the machine started in
`c`: halting, running for at least `m` steps, or reaching `tgt R'` (with `R'`
a non-empty list without blanks). -/
def Good (m : Nat) (c : Cfg) (tgt : List Sym → Cfg) (o : Out) : Prop :=
  (o = .halt → ∃ k, run k c = none) ∧ (o = .oof → run m c ≠ none) ∧
  (∀ R', o = .ok R' → R' ≠ [] ∧ (0 : Sym) ∉ R' ∧ ∃ k, run k c = some (tgt R'))

/-- `g` correctly describes the machine on half-tapes without blank cells. -/
def Sound (m : Nat) (g : St → List Sym → Out) : Prop :=
  ∀ x R L, (0 : Sym) ∉ R →
    Good m ⟨x, L, hdz R, tlz R⟩ (fun R' => ⟨retSt x R, tlz L, hdz L, R'⟩) (g x R)

theorem good_halt {m : Nat} {c : Cfg} {tgt : List Sym → Cfg} (k : Nat) (h : run k c = none) :
    Good m c tgt .halt := by
  unfold Good
  exact ⟨fun _ => ⟨k, h⟩, (fun h' => by cases h'), (fun _ h' => by cases h')⟩

theorem good_ret {m : Nat} {c : Cfg} {tgt : List Sym → Cfg} {w : Sym} {T : List Sym} (k : Nat)
    (hw : w ≠ 0) (hT : (0 : Sym) ∉ T) (h : run k c = some (tgt (w :: T))) :
    Good m c tgt (.ok (w :: T)) := by
  unfold Good
  refine ⟨(fun h' => by cases h'), (fun h' => by cases h'), fun R' h' => ?_⟩
  cases h'
  refine ⟨List.cons_ne_nil _ _, ?_, k, h⟩
  simp only [List.mem_cons, not_or]
  exact ⟨fun e => hw e.symm, hT⟩

/-- One recursive call into the right neighbour. -/
theorem good_call {m : Nat} {g : St → List Sym → Out} {y : St} {T : List Sym} {a : Nat}
    {c : Cfg} {w : Sym} {L : List Sym} {tgt : List Sym → Cfg} {cont : List Sym → Out}
    (hS : Sound m g) (hT : (0 : Sym) ∉ T) (h1 : run a c = some ⟨y, w :: L, hdz T, tlz T⟩)
    (ha : 1 ≤ a)
    (hk : ∀ T' k, T' ≠ [] → (0 : Sym) ∉ T' → run k c = some ⟨retSt y T, L, w, T'⟩ →
      Good (m + 1) c tgt (cont T')) :
    Good (m + 1) c tgt (bindO (g y T) cont) := by
  have H := hS y T (w :: L) hT
  simp only [tlz, hdz] at H
  obtain ⟨H1, H2, H3⟩ := H
  cases hg : g y T with
  | halt =>
      obtain ⟨k, hk'⟩ := H1 hg
      exact good_halt (a + k) (run_comp_none h1 hk')
  | oof =>
      unfold Good
      refine ⟨(fun h' => by cases h'), fun _ => ?_, (fun _ h' => by cases h')⟩
      have := run_comp_ne_none h1 (H2 hg)
      obtain ⟨j, hj⟩ : ∃ j, a + m = (m + 1) + j := ⟨a - 1, by omega⟩
      rw [hj] at this
      intro hn
      apply this
      rw [run_add, hn]; rfl
  | ok T' =>
      obtain ⟨hne, hz, k, hk'⟩ := H3 T' hg
      exact hk T' (a + k) hne hz (run_comp h1 hk')

theorem bindO_ok (R : List Sym) (k : List Sym → Out) : bindO (.ok R) k = k R := rfl

theorem nz_cons {w : Sym} {T : List Sym} (h : (0 : Sym) ∉ w :: T) : (0 : Sym) ∉ T := by
  intro h'; exact h (List.mem_cons_of_mem _ h')

theorem nz_head {w : Sym} {T : List Sym} (h : (0 : Sym) ∉ w :: T) : w ≠ 0 := by
  intro h'; exact h (h' ▸ List.mem_cons_self)

theorem stp {k : Nat} {c d e : Cfg} (h : run k c = some d) (h2 : run 1 d = some e) :
    run (k + 1) c = some e := run_comp h h2

theorem retSt_cons (x : St) (y : Sym) (T : List Sym) : retSt x (y :: T) = .A := by
  cases x <;> rfl

theorem hdz_nil : hdz [] = 0 := rfl
theorem tlz_nil : tlz [] = [] := rfl
theorem hdz_cons (a : Sym) (l : List Sym) : hdz (a :: l) = a := rfl
theorem tlz_cons (a : Sym) (l : List Sym) : tlz (a :: l) = l := rfl

theorem bindO_assoc (o : Out) (f k : List Sym → Out) :
    bindO (bindO o f) k = bindO o (fun R => bindO (f R) k) := by
  cases o <;> rfl

theorem sound_succ {m : Nat} {g : St → List Sym → Out} (hS : Sound m g) :
    Sound (m + 1) (step1 (seqO g)) := by
  intro x R L hR
  rcases R with _ | ⟨w, R0⟩
  · cases x
    · simp only [step1, seqO, hdz_nil, tlz_nil, nbr, cell1, bindO_assoc, bindO_ok]
      refine good_call (a := 1) hS (by simp) rfl (Nat.le_refl 1) ?_
      intro T1 k1 _ hz1 hk1
      exact good_ret (k1 + 1) (by decide) hz1 (stp hk1 rfl)
    · simp only [step1, seqO, hdz_nil, tlz_nil, nbr, cell1, bindO_ok]
      exact good_ret 1 (by decide) (by simp) rfl
  · have hw := nz_head hR
    have hR0 := nz_cons hR
    have key : ∀ v : Sym, v ≠ 0 → v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by decide
    have hw' := key w hw
    rcases hw' with rfl | rfl | rfl | rfl <;> cases x
    · -- content 1, arrival A
      simp only [step1, seqO, hdz_cons, tlz_cons, cell1, bindO_assoc, bindO_ok]
      refine good_call (a := 1) hS hR0 rfl (Nat.le_refl 1) ?_
      intro T1 k1 _ hz1 hk1
      exact good_ret (k1 + 1) (by decide) hz1 (stp hk1 rfl)
    · -- content 1, arrival B
      simp only [step1, seqO, hdz_cons, tlz_cons, cell1, bindO_ok]
      exact good_ret 1 (by decide) hR0 rfl
    · -- content 2, arrival A
      simp only [step1, seqO, hdz_cons, tlz_cons, cell1, bindO_ok]
      exact good_ret 1 (by decide) hR0 rfl
    · -- content 2, arrival B
      rcases R0 with _ | ⟨v, R1⟩
      · simp only [step1, seqO, hdz_cons, tlz_cons, nbr, List.isEmpty_nil,
          Bool.not_true, cell1, bindO_assoc, bindO_ok]
        refine good_call (a := 1) hS hR0 rfl (Nat.le_refl 1) ?_
        intro T1 k1 _ hz1 hk1
        exact good_ret (k1 + 1) (by decide) hz1 (stp hk1 rfl)
      · simp only [step1, seqO, hdz_cons, tlz_cons, nbr, List.isEmpty_cons,
          Bool.not_false, cell1, bindO_assoc, bindO_ok]
        refine good_call (a := 1) hS hR0 rfl (Nat.le_refl 1) ?_
        intro T1 k1 hne1 hz1 hk1
        refine good_call hS hz1 (stp hk1 rfl) (by omega) ?_
        intro T2 k2 _ hz2 hk2
        exact good_ret (k2 + 1) (by decide) hz2 (stp hk2 rfl)
    · -- content 3, arrival A
      rcases R0 with _ | ⟨v, R1⟩
      · simp only [step1, hdz_cons, tlz_cons, nbr, List.isEmpty_nil,
          Bool.not_true, cell1]
        exact good_halt 3 rfl
      · simp only [step1, seqO, hdz_cons, tlz_cons, nbr, List.isEmpty_cons,
          Bool.not_false, cell1, bindO_assoc, bindO_ok]
        refine good_call (a := 1) hS hR0 rfl (Nat.le_refl 1) ?_
        intro T1 k1 _ hz1 hk1
        exact good_ret (k1 + 1) (by decide) hz1 (stp hk1 rfl)
    · -- content 3, arrival B
      simp only [step1, seqO, hdz_cons, tlz_cons, cell1, bindO_assoc, bindO_ok]
      refine good_call (a := 1) hS hR0 rfl (Nat.le_refl 1) ?_
      intro T1 k1 _ hz1 hk1
      exact good_ret (k1 + 1) (by decide) hz1 (stp hk1 rfl)
    · -- content 4, arrival A
      simp only [step1, seqO, hdz_cons, tlz_cons, cell1, bindO_ok]
      exact good_ret 1 (by decide) hR0 rfl
    · -- content 4, arrival B: halt
      simp only [step1, hdz_cons, cell1]
      exact good_halt 1 rfl

theorem sound_lvl (n : Nat) : Sound n (lvl n) := by
  induction n with
  | zero =>
      intro x R L _
      unfold Good
      refine ⟨(fun h => by cases h), fun _ => ?_, (fun _ h => by cases h)⟩
      simp [run]
  | succ n ih => exact sound_succ ih

/-! ## The arrival stream and the reduction -/

/-- The `i`-th state in which the head arrives at cell `0`: the initial `A`,
then the return states of the wall. -/
def inSt : Nat → St
  | 0 => .A
  | i + 1 => outSt (i % 5)

/-- The first `N` arrivals at cell `0`. -/
def word (N : Nat) : List St := (List.range N).map inSt

/-- The configuration just before the `N`-th arrival is processed: the head
is on cell `0` in state `inSt N`, the wall is in phase `N % 5` with `N / 5`
blocks, and `T` is the right half-tape (cells `≥ 0`). -/
def preCfg (N : Nat) (T : List Sym) : Cfg := ⟨inSt N, wall (N % 5) (N / 5), hdz T, tlz T⟩

/-! ### Auxiliary facts -/

theorem seqO_append (g : St → List Sym → Out) (xs ys : List St) (R : List Sym) :
    seqO g (xs ++ ys) R = bindO (seqO g xs R) (seqO g ys) := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, seqO]
      cases g x R with
      | ok R' => exact ih R'
      | halt => rfl
      | oof => rfl

theorem seqO_single (g : St → List Sym → Out) (x : St) (R : List Sym) :
    seqO g [x] R = g x R := by
  simp only [seqO]
  cases g x R <;> rfl

theorem word_succ (N : Nat) : word (N + 1) = word N ++ [inSt N] := by
  simp [word, List.range_succ]

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

theorem seqO_lvl_ne_nil {n : Nat} : ∀ {xs : List St} {R T : List Sym}, xs ≠ [] →
    seqO (lvl n) xs R = .ok T → T ≠ [] := by
  intro xs
  induction xs with
  | nil => intro R T h; exact absurd rfl h
  | cons x xs ih =>
      intro R T _ h
      simp only [seqO] at h
      cases hx : lvl n x R with
      | ok T1 =>
          rw [hx, bindO_ok] at h
          cases xs with
          | nil => cases h; exact lvl_ok_ne_nil hx
          | cons y ys => exact ih (List.cons_ne_nil _ _) h
      | halt => rw [hx] at h; cases h
      | oof => rw [hx] at h; cases h

/-- Agreement of two processing functions whenever the first one does not run
out of depth. -/
def Agree (g g' : St → List Sym → Out) : Prop := ∀ x R, g x R ≠ .oof → g' x R = g x R

theorem seqO_agree {g g' : St → List Sym → Out} (h : Agree g g') :
    ∀ xs R, seqO g xs R ≠ .oof → seqO g' xs R = seqO g xs R := by
  intro xs
  induction xs with
  | nil => intro R _; rfl
  | cons x xs ih =>
      intro R hne
      simp only [seqO] at hne ⊢
      cases hg : g x R with
      | oof => rw [hg] at hne; exact absurd rfl hne
      | halt => rw [h x R (by rw [hg]; exact fun e => by cases e), hg]; rfl
      | ok R' =>
          rw [h x R (by rw [hg]; exact fun e => by cases e), hg]
          rw [hg] at hne
          exact ih R' hne

theorem lvl_agree_succ (n : Nat) : Agree (lvl n) (lvl (n + 1)) := by
  induction n with
  | zero => intro x R h; exact absurd rfl h
  | succ n ih =>
      intro x R hne
      show step1 (seqO (lvl (n + 1))) x R = step1 (seqO (lvl n)) x R
      change step1 (seqO (lvl n)) x R ≠ .oof at hne
      unfold step1 at hne ⊢
      split
      · rfl
      · rename_i c' f' o heq
        rw [heq] at hne
        dsimp only at hne
        have hsub : seqO (lvl n) o (tlz R) ≠ .oof := by
          intro e; rw [e] at hne; exact hne rfl
        rw [seqO_agree ih o (tlz R) hsub]

theorem lvl_mono {n n' : Nat} (h : n ≤ n') (x : St) (R : List Sym) (hne : lvl n x R ≠ .oof) :
    lvl n' x R = lvl n x R := by
  obtain ⟨d, rfl⟩ : ∃ d, n' = n + d := ⟨n' - n, by omega⟩
  induction d with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, lvl_agree_succ (n + k) x R (by rw [ih (by omega)]; exact hne),
      ih (by omega)]

theorem seqO_lvl_mono {n n' : Nat} (h : n ≤ n') (xs : List St) (R : List Sym)
    (hne : seqO (lvl n) xs R ≠ .oof) : seqO (lvl n') xs R = seqO (lvl n) xs R :=
  seqO_agree (fun x R hx => lvl_mono h x R hx) xs R hne

theorem nextPh_mod (N : Nat) : nextPh (N % 5) = (N + 1) % 5 := by
  have : N % 5 = 0 ∨ N % 5 = 1 ∨ N % 5 = 2 ∨ N % 5 = 3 ∨ N % 5 = 4 := by omega
  rcases this with h | h | h | h | h <;> rw [h] <;> simp only [nextPh] <;> omega

theorem nextN_mod (N : Nat) : nextN (N % 5) (N / 5) = (N + 1) / 5 := by
  have : N % 5 = 0 ∨ N % 5 = 1 ∨ N % 5 = 2 ∨ N % 5 = 3 ∨ N % 5 = 4 := by omega
  rcases this with h | h | h | h | h <;> rw [h] <;> simp only [nextN] <;> omega

theorem wsteps_pos (ph n : Nat) : 1 ≤ wsteps ph n := by
  unfold wsteps; split <;> omega

/-- The arrival `inSt N` is processed on a half-tape that is non-empty unless
`N = 0`, so the head always leaves cell `0` to the left in state `A`. -/
theorem retSt_pre {n N : Nat} {T : List Sym} (h : seqO (lvl n) (word N) [] = .ok T) :
    retSt (inSt N) T = .A := by
  cases N with
  | zero => rfl
  | succ N =>
      have hne : T ≠ [] := seqO_lvl_ne_nil (by simp [word]) h
      cases T with
      | nil => exact absurd rfl hne
      | cons y T' => exact retSt_cons _ _ _

/-- The machine configuration before the `N`-th arrival at cell `0`, as long as
the cascade has processed the first `N` arrivals successfully. -/
theorem reach (n : Nat) : ∀ N T, seqO (lvl n) (word N) [] = .ok T →
    (0 : Sym) ∉ T ∧ ∃ t, N ≤ t ∧ run t init = some (preCfg N T) := by
  intro N
  induction N with
  | zero =>
      intro T h
      simp only [word, List.range_zero, List.map_nil, seqO] at h
      cases h
      exact ⟨by simp, 0, Nat.le_refl 0, rfl⟩
  | succ N ih =>
      intro T h
      rw [word_succ, seqO_append] at h
      cases hp : seqO (lvl n) (word N) [] with
      | halt => rw [hp] at h; cases h
      | oof => rw [hp] at h; cases h
      | ok T1 =>
          rw [hp, bindO_ok, seqO_single] at h
          obtain ⟨hz1, t, ht, hrun⟩ := ih T1 hp
          obtain ⟨hne, hz, k, hk⟩ :=
            (sound_lvl n (inSt N) T1 (wall (N % 5) (N / 5)) hz1).2.2 T h
          rw [retSt_pre hp] at hk
          obtain ⟨y, T', rfl⟩ : ∃ y T', T = y :: T' := by
            cases T with
            | nil => exact absurd rfl hne
            | cons y T' => exact ⟨y, T', rfl⟩
          have hw := wall_excursion (N % 5) (Nat.mod_lt _ (by decide)) (N / 5) y T'
          refine ⟨hz, t + k + wsteps (N % 5) (N / 5), ?_, ?_⟩
          · have := wsteps_pos (N % 5) (N / 5); omega
          · rw [run_comp (run_comp hrun hk) hw]
            simp only [wexit, preCfg, nextPh_mod, nextN_mod, hdz_cons, tlz_cons]
            rfl

theorem exists_halt_letter (g : St → List Sym → Out) : ∀ N, seqO g (word N) [] = .halt →
    ∃ N' T, seqO g (word N') [] = .ok T ∧ g (inSt N') T = .halt := by
  intro N
  induction N with
  | zero => intro h; simp [word, seqO] at h
  | succ N ih =>
      intro h
      rw [word_succ, seqO_append] at h
      cases hp : seqO g (word N) [] with
      | halt => exact ih hp
      | oof => rw [hp] at h; cases h
      | ok T1 =>
          rw [hp, bindO_ok, seqO_single] at h
          exact ⟨N, T1, hp, h⟩

/-- If the cascade gets stuck in an infinite recursion on some arrival, the
machine runs forever. -/
theorem not_halts_of_stuck {n N : Nat} {T : List Sym} (hp : seqO (lvl n) (word N) [] = .ok T)
    (hst : ∀ m, lvl m (inSt N) T = .oof) : ¬ Halts := by
  obtain ⟨hz1, t, _, hrun⟩ := reach n N T hp
  rintro ⟨j, hj⟩
  by_cases hle : j ≤ t
  · obtain ⟨d, hd⟩ : ∃ d, t = j + d := ⟨t - j, by omega⟩
    rw [hd] at hrun
    exact run_ne_none_of_le hrun hj
  · obtain ⟨d, hd⟩ : ∃ d, j = t + d := ⟨j - t, by omega⟩
    have hS := (sound_lvl d (inSt N) T (wall (N % 5) (N / 5)) hz1).2.1 (hst d)
    rw [hd, run_add, hrun] at hj
    exact hS hj

/-- **Non-halting criterion.** If the cascade processes every finite prefix of
the arrival stream successfully, the machine never halts. -/
theorem not_halts_of_cascade_ok (h : ∀ N, ∃ n T, seqO (lvl n) (word N) [] = .ok T) :
    ¬ Halts := by
  rintro ⟨i, hi⟩
  obtain ⟨n, T, hT⟩ := h i
  obtain ⟨_, t, ht, hrun⟩ := reach n i T hT
  obtain ⟨d, hd⟩ : ∃ d, t = i + d := ⟨t - i, by omega⟩
  rw [hd] at hrun
  exact run_ne_none_of_le hrun hi

/-- **Reduction theorem.** The machine halts if and only if the cascade of cell
transducers on the (initially blank) right half-tape, fed with a finite prefix
of the arrival stream `A B A B A B B A B A B …`, halts. -/
theorem halts_iff : Halts ↔ ∃ N n, seqO (lvl n) (word N) [] = .halt := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hne
    apply not_halts_of_cascade_ok _ hH
    intro N
    induction N with
    | zero => exact ⟨0, [], rfl⟩
    | succ N ih =>
        obtain ⟨n, T, hT⟩ := ih
        by_cases hex : ∃ m, lvl m (inSt N) T ≠ .oof
        · obtain ⟨m, hm⟩ := hex
          have e1 := seqO_lvl_mono (Nat.le_max_left n m) (word N) [] (by rw [hT]; exact fun e => by cases e)
          have e2 := lvl_mono (Nat.le_max_right n m) (inSt N) T hm
          rw [hT] at e1
          cases hl : lvl m (inSt N) T with
          | oof => exact absurd hl hm
          | halt =>
              exfalso; apply hne
              refine ⟨N + 1, max n m, ?_⟩
              rw [word_succ, seqO_append, e1, bindO_ok, seqO_single, e2, hl]
          | ok T' =>
              refine ⟨max n m, T', ?_⟩
              rw [word_succ, seqO_append, e1, bindO_ok, seqO_single, e2, hl]
        · exact absurd hH (not_halts_of_stuck hT (fun m => by
            apply Classical.byContradiction; intro h; exact hex ⟨m, h⟩))
  · rintro ⟨N, n, h⟩
    obtain ⟨N', T, hp, hl⟩ := exists_halt_letter (lvl n) N h
    obtain ⟨hz1, t, _, hrun⟩ := reach n N' T hp
    obtain ⟨k, hk⟩ := (sound_lvl n (inSt N') T (wall (N' % 5) (N' / 5)) hz1).1 hl
    exact ⟨_, run_comp_none hrun hk⟩

end BCM
