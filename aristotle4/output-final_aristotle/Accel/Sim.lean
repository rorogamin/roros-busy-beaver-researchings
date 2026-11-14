import Accel.Drain

/-!
# A certified accelerated simulator

`accelStep` performs one *drain* (`drain`) when the configuration has the
required shape — state `A`, a base-3 counter with frontier `1` on the left, a
non-empty token word on the right — and otherwise one literal machine step.
`accelStep_sound` shows that every accelerated step is an exact run of the
machine, so the evaluation of `runAccel` can be used as a certificate.
-/

namespace TM2x5

/-! ## Parsing -/

/-- Split off the maximal token word at the front of a list of cells. -/
def parseToks : List Sym → List Tok × List Sym
  | Sym.s2 :: xs => let p := parseToks xs; (Tok.two :: p.1, p.2)
  | Sym.s4 :: Sym.s0 :: xs => let p := parseToks xs; (Tok.p0 :: p.1, p.2)
  | Sym.s4 :: Sym.s2 :: xs => let p := parseToks xs; (Tok.p2 :: p.1, p.2)
  | Sym.s4 :: Sym.s3 :: xs => let p := parseToks xs; (Tok.p3 :: p.1, p.2)
  | Sym.s4 :: Sym.s4 :: xs => let p := parseToks xs; (Tok.p4 :: p.1, p.2)
  | xs => ([], xs)

theorem parseToks_spec : ∀ xs : List Sym, decode (parseToks xs).1 ++ (parseToks xs).2 = xs
  | Sym.s2 :: xs => by simp [parseToks, decode, Tok.syms, parseToks_spec xs]; rfl
  | Sym.s4 :: Sym.s0 :: xs => by
    simp [parseToks, decode, Tok.syms, parseToks_spec xs]; exact ⟨rfl, rfl⟩
  | Sym.s4 :: Sym.s2 :: xs => by
    simp [parseToks, decode, Tok.syms, parseToks_spec xs]; exact ⟨rfl, rfl⟩
  | Sym.s4 :: Sym.s3 :: xs => by
    simp [parseToks, decode, Tok.syms, parseToks_spec xs]; exact ⟨rfl, rfl⟩
  | Sym.s4 :: Sym.s4 :: xs => by simp [parseToks, decode, Tok.syms, parseToks_spec xs]; rfl
  | [] => rfl
  | [Sym.s0] => rfl
  | [Sym.s1] => rfl
  | [Sym.s3] => rfl
  | [Sym.s4] => rfl
  | Sym.s0 :: _ :: _ => rfl
  | Sym.s1 :: _ :: _ => rfl
  | Sym.s3 :: _ :: _ => rfl
  | Sym.s4 :: Sym.s1 :: _ => rfl

/-- Split a left tape (nearest cell first) into counter digits, the frontier `1`
and the rest. -/
def parseCounter : List Sym → Option (List Sym × List Sym)
  | Sym.s1 :: L => some ([], L)
  | Sym.s3 :: xs => (parseCounter xs).map fun p => (Sym.s3 :: p.1, p.2)
  | Sym.s4 :: xs => (parseCounter xs).map fun p => (Sym.s4 :: p.1, p.2)
  | Sym.s0 :: xs => (parseCounter xs).map fun p => (Sym.s0 :: p.1, p.2)
  | _ => none

theorem parseCounter_spec : ∀ (l ds L : List Sym), parseCounter l = some (ds, L) →
    l = ds ++ (1 : Sym) :: L
  | [], ds, L, h => by simp [parseCounter] at h
  | Sym.s1 :: L', ds, L, h => by
    simp only [parseCounter, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | Sym.s2 :: _, ds, L, h => by simp [parseCounter] at h
  | Sym.s3 :: xs, ds, L, h => by
    simp only [parseCounter, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, b⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [parseCounter_spec xs a b h1]; rfl
  | Sym.s4 :: xs, ds, L, h => by
    simp only [parseCounter, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, b⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [parseCounter_spec xs a b h1]; rfl
  | Sym.s0 :: xs, ds, L, h => by
    simp only [parseCounter, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, b⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [parseCounter_spec xs a b h1]; rfl

/-- Number of base-3 digits of `n` (`0` for `n = 0`). -/
def len3 (n : ℕ) : ℕ := if n = 0 then 0 else len3 (n / 3) + 1

/-! ## One accelerated step -/

/-- The width of the counter after it has been raised to `N'`. -/
def newWidth (m N' : ℕ) : ℕ := if N' < 3 ^ m then m else len3 N'

/-- The data of a drain, if the configuration admits one: the number of steps
and the resulting configuration. -/
def drainStep (c : Cfg) : Option (ℕ × Cfg) :=
  if c.st ≠ St.A then none else
  match parseCounter c.left with
  | none => none
  | some (ds, L) =>
    let pt := parseToks (c.cur :: c.right)
    let w := pt.1
    if w = [] then none else
    let m := ds.length
    let N := counterValue ds
    let e := exh w
    let C := e.1
    let N' := N + C
    let m' := newWidth m N'
    if 1 ≤ m ∧ enc m N = ds ∧ N < 3 ^ m ∧ m ≤ m' ∧ N' < 3 ^ m' ∧
        (m < m' → 3 ^ (m' - 1) ≤ N') ∧ (m < m' → L = []) then
      some (e.2.2 + (2 * C + dsum m' N + 2 * (m' - m) - dsum m' N'),
        onFirst St.A (e.2.1.reverse ++ enc m' N' ++ (1 : Sym) :: L) pt.2)
    else none

theorem drainStep_sound (c : Cfg) (n : ℕ) (c' : Cfg) (h : drainStep c = some (n, c')) :
    iter n (some c) = some c' := by
  obtain ⟨st, l, x, rs⟩ := c
  unfold drainStep at h
  by_cases hst : st = St.A
  swap
  · simp [hst] at h
  subst hst
  simp only [ne_eq, not_true_eq_false, if_false] at h
  cases hpc : parseCounter l with
  | none => simp [hpc] at h
  | some p =>
    obtain ⟨ds, L⟩ := p
    simp only [hpc] at h
    split_ifs at h with hw hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hm, henc, hN, hmm, hk, hpow, hL⟩ := hcond
    have hl := parseCounter_spec l ds L hpc
    have hx := parseToks_spec (x :: rs)
    obtain ⟨T, hT, hc⟩ := drain (parseToks (x :: rs)).1 ds.length (counterValue ds) L
      (parseToks (x :: rs)).2 _ hm hN hmm hk hpow hL
    have hTeq : T = 2 * (exh (parseToks (x :: rs)).1).1 +
        dsum (newWidth ds.length (counterValue ds + (exh (parseToks (x :: rs)).1).1)) (counterValue ds) +
        2 * (newWidth ds.length (counterValue ds + (exh (parseToks (x :: rs)).1).1) - ds.length) -
        dsum (newWidth ds.length (counterValue ds + (exh (parseToks (x :: rs)).1).1))
          (counterValue ds + (exh (parseToks (x :: rs)).1).1) := by
      omega
    rw [← hTeq]
    rw [henc, hx, ← hl] at hT
    exact hT

/-- One accelerated step: a drain if possible, otherwise a literal step. -/
def accelStep (c : Cfg) : Option (ℕ × Cfg) :=
  match drainStep c with
  | some r => some r
  | none => (step c).map fun d => (1, d)

theorem accelStep_sound (c : Cfg) (n : ℕ) (c' : Cfg) (h : accelStep c = some (n, c')) :
    iter n (some c) = some c' := by
  unfold accelStep at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h
    subst h
    exact drainStep_sound c n c' hr
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl⟩ := h
    simpa [iter_one] using hd

/-- Run accelerated steps (at most `fuel` of them) until the step count reaches
`target`; returns the step count and the configuration reached. -/
def runAccel : ℕ → ℕ → Cfg → ℕ → Option (ℕ × Cfg)
  | 0, _, _, _ => none
  | fuel + 1, target, c, t =>
    if target ≤ t then some (t, c) else
    match accelStep c with
    | none => none
    | some (n, c') => runAccel fuel target c' (t + n)

theorem runAccel_sound : ∀ (fuel target : ℕ) (c : Cfg) (t t' : ℕ) (c' : Cfg),
    runAccel fuel target c t = some (t', c') →
      t ≤ t' ∧ target ≤ t' ∧ iter (t' - t) (some c) = some c'
  | 0, _, _, _, _, _, h => by simp [runAccel] at h
  | fuel + 1, target, c, t, t', c', h => by
    unfold runAccel at h
    split_ifs at h with ht
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨le_refl _, ht, by simp; rfl⟩
    · split at h
      · simp at h
      · rename_i n d hstep
        obtain ⟨h1, h2, h3⟩ := runAccel_sound fuel target d (t + n) t' c' h
        refine ⟨by omega, h2, ?_⟩
        rw [show t' - t = n + (t' - (t + n)) by omega, iter_add, accelStep_sound c n d hstep, h3]

/-- If the accelerated simulator, started from the blank tape, reaches the step
count `target`, the machine has not halted within `target` steps. -/
theorem no_halt_of_runAccel {fuel target : ℕ}
    (h : (runAccel fuel target init 0).isSome = true) : ∀ n ≤ target, run n ≠ none := by
  obtain ⟨⟨t', c'⟩, hr⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨_, h2, h3⟩ := runAccel_sound fuel target init 0 t' c' hr
  intro n hn hnone
  have := run_eq_none_of_le (show n ≤ t' by omega) hnone
  simp only [Nat.sub_zero] at h3
  rw [run] at this
  rw [this] at h3
  exact absurd h3 (by simp)

end TM2x5
