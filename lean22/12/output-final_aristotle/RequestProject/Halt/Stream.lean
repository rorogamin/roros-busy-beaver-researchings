module

public import RequestProject.Halt.Periodic

/-!
# Correctness of the engine, part 5: streaming through the pipeline

`chain q S j` is the level word of level `q + j` when level `q` receives `S`.
`pushChunk_spec` and `streamArr_spec` show that the engine's pipeline keeps the
cell states of all levels in sync with these words, and that a reported quiet
halt at level `q + l` is a genuine halt of that level on its word, after which
level `q + l + 1` has received nothing.
-/

@[expose] public section

namespace TM5.Eng

open HaltEngine

/-- Level words from level `q` on, as a function of the level word `S` of
level `q`. -/
def chain (q : Nat) (S : List St) : Nat → List St
  | 0 => S
  | j + 1 => cellOut (dec (initSt (q + j))).1 (dec (initSt (q + j))).2 (chain q S j)

theorem lev_chain (xs : List St) (q : Nat) : ∀ j, lev R0 xs (q + j) = chain q (lev R0 xs q) j
  | 0 => rfl
  | j + 1 => by rw [← Nat.add_assoc, lev_step, lev_chain xs q j]; rfl

theorem chain_eq_from {q : Nat} {S S' : List St} {j : Nat} (h : chain q S' j = chain q S j) :
    ∀ l, j ≤ l → chain q S' l = chain q S l := by
  intro l hl
  induction l with
  | zero => have : j = 0 := by omega
            subst this; exact h
  | succ l ih =>
    rcases Nat.lt_or_ge l j with h1 | h1
    · have : j = l + 1 := by omega
      subst this; exact h
    · simp only [chain]; rw [ih h1]

/-- The pipeline states `sts` (levels `q, q+1, …`) are those reached after the
level-`q` word `S`. -/
def Inv (q : Nat) (S : List St) (sts : Array UInt8) : Prop :=
  ∀ j, j < sts.size → (sts[j]!).toNat < 10 ∧
    cellEnd (dec (initSt (q + j))).1 (dec (initSt (q + j))).2 (chain q S j) = some (dec sts[j]!)

/-- Level `q + l` halts on its word, and emits nothing. -/
def HaltAt (q : Nat) (S : List St) (l : Nat) : Prop :=
  cellEnd (dec (initSt (q + l))).1 (dec (initSt (q + l))).2 (chain q S l) = none ∧
    chain q S (l + 1) = []

/-- The content after one cell step (`1` on a halt). -/
def newC (c : Sym) (f : Bool) (x : St) : Nat :=
  match cell1 c f x with
  | none => 1
  | some (c', _, _) => c'.val

theorem newC_ne_zero_aux : ∀ (c : Sym) (f : Bool) (x : Bool), newC c f (ofB x) ≠ 0 := by decide

theorem cellEnd_ne_zero : ∀ (w : List St) (c : Sym) (f : Bool) (c' : Sym) (f' : Bool),
    cellEnd c f w = some (c', f') → w ≠ [] → c' ≠ 0
  | [], _, _, _, _, _, h => absurd rfl h
  | x :: w, c, f, c', f', h, _ => by
    have hz := newC_ne_zero_aux c f (toB x)
    rw [ofB_toB] at hz
    simp only [cellEnd] at h
    unfold newC at hz
    revert h hz
    cases cell1 c f x with
    | none => intro h; cases h
    | some v =>
      obtain ⟨c1, f1, o⟩ := v
      intro h hz
      cases w with
      | nil =>
        simp only [cellEnd, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; intro e; apply hz; rw [e]; rfl
      | cons y w => exact cellEnd_ne_zero (y :: w) c1 f1 c' f' h (List.cons_ne_nil _ _)

theorem cellEnd_zero (w : List St) (c : Sym) (f f' : Bool) (h : cellEnd c f w = some (0, f')) :
    w = [] := by
  cases w with
  | nil => rfl
  | cons x w => exact absurd rfl (cellEnd_ne_zero _ c f 0 f' h (List.cons_ne_nil _ _))

theorem set_ne (a : Array UInt8) (j l : Nat) (s : UInt8) (h : l ≠ j) : (a.set! j s)[l]! = a[l]! := by
  rcases Nat.lt_or_ge l a.size with hl | hl
  · rw [getElem!_pos _ l (by simp [Array.set!]; exact hl), getElem!_pos a l hl]
    simp only [Array.set!]
    rw [Array.getElem_setIfInBounds_ne hl (Ne.symm h)]
  · rw [getElem!_neg _ l (by simp [Array.set!]; omega), getElem!_neg a l (by omega)]

theorem set_eq (a : Array UInt8) (j : Nat) (s : UInt8) (h : j < a.size) : (a.set! j s)[j]! = s := by
  simp [Array.set!, h]

theorem size_set (a : Array UInt8) (j : Nat) (s : UInt8) : (a.set! j s).size = a.size := by
  simp [Array.set!]

/-- Specification of `pushChunk`. -/
def PushOK (q : Nat) (S : List St) (sts : Array UInt8) : CR → Prop
  | .ok sts' => sts'.size = sts.size ∧ Inv q S sts'
  | .halt l b => b = true → HaltAt q S l
  | .overflow => True

theorem pushChunk_spec (q : Nat) (S S' : List St) : ∀ fuel j sts inp i n,
    (∀ l, l < j → l < sts.size → (sts[l]!).toNat < 10 ∧
      cellEnd (dec (initSt (q + l))).1 (dec (initSt (q + l))).2 (chain q S' l) = some (dec sts[l]!)) →
    (∀ l, j ≤ l → l < sts.size → (sts[l]!).toNat < 10 ∧
      cellEnd (dec (initSt (q + l))).1 (dec (initSt (q + l))).2 (chain q S l) = some (dec sts[l]!)) →
    chain q S' j = chain q S j ++ (rd inp i n).map ofB →
    PushOK q S' sts (pushChunk sts inp i n j fuel) := by
  intro fuel
  induction fuel with
  | zero => intro j sts inp i n _ _ _; trivial
  | succ fuel ih =>
    intro j sts inp i n hlo hhi hC
    simp only [pushChunk]
    by_cases hn : n = 0
    · simp only [hn, beq_self_eq_true, if_true]
      refine ⟨rfl, fun l hl => ?_⟩
      rcases Nat.lt_or_ge l j with h1 | h1
      · exact hlo l h1 hl
      · have e : chain q S' j = chain q S j := by rw [hC, hn]; simp [rd, rdBytes]
        rw [chain_eq_from e l h1]; exact hhi l h1 hl
    have hn' : (n == 0) = false := by simpa using hn
    simp only [hn', Bool.false_eq_true, if_false]
    by_cases hj : j + 1 ≥ sts.size
    · simp only [hj, if_true]; trivial
    simp only [hj, if_false]
    obtain ⟨hv, hend⟩ := hhi j (Nat.le_refl _) (by omega)
    obtain ⟨fv, fb⟩ := fresh_spec (n / 8 + n / 32 + 64)
    have hf := feed_spec inp i n sts[j]! _ hv fv
    revert hf
    cases feed inp i n sts[j]! (Acc.fresh (n / 8 + n / 32 + 64)) with
    | halt b =>
      intro hf
      obtain ⟨h1, h2⟩ := hf
      intro hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨hb1, hb2⟩ := hb
      obtain ⟨_, hq2⟩ := h2 hb1
      have hz := (hhi (j + 1) (by omega) (by omega)).2
      rw [hb2] at hz
      have hnil : chain q S (j + 1) = [] := cellEnd_zero _ _ _ _ hz
      refine ⟨?_, ?_⟩
      · rw [hC, cellEnd_append _ _ _ _ (dec sts[j]!).1 (dec sts[j]!).2 hend]; exact h1
      · show cellOut _ _ (chain q S' j) = []
        rw [hC, cellOut_append_of_end _ _ _ _ (dec sts[j]!).1 (dec sts[j]!).2 hend, hq2, List.append_nil]
        exact hnil
    | ok s a =>
      intro hf
      obtain ⟨h1, h2, h3, h4⟩ := hf
      rw [fb] at h4
      have hcl := close_letters a h3 _ h4
      simp only
      generalize a.close = oc at hcl ⊢
      obtain ⟨o, m⟩ := oc
      have := ih (j + 1) (sts.set! j s) o 0 m ?_ ?_ ?_
      · revert this
        cases pushChunk (sts.set! j s) o 0 m (j + 1) fuel with
        | ok sts' => intro h; exact ⟨by rw [h.1, size_set], h.2⟩
        | halt l b => exact id
        | overflow => intro _; trivial
      · intro l hl hls
        rw [size_set] at hls
        rcases Nat.lt_or_ge l j with h5 | h5
        · rw [set_ne _ _ _ _ (by omega)]; exact hlo l h5 hls
        · have e : l = j := by omega
          rw [e] at hls ⊢
          rw [set_eq _ _ _ hls, hC, cellEnd_append _ _ _ _ (dec sts[j]!).1 (dec sts[j]!).2 hend]
          exact ⟨h1, h2⟩
      · intro l hl hls
        rw [size_set] at hls
        rw [set_ne _ _ _ _ (by omega)]; exact hhi l (by omega) hls
      · show cellOut _ _ (chain q S' j) = cellOut _ _ (chain q S j) ++ _
        rw [hC, cellOut_append_of_end _ _ _ _ (dec sts[j]!).1 (dec sts[j]!).2 hend, hcl]


theorem rd_zero (a : ByteArray) (i : Nat) : rd a i 0 = [] := by simp [rd, rdBytes]

theorem rd_split (src : ByteArray) (c i n : Nat) :
    rd src i n = rd src i (min (8 * c) n) ++ rd src (i + c) (n - min (8 * c) n) := by
  rcases Nat.le_total n (8 * c) with h | h
  · rw [Nat.min_eq_right h, Nat.sub_self, rd_zero, List.append_nil]
  · rw [Nat.min_eq_left h]
    unfold rd
    have e1 : n / 8 = c + (n - 8 * c) / 8 := by omega
    have e2 : (n - 8 * c) % 8 = n % 8 := by omega
    rw [e1, rdBytes_add, show 8 * c / 8 = c by omega, show 8 * c % 8 = 0 by omega, e2,
      ← Nat.add_assoc]
    simp

/-- Specification of `streamArr`. -/
def StreamOK (q : Nat) (S R : List St) (sts : Array UInt8) : SR → Prop
  | .done sts' => sts'.size = sts.size ∧ Inv q (S ++ R) sts'
  | .halt l b => b = true → ∃ U, U <+: R ∧ HaltAt q (S ++ U) l
  | .overflow => True

theorem streamArr_spec (q : Nat) (src : ByteArray) (c : Nat) (hc : 0 < c) :
    ∀ fuel sts i n S, n ≤ fuel → Inv q S sts →
      StreamOK q S ((rd src i n).map ofB) sts (streamArr src c sts i n fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro sts i n S hn hI
    have : n = 0 := by omega
    subst this
    exact ⟨rfl, by rw [rd_zero, List.map_nil, List.append_nil]; exact hI⟩
  | succ fuel ih =>
    intro sts i n S hn hI
    simp only [streamArr]
    by_cases h0 : n = 0
    · subst h0
      exact ⟨rfl, by rw [rd_zero, List.map_nil, List.append_nil]; exact hI⟩
    have h0' : (n == 0) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, if_false]
    have hp := pushChunk_spec q S (S ++ (rd src i (min (8 * c) n)).map ofB) (sts.size + 1) 0 sts
      src i (min (8 * c) n) (fun l hl _ => absurd hl (Nat.not_lt_zero _))
      (fun l _ hl => hI l hl) rfl
    have hsplit := rd_split src c i n
    revert hp
    cases pushChunk sts src i (min (8 * c) n) 0 (sts.size + 1) with
    | ok sts' =>
      intro hp
      dsimp only
      obtain ⟨hs1, hs2⟩ := hp
      have := ih sts' (i + c) (n - min (8 * c) n) _ (by omega) hs2
      revert this
      cases streamArr src c sts' (i + c) (n - min (8 * c) n) fuel with
      | done sts'' =>
        intro h
        dsimp only [StreamOK] at h ⊢
        refine ⟨by rw [h.1, hs1], ?_⟩
        rw [hsplit, List.map_append, ← List.append_assoc]
        exact h.2
      | halt l b =>
        intro h
        dsimp only [StreamOK] at h ⊢
        intro hb
        obtain ⟨U, hU, hH⟩ := h hb
        refine ⟨(rd src i (min (8 * c) n)).map ofB ++ U, ?_, by rw [← List.append_assoc]; exact hH⟩
        rw [hsplit, List.map_append]
        exact List.prefix_append_right_inj _ |>.mpr hU
      | overflow => intro _; trivial
    | halt l b =>
      intro hp
      dsimp only [StreamOK, PushOK] at hp ⊢
      intro hb
      refine ⟨(rd src i (min (8 * c) n)).map ofB, ?_, hp hb⟩
      rw [hsplit, List.map_append]
      exact List.prefix_append _ _
    | overflow => intro _; trivial

end TM5.Eng
