import RequestProject.Tokens

/-!
# The macro rules at the left end

Every three cells of leftward growth the machine returns to a configuration of the form

> state `B`, head on the leftmost non-blank cell, tape a word over the tokens of
> `Tokens.lean`.

Writing `P1`, `P2`, `P3` for the three shapes that the left end of such a configuration
takes, the observed cycle is

```
P1 :  0 4 4 2 · 0 4 4 4 4 2 · R          (tokU 2 1, tokU 4 1, …)
P2 :  0 4 4 2 2 · 0 4 2 · R'             (tokU 2 2, tokU 1 1, …)
P3 :  0 4 4 2 2 · 4 3 2 · 0 4 2 · R'     (tokU 2 2, tokV 1, tokU 1 1, …)
```

This file proves the three *local* macro rules that implement this cycle whenever the
first token of the tail has `b ≥ 2` and `a = 1`:

* `rule_P2` — `P2 → P3` in exactly `31` steps, **independently of the rest of the tape**;
* `rule_P1` — `P1 → P2` in exactly `59 + 20m` steps, for `tokU 1 (2m)` as third token;
* `rule_P3` — `P3 → P1` in exactly `71 + 20m` steps, for `tokU 1 (2m)` as fourth token.

Each is stated in the `Win` format of `Local.lean`, so each also says that the head never
leaves the stated window: in particular the rest of the tape is arbitrary and untouched,
and the machine does not halt while the rule is being applied.
-/

namespace BB25

/-! ### Two structural lemmas about window rules -/

/-- A window rule may be embedded in a larger window: since the head provably never leaves
the window, adjacent material is irrelevant. -/
theorem Win.embed {q q' : St} {k k' : ℕ} {l l' : List Sym} {n : ℕ}
    (h : Win q q' k k' l l' n) (hlen : l'.length = l.length) (p s : List Sym) :
    Win q q' (p.length + k) (p.length + k') (p ++ l ++ s) (p ++ l' ++ s) n := by
  intro T a hseg
  rw [List.append_assoc, Seg_append] at hseg
  obtain ⟨hp, hrest⟩ := hseg
  rw [Seg_append] at hrest
  obtain ⟨hl, hs⟩ := hrest
  obtain ⟨T', hstep, hl', hout⟩ := h T (a + (p.length : ℤ)) hl
  refine ⟨T', ?_, ?_, ?_⟩
  · rw [show a + ((p.length + k : ℕ) : ℤ) = a + (p.length : ℤ) + (k : ℤ) by push_cast; ring]
    rw [hstep]
    congr 1
    push_cast; ring
  · rw [List.append_assoc, Seg_append]
    refine ⟨?_, ?_⟩
    · exact Seg_congr (fun i hi => hout _ (Or.inl (by omega))) hp
    · rw [Seg_append]
      refine ⟨hl', ?_⟩
      rw [hlen]
      exact Seg_congr (fun i hi => hout _ (Or.inr (by omega))) hs
  · intro i hi
    refine hout i ?_
    simp only [List.length_append] at hi
    rcases hi with hi | hi
    · left; omega
    · right; push_cast at hi ⊢; omega

/-- Window rules compose. -/
theorem Win.trans {q q1 q' : St} {k k1 k' : ℕ} {l l1 l' : List Sym} {n1 n2 : ℕ}
    (h1 : Win q q1 k k1 l l1 n1) (h2 : Win q1 q' k1 k' l1 l' n2)
    (hlen : l1.length = l.length) :
    Win q q' k k' l l' (n1 + n2) := by
  intro T a hseg
  obtain ⟨T1, hs1, hl1, hout1⟩ := h1 T a hseg
  obtain ⟨T2, hs2, hl2, hout2⟩ := h2 T1 a hl1
  refine ⟨T2, ?_, hl2, ?_⟩
  · rw [Nat.add_comm, Function.iterate_add_apply, hs1, hs2]
  · intro i hi
    rw [hout2 i (by rw [hlen]; exact hi), hout1 i hi]

/-! ### Bridges from the `SweepR`/`SweepL` rules -/

/-- A rightward sweep is a local rule on the window `u ++ [x]`: the head enters at the
left end and stops on the extra cell `x`, which it never acts on. -/
theorem Win.of_sweepR {q q' : St} {u v : List Sym} {n : ℕ} (h : SweepR q q' u v n)
    (hlen : v.length = u.length) (x : Sym) :
    Win q q' 0 u.length (u ++ [x]) (v ++ [x]) n := by
  intro T a hseg
  rw [Seg_append] at hseg
  obtain ⟨hu, hx⟩ := hseg
  obtain ⟨T', hstep, hv, hout⟩ := h T a hu
  refine ⟨T', ?_, ?_, ?_⟩
  · simpa using hstep
  · rw [Seg_append]
    refine ⟨hv, ?_⟩
    rw [hlen]
    exact Seg_congr (fun i hi => hout _ (Or.inr (by omega))) hx
  · intro i hi
    refine hout i ?_
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    rcases hi with hi | hi
    · left; omega
    · right; push_cast at hi ⊢; omega

/-- A leftward sweep is a local rule on the window `x :: u`: the head enters at the right
end and stops on the extra cell `x`, which it never acts on. -/
theorem Win.of_sweepL {q q' : St} {u v : List Sym} {n : ℕ} (h : SweepL q q' u v n)
    (x : Sym) :
    Win q q' u.length 0 (x :: u) (x :: v) n := by
  intro T a hseg
  rw [Seg_cons] at hseg
  obtain ⟨hx, hu⟩ := hseg
  obtain ⟨T', hstep, hv, hout⟩ := h T (a + 1) hu
  refine ⟨T', ?_, ?_, ?_⟩
  · rw [show a + ((u.length : ℕ) : ℤ) = a + 1 + (u.length : ℤ) - 1 by ring,
      hstep]
    congr 1
    push_cast; ring
  · rw [Seg_cons]
    exact ⟨by rw [hout a (Or.inl (by omega))]; exact hx, hv⟩
  · intro i hi
    refine hout i ?_
    simp only [List.length_cons] at hi
    rcases hi with hi | hi
    · left; omega
    · right; push_cast at hi ⊢; omega

/-! ### `P2 → P3` -/

/-- **The `P2` rule.**  The head is in state `B` on the leftmost non-blank cell, which
begins the token `0 4 4 2 2`; the next cell is the `0` of the following token, and the
three cells to the left are blank.  Then in exactly `31` steps the machine inserts the
token `4 3 2` and arrives, again in state `B`, on the new leftmost non-blank cell three
cells further left.  Nothing outside the nine-cell window is read or written, so the rest
of the tape is completely arbitrary. -/
theorem rule_P2 :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ [0])
      (tokU 2 2 ++ tokV 1 ++ [0]) 31 :=
  Win.of_lrun (by decide)

/-- The machine does not halt while `rule_P2` is being applied. -/
theorem rule_P2_no_halt (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ [0])) :
    ∀ m ≤ 31, ¬ Halted (step^[m] ⟨St.B, a + 3, T⟩) := by
  have := rule_P2.no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this


/-! ### The repeated region: the period-`8` ping-pong through a run of `2`s -/

/-- The trivial window rule. -/
theorem Win.refl (q : St) (k : ℕ) (l : List Sym) : Win q q k k l l 0 := by
  intro T a hs
  exact ⟨T, rfl, hs, fun _ _ => rfl⟩

/-- **The ping-pong unit.**  A marker `1 0 3` immediately to the left of a run of `2`s
travels two cells into the run in exactly `8` steps, leaving `1`s behind.  Only six cells
are involved, so the rule holds wherever this pattern occurs. -/
theorem pingpong_unit : Win St.A St.A 3 5 [1, 0, 3, 2, 2, 2] [1, 1, 1, 0, 3, 2] 8 :=
  Win.of_lrun (by decide)

lemma pingpong_list (n : ℕ) :
    [(1 : Sym), 0, 3] ++ List.replicate (2 * n + 3) 2
      = ([1, 0, 3, 2, 2, 2] : List Sym) ++ List.replicate (2 * n) 2 := by
  have : (2 * n + 3) = 3 + 2 * n := by ring
  rw [this, List.replicate_add]
  simp

lemma pingpong_list' (n : ℕ) :
    ([1, 1] : List Sym) ++ ([1, 0, 3] ++ List.replicate (2 * n + 1) 2)
      = ([1, 1, 1, 0, 3, 2] : List Sym) ++ List.replicate (2 * n) 2 := by
  have : (2 * n + 1) = 1 + 2 * n := by ring
  rw [this, List.replicate_add]
  simp

/-- **The ping-pong chain.**  The marker `1 0 3` crosses `2n` cells of a run of `2`s in
exactly `8n` steps, turning them into `1`s.  The window contains one `2` beyond the cells
that are consumed — that is where the head ends up — and, as for every `Win` rule, the
tape outside the window is arbitrary and untouched. -/
theorem pingpong_chain (n : ℕ) :
    Win St.A St.A 3 (2 * n + 3)
      ([1, 0, 3] ++ List.replicate (2 * n + 1) 2)
      (List.replicate (2 * n + 1) 1 ++ [0, 3, 2]) (8 * n) := by
  induction n with
  | zero => simpa using Win.refl St.A 3 ([1, 0, 3] ++ List.replicate 1 2)
  | succ n ih =>
      have e1 : 2 * (n + 1) + 3 = 2 * n + 5 := by ring
      have e2 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
      have e3 : 8 * (n + 1) = 8 + 8 * n := by ring
      rw [e1, e2, e3]
      have h1 : Win St.A St.A 3 5
          ([1, 0, 3] ++ List.replicate (2 * n + 3) 2)
          (([1, 1, 1, 0, 3, 2] : List Sym) ++ List.replicate (2 * n) 2) 8 := by
        have := pingpong_unit.embed (by simp) [] (List.replicate (2 * n) 2)
        simpa [pingpong_list n] using this
      have h2 : Win St.A St.A 5 (2 * n + 5)
          (([1, 1, 1, 0, 3, 2] : List Sym) ++ List.replicate (2 * n) 2)
          (([1, 1] : List Sym) ++ (List.replicate (2 * n + 1) 1 ++ [0, 3, 2])) (8 * n) := by
        have h := ih.embed (by simp) [1, 1] []
        rw [pingpong_list' n] at h
        have ek : ([1, 1] : List Sym).length + 3 = 5 := by simp
        have ek' : ([1, 1] : List Sym).length + (2 * n + 3) = 2 * n + 5 := by simp; ring
        rw [ek, ek'] at h
        simpa using h
      have hlen : (([1, 1, 1, 0, 3, 2] : List Sym) ++ List.replicate (2 * n) 2).length
          = ([1, 0, 3] ++ List.replicate (2 * n + 3) 2 : List Sym).length := by
        simp only [List.length_append, List.length_replicate, List.length_cons,
          List.length_nil]
        omega
      have hc := h1.trans h2 hlen
      have hl : ([1, 1] : List Sym) ++ (List.replicate (2 * n + 1) 1 ++ [0, 3, 2])
          = List.replicate (2 * n + 3) 1 ++ [0, 3, 2] := by
        have e : 2 * n + 3 = 2 + (2 * n + 1) := by ring
        rw [e, List.replicate_add 2 (2 * n + 1) (1 : Sym), List.append_assoc]
        rfl
      rw [hl] at hc
      exact hc

end BB25
