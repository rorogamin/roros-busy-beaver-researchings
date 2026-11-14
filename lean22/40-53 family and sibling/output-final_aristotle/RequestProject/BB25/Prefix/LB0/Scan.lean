/-
# `0LB`: the `<B1` sweep over a paid reset stack

The `A> 241` rule of `0LB` is `A> 241 → <A 101`; together with the auxiliary
rules `A> 101 → <A 201` and `A> 201 → <B1 22` a pop met by the `<B1` sweep
costs **four** decrements of the counter below it:

```
  c W <B1 …  ⟶  D⁴(c) <B1 22 …        (when cval c ≥ 4)
```

The sweep is followed here on a stack `D^n (T u)` — `n` decrements owed by
the paid reset stack of a word `u` — reading `u` backwards (the reverse-debt
table of Section 6 of the submitted argument):

| last letter | action                                   |
| ----------- | ---------------------------------------- |
| `X`         | cross the pop, debt `n ↦ 2n + 6`         |
| `Y`, odd    | cross a zero bit, debt `n ↦ (n - 1)/2`   |
| `Y`, even   | stop at a one bit, core `D^(n/2) (T u')` |
| `V`, even   | cross a zero bit, debt `n ↦ n/2`         |
| `V`, odd    | stop at a one bit, core `D^((n+1)/2) (T u')` |

The supply of every pop is certified by the energy of the word:
`n ≤ erun u 0` is carried along the whole sweep.
-/
import RequestProject.BB25.Prefix.LB0.Clock

namespace BB25.Prefix

open BB25

/-! ## Configurations -/

/-- The right side of a sweep: a run of `22` blocks and the terminal `1`. -/
def ytail (j : ℕ) : List RB := List.replicate j .Y ++ [.R1]

theorem Y_ytail (j : ℕ) : RB.Y :: ytail j = ytail (j + 1) := by
  rw [ytail, ytail, List.replicate_succ, List.cons_append]

/-- A **Z checkpoint**: the sweep has stopped at a one bit above the core `c`,
with `r` blocks `22` in front of the terminal `1`. -/
def zCfg (c : List LB) (r : ℕ) : BCfg := ⟨.Z :: c, .Bt, ytail r⟩

/-! ## The reverse-debt identities -/

section Debt

variable {u : List RB} {n : ℕ}

theorem dpow_TW_Y_even (h : n % 2 = 0) : dpow n (TW (u ++ [.Y])) = .Z :: dpow (n / 2) (TW u) := by
  rw [TW_Y]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨(n - 2) / 2, by omega⟩
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, dpow_succ', cdec_Z, dpow_X_odd]
    congr 2
    omega

theorem dpow_TW_Y_odd (h : n % 2 = 1) : dpow n (TW (u ++ [.Y])) = .X :: dpow ((n - 1) / 2) (TW u) := by
  rw [TW_Y]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨(n - 1) / 2, by omega⟩
  rw [dpow_succ', cdec_Z, dpow_X_even]
  congr 2
  omega

theorem dpow_TW_V_even (h : n % 2 = 0) : dpow n (TW (u ++ [.V])) = .X :: dpow (n / 2) (TW u) := by
  rw [TW_V]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rw [dpow_X_even]
  congr 2
  omega

theorem dpow_TW_V_odd (h : n % 2 = 1) : dpow n (TW (u ++ [.V])) = .Z :: dpow ((n + 1) / 2) (TW u) := by
  rw [TW_V]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨(n - 1) / 2, by omega⟩
  rw [dpow_X_odd]
  congr 2
  omega

theorem dpow_TW_X' : dpow n (TW (u ++ [.X])) = .W :: dpow (2 * n + 2) (TW u) := by
  rw [TW_X, dpow_W, ← dpow_add]

end Debt

/-! ## The machine steps of the sweep -/

variable {b4 : Option (Sym × Dir × St)}

/-- **A pop costs four decrements** (`0LB`). -/
theorem brun_pop_0LB {s : List LB} (hst : CStack s) (h4 : 4 ≤ cval s) (rt : List RB) :
    ∃ k, BRun b4_0LB ⟨.W :: s, .Bt, rt⟩ ⟨dpow 4 s, .Bt, .Y :: rt⟩ k := by
  have hst1 : CStack (dpow 1 s) := CStack_dpow hst 1
  have hst2 : CStack (dpow 2 s) := CStack_dpow hst 2
  have hst3 : CStack (dpow 3 s) := CStack_dpow hst 3
  have hc1 : cval (dpow 1 s) = cval s - 1 := cval_dpow hst 1 (by omega)
  have hc2 : cval (dpow 2 s) = cval s - 2 := cval_dpow hst 2 (by omega)
  have hc3 : cval (dpow 3 s) = cval s - 3 := cval_dpow hst 3 (by omega)
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4_0LB) hst (by omega) (.F :: rt)
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_0LB) hst1 (by omega) (.G :: rt)
  obtain ⟨k3, hr3⟩ := brun_cdec_of (b4 := b4_0LB) hst2 (by omega) (.N1 :: rt)
  obtain ⟨k4, hr4⟩ := brun_cdec_of (b4 := b4_0LB) hst3 (by omega) (.N2 :: rt)
  refine ⟨_, BRun.head (show bstep b4_0LB ⟨.W :: s, .Bt, rt⟩ = some (⟨s, .Lt, .F :: rt⟩, 2) from rfl)
    (hr1.trans (BRun.head
      (show bstep b4_0LB ⟨cdec s, .Rt, .F :: rt⟩ = some (⟨cdec s, .Lt, .G :: rt⟩, 1) from rfl)
      (hr2.trans (BRun.head
        (show bstep b4_0LB ⟨cdec (dpow 1 s), .Rt, .G :: rt⟩
          = some (⟨cdec (dpow 1 s), .Lt, .N1 :: rt⟩, 3) from rfl)
        (hr3.trans (BRun.head
          (show bstep b4_0LB ⟨cdec (dpow 2 s), .Rt, .N1 :: rt⟩
            = some (⟨cdec (dpow 2 s), .Lt, .N2 :: rt⟩, 1) from rfl)
          (hr4.trans (BRun.of_step
            (show bstep b4_0LB ⟨cdec (dpow 3 s), .Rt, .N2 :: rt⟩
              = some (⟨cdec (dpow 3 s), .Bt, .Y :: rt⟩, 9) from rfl)))))))))⟩

/-- The counter of a paid reset stack of a word of nonnegative energy. -/
theorem TW_of_energy {u : List RB} (hu : Digs u) {e : ℤ} (he : 0 ≤ e) (h : e ≤ erun u 0) :
    CStack (TW u) ∧ e ≤ (cval (TW u) : ℤ) := by
  have hr : erun u 0 ≤ rrun u 0 := erun_le_rrun u le_rfl
  obtain ⟨hst, -, -, hcv, -⟩ := TW_facts hu (by omega)
  exact ⟨hst, by omega⟩

section Steps

variable {u : List RB} {n j : ℕ}

/-- Crossing a final `V` under an even debt. -/
theorem scan_V_even (h : n % 2 = 0) (he : (n : ℤ) ≤ erun (u ++ [.V]) 0) :
    BRun b4 ⟨dpow n (TW (u ++ [.V])), .Bt, ytail j⟩ ⟨dpow (n / 2) (TW u), .Bt, ytail (j + 1)⟩ 6 ∧
      ((n / 2 : ℕ) : ℤ) ≤ erun u 0 := by
  rw [dpow_TW_V_even h, ← Y_ytail]
  refine ⟨BRun.of_step rfl, ?_⟩
  rw [erun_append, erun_singleton, estep_V] at he
  omega

/-- Crossing a final `Y` under an odd debt. -/
theorem scan_Y_odd (h : n % 2 = 1) (he : (n : ℤ) ≤ erun (u ++ [.Y]) 0) :
    BRun b4 ⟨dpow n (TW (u ++ [.Y])), .Bt, ytail j⟩
      ⟨dpow ((n - 1) / 2) (TW u), .Bt, ytail (j + 1)⟩ 6 ∧
      (((n - 1) / 2 : ℕ) : ℤ) ≤ erun u 0 := by
  rw [dpow_TW_Y_odd h, ← Y_ytail]
  refine ⟨BRun.of_step rfl, ?_⟩
  rw [erun_append, erun_singleton, estep_Y] at he
  omega

/-- Stopping at a final `Y` under an even debt. -/
theorem scan_Y_even (h : n % 2 = 0) (he : (n : ℤ) ≤ erun (u ++ [.Y]) 0) :
    (⟨dpow n (TW (u ++ [.Y])), .Bt, ytail j⟩ : BCfg) = zCfg (dpow (n / 2) (TW u)) j ∧
      ((n / 2 : ℕ) : ℤ) ≤ erun u 0 := by
  rw [dpow_TW_Y_even h]
  refine ⟨rfl, ?_⟩
  rw [erun_append, erun_singleton, estep_Y] at he
  omega

/-- Stopping at a final `V` under an odd debt. -/
theorem scan_V_odd (h : n % 2 = 1) (he : (n : ℤ) ≤ erun (u ++ [.V]) 0) :
    (⟨dpow n (TW (u ++ [.V])), .Bt, ytail j⟩ : BCfg) = zCfg (dpow ((n + 1) / 2) (TW u)) j ∧
      (((n + 1) / 2 : ℕ) : ℤ) ≤ erun u 0 := by
  rw [dpow_TW_V_odd h]
  refine ⟨rfl, ?_⟩
  rw [erun_append, erun_singleton, estep_V] at he
  omega

/-- Crossing a final pop: four decrements, supplied by the energy. -/
theorem scan_X (hu : Digs u) (he : (n : ℤ) ≤ erun (u ++ [.X]) 0) :
    ∃ k, BRun b4_0LB ⟨dpow n (TW (u ++ [.X])), .Bt, ytail j⟩
      ⟨dpow (2 * n + 6) (TW u), .Bt, ytail (j + 1)⟩ k ∧
      ((2 * n + 6 : ℕ) : ℤ) ≤ erun u 0 := by
  rw [erun_append, erun_singleton, estep_X] at he
  have he' : ((2 * n + 6 : ℕ) : ℤ) ≤ erun u 0 := by push_cast; omega
  obtain ⟨hst, hcv⟩ := TW_of_energy hu (by positivity) he'
  have hcv' : 2 * n + 6 ≤ cval (TW u) := by exact_mod_cast hcv
  have hsst : CStack (dpow (2 * n + 2) (TW u)) := CStack_dpow hst _
  have hsv : cval (dpow (2 * n + 2) (TW u)) = cval (TW u) - (2 * n + 2) :=
    cval_dpow hst _ (by omega)
  obtain ⟨k, hk⟩ := brun_pop_0LB hsst (by omega) (ytail j)
  rw [← dpow_add, show 4 + (2 * n + 2) = 2 * n + 6 by ring, Y_ytail] at hk
  rw [dpow_TW_X']
  exact ⟨k, hk, he'⟩

end Steps

/-! ## Sweeping a run of pops -/

/-- **A run of `X` pops** multiplies `n + 6` by two per pop. -/
theorem scan_Xrun_lb : ∀ (s : ℕ) (pre : List RB) (n j : ℕ), Digs pre →
    (n : ℤ) ≤ erun (pre ++ List.replicate s .X) 0 →
    ∃ k, BRun b4_0LB ⟨dpow n (TW (pre ++ List.replicate s .X)), .Bt, ytail j⟩
      ⟨dpow (2 ^ s * (n + 6) - 6) (TW pre), .Bt, ytail (j + s)⟩ k ∧
      ((2 ^ s * (n + 6) - 6 : ℕ) : ℤ) ≤ erun pre 0 := by
  intro s
  induction s with
  | zero => intro pre n j _ he; exact ⟨0, by simpa using BRun.refl _, by simpa using he⟩
  | succ s ih =>
      intro pre n j hpre he
      have hcat : pre ++ List.replicate (s + 1) RB.X = (pre ++ List.replicate s RB.X) ++ [RB.X] := by
        rw [List.replicate_succ']; simp
      rw [hcat] at he ⊢
      have hdig : Digs (pre ++ List.replicate s RB.X) :=
        hpre.append (fun b hb => by
          rw [List.mem_replicate] at hb
          rw [hb.2]; exact Or.inr (Or.inr rfl))
      obtain ⟨k1, hr1, he1⟩ := scan_X (j := j) hdig he
      obtain ⟨k2, hr2, he2⟩ := ih pre (2 * n + 6) (j + 1) hpre he1
      have hpow : 2 ^ s * (2 * n + 6 + 6) - 6 = 2 ^ (s + 1) * (n + 6) - 6 := by
        rw [pow_succ]; congr 1; ring
      rw [hpow, show j + 1 + s = j + (s + 1) by ring] at hr2
      rw [hpow] at he2
      exact ⟨k1 + k2, hr1.trans hr2, he2⟩

/-- **Sweeping a word of pops.**  Either the sweep stops at a `V` read under an
odd debt — and then, if it entered with an even debt, at least one letter was
crossed before it, at least two if it entered with no debt — or it crosses the
whole word, and the debt `n + 6` has at most doubled per letter. -/
theorem scan_pops : ∀ (t : List RB), Pops t → ∀ (pre : List RB) (n j : ℕ), Digs pre →
    (n : ℤ) ≤ erun (pre ++ t) 0 →
    (∃ (η t2 : List RB) (k' T : ℕ), t = η ++ RB.V :: t2 ∧ (k' : ℤ) ≤ erun (pre ++ η) 0 ∧
        (n % 2 = 0 → 1 ≤ t2.length) ∧ (n = 0 → 2 ≤ t2.length) ∧
        BRun b4_0LB ⟨dpow n (TW (pre ++ t)), .Bt, ytail j⟩
          (zCfg (dpow k' (TW (pre ++ η))) (j + t2.length)) T) ∨
    (∃ (n' T : ℕ), (n' : ℤ) ≤ erun pre 0 ∧ n' + 6 ≤ 2 ^ t.length * (n + 6) ∧
        BRun b4_0LB ⟨dpow n (TW (pre ++ t)), .Bt, ytail j⟩
          ⟨dpow n' (TW pre), .Bt, ytail (j + t.length)⟩ T) := by
  intro t
  induction t using List.reverseRecOn with
  | nil =>
      intro _ pre n j _ he
      refine Or.inr ⟨n, 0, by simpa using he, by simp, by simpa using BRun.refl _⟩
  | append_singleton t b ih =>
      intro hp pre n j hpre he
      have hpt : Pops t := hp.of_append.1
      have hb : b = RB.X ∨ b = RB.V := hp b (by simp)
      have hdig : Digs (pre ++ t) := hpre.append hpt.digs
      have hcat : pre ++ (t ++ [b]) = (pre ++ t) ++ [b] := by simp
      rw [hcat] at he ⊢
      rcases hb with rfl | rfl
      · -- a pop `X`: always crossed
        obtain ⟨k1, hr1, he1⟩ := scan_X (j := j) hdig he
        rcases ih hpt pre (2 * n + 6) (j + 1) hpre he1 with
            ⟨η, t2, k', T, rfl, hk', h1, h0, hr⟩ | ⟨n', T, hn', hbd, hr⟩
        · refine Or.inl ⟨η, t2 ++ [RB.X], k', k1 + T, by simp, hk', ?_, ?_, ?_⟩
          · intro _; simp
          · intro _
            have := h1 (by omega)
            simp; omega
          · have := hr1.trans hr
            simpa [Nat.add_assoc, Nat.add_comm 1] using this
        · refine Or.inr ⟨n', k1 + T, hn', ?_, ?_⟩
          · rw [List.length_append, List.length_singleton, pow_succ]
            have : 2 ^ t.length * (2 * n + 6 + 6) = 2 ^ t.length * 2 * (n + 6) := by ring
            omega
          · have := hr1.trans hr
            simpa [Nat.add_assoc, Nat.add_comm 1] using this
      · by_cases hpar : n % 2 = 1
        · -- stop at once
          obtain ⟨hcfg, hk⟩ := scan_V_odd (j := j) hpar he
          refine Or.inl ⟨t, [], (n + 1) / 2, 0, by simp, hk, by omega, by omega, ?_⟩
          rw [hcfg]
          simpa using BRun.refl _
        · have hpar' : n % 2 = 0 := by omega
          obtain ⟨hr1, he1⟩ := scan_V_even (b4 := b4_0LB) (j := j) hpar' he
          rcases ih hpt pre (n / 2) (j + 1) hpre he1 with
              ⟨η, t2, k', T, rfl, hk', h1, h0, hr⟩ | ⟨n', T, hn', hbd, hr⟩
          · refine Or.inl ⟨η, t2 ++ [RB.V], k', 6 + T, by simp, hk', ?_, ?_, ?_⟩
            · intro _; simp
            · intro hn0
              have := h0 (by omega)
              simp; omega
            · have := hr1.trans hr
              simpa [Nat.add_assoc, Nat.add_comm 1] using this
          · refine Or.inr ⟨n', 6 + T, hn', ?_, ?_⟩
            · rw [List.length_append, List.length_singleton, pow_succ]
              have h2 : 2 ^ t.length * (n / 2 + 6) ≤ 2 ^ t.length * 2 * (n + 6) := by
                rw [Nat.mul_assoc]
                exact Nat.mul_le_mul_left _ (by omega)
              omega
            · have := hr1.trans hr
              simpa [Nat.add_assoc, Nat.add_comm 1] using this

end BB25.Prefix
