module

public import RequestProject.Driver
public import RequestProject.Fractal

/-!
# Non-halting of `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`

Assembly of the finite-rectangle argument:

* `all_ranks` (in `Fractal.lean`) gives, for every bound, a triangle rectangle
  `Z_w (a D^(M-1) c a^(w+1)) P` with `w` and `M` above the bound;
* `rect_sound` (in `Oracle.lean`) says that such a rectangle is executed by the oracle
  machine whose oracle is the (unrealised) left boundary word `P`;
* the three driver rules (in `Driver.lean`) show that the blank right half of the tape feeds
  the window exactly the letters `a (cab)^(M-1)`;
* before the head first reaches cell `-w`, the oracle machine and the real machine coincide,
  and the head cannot reach cell `-w` in fewer than `w` steps.
-/

@[expose] public section

namespace BB25
namespace LR

open Letter

theorem step_pos_ge (c : Cfg) : c.pos - 1 ≤ (step c).pos := by
  obtain ⟨st, p, τ⟩ := c
  unfold step
  split <;> simp <;> omega

theorem run_pos_ge (i : Nat) : -(i : Int) ≤ (run i).pos := by
  induction i with
  | zero => simp [run, init]
  | succ i ih =>
    show -((i + 1 : Nat) : Int) ≤ (step (run i)).pos
    have := step_pos_ge (run i)
    push_cast
    omega

theorem Holds_const (v : Sym) (p : Int) (n : Nat) : Holds (fun _ => v) p (List.replicate n v) := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih => exact ⟨rfl, ih _⟩

/-- A visit to the window `[1 - w, 0]`. -/
theorem win_visit {w : Nat} {S T : List Sym} (hl : S.length = w) {r : Letter} {L : List Letter}
    (hR : Rect S [r] L T) (τ : Int → Sym) (O : List Letter) (hH : Holds τ 0 S) :
    ∃ k, (ostep (1 - w))^[k] (⟨r.ent, 0, τ⟩, L ++ O) = (⟨r.ext, 1, wl τ 0 T⟩, O) := by
  have h := rect_sound (1 - w) w S r L T hl hR τ O
  rw [hl, show (1 - (w : Int)) + w - 1 = 0 by omega, show (1 - (w : Int)) + w = 1 by omega] at h
  exact h hH

/-- The driver invariant: after the window has processed `a D^j`, the machine is back on
cell `0` in state `A`, the right half carries `(042)^j`, and the remaining rectangle is
available. -/
theorem driver_inv {w M : Nat} {P : List Letter} (hw : 1 ≤ w)
    (hT : Rect (List.replicate w 0) (a :: (pw D (M - 1) ++ [c] ++ A (w + 1))) P
      (List.replicate w 1)) :
    ∀ j, j ≤ M - 1 → ∃ t, j ≤ t ∧ ∃ (S' : List Sym) (L2 : List Letter) (τ : Int → Sym),
      S'.length = w ∧ Rect S' (pw D (M - 1 - j) ++ [c] ++ A (w + 1)) L2 (List.replicate w 1) ∧
      (ostep (1 - w))^[t] (init, P) = (⟨St.A, 0, τ⟩, L2) ∧ Holds τ 0 S' ∧ RightIs τ 1 (U j)
  | 0, _ => by
    have hT' : Rect (List.replicate w 0) ([a] ++ (pw D (M - 1) ++ [c] ++ A (w + 1))) P
        (List.replicate w 1) := hT
    obtain ⟨L1, L2, S0, rfl, h1, h2⟩ := hT'.split
    obtain ⟨k, hk⟩ := win_visit (w := w) (by simp) h1 (fun _ => 0) L2 (Holds_const 0 0 w)
    simp only [Letter.ent, Letter.ext] at hk
    have hS0 : S0.length = w := by rw [Rect.length_eq h1]; simp
    refine ⟨k + 1, by omega, S0, L2, wr (wl (fun _ => 0) 0 S0) 1 0, hS0, by simpa using h2, ?_,
      ?_, ?_⟩
    · rw [iter_succ', show init = ⟨St.A, 0, fun _ => 0⟩ from rfl, hk,
        ostep_of_ne (by dsimp only; omega)]
      simp only
      rw [step_left (s := 0) rfl (by rw [wl_gt _ (by omega)])]
      rfl
    · exact Holds_congr (Holds_wl _ _ _) (fun i _ hi => wr_of_ne _ _ _ (by omega))
    · intro i
      simp only [U, List.getD_nil]
      by_cases hi : (1 : Int) + i = 1
      · rw [hi, wr_self]
      · rw [wr_of_ne _ _ _ hi, wl_gt _ (by omega)]
  | j + 1, hj => by
    obtain ⟨t, hjt, S', L2, τ, hS', hR, ht, hH, hRt⟩ := driver_inv hw hT j (by omega)
    have e : pw D (M - 1 - j) ++ [c] ++ A (w + 1) =
        [c] ++ ([a] ++ ([b] ++ (pw D (M - 1 - (j + 1)) ++ [c] ++ A (w + 1)))) := by
      rw [show M - 1 - j = M - 1 - (j + 1) + 1 by omega, pw_succ]; simp [D]
    rw [e] at hR
    obtain ⟨Lc, L3, S1, rfl, hc, hR⟩ := hR.split
    obtain ⟨La, L4, S2, rfl, ha, hR⟩ := hR.split
    obtain ⟨Lb, L5, S3, rfl, hb, hR⟩ := hR.split
    have hS1 : S1.length = w := (Rect.length_eq hc).trans hS'
    have hS2 : S2.length = w := (Rect.length_eq ha).trans hS1
    have hS3 : S3.length = w := (Rect.length_eq hb).trans hS2
    -- letter `c`
    obtain ⟨k1, hk1⟩ := win_visit hS' hc τ (La ++ Lb ++ L5) hH
    obtain ⟨k2, τa, hk2, hRa, hina, hk2p⟩ := rule1 (1 - w) j 1 (wl τ 0 S1) (La ++ Lb ++ L5)
      (by omega) (RightIs_congr hRt (fun i hi => wl_gt _ (by omega)))
    have hHa : Holds τa 0 S1 :=
      Holds_congr (Holds_wl _ _ _) (fun i _ hi => hina i (by omega))
    -- letter `a`
    obtain ⟨k3, hk3⟩ := win_visit hS1 ha τa (Lb ++ L5) hHa
    obtain ⟨k4, τb, hk4, hRb, hinb, hk4p⟩ := rule2 (1 - w) j 1 (wl τa 0 S2) (Lb ++ L5)
      (by omega) (RightIs_congr hRa (fun i hi => wl_gt _ (by omega)))
    have hHb : Holds τb 0 S2 :=
      Holds_congr (Holds_wl _ _ _) (fun i _ hi => hinb i (by omega))
    -- letter `b`
    obtain ⟨k5, hk5⟩ := win_visit hS2 hb τb L5 hHb
    obtain ⟨k6, τc, hk6, hRc, hinc, hk6p⟩ := rule3 (1 - w) j 1 (wl τb 0 S3) L5
      (by omega) (RightIs_congr hRb (fun i hi => wl_gt _ (by omega)))
    have hHc : Holds τc 0 S3 :=
      Holds_congr (Holds_wl _ _ _) (fun i _ hi => hinc i (by omega))
    refine ⟨k6 + k5 + k4 + k3 + k2 + k1 + t, by omega, S3, L5, τc, hS3, hR, ?_, hHc, hRc⟩
    simp only [iter_add]
    simp only [Letter.ent, Letter.ext] at hk1 hk3 hk5
    rw [ht, show Lc ++ (La ++ (Lb ++ L5)) = Lc ++ (La ++ Lb ++ L5) by simp, hk1]
    rw [hk2, show (1 : Int) - 1 = 0 by omega, List.append_assoc, hk3, hk4,
      show (1 : Int) - 1 = 0 by omega, hk5, hk6, show (1 : Int) - 1 = 0 by omega]

end LR

open LR

/-- **The machine `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`, started on the blank tape, never
halts.** -/
theorem never_halts : ∀ n : Nat, ¬ Halted (run n) := by
  intro h hH
  obtain ⟨d, w, M, P, hM, hd, hw, hhw, hhM, hG⟩ := all_ranks h
  have hT := hG.2 0 0 0
  simp only [Z, Nat.add_zero, Nat.mul_zero, theta, if_true, List.append_nil, pw_zero] at hT
  obtain ⟨t, hjt, S', L2, τ, -, -, ht, -, -⟩ := driver_inv (by omega) hT (M - 1) (Nat.le_refl _)
  -- before time `h`, the oracle machine is the real machine
  have agree : ∀ i, i ≤ h → (ostep (1 - w))^[i] (init, P) = (run i, P) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [iter_succ', ih (by omega)]
      have hpos := run_pos_ge i
      rw [ostep_of_ne (by dsimp only; omega)]
      rfl
  have hHt := ostep_iterate_H (lo := 1 - w) (x := (run h, P)) hH (t - h)
  rw [← agree h (Nat.le_refl _), ← iter_add, show t - h + h = t by omega, ht] at hHt
  exact St.noConfusion hHt

end BB25
