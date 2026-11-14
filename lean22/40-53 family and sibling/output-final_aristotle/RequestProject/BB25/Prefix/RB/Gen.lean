/-
# The right words of the `0RB` sweep

While the `<B1` sweep of `0RB` works its way down the counter stack, the word
in front of the head grows.  It starts as a run of `22` blocks over the
terminal `1$`; the first pop turns it into one of the words

```
  w0 2 = Y X Y Y V                    (r = 2)
  w0 3 = Y Y V Y Y V                  (r = 3)
  w0 r = Y (kword (r-2))              (r ≥ 4)
       = Y^(r-1) V Y Y V X V^(r-3)
```

over the *bare* right end, where `r` is the number of `22` blocks the sweep had
built.  Afterwards every stripped zero bit prepends one `Y`, and every further
pop applies the marker transform `w ↦ Y w X^h V` of `Count.lean`, where `h` is
the Dyck height of `w`.

`Gen w h` is that language, with the height carried along.
-/
import RequestProject.BB25.Prefix.RB.Base

namespace BB25.Prefix

open BB25

/-! ## The base words -/

/-- The Dyck height of the base word `w0 r`. -/
def h0 (r : ℕ) : ℕ := if r = 3 then 2 else 1

/-- The word the first pop of the sweep leaves, after a run of `r` `22`
blocks. -/
def w0 : ℕ → List RB
  | 2 => [.Y, .X, .Y, .Y, .V]
  | 3 => [.Y, .Y, .V, .Y, .Y, .V]
  | r => .Y :: kword (r - 2)

theorem w0_two : w0 2 = [.Y, .X, .Y, .Y, .V] := rfl
theorem w0_three : w0 3 = [.Y, .Y, .V, .Y, .Y, .V] := rfl

theorem w0_big (k : ℕ) : w0 (k + 4) = .Y :: kword (k + 2) := by
  show w0 (k + 4) = _
  rfl

/-! ## Dyck runs of the base words -/

theorem dyckRun_Vrun : ∀ (k h : ℕ), DyckRun (h + k) (List.replicate k .V) h := by
  intro k
  induction k with
  | zero => intro h; simpa using DyckRun.nil h
  | succ k ih =>
      intro h
      rw [List.replicate_succ, show h + (k + 1) = (h + k) + 1 by omega]
      exact DyckRun.consV (ih h)

theorem dyckRun_w0 : ∀ (r : ℕ), 2 ≤ r → DyckRun 0 (w0 r) (h0 r) := by
  intro r hr
  match r, hr with
  | 2, _ =>
      rw [w0_two, h0]
      norm_num
      exact DyckRun.consY (DyckRun.consX (DyckRun.consY (DyckRun.consY
        (DyckRun.consV (DyckRun.nil 1)))))
  | 3, _ =>
      rw [w0_three, h0]
      norm_num
      exact DyckRun.consY (DyckRun.consY (DyckRun.consV (DyckRun.consY (DyckRun.consY
        (DyckRun.consV (DyckRun.nil 2))))))
  | (k + 4), _ =>
      rw [w0_big, h0, if_neg (by omega), kword]
      refine DyckRun.consY ?_
      have h1 : DyckRun 1 (List.replicate (k + 2) .Y) (1 + (k + 2)) := dyckRun_Yrun _ _
      have h2 : DyckRun (1 + (k + 2)) [RB.V, RB.Y, RB.Y, RB.V, RB.X] (k + 2) := by
        rw [show 1 + (k + 2) = (k + 2) + 1 by omega]
        refine DyckRun.consV ?_
        refine DyckRun.consY ?_
        refine DyckRun.consY ?_
        rw [show (k + 2) + 1 + 1 = ((k + 2) + 1) + 1 by omega]
        refine DyckRun.consV ?_
        refine DyckRun.consX ?_
        exact DyckRun.nil (k + 2)
      have h3 : DyckRun (k + 2) (List.replicate (k + 2 - 1) .V) 1 := by
        have := dyckRun_Vrun (k + 1) 1
        rw [show 1 + (k + 1) = k + 2 by omega] at this
        rw [show k + 2 - 1 = k + 1 by omega]
        exact this
      exact (h1.append h2).append h3

/-! ## The language -/

/-- **The right words of the `0RB` sweep**, with their Dyck height.  A pop
after a run of `r` `22` blocks starts the language at `w0 r`; a stripped zero
bit prepends a `Y`; a further pop applies the marker transform. -/
inductive Gen : List RB → ℕ → Prop
  | base {r : ℕ} (hr : 2 ≤ r) : Gen (w0 r) (h0 r)
  | pre {w : List RB} {h : ℕ} : Gen w h → Gen (.Y :: w) (h + 1)
  | mark {w : List RB} {h : ℕ} : Gen w h → Gen (.Y :: (w ++ List.replicate h .X ++ [.V])) 0

/-- Every generated word is a colored Dyck prefix of the stated height. -/
theorem Gen.dyck : ∀ {w : List RB} {h : ℕ}, Gen w h → DyckRun 0 w h := by
  intro w h hg
  induction hg with
  | base hr => exact dyckRun_w0 _ hr
  | pre _ ih => exact DyckRun.consY (by simpa using ih.shift 1)
  | @mark w h _ ih =>
      refine DyckRun.consY ?_
      have h1 : DyckRun 1 w (h + 1) := by simpa using ih.shift 1
      have h2 : DyckRun (h + 1) (List.replicate h .X) 1 := by
        simpa using (dyckRun_Xrun h).shift 1
      have h3 : DyckRun 1 [RB.V] 0 := DyckRun.consV (DyckRun.nil 0)
      exact (h1.append h2).append h3

theorem Gen.digs {w : List RB} {h : ℕ} (hg : Gen w h) : Digs w := hg.dyck.digs

end BB25.Prefix
