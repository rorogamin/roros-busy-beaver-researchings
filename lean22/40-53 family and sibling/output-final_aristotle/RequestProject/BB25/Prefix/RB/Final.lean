/-
# `0RB` from the blank tape

The blank tape reaches the seed checkpoint of the family after `156` base steps
(`seed_run`), and the seed is a `0RB` checkpoint: it is safe, its scan strips
three zero bits and stops at the first one bit, and it is strictly admissible.
So `0RB` never halts as soon as its two `01` branches return
(`not_halts_0RB_of`).
-/
import RequestProject.BB25.Prefix.RB.Even

namespace BB25.Prefix

open BB25

/-- **The `01` branch before the first pop returns.**  There the right word is
still a run of `22` blocks over the terminal `1$`, so this is the
member-independent branch, already settled for the whole family; the
checkpoint it reaches is a paid reset from the left end, hence strictly
admissible. -/
theorem zodd : ZOdd := by
  intro c r hst hadm hg _ hr
  rcases zready (b4 := b4_0RB) c r hst hadm hg hr with ⟨s, k, hs, hrun⟩ | hnh
  · exact Or.inl ⟨s, k, hs.toCP0, hrun.sound⟩
  · exact Or.inr hnh

/-- The seed checkpoint is a `0RB` checkpoint. -/
theorem cp0_seed : CP0 seedStack :=
  ⟨safeCP_seed, readyCP_seed.ready, strict_seedStack⟩

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB0RB` never halts**, granted the `01` branch
met after the first pop. -/
theorem not_halts_0RB_of (hZe : ZEven) : ¬ Halts (M b4_0RB) init := by
  rintro ⟨n, hn⟩
  have hlt : 156 < n := by
    by_contra hc
    exact not_halts_within (seed_run (b4 := b4_0RB)) n (by omega) hn
  have h2 : steps (M b4_0RB) (156 + (n - 156)) init = none := by
    rw [show 156 + (n - 156) = n by omega]
    exact hn
  rw [steps_add, seed_run] at h2
  simp only [Option.bind_some] at h2
  exact not_halts_of_CP0 zodd hZe (n - 156) seedStack cp0_seed h2

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB0RB` never halts.** -/
theorem not_halts_0RB : ¬ Halts (M b4_0RB) init := not_halts_0RB_of zeven

end BB25.Prefix
