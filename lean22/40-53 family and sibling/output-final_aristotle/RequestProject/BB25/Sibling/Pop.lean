/-
# The pop episode of the sibling

The sibling meets a pop `03 <B1` of the `<B1` sweep with a different rule:
`03 <B1 → 043 A>`.  The new marker `Q = 043` protects the stack below it while
the head runs the *same* local computation above it as `0RB` does above its
marker `J0 = 003`; when the head comes back, `043 <A → <A 101`, and only then
the two decrements are spent, through the blocks `N1 = 101` and `N2 = 201`,
ending with `A> 201 → <B1 22`.

The local computation above the marker is taken from the `0RB` development,
run over the *empty* bottom `β = []` and transferred to the sibling over the
raw marker cells `3 4 0` followed by the stack (`BRun.sib_frame`).
-/
import RequestProject.BB25.Sibling.Transfer

namespace BB25.Sibling

open BB25 BB25.Prefix

/-! ## The pop, given the local computation above the marker -/

/-- **The sibling pop.**  If the head, started at `A>` over the empty bottom in
front of the word `t`, comes back to the bottom in state `<A` with the word
`out` in front of it, then the sibling turns `W :: c` at `<B1` in front of `t`
into `cdec (cdec c)` at `<B1` in front of `Y out` — provided the counter of `c`
supplies the two decrements. -/
theorem sib_pop {c : List LB} (hst : CStack c) (h2 : 2 ≤ cval c) {t out : List RB}
    (hft : fgc t = 0) (hfo : fgc out = 0) {tau : ℕ}
    (hm : BRun none ⟨[], .Rt, t⟩ ⟨[], .Lt, out⟩ tau) :
    ∃ k, steps machine k (⟨.W :: c, .Bt, t⟩ : BCfg).den
      = some (⟨cdec (cdec c), .Bt, .Y :: out⟩ : BCfg).den := by
  have h1 : 1 ≤ cval c := by omega
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hcvd : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  -- the two decrements, after the marker is gone
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := none) hst h1 (.N1 :: out)
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := none) hstd h1' (.N2 :: out)
  have hdec : BRun none ⟨c, .Lt, .N1 :: out⟩ ⟨cdec (cdec c), .Bt, .Y :: out⟩
      (k1 + (1 + (k2 + 9))) :=
    hr1.trans (BRun.head (show bstep none ⟨cdec c, .Rt, .N1 :: out⟩
      = some (⟨cdec c, .Lt, .N2 :: out⟩, 1) from rfl)
      (hr2.trans (BRun.of_step (show bstep none ⟨cdec (cdec c), .Rt, .N2 :: out⟩
        = some (⟨cdec (cdec c), .Bt, .Y :: out⟩, 9) from rfl))))
  have hdec' := hdec.sib (by simpa using hfo) (by simpa using hfo)
  -- the marker excursion, over the raw marker cells
  have hmk := hm.sib_frame hft hfo (by simp) ([3, 4, 0] ++ denL c)
  refine ⟨2 + (tau + (3 + (k1 + (1 + (k2 + 9))))), ?_⟩
  have e1 : steps machine 2 (⟨.W :: c, .Bt, t⟩ : BCfg).den
      = some (denB ⟨[], .Rt, t⟩ ([3, 4, 0] ++ denL c)) := rule_W_B1 (denL c) (denR t)
  have e3 : steps machine 3 (denB ⟨[], .Lt, out⟩ ([3, 4, 0] ++ denL c))
      = some (⟨c, .Lt, .N1 :: out⟩ : BCfg).den := rule_Q_A (denL c) (denR out)
  exact steps_trans e1 (steps_trans hmk (steps_trans e3 hdec'))

/-! ## The local computations above the marker -/

/-- **A later pop.**  In front of a colored Dyck word `w` of height `h` over the
bare right end the head builds the counter of `w`, drains it and comes back
with `w X^h V` (`marker_return_word`). -/
theorem sib_pop_word {c : List LB} (hst : CStack c) (h2 : 2 ≤ cval c) {h : ℕ} {w : List RB}
    (hd : DyckRun 0 w h) :
    ∃ k, steps machine k (⟨.W :: c, .Bt, w ++ [.R]⟩ : BCfg).den
      = some (⟨cdec (cdec c), .Bt, (.Y :: (w ++ List.replicate h .X ++ [.V])) ++ [.R]⟩
          : BCfg).den := by
  obtain ⟨tau, hm⟩ := marker_return_word (b4 := none) (β := []) hd
  have hfw : fgc w = 0 := fgc_digs hd.digs
  exact sib_pop hst h2 (by simp [fgc_append, hfw])
    (by simp [fgc_append, hfw, fgc_replicate]) hm

/-- **The first pop, above the marker.**  In front of a run of `j + 2` `22`
blocks and the terminal `1$` the head comes back to the marker with a word
which, preceded by `22` and after the zero-cost re-parsing of the pending
digit, is `w0 (j + 2)` over the bare right end.  This is the local part of
`first_episode`. -/
theorem first_marker (j : ℕ) :
    ∃ (out : List RB) (tau : ℕ), fgc out = 0 ∧
      BRun none ⟨[], .Rt, List.replicate (j + 2) .Y ++ [.R1]⟩ ⟨[], .Lt, out⟩ tau ∧
      ∀ c2 : List LB, (⟨c2, .Bt, .Y :: out⟩ : BCfg).den
        = (⟨c2, .Bt, w0 (j + 2) ++ [.R]⟩ : BCfg).den := by
  set β : List LB := [] with hβ
  set p : List LB := List.replicate (j + 2) .Z ++ [.L] with hp
  have hstp : CStack p := CStack_Zrun _ CStack.base
  have hcvp : cval p = 2 ^ (j + 2) - 1 := by rw [hp, cval_Zrun]; simp
  have hpow : 4 ≤ 2 ^ (j + 2) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrep : rep β p = List.replicate (j + 2) .Z ++ β := by rw [hp, rep_Zrun, rep_L]
  have hcvp1 : 1 ≤ cval p := by omega
  obtain ⟨k3, hr3⟩ := brun_cdec_rep_of (b4 := none) (β := β) hstp hcvp1 [.R2]
  have hcdecp : cdec p = .X :: (List.replicate (j + 1) .Z ++ [.L]) := by
    rw [hp, List.replicate_succ, List.cons_append, cdec_Z]
  rw [hcdecp] at hr3
  have hA := brun_Yrun (b4 := none) (j + 2) β [.R1]
  rw [← hrep] at hA
  have hrepX : rep β (.X :: (List.replicate (j + 1) .Z ++ [.L]))
      = .X :: .Z :: (List.replicate j .Z ++ β) := by
    rw [rep_X, List.replicate_succ, List.cons_append, rep_Z, rep_Zrun, rep_L]
  rw [hrepX] at hr3
  -- the run down to the marker's top block
  have hpre : BRun none ⟨β, .Rt, List.replicate (j + 2) .Y ++ [.R1]⟩
      ⟨List.replicate j .Z ++ β, .Lt, [.X, .P2, .Y, .Y, .R1]⟩
      (2 * (j + 2) + (1 + (k3 + (11 + (6 + 4))))) :=
    hA.trans (BRun.head (show bstep none ⟨rep β p, .Rt, [RB.R1]⟩
        = some (⟨rep β p, .Lt, [.R2]⟩, 1) from rfl)
      (hr3.trans (BRun.head (show bstep none ⟨.X :: .Z :: (List.replicate j .Z ++ β), .Rt,
          [RB.R2]⟩ = some (⟨.X :: .Z :: (List.replicate j .Z ++ β), .Bt, [.Y, .R1]⟩, 11)
          from rfl)
        (BRun.head (show bstep none ⟨.X :: .Z :: (List.replicate j .Z ++ β), .Bt,
            [RB.Y, .R1]⟩ = some (⟨.Z :: (List.replicate j .Z ++ β), .Bt, [.Y, .Y, .R1]⟩, 6)
            from rfl)
          (BRun.of_step (show bstep none ⟨.Z :: (List.replicate j .Z ++ β), .Bt,
            [RB.Y, .Y, .R1]⟩ = some (⟨List.replicate j .Z ++ β, .Lt, [.X, .P2, .Y, .Y, .R1]⟩, 4)
            from rfl))))))
  match j with
  | 0 =>
      exact ⟨[.X, .P2, .Y, .Y, .R1], _, rfl, by simpa using hpre, fun c2 => den_w0_two c2⟩
  | 1 =>
      have hpost : BRun none ⟨[LB.Z], .Lt, [RB.X, .P2, .Y, .Y, .R1]⟩
          ⟨[], .Lt, [RB.Y, .V, .P2, .Y, .Y, .R1]⟩ (3 + (1 + 2)) :=
        BRun.head (show bstep none ⟨[LB.Z], .Lt, [RB.X, .P2, .Y, .Y, .R1]⟩
            = some (⟨[LB.X], .Rt, [RB.X, .P2, .Y, .Y, .R1]⟩, 3) from rfl)
          (BRun.head (show bstep none ⟨[LB.X], .Rt, [RB.X, .P2, .Y, .Y, .R1]⟩
              = some (⟨[LB.X], .Lt, [RB.V, .P2, .Y, .Y, .R1]⟩, 1) from rfl)
            (BRun.of_step (show bstep none ⟨[LB.X], .Lt, [RB.V, .P2, .Y, .Y, .R1]⟩
              = some (⟨[], .Lt, [RB.Y, .V, .P2, .Y, .Y, .R1]⟩, 2) from rfl)))
      exact ⟨[.Y, .V, .P2, .Y, .Y, .R1], _, rfl, hpre.trans hpost, fun c2 => den_w0_three c2⟩
  | (k + 2) =>
      obtain ⟨k4, hr4⟩ := marker_drain_gen (b4 := none) (β := β) k
        (P := fun cfg => ∃ k', BRun none cfg ⟨β, .Lt, kword (k + 2) ++ [.R]⟩ k')
        (fun hrun ⟨k', h⟩ => ⟨_, hrun.trans h⟩) ⟨0, BRun.refl _⟩
      refine ⟨kword (k + 2) ++ [.R], _, ?_, hpre.trans hr4, fun c2 => ?_⟩
      · simp [fgc_append, fgc_digs (digs_kword (k + 2))]
      · have hw : RB.Y :: (kword (k + 2) ++ [RB.R]) = w0 (k + 4) ++ [RB.R] := by
          rw [w0_big]
          rfl
        rw [hw]

/-- **The first pop of the sibling.** -/
theorem sib_first_pop {c : List LB} (hst : CStack c) (h2 : 2 ≤ cval c) {r : ℕ} (hr : 2 ≤ r) :
    ∃ k, steps machine k (⟨.W :: c, .Bt, List.replicate r .Y ++ [.R1]⟩ : BCfg).den
      = some (⟨cdec (cdec c), .Bt, w0 r ++ [.R]⟩ : BCfg).den := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
  obtain ⟨out, tau, hfo, hm, hden⟩ := first_marker j
  obtain ⟨k, hk⟩ := sib_pop hst h2 (t := List.replicate (j + 2) .Y ++ [.R1])
    (by simp [fgc_append, fgc_replicate]) hfo hm
  exact ⟨k, by rw [hk, hden]⟩

end BB25.Sibling
