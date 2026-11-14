/-
# The member `1RA`

Its `A> 241` rule is

```
  A> 241  ⟶  11 A> 2>        (six base steps)
```

so the `241` block is replaced by a zero bit *pushed on the left stack*, and
the head keeps going right with a pending `2>`.  Goodness of the stack is
preserved by the push, so the `W` case of the `<B1` sweep ends in an ordinary
pending-`2>` tail and no exceptional configuration ever arises.
-/
import RequestProject.BB25.Prefix.Return

namespace BB25.Prefix

open BB25

/-- The `A> 241` rule of `1RA`. -/
theorem gStep_1RA (lt : List LB) (rest : List RB) :
    gStep b4_1RA lt rest = some (⟨.X :: lt, .Rt, .P2 :: rest⟩, 6) := rfl

/-- **The `W` case of the sweep for `1RA`.**  Two decrements bring the head to
the `241` block, the rule pushes a zero bit and the pending `2>` runs into the
tail. -/
theorem wcase_1RA : WCase b4_1RA := by
  intro c r hst hadm hg hv _ _ hr2
  have hr : 1 ≤ r := by omega
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval c := by omega
  have hcv : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hadmd : Adm (cdec c) := Adm.cdec hst hadm h1
  have hgd : Good (cdec c) := Good.cdec hst hg h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  have hstd2 : CStack (cdec (cdec c)) := cdec_CStack_all hstd
  have hadmd2 : Adm (cdec (cdec c)) := Adm.cdec hstd hadmd h1'
  have hgd2 : Good (cdec (cdec c)) := Good.cdec hstd hgd h1'
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4_1RA) hst h1 (.F :: tail)
  have hsF : bstep b4_1RA ⟨cdec c, .Rt, .F :: tail⟩
      = some (⟨cdec c, .Lt, .G :: tail⟩, 1) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_1RA) hstd h1' (.G :: tail)
  have hsG : bstep b4_1RA ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨.X :: cdec (cdec c), .Rt, .P2 :: tail⟩, 6) := gStep_1RA _ _
  refine Returns.of_run
    (hr1.trans (BRun.head hsF (hr2.trans (BRun.of_step hsG)))) ?_
  exact returns_tail hstd2.consX (adm_consX hadmd2)
    (tail_bound_of_good (good_consX hgd2)) (Or.inl hr)

end BB25.Prefix
