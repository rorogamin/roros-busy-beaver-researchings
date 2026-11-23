# Wiki cross-check, 2026-11-23

Source: live wikitext of <https://wiki.bbchallenge.org/wiki/Champions>
(`?action=raw`, fetched 2026-11-23), evaluated against the fundamental sequences
used by `lean/BB/FGH.lean`:

    f_0(n) = n+1,  f_(a+1)(n) = f_a^n(n),  f_w(n) = f_n(n),
    f_(w*(a+1))(n) = f_(w*a+n)(n),  f_(w^2*(c+1))(n) = f_(w^2*c+w*n)(n)

**Bounds must be expanded at their own argument.** Comparing ordinal families
alone is wrong in both directions:

* one extra diagonalization beats an arbitrarily high iteration of the level
  below — `f_(a+1)(n) = f_a^n(n)` re-iterates at the *value*, so `f_(w+1)^2(3)`
  already dwarfs `f_w^4(6)`;
* but a *limit* family evaluated at a small argument only reaches the n-th
  member of its fundamental sequence — `f_(w*2)(1) = f_(w+1)(1) = 2` and
  `f_(w*2)(2) = f_(w+2)(2) = f_(w+1)^2(2)`.

## Verdicts

| cell | core | bound | expansion | wiki | verdict |
|---|---|---|---|---|---|
| BB(3,4) | `fw_4` | `f_{ω}(3)` | f_w(3)=f_3(3)~2^^32 | 2^^15 5 | **LOSE** |
| BB(7,3) | `fw1_3` | `f_{ω+1}(3)` | f_{w+1}(3) | *blank* | **WIN** |
| BB(8,3) | `fw2_3` | `f_{ω+2}(4)` | f_{w+2}(4)=f_{w+1}^4(4) | f_{omega+1}^4(f_omega^3(14)) | **LOSE** |
| BB(5,5) | `fw2_5` | `f_{ω+2}(3)` | f_{w+2}(3)=f_{w+1}(f_{w+1}^2(3)) | f_{omega+1}(f_omega^4(6)) | **WIN** |
| BB(6,5) | `fwm2_5` | `f_{ω×2}(2)` | f_{w*2}(2)=f_{w+2}(2)=f_{w+1}^2(2) | f_{omega+3}(11) | **LOSE** |
| BB(8,4) | `fwm2_3` | `f_{ω×2}(1)` | f_{w*2}(1)=f_{w+1}(1)=2 | f_{omega+8}^2(4) | **LOSE** |
| BB(7,5) | `fwm2fw_5` | `f_{ω×2}(1)` | f_{w*2}(1)=2 | f_{omega+3}^2(10) | **LOSE** |
| BB(10,4) | `fwp21_4` | `f_{ω^2+1}(3)` | f_{w^2+1}(3)=f_{w^2}^3(3) | f_{omega^2}^3(3) | **TIE** |
| BB(11,4) | `fwp22_4` | `f_{ω^2+2}(1)` | f_{w^2+2}(1)=f_{w^2+1}(1)=f_{w^2}(1)=f_w(1)=2 | f_{omega^2+1}(f_{omega^2}(f_{omega+3}^2(4))) | **LOSE** |

## Result

Two of the 123 landmark machines beat the record listed for their cell:

* **BB(7,3)** — `fw1_3` reaches `f_(w+1)(3)`; the wiki lists no champion there.
* **BB(5,5)** — `fw2_5` reaches `f_(w+2)(3) = f_(w+1)^3(3)`, and the middle
  iterate `f_(w+1)^2(3) = f_w^(f_w^3(3))(f_w^3(3))` already exceeds the wiki's
  `f_(w+1)(f_w^4(6))`.

`fwp21_4` at BB(10,4) ties the listed `f_(w^2)^3(3)` and is not a new record.
The other six are strictly below the record for their cell.

**This supersedes both `champions_2026_11_23.json` (38 machines) and the earlier
family-rank pass in this file (9 machines).** The single-argument comparison is
the load-bearing correction: a higher ordinal name does not imply a higher value
at a fixed small argument.

## Cells above w^2

The batch does contain 16 machines above w^2 — `fwpw_*` at 12x5, 9x9, 14x8, 15x6,
15x8, 16x8, 16x9, 18x6 (w^w), `fe0_5_16` at 16x6 (e0) and `fe1_6/7/8` at
19x8..23x6 (e1). None is among the winners, for three reasons:

1. **The Lean hierarchy stops at w^2.** `FGH.lean` provides only
   `fOmega2 c a b`; there is no `f_(w^w)` or `f_e0` constructor, so this pipeline
   cannot even *state* a bound above w^2. The e0/e1 proofs live in Rocq
   (`Fe1.v`, `Fe0_5_16.v`) from the 2026-11-21 corpus, and every e/w^w machine in
   this batch is `pre_existing: true` — a re-verification, not a discovery.
2. **The e cores do not bootstrap.** The 2e9-step rerun explored `fe1_8` 10607
   nodes, `fe1_7` 2751, `fe1_6` 519, `fe0_5_16` 4786, all ending `abort=1`.
   No new e machine was found.
3. **Their cells are elided on the wiki** (`...` rows), so the record for
   BB(16,6), BB(19..23,6), BB(20,7), BB(21,7), BB(19,8) is unknown here.

To make a w^w or e0 claim, `FGH.lean` needs `fDiag` over the w^2 family followed
by the e0 collapsing sequence — that is the actual blocker, not the search.
