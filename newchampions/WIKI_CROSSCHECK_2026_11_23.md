# Wiki cross-check, 2026-11-23

Source: live wikitext of <https://wiki.bbchallenge.org/wiki/Champions>
(`?action=raw`, fetched 2026-11-23). Bounds are compared as ordinal families:
`epsilon1 > epsilon0 > omega^omega+k > omega^2+k > omega*2+k > omega+k > fixed number`.
A higher family dominates any fixed argument and any finite iterate of a lower
one, so a family jump is a proof of a strictly larger runtime.

## Result

Of the 123 landmark machines in `landmarks_2026_11_23.json`:

| verdict | count |
|---|---|
| strictly beats the wiki's stated bound | 8 |
| wiki cell is blank | 1 |
| same family as wiki bound, argument not comparable | 20 |
| weaker than the wiki's stated bound | 42 |
| cell hidden behind `...` on the wiki | 52 |

**This supersedes the 38-machine claim in `champions_2026_11_23.json`.** Most of
those were landings on cells that already hold a stronger machine; the wiki bound
for the cell is what decides, and it does so only for the rows below.

## Machines that beat the current champion

| cell | core | steps | wiki bound | why |
|---|---|---|---|---|
| BB(3,4) | `fw_4` | 241 | 2^^15 5 | (1, 0) > wiki (0, 0) |
| BB(7,3) | `fw1_3` | 752 | *blank* | cell empty on wiki |
| BB(8,3) | `fw2_3` | 77 | f_{omega+1}^4(f_omega^3(14)) | (1, 2) > wiki (1, 1) |
| BB(5,5) | `fw2_5` | 50 | f_{omega+1}(f_omega^4(6)) | (1, 2) > wiki (1, 1) |
| BB(6,5) | `fwm2_5` | 131 | f_{omega+3}(11) | (2, 0) > wiki (1, 3) |
| BB(8,4) | `fwm2_3` | 90 | f_{omega+8}^2(4) | (2, 0) > wiki (1, 8) |
| BB(7,5) | `fwm2fw_5` | 20 | f_{omega+3}^2(10) | (2, 0) > wiki (1, 3) |
| BB(10,4) | `fwp21_4` | 31 | f_{omega^2}^3(3) | (3, 1) > wiki (3, 0) |
| BB(11,4) | `fwp22_4` | 13 | f_{omega^2+1}(f_{omega^2}(f_{omega+3}^2(4))) | (3, 2) > wiki (3, 1) |

The two `f_omega^2` entries are offset-only wins (`f_{omega^2+1}` vs `f_{omega^2}`
and `f_{omega^2+2}` vs `f_{omega^2+1}`), so they hold only if the hydra argument
in the certificate exceeds the wiki's iteration count: treat them as probable.

## Everything else

The remaining machines are still kernel-checked halting proofs at their landmarks
(see `Landmarks2026_11_23_S*.lean`) but do not beat the record listed for their
cell, and are not claimed as champions.
