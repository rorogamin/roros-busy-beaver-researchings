import RequestProject.Carry

/-!
# Two more instances of the fractal unfolding

`Carry.lean` proves the two smallest instances of the unfolding of a compressed token,
`unfold_U4` (`a = 4`, `j = 1`) and `unfold_U10` (`a = 10`, `j = 3`).  This file adds the
next two that are still *window* rules, `a = 13` (`j = 4`) and `a = 16` (`j = 5`).

The mechanism is the one of `Fractal.lean` and `ANALYSIS.md` §24, §52: the rightward sweep
rewrites `U(a,1) = 0 4^a 2` as `1 0^a 3`, so the `4`-run becomes a run of `a` blank cells,
and the machine then performs `j = (a-1)/3` macro steps of its own computation inside that
run before the cells are used up.  For `a = 13` the run hosts four inner synchronisation
moments, whose tape words are `U(2,1)`, `U(2,2)`, `U(2,2) V(1)` and `U(2,1) U(4,1)` — the
machine's own first four tape words — and the token comes out as `u U(1,2) u`; for
`a = 16` there are five of them and it comes out as `u U(1,2) V(1) u`.

Each theorem below is a single kernel computation over its window, and each is a `Win`
rule, so it also certifies that the head never leaves the window (in particular that the
sub-computation really is confined to the `4`-run and the tokens beyond it that absorb the
carry) and that the machine does not halt during the steps it covers.
-/

namespace BB25

set_option maxRecDepth 60000 in
/-- **`U(13,1)` unfolds into `u U(1,2) u`.**  The `4`-run of length `13 = 3·4 + 1` hosts
four macro steps of the machine's own computation; `561` steps after the carry sets out,
the machine is back at the left end, three cells further left, in state `B`. -/
theorem unfold_U13 :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 13 1 ++ tokU 1 1 ++ tokU 1 1 ++
        tokU 1 2 ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 2 ++ tokU 1 1 ++ tokU 2 16 ++ [0]) 561 :=
  Win.of_lrun (by decide)

set_option maxRecDepth 60000 in
/-- **`U(16,1)` unfolds into `u U(1,2) V(1) u`.**  The `4`-run of length `16 = 3·5 + 1`
hosts five macro steps of the machine's own computation, and the extra step is exactly the
`P2` step that inserts the token `V(1)`. -/
theorem unfold_U16 :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 16 1 ++ tokU 1 1 ++ tokU 1 1 ++
        tokU 1 2 ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 16 ++
        [0]) 595 :=
  Win.of_lrun (by decide)

end BB25
