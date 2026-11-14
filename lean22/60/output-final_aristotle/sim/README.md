# Simulation scripts

These are *exploratory* scripts.  They are not part of the Lean development and nothing
they output is machine-checked; they were used to find the macro rules that are proved in
`RequestProject/`.

* `sim.py` — a plain simulator of `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`.
* `img.py` — writes a PNG from a list of tape rows.  `st.png` is the space-time diagram of
  the first 4000 steps; `ev.png` has one row per *left-end event* (the head reaching a new
  leftmost cell in state `A`), which makes the self-similar structure visible.
* `cover2.py` — the *coverage* experiment: it simulates the machine and, at every step,
  tries to apply one of the general macro rules that are proved in the Lean development
  (`blockR`, `sweepL_103`, `sweepL_310`, `sweepR_204`, `sweepR_420`, `sweepL_031`,
  `blockL_13`, `blockL_1003`, `turn_wall`, `run_ones_A`, `run_ones_B`, `run_fours`,
  `wall_step`, `left_blank_extend`); when no rule matches it takes a single step and
  records the local context.  Over 3 000 000 steps the rules cover 98.3 % of the steps and
  the set of local contexts where no rule matches stays constant at 75 (it is already
  complete after 50 000 steps).
* `cross.py` — the crossing sequences `X_i` of §11 of `ANALYSIS.md`: their transient
  prefixes and the universal periodic tail `(AAABBB)^ω`.
* `ctl.py` — a saturation search for an invariant given by *local* constraints (allowed
  tape words of length `w` plus allowed `(state, window)` pairs of width `2k+1`).  For all
  sound parameter pairs (`2k+1 ≥ 2w-1`, `w ≤ 6`) the saturation reaches a halting
  configuration, i.e. no such purely local invariant exists.
* `toklib.py` — token parsing and printing (`U(a,b) = 0 4^a 2^b`, `V(c) = 4 3 2^c`);
  importable, no side effects.
* `be.py`, `be2.py`, `be3.py` — the sequence of `B`-events: the token word at each one,
  the transition between consecutive ones, and how far right the head travels in between
  (which shows which transitions are local).
* `probe.py` — the carry table of §19 of `ANALYSIS.md`: it runs the machine on an
  artificial tape `0 0 0 · <prefix> <test tokens> u^N` and reports what a carry of four
  `2`s does to the test tokens.
* `winchk.py` — a list-level simulator that refuses to let the head leave the window; this
  is the Python twin of `lrun` in `RequestProject/Local.lean` and is what was used to
  check every candidate `Win` rule before proving it.
* `wintrace.py`, `pieces.py` — the step-by-step trace of a candidate rule and the fixed
  pieces of its phase decomposition.
* `fractal.py` — checks the fractal identity of §20: the unfolding of a token
  `U(3j+1,1)` reproduced from the tape at the `j`-th `B`-event, for `j = 0, …, 25`.
* `self2.py` — the evidence for §24 of `ANALYSIS.md`: it runs the machine against an
  isolated token `U(a,1)` and prints the tape at every moment at which the head reaches a
  new leftmost cell *inside* the former `4`-run, showing that these are the successive
  tape words of the machine's own computation.
* `carrytab.py` — for every `B`-event transition of phase `P1` or `P3`, the input and the
  output of the carry transducer (the tape word after the fixed prefix).  This is the data
  behind the general carry table of §25.
* `p1gen.py` — the general shape and step count of the `P1` rule with `r` intervening `u`
  tokens, which is what `rule_P1_gen` proves.
* `flat.py` — the general "flat" `P3` macro step: the prefix, a run of `u`s, a token
  `U(2,1)` and then an arbitrary sequence of blocks `U(k,1)` with `k ∈ {1,2}`.  It checks
  the closed form (output word and step count) that `rule_P3_flat` proves, for every block
  sequence of length ≤ 3 and small `r`, `m`.
* `probe2.py` — the macro step with a general absorbing token `U(a,b)` and a general
  follower (`u` or `V(c)`), in both phases `P1` and `P3`.  This is where the two rows of
  §32 of `ANALYSIS.md` come from.
* `shapes.py` — the census of §31: it classifies every `B`-event of the real orbit by the
  data a macro rule needs (phase, exponents of the crossed blocks, the absorbing token,
  the token after it) and counts the classes.
* `winck2.py` — a small window-rule checker (run a candidate rule and compare with its
  claimed output); used to validate candidate pieces before proving them.
* `u2b.py`, `vrow.py` — the stage decompositions behind `rule_P3_U2b` and `rule_P3_V`:
  each lists the macro pieces of the rule with their step counts and checks the resulting
  head positions and states against the real computation.
* `u2bv.py` — the probe showing that an isolated `U(2,b)` immediately followed by a `V`
  makes the machine halt, which is why the rules with a `V` are stated for `V(2c+5)`.
* `p1v.py`, `p1v2.py` — the `P1` macro step with a `V` after the absorbing token (the rule
  that `rule_P1_V` proves) and its stage decomposition.
* `u21b.py` — the `P3` macro step with a crossed `U(2,1)` and an absorbing `U(2,2m+4)`,
  with the stage decomposition behind `rule_P3_U21_U2b`.
* `p1fr.py`, `u2bv2.py`, `u21bv.py` — the three census rows of §36 of `ANALYSIS.md` that
  are still open: the `P1` row with `r ≥ 1` (in which the prefix of a `P3` configuration
  occurs inside the tape), the `P3` row with a `V` after an absorbing `U(2,8)`, and the row
  with both a crossed exponent `2` and a `V`.  Each script checks the closed form of its
  row over a range of parameters; none of it is machine-checked.

## Part VIII scripts

* `u21bv2.py` — the stage decomposition of `rule_P3_U21_U2b_V` (the rule of §36, third
  row): it prints the configuration at each of the twenty-six stage boundaries the Lean
  proof uses, and checks the head position and state at each of them.
* `u21v.py` — probes the `P3` configuration with a crossed `U(2,1)`, an absorbing
  `U(1,even)` and a `V(2c+5)` after it, and prints the resulting tape word and step count,
  from which `rule_P3_U21_V` was read off.
* `u21v2.py` — the stage decomposition of `rule_P3_U21_V`, with a check of the rule and of
  every stage boundary for all parameters up to `2`.

As with every script here, these are exploratory: nothing they print is machine-checked.

## Part X scripts

* `p1fr2.py`, `p1fr3.py` — the stage decomposition of `rule_P1_fractal` (the `P1` row of
  the census in which the absorbing token comes straight after the inner `U(2,2) V(1) u`).
* `p1fs.py` — the same for `rule_P1_fractal_gen`, the variant with a further run of `s+1`
  tokens `u` in between: it replays the thirty-five stages against the real machine for
  all `r, s, m ≤ 2`, checking the state and head position at every boundary, the total
  step count and the final word, and prints each stage's window.
* `p1cover.py` — checks which `B`-events of the first million steps have the shape of one
  of the two `P1` fractal rules, and prints the parameters that occur.

As with every script here, these are exploratory: nothing they print is machine-checked.

## Part XI scripts

* `u2bv.py`, `u2bv2.py` — probe the `P3` configuration with an absorbing `U(2,8)` and a
  `V(1)` after it, and give the tape word and step count of the row that became
  `rule_P3_U2b_V`.
* `u2bv3.py`, `u2bv4.py` — the stage decomposition of that row: `u2bv4.py` replays the
  thirty-three stages against the real machine for `1 ≤ t ≤ 4`, `0 ≤ m ≤ 4`, checking the
  state and head position at every stage boundary, the total step count and the final
  word, and prints the window of each stage.
* `u2bv5.py` — prints, for each of the six *fixed* stretches of that decomposition, the
  twenty-nine cell word before and after it; these are the words of the
  `Win.of_lrun (by decide)` lemmas `u2bv_fix0 … u2bv_fix5`.
* `u2bvcover.py` — checks which `B`-events of the first million steps have the shape of
  `rule_P3_U2b_V`, and prints the parameters that occur.

As with every script here, these are exploratory: nothing they print is machine-checked.

## Part XII

* `blank.py` — the carry running off the *blank* right end (`ANALYSIS.md` §53).  With no
  argument it prints the two families
  `P1, u^N -> U2,2 u U2,1 u^(N+1)` in `47 + 12N` steps and
  `P3, u^N -> U2,1 U4,1 u^(N+2)` in `59 + 12N` steps, which are the rules
  `rule_P1_blank` and `rule_P3_blank`; with `--trace N` it dumps the cell-by-cell trace of
  the `P3` case, from which the nine-stage decomposition of the Lean proof was read off.

As with every script here, these are exploratory: nothing they print is machine-checked.
* `unfold.py` — searches, for each `a`, the shortest tail `u^k · U(1,2)` that turns the
  unfolding of `U(a,1)` into a *window* rule, and prints the resulting word and step count
  (`ANALYSIS.md` §55); this is where `unfold_U13` and `unfold_U16` came from.
