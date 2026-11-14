# BVE tape layout and rewrite-cursor budget

Date: 2026-11-11.  Status: layout, codec, cursor, predecessor, and
flag-dispatch tables, a fixed-case 5-tuple FS table, and a semantic general
FS arm; **no general 5-tuple FS table, no full rewrite table, and no FGH
claim**.

The BVE term system is in `tools/eps1_bve.py`.  This note fixes how a term is
put on a one-track, two-symbol tape and what the cursor has to do.  The codec
and suffix checks are `tools/bve_tape.py` and `tools/bve_two_bank.py`.

## 1. Why reverse postfix

The ordinary BVE postfix string is `left right op`.  The right spine — the
additive principal terms — is the path of right children, but in ordinary
postfix the last principal is buried before the root operator and before older
exponents.  Reversing each node,

    node = op right left,

makes the right spine a **contiguous prefix**.  For a normal form

    P1 + P2 + ... + Pk

the reversed field starts

    op(P1) op(P2) ... op(Pk) 0 ...

so a cursor reaches the last principal by walking token-to-token; it never
walks over an exponent subtree.

`tools/bve_tape.py` checks this for 107 terms: every term round-trips, the
scanned headers have the same labels as `v.terms`, and the last principal's
exponent begins at the predicted cell.  This is the simplest layout and is kept
as the reference.  It has one expensive defect: a coefficient deletion removes
the last principal's `op 0 exponent` block, which is followed by older
exponents, so the deletion is a middle shift.  The recommended layout fixes
that by splitting the two banks.

## 2. Token framing

Four BVE codes need four tokens, and the field delimiter must be unambiguous
using only `0` and `1`.  Use four cells per token:

    1001 = 0        1011 = 1        1101 = phi_0        1111 = phi_1

Every token starts and ends with `1`, and no token contains `000`; a
concatenation of tokens cannot create `000` either.  Therefore:

    000  = separator inside the term
    0000 = term-field boundary

No third symbol is needed.  The codec checks that `000` never appears in a
token stream.  A three-cell token (`1bb`) would need a sentinel cell to avoid
the `...0|000...` collision at the field end; the four-cell frame buys the
unambiguous separator for one extra cell per token.

## 3. Recommended: the two-bank layout

Put the right spine and the exponents in separate banks:

    H = f1 op1  f2 op2  ...  fk opk
    E = postfix(a1) 000 postfix(a2) 000 ... 000 postfix(ak)

where `Pi = phi_i(ai)` and `fi` is one cell:

    fi = 1  iff  Pi is the same ordinal as P(i-1)   (coefficient > 1)
    fi = 0  otherwise

The exponents are in the **same order** as H and use ordinary postfix
(`left right op`), so each exponent's root is its last token.  The complete
term field is

    H 000 E

and the tape is

    0000 [H 000 E] 0000 [cursor work/return stack] 0000 [index] 0000

The zero term is represented by `H = 1001` and an empty E.

Examples from the codec:

    epsilon_1 = phi_1(1)
      H = 0 1111
      E = 1011                  (postfix of 1)
      tape = 0000 01111 000 1011 0000 ...

    w + 1
      H = 0 1101  0 1101
      E = 1011 000 1001         (postfix of 1, then postfix of 0)

The second example is the reason for the duplicate flag: both headers have the
same op label `1101`, but the flags are `0`, because `w` and `1` are different
principals.  A cursor must not infer a coefficient from the label alone.

### Why this is the rewrite-friendly layout

* **H is the right spine.**  It is a contiguous bank of fixed five-cell
  headers; no exponent is interleaved.
* **The last header is a suffix.**  It is the five cells immediately before
  the H delimiter.
* **The last exponent is a suffix.**  It is the block after the last `000` in
  E; its postfix root is the final token of E.
* **Predecessor is a suffix truncation.**  If the last flag is `1`, the cursor
  zeros the last five header cells and the last exponent block (plus its
  separator).  The field end becomes a longer zero run; nothing to the left
  shifts.  `truncate_last` in `bve_two_bank.py` checks this against
  `V(v.terms[:-1])` for repeated principals.
* **FS append is also at the suffixes.**  A new `(flag, op)` header goes at
  the end of H and a copied exponent goes at the end of E.  The expensive part
  is the copy, not field finding.

The codec check is `python tools/bve_two_bank.py`: 129 terms round-trip, the
headers match, the last exponent suffix matches `postfix(last exponent)`, and
every repeated last principal passes the suffix-pop test.

## 4. Cursor path

A full rewrite cursor has six phases:

1. **H-end locate.**  Walk right through H to its `000` delimiter.  H headers
   are fixed five cells, so the last header starts five cells left of the
   delimiter.
2. **Header decode.**  Read the duplicate flag and the op label.  Only the
   first two data bits of the four-cell op token are needed to distinguish
   `phi_0` from `phi_1`.
3. **E-tail locate.**  Cross the H/E separator, walk right to the `0000` field
   end, then back to the last `000` separator (or the E start).  The suffix is
   the last exponent.
4. **Predecessor / FS dispatch.**  If the flag is `1`, truncate the two
   suffixes.  If it is `0`, dispatch on `phi_0` versus `phi_1` and enter the
   exponent.
5. **Exponent rewrite / append.**  For the `phi_0` successor case the new
   exponent is `n+1` unary marks; for `phi_1` it is a tower over the previous
   epsilon, and for a limit exponent the cursor recurses.  The exponent suffix
   is the natural copy source.
6. **Return stack.**  Only recursion into an exponent needs a return context.
   The right-spine walk itself never pushes.  The work field holds the stack;
   the index field holds the Hardy index and is incremented on predecessor
   moves.

## 5. State budget

This is a **paper estimate** from the phase structure, using the repository's
measured primitives where they apply.  It is not a state table and has not been
minimised.

| phase | states | note |
|---|---:|---|
| H-end scan + last-header backstep | 4 | fixed five-cell headers; no counting |
| header flag/op decode | 3 | one flag cell + two op bits |
| E-end scan + last-suffix backstep | 4 | suffix of E; no exponent walk |
| predecessor truncation | 4 | zero header suffix + exponent suffix |
| phi_0/phi_1 FS dispatch | 3 | two labels plus halt/limit arm |
| **locate/dispatch cursor** | **18** | the part that finds and classifies the active site |
| exponent copy/append | 11 | reuses the 9-state copy plus 2 boundary states |
| recursive return stack | 5 | push/pop only on exponent recursion |
| index read / n+1 | 4 | index home outside the term banks |
| boot / halt / glue | 2 | blank-tape entry and final handoff |
| **full rewrite cursor** | **40** | locate 18 + copy 11 + stack 5 + index 4 + glue 2 |

Honest band: **36-44** for the full cursor before minimisation.  The 9-state
copy is the measured copy primitive in `FGH_HANDBOOK.md` §10.2; the 5-state
walk is the scale used by the chain design in `FGH_MACHINES_PLAN.md`; the
header/suffix scans are shorter than the chain walk because every header is a
fixed five cells.  The 11-state exponent copy is estimated, not built.

This supersedes the earlier ~27-state whole-machine estimate as a *cursor*
budget: 27 was an optimistic total for the full BVE rewriter, and the two-bank
design spends 18 states before any exponent copy.  A full engine that also
performs the FS tower construction and maintains the index will be above 40,
not at 27, unless the layout is compressed further.

## 6. What is still open

* **Flag maintenance.**  The boot/normaliser must set `fi` correctly; FS
  append must set the new flag from the new principal and the previous header.
* **Suffix zeroing.**  The predecessor arm and its composition with the
  cursor are built (§8-9); delimiter handling is checked on 205 flag-1 terms,
  but a full FS rewrite still has to preserve it.
* **Exponent copy.**  The 9-state copy is for a run; copying a postfix
  exponent suffix with its separators is the 11-state estimate.
* **Return context.**  A stack of positions in the work field has not been
  designed at cell level.
* **Index home and closure.**  The index must be available at both the top
  (FS append) and the bottom (epsilon atom expansion); the travelling-index
  options in `FGH_MACHINES_PLAN.md` still apply.
* **Full FS semantics.**  The BVE prototype (`tools/eps1_bve.py`) is the
  semantic oracle; the tape cursor must match its `model_step` before any
  claim.  No full rewrite table, state count, or Rocq proof exists yet.

## 7. The composed cursor (built)

`tools/bve_cursor.py` contains two tables.  The **18-state active-site core**
starts at the duplicate-flag cell of the **last header**.  The **23-state
composed table** prepends a five-state left-walk from the first zero of the
H/E separator to that header, then enters the core.

The core:

1. reads the duplicate flag (states 1/2) and op label (states 5/6), so the
dispatch path is observable;
2. crosses the H/E separator and scans E to its four-zero field end;
3. walks back to the last `000` exponent separator and halts on its first
   zero (the third zero counted from the right).  The last exponent starts at
   `head + 3`, which is the reported exponent offset.

The checker `python tools/bve_cursor.py` runs 207 terms (7 hand cases and 200
random depth-3 terms) through both the 18-state core and the 23-state composed
table, comparing each halt to `bve_two_bank.header_scan` and `last_exponent`.
All 207 pass in both modes, including terms with multiple headers, a
last-coefficient flag, and exponent-bank separators.  The composed table starts
at the H/E separator and halts at the last separator's first zero (third from
the right); its final head + 3 is the exponent offset.  This is a cursor test,
not an FGH or blank-tape claim.

The predecessor suffix truncation is built and composed with this cursor
(§8-9).  The full rewrite cursor still needs the exponent copy, return stack,
index field, and FS expansion; the 36-44 state band remains an estimate for
that larger rewrite cursor.

## 8. Predecessor suffix-truncation arm (built)

`tools/bve_pred.py` is a 24-state table (states 0..23).  It assumes entry at
the last header flag with flag = 1, zeros the five header cells, scans E to
the four-zero field end, walks back to the last `000` separator, and zeros
from that separator through the field end.  The zero run is the new boundary;
after `bve_two_bank.split` skips the H zero run, the remaining exponent bank
decodes as the previous term.

`python tools/bve_pred.py` checks 205 duplicate-tail terms (5 fixed terms plus
200 generated duplicates) and decodes every output to `BVE.pred(v)`.  All 205
pass.  Example: the three-mark term `1 + 1 + 1` becomes `1 + 1`.  State 23 is
the gap normaliser: after a prior predecessor, it skips the whole H/E zero run
and starts the E scan at the first 1, so the raw output can be fed to another
predecessor without moving cells.

The arm is composed with the 23-state cursor in §9.  It is still not a full
predecessor rule for flag = 0 terms (those are successor/limit FS cases).

## 9. Cursor + predecessor composition (built)

`tools/bve_compose.py` is a 46-state table (states 0..45).  It starts at the
first zero of the H/E separator.  The first five states are the cursor's
H-end prefix; at the last header, the cursor's core flag branch is rerouted:

* **flag 0:** run the ordinary cursor core and halt unchanged on the last
exponent separator in the raw 46-state table.  The semantic FS arm in §10
expands this case when driven through `bve_fs.composed_step`.
* **flag 1:** write 0 over the flag, move to the first op cell, and enter the
predecessor arm at its second state (states 23..44).  The predecessor zeroes
the remaining four op cells and truncates the last exponent suffix.

One predecessor state is shared: the cursor's flag read performs the arm's
state 0 by zeroing the flag in the flag-1 route.  The remaining 22 arm states
are shifted by 22.

`python tools/bve_compose.py` checks 205 duplicate-tail terms against
`BVE.pred(v)` and 204 non-duplicate-tail terms for an unchanged tape.  All
409 pass.  The flag-0 route halts in the cursor core (state 22) with the tape
unchanged; the flag-1 route decodes to the previous term.

This is a routing/composition result, not a full rewrite: the raw table's
flag-0 route halts, and no blank-tape, FGH, or Rocq claim is made.

The predecessor output is directly re-usable as raw tape.  Suffix truncation
leaves a long zero run where the removed header/exponent block was; the
predecessor's state 23 skips that whole H/E run and starts the E scan at the
first 1.  `tools/bve_compose.py` checks this with a raw predecessor chain:
24 terms (4 fixed triple-coefficient terms plus 20 random ones) are run through
one predecessor, then the raw output is fed into a second predecessor without
re-encoding, and both results decode to `BVE.pred`.  All 24 pass.

## 10. Flag-0 FS arms (fixed-case table + semantic general)

`tools/bve_fs_simple.py` is the first real 5-tuple FS arm.  It implements the
fixed simplest case `omega[1] = 2`: 41 states and 40 rows.  It validates the
28-cell input tape and writes the 40-cell output tape (two `phi_0(0)`
headers and two zero exponents).  `python tools/bve_fs_simple.py` passes the
input/output constants, the table run, and the decoded model result.  The
composed driver uses this table when the term is exactly `omega` and `n = 1`.

`tools/bve_fs.py` implements the general flag-0 FS arm at the tape level.  `fs_tape`
decodes the two-bank term, applies `eps1_bve.model_fs`, and re-encodes the
result.  `composed_step` is a small driver that routes:

* flag-0 limit terms to the semantic FS arm;
* duplicate-flag terms through the 46-state composed predecessor table;
* flag-0 successors to a temporary semantic predecessor;
* zero to halt.

`python tools/bve_fs.py` checks 200 limit terms against `B.model_fs`, 200
composed steps against `B.model_step`, and a bounded full descent against
`B.hardy`; all pass.  The measured route split is 347 FS, 53 predecessor, and
0 halt.  The predecessor route now returns its raw tape, not a re-encoded
canonical string; the gap normaliser makes the next predecessor pass valid.  The descent corpus is 13 fixed cases (`0`, `1`, `omega`, `omega+1`,
`omega^omega`, `epsilon_0`, `epsilon_1`, and a deliberate cap case) plus 30
shallow random depth-1 terms at `n = 0`; all 43 match the oracle at cap 40.
Deep epsilon towers are intentionally excluded from that bounded corpus: the
term oracle handles them, while re-encoding every tower as tape cells is much
slower and tests the codec's size limit rather than the transition policy.
Examples: `omega^omega [1]` maps to `omega^(1+1)`, `epsilon_0 [1]` maps to
`omega^omega`, and `epsilon_1 [1]` maps to `omega^(epsilon_0+1)`.

The general FS arm is **not** a 5-tuple transition table.  It does not copy an
exponent, build a tower on the tape, or carry an index field; it is the
semantic target that a later general FS table must match.  The fixed
`omega[1]` case does have the real table above.  The raw `bve_compose` table
still halts on flag 0, while the composed driver expands it.

## 11. The 38-state quotient (11 November 2026)

This is the under-50 table the BVE layout actually supports today.  It is a
**new construction** relative to the 71-state odometer: the postfix Veblen
term is self-delimiting, the active site is found by fixed five-cell headers,
and the predecessor is a suffix truncation rather than a walk-back family.

Measured with `python tools/bve_minimise.py`, `python tools/bve_compose44.py`,
`python tools/bve_contextmin.py`, and `python tools/bve_searchmin*.py`:

| item | count |
|---|---:|
| `bve_compose.py` raw states | 46 |
| reachable from entry 0 | 45 |
| Moore quotient classes | 44 |
| greedy observed-context quotient | 40 |
| backtracking quotient | 39 |
| **final quotient** | **38** |
| 38-state rows | 72 |
| `bve_compose38` flag-1 predecessor checks | 205 / 205 |
| `bve_compose38` flag-0 unchanged checks | 204 / 204 |
| raw predecessor chain (two passes) | 24 / 24 |
| held-out tapes equal to the 44-state reference | 719 / 719 |

The greedy pass (`bve_contextmin.py`, 360 valid term tapes) found 44 -> 40.
The backtracking searches widened the corpus to 570 tapes and screened every
candidate against the reference outputs before the full 409-term check.  The
39-state path was `(38,41) (37,39) (36,37) (27,40) (26,39)`; the 38-state
step was `(25,38)` (state names are pre-quotient at each step, so they are not
the final labels).  `bve_searchmin_any.py bve_compose38 38` found no further
merge on the same corpus and beam.  The 38-state table is
`tools/bve_compose38.py`; its checks exit 0.

The held-out check is distinct from the search corpus: 719 fresh deep terms
plus raw predecessor outputs, compared cell-for-cell with the 44-state
reference.  All 719 agree.  The 44-state plain Moore quotient remains a useful
intermediate; its only class was `{10, 11}`.

**Scope, stated plainly:** this is the cursor + predecessor table.  It is not
a full epsilon_1 machine: there is no blank-tape boot, no index field, and the
general flag-0 FS arm is still semantic (`bve_fs.py`), not a 5-tuple table.
`tools/bve_fs40.py` binds the general semantic arm to the 40-state
predecessor route and reruns 200 limit terms, 200 composed steps, and the
43-term bounded descent; all pass.  The separate fixed-case `omega[1] = 2` FS
table is 41 states.  No epsilon_1/FGH/Rocq claim follows from the 38-state
count, and the shrunken table is a predecessor/cursor quotient rather than a
new FS arm.
