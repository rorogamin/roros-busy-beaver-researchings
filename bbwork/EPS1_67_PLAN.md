# Architecture reset: the ε₁ machine must be ≤ 67 states, and the current
# encoding cannot get there

## 0. The verdict, and why it is not negotiable

The completed table (`tools/eps1_table.py`) implements the entire ε₁ descent and
passes every check against `eps1_chain` — and it uses **150 states / 207 rows
raw, 143 / 198 after Moore refinement**.  That is not a near-miss to tolerate:

  * a machine with 150 states is *inside* the range where BB(150) is astronomically
    larger than f_ε₁ of any relevant n — a 150-state machine's halting time
    simply does not evidence an ε₁-level machine for the bound we care about;
  * the whole point of the ≤ 67 cap is that 67 is the regime where the state
    count *is* the claim.  143 or even 120 states buries the level.

So the architecture, not the engineering, must change.  This file records where
the states actually go, why re-cutting this encoding is hopeless, and the
concrete replacement plan with its budget, open questions and validation path.

## 1. Where the 143 states go (measured dissection)

`HANDOFF.md`'s cost drivers (own states before double counting; sum 151):

| routine | states | what it pays for |
|---|---|---|
| fs-limit | 27 | two separate passes: the right-to-left index shift (13) plus the park-growth hole-restore shuttle (14) |
| absorb | 25 | index moved five cells left over an overlap (erase-old-then-write-new), index bump sentinel, park write, two homes |
| copy | 20 | the conveyor (new run + new index, one trip each) plus three-gap walks and the finish |
| dispatch+pred | 19 | two count walks (bit 0 and bit 1), the L=4 bottom test, pred's two-direction visit of E+1 |
| build | 14 | seven marks written with distinct states because a state cannot count |
| spend | 14 | the chain-to-park walk, park erase/test, and two flag arms home |
| head-empty | 12 | erase 3 + shift the index left three, spliced into the copy's shuttle |
| 3-run normalisation | 9 | the `[.., 1, n+1]` re-shape |
| helper folds / erase | ~12 | unit fold, absorb-three, erase-for-copy |

The pattern: **the model is tiny; the encoding is not.**  `eps1_chain.step`
is four moves.  What the tape spends is:

  1. *field-finding walks* — the park, chain and index are far apart, and a
     state cannot count cells, so every direction-significant walk is one or
     two states per kind of position (over-marks loop, over-gaps check, stop);
  2. *format preservation* — two-blank gaps, the park's fixed right end
     (`C0-3`), the decoded entry code: every write must re-establish them, and
     the code provides no spare marker (the tracker's hole-restore tricks
     already exploit everything two symbols allow);
  3. *shuttle-and-return* — every cross-field edit (copy, absorb, spend,
     fs-limit) is a round trip, each leg 2-5 states, doubled by the wrap bit's
     two exits.

Fourteen minor routines × ~10 format states ≈ the 143.  The Moore refinement
found only five mergeable classes — the rows are *genuinely different*, i.e.
the cost is structural, not sloppiness.

## 2. Why re-cutting this encoding is hopeless

Concrete re-cuts, priced optimistically:

  * fs-limit: merge the shift and the park shuttle into one per-mark trip →
    27 → ~17 (−10);
  * spend: unify the two flag arms into one walk that re-reads the park mark
    on the way → −2;
  * dispatch: share the L=1/L=2/L≥5 exits across the bit with a delayed-home
    landing → −2 at most (the bit must still reach H0/H1);
  * absorb and copy: already share as far as two symbols allow.

Total plausible floor ≈ **120**, and every further standard trick (Moore
refinement, splicing arms, hole-restore shuttles) has already been applied.
120 ≫ 67, so no amount of re-cutting this three-field, fourteen-routine
encoding reaches the cap.  The dissection above *is* the argument: the cost
lives in the encoding's data layout, not in any one routine.

## 3. What the repository already knows that this must reuse

Verified assets (all green as of 2 November 2026):

  * `tools/eps1_chain.py` — **the ε₁ rule set, machine-checked** (400 chains × 4
    moves against the ordinal model, lengths equal `hardy()`).  Any new table is
    checked against this, exactly as the 150-state table was.
  * `tools/eps1_descent.py` — the ordinal model (`fs`, `pred`, `tower`, `hardy`).
  * `tools/eps1_full.py` — the whole ε₀ descent as a 2-symbol table, 71 states,
    move-for-move against `tower_free`.  Proven machinery at ε₀.
  * `rocq/` — 16 modules, 156 theorems, no forbidden vernacular.  Of these,
    `ModuleK.v` proves the 7-state module K (append-2 copy, source consumed),
    and `Eps1Tape.v` / `Eps1Copy.v` prove the rung branch and the copy's sweep
    for the stage/rung machine (`tools/eps1_machine.py`, 61 → 57 states).

Handbook knowledge to build on (`FGH_HANDBOOK.md` §10):

  * the **9-state zero-marker copy** (§10.2): a single `0` inside `1^k` is the
    only spare marker two symbols offer; the copy primitive that uses it is 9
    states, already written out row by row in the handbook;
  * **Blueprint A** (§10.3): the growing fuel stack `[F_k 00 ... 00 F_1 00 C]`
    with borrow / refill / push ≈ 44 states — the ω^ω rung;
  * the census scaling: **BB(29) > f_{ω^ω}(3), BB(31) > f_{ω↑↑4}(3),
    BB(33) > f_{ω↑↑6}(3) — roughly two states per tetration level**;
  * the crucial honest line: crossing into the ε-family is **"a change of data
    structure (a well-founded lexicographic descent), not one more axis"**, and
    this repository's *working targets* are **ε₁ ≤ 40, ζ₀ ≤ 45 states** with
    Rocq-checked halting theorems.

`EPS1_35_STATES.md`'s lineage is the missing half of this: its stage/rung
machine (module K + drive + second feedback) reaches **57 states** and sits
one level *below* ε₁ — its note says what's missing is exactly "a descent on an
ordinal notation".  That descent now exists and is checked: it is
`eps1_chain.step`.  The fusion of the two is the build.

## 4. The replacement architecture: the ε₀+1-based stack, fused

Goal state (drawn from the loader-3229 conventions used elsewhere in this
repository — the `f_(ω↑↑k)` style): a machine whose halting step count is
`f_ε₁(n)` for the tape n > 2, at ≤ 67 states, minimised toward the census's ~40.

### Layer sketch

    drive layer: borrow / refill / push across a fuel stack        ~26
    second feedback: value -> stage counter, the rung branch       ~8
    module K (append-2 copy, source consumed, Rocq-proved)          7
    the ε₀+1 bottom: the eps0 descent as the stack's base case     glue
    ------------------------------------------------------------------

### What changes semantically, move by move

The (p, chain, n) level stays the *checked spec*; the stack is its encoding:

  * `p`    — the wrap borrow: the count that the stack machinery already
             carries as its "how many marks are left in this rung's fuel";
  * `chain` — the active descent, bottom-first; in the stack encoding this is
             *which rung the head is working on*, not a separate field;
  * `n`    — the Hardy index, which in the stage/rung lineage is the value the
             counter reads — the "second feedback" (value re-read as count).

The ε₁-specific part is only this: **the stack's bottom rung is ε₀+1, not a
number**, so when the descent reaches the bottom the machine must run the
*ε₀ machine's rounds in place* — the fusion point.  The 150-state table paid
for exactly this by carrying `[ATOM]`/`[ATOM1]` as decoded entries and
shuttling; the stack notation instead lets `ε₀+1` be the *base case of the same
borrow/push recursion* (this is the handbook's "change of data structure").

### Open design questions (to settle before any rows are written)

1. **The ε₀+1 bottom fusion.** `eps1_full` is 71 states as a standalone
   machine; inside the stack it must share the drive's states.  Candidate:
   the drive's borrow/refill rounds *are* the ε₀ rounds once the stack depth is
   1 — express the ε₀ descent itself in borrow/push form and show the two
   coincide at the model level *before* any tape work (a small `eps1_chain`
   sibling above the ε₀ model).
2. **Where the index lives.** The stage/rung machine keeps the value block
   alive right of the wall and spends a *budget* left of it; the Hardy index
   must be re-read as the count each rung, and it also n+1's on preds.  Decide
   whether the index is a fuel block of the stack (a rung's marks) or the
   counter region the drive already re-reads; the two layouts have different
   glue costs (EPS1_35_STATES.md's measured bias: budget left, value right,
   the seed untouched).
3. **The build** — blank tape → the initial stack for ε₁[3] (tower of three
   omegas over ε₀+1) in a bounded number of boot states.
4. **The state budget v1 (paper).** drive 26 + second feedback 8 + module K 7
   + boot ~4 = 45 for the machinery that sits *below* ε₁; add the ε₀+1 bottom
   fusion and the ε-list re-indexing (handbook's +13 estimate) → ~58 **if the
   fusion reuses the drive** rather than duplicating eps1_full.  That is the
   only route the cap allows, and it is within the census's ε₁ ≤ 40 ambition
   only if the drive itself can be shrunk; treat 45-65 as the honest paper band
   until simulated.

## 5. Validation path (unchanged order, new bridge)

1. **Model first**: extend the verified model side so the stack semantics is a
   provable re-notation of `(p, chain, n)` (a `chain_of`-style bijection plus
   move-for-move equality in Python, in the style of `eps1_chain`'s own checks).
   Nothing is trusted below this.
2. **Frame/decode on the new layout**, as the 150-state table did: every home
   decodes back to `(p, chain, n)` and is compared **by value** against
   `eps1_chain.step`.  400 chains × 4 moves is the standard gate.
3. **Halting counts** on small terminating starts (`(0,[NUM(1)])` 1 move, etc.).
4. **State count + Moore refinement**, recorded honestly.
5. **Rocq** afterwards, module by module, reusing `ModuleK.v` — with the global
   constraint: never write `admit`/`Admitted`/`Axiom`/`Parameter`.

## 6. Disposition of the 150-state table

Do **not** delete it.  It is the reference by which the fused machine's moves
can be debugged (its homes, its `frame`/`decode`, and its checks are
transplantable), and its 143-state floor is the measured evidence that the
three-field encoding is the wrong one.  Keep it green; build the stack machine
in a new module (`tools/eps1_stack.py` + a new spec bridge) alongside it.

## 7. Next steps, in order

1. ~~Write the model-level bridge: `(stack, head)` ↔ `(p, chain, n)` and its
   move-for-move check against `eps1_chain` (Python, before any tape work).~~
   **Done** — `tools/eps1_stack.py`, green (§8).
2. ~~Fuse the ε₀+1 bottom (open question 1) — show the ε₀ descent in
   borrow/push form and match the ε₀ machinery on the model.~~ **Done in
   its model half** — `tools/eps0_fusion.py`, green (§8); the tapes-level
   half rides on the new table's transcription.
3. ~~Measure where the stage/rung machine sits against `eps1_level`'s
   ladders.~~ **Done** — `tools/eps1_rung_pos.py`: one level below ε₁
   (§8).
4. Port module K's frame; bolt the drive's borrow/push onto the stack
   layout; decide the tape home for the running index (open question 2).
5. Then the table, the frame/decode checks against `eps1_chain`, the halt
   counts, the state count, minimisation, Rocq.


## 8. Model-level results (2 November 2026)

All three model-side pieces of this plan are written, run, and green:

### `tools/eps1_stack.py` — the stack bridge (§7 step 1)

The ε₁ descent re-derived as **local top-of-stack edits**, with the wraps
represented in place as a trailing block of unit rungs (no park counter, no
normalise bookkeeping).  Checked and green:

* bijection `model_of`/`stack_of`: 400 random stacks round-trip with
  `val(stack) == full(p, chain)` exactly, including eps1_chain's own
  corners (the `len(chain) > 1` guard on the all-unit stack, the sole unit
  rung as `p=0, chain=[NUM(1)]`, the atom bottoms);
* **400 chains × 4 moves against `eps1_chain.step`: bookkeeping-exact**
  (`(p', chain', n')` identical, not merely value-equal), and the decoded
  value equals the ordinal model's `fs`/`pred` with the index bumped
  exactly on predecessor moves (3 of the 1600 reach the empty stack);
* run lengths against `hardy()` on the ε₁ members, 0..3 × n 1..3:
  identical where both run (member 0, n=1: 21 = 21), cap-bound equally
  elsewhere.

The first version put the atom-bottom fs cases *before* locating the acting
site and collapsed `[E0, 3, 1]` wrongly; the checker caught it and the rule
now is: locate the site (topmost rung with count ≥ 2), and only if the site
is the bottom atom are those cases special.  The locality claim is
structural: every move touches the top unit rung, the acting site, and the
rung written next to it — the template the ≤ 67-state rows need.

### `tools/eps0_fusion.py` — the ε₀ borrow/push fusion (open question 1)

`tower_free.step` = `eps1_chain`'s case analysis **with the index frozen**,
reusing eps1_chain's own helpers so the only delta is the convention.
Checked and green:

* exhaustive over the plain-numeral product (bottom 1..3, tails to depth 3,
  p 0..2, n 1..3): **351 states, exact**, including the 3 halting and the
  bottom-unit corner (tower_free's `None` ↔ eps1_chain's drained `(p, [])`,
  and the all-unit canonical `(m-1, [NUM(1)])`);
* run lengths agree on five small starts;
* the *index-convention* difference is shown concretely on one run
  (`(0, [NUM(1), 2])`, n=2): the first pred bumps to 3, so the next fs
  writes 4 on the bumped side and 3 on the frozen side — from then on the
  two worlds produce different values.  eps1_full ties in through its own
  green move-for-move check against tower_free, so **machine = tower_free =
  eps1_chain-with-frozen-index** on the plain world: the ε₀ engine is the
  base case of the stack bookkeeping.  The dynamic-index fulfillment is the
  stack model's job (done) and the tape's open question 2 (the index's home).

### `tools/eps1_rung_pos.py` — the stage/rung position (measurement)

The 57-state stage/rung machine (`tools/eps1_machine.py`), measured:

* a=0: values 0..6 all halting in 7 steps;
* **(a=1, v=1): 105 steps → value 3; (a=1, v=2): 68 384 steps → value
  255** — the only two rung simulations reachable, because `run(c, v)`
  applies eps_0's stage *c* times, so (1,3) already asks eps_0 for 2^65536
  rounds, (2,1) a stage over a 65535-mark block (~4e9 steps), and (2,2) a
  stage of 2^256−1 marks;
* against `eps1_level`'s own ladders (cap 2e6): the flat towers over 1 pass
  the cap at height 3 (n=2; heights 1-2 are 4 and 19), while **every ε₁
  member k ≥ 1 exceeds the cap at every n**, and even member 0 already is
  cap-bound at n=2 (21 exactly at n=1).

Verdict, measured not asserted: the machine's whole reachable ladder is the
flat world — every rung is eps_0's own machinery over unary blocks, no ε₁
member is entered at any rung, and no ordinal notation is descended
anywhere.  **One level below ε₁**, confirming `EPS1_35_STATES.md`'s
characterisation; the descent it lacks is exactly what the stack bridge now
supplies at model level.  Not a claim about f_ε₁.

### What this changes in the budget picture

The stack model has no park, no index field and no normalise: the fs move's
n+1 marks are written *at one site*, the pred move *is* one decrement at the
top, and the atom cases are rung-kind flips at the bottom.  The state sinks of
§1 (the fs-limit's two passes, absorb's index shuttle, the park round trips)
haven't natural analogues in this vocabulary — what replaces them is the
fs write's n-source (open question 2) and the copy the write implies.  The
paper band of §4 stands until simulated; the next artifact is the tape frame
and its row transcription, checked through frame/decode exactly as
§5 prescribes.

## 9. The 40-state verdict (measured, this turn)

Census target: ε₁ ≤ 40, ideally exactly 40 states, 2 symbols, blank start.
The re-cut question of §2 was settled by row experiment, not estimate:
`tools/eps1_s40.py` implements the cheapest candidate — **the drain**: a
per-slot park-growth loop (erase an index slot, walk left over the restored
prefix, the E-to-X gap, the chain and the park, write one mark at the park's
extension cell, walk back, hole-surround restore, repeat), on the very
canonical layout of the 150-state table, checked decode-exact on 213 starts
(13 fixed edge cases + 200 random), halting on the home E with the index
restored and the chain untouched.

**Result: the drain needs 20 active states + a halt state (31 rows).  The
fs-limit's pass 2 of record does the same job in 14.**  The re-cut is
worse, and the difference is not loop arithmetic — it is the walk floor:
three field crossings per direction (index gap, chain with its one-blank
inner gaps and their through-and-resume pairs, park gap), plus the
hole-surround test, plus the done-arm home walk.  The three growing fields
(the park extending left at its sea, the chain's indexed appends right, the
index's +1-per-pred) have no free sea between park and chain, so the index
relocation costs are structural, and every cheaper-looking rewrite pays the
same crossings.

Consequences, recorded as the turn's honest position:

* the fs-limit's 27 states (pass 1 17 + 2 shared + pass 2 14) stand as the
  floor for THIS data layout; re-cutting does not reach below it;
* the total budget therefore stays at the §2 floor of ~120-130 for the
  fused ε₁ machine over (p, chain, n);
* **an exactly-40-state ε₁ machine is not reachable by re-cutting this
  architecture** — it would need a representation of the descent without a
  third growing field, i.e. a device where the index never sits between two
  other fields (candidates: the fixed-index omega-tower engines of
  `eps1_full`/`omega2`, which are one level below ε₁ because the Hardy
  index must grow at every pred, or a fundamentally new encoding).  That is
  a multi-session build, not a refactor of the 150-state table;
* the drain device itself IS verified and reusable — as the pass-2
  replacement it costs more, so the table keeps its 14-state pass; the
  file remains as evidence and as a building block for layouts that do
  re-balance the walks.

### Where the 14 wins (rows read, not asserted)

Reading `fs_limit`'s pass-2 rows (`P3, QIL, QIG, QIR, QIB, QIP, QIW, QIK,
QIG2, QIR2, QIG3, QII, QIN, QIH`) against the drain: the table's pass pays
none of the three costs the drain pays.  (1) At fs-limit time the chain is
always the single extended run `[C0..C0+2]`; there are no one-blank inner
gaps, so the return walks `QIR2` and `QIL` miss the through-and-resume pairs
(the drain's `W6b`/`W14` are exactly for the general chain).  (2) The
table's erase order is right-to-left over the index, so the hole is,
by construction, the first blank reached walking left after the remaining
prefix; `QII`'s restore needs no surround test — the drain pays the
`W15`/`W16` peek because it erases leftmost-first over a general index.
(3) Pass-1's tail (`FLP2`'s 0-arm) parks the head ON the re-shifted index's
rightmost mark, so pass-2 needs no entry walk at all — the drain's
`W1`/`W2`/`W2b` are pure setup.  Conclusion: the 14-state pass is tight at
its own call sites; the drain's extra states are the price of generality,
not slack.  A 40-state device must avoid the generality, not pay it —
which is precisely what the prior art below does.

## 10. Prior art: the corpus, and the index-free descent candidate

Source: `Yeyito777/bbchallenge-corpus` (snapshot 2026-10-29 — one local
clone at `corpus/`).  The wiki and Talk pages quoted below are ORIGINAL text
read directly in the clone; its Discord digests are AI-reduced summaries
(their own notes say ~98% spot-checked, attachments missing), so only the
direct quotes here are used as claims.

The community's ladder (wiki `Measuring_large_numbers`, original text):

| ordinal | measured states |
|---|---|
| ω+1 | 10 (Ketchersid, Oct 2026, GitHub) |
| ω+2 | 12 |
| ω×2 | 14 |
| ω² | 21 |
| ω^ω | **40** |
| ω^ω+1 | 51 |
| ε₀ | **51** (BB(51), Sligocki, Sep 2024) |
| φ(ω,0) | — (no machine) |

**No ε₁-level machine anywhere in the corpus**: the grep sweep over all
channels, the forum, the wiki and its history surfaced no ε₁ machine and no
entry above ε₀ in the ladder; the wiki's `User:Jacobzheng/BB(40)` page is an
unrelated 40-state machine page.  The large-bb-domains channel's pinned
list is BB(14) Graham, BB(51) ε₀, BB(150) BMS, BB(1015) Loader's.

The BB(51) ε₀ champion (wiki `Talk:Champions`, original text) is by
Racheline: it directly simulates **Address Notation** — a Primitive Sequence
System (1-row Bashicu) variant.  The notation state is a lexicographic list
of naturals; the expansion of a step happens in place: the last element c is
decremented, and copies of the list segment after the last r < c are
appended.  Racheline's analysis: the TM computes a Hardy hierarchy h with
FS ε₀[n] = ω↑↑⌊(n+c₃)/2⌋, iterated as `h^8(n)` from a large seed, so
Σ(51) > (f_ε₀)^8(…) > f_{ε₀+1}(8), with c₀..c₄ non-degeneracy constants
deduced from the space-time diagram.

**Structural insight for our device**: the champion carries NO SEPARATE
index field and NO park counter — the notation list is the ONLY growing
object; both the fs-like expansion and the pred-like decrement are in-place
edits, and the index never exists as a field: the large seed is written
once by the boot, in the same spirit as our 6-state loader.  This is the
concrete form of §9's "no-third-field device": replace the (p, chain, n)
triple by a PrSS-style rank list on which BOTH moves are in-place edits;
the per-pred index growth disappears (it becomes the harness constant).
Our `eps1_stack` bridge is the model-level ancestor of this shape (the
stack of rungs IS such a list).  This is a NEW BUILD, not a refactor: the
model to check is a
PrSS-valued descent against `eps1_descent` via the address-to-chain map
(to be defined and machine-checked), then a new tape layout and rows.
The community's best at ε₀ is 51 states; our open census (ε₁ ≤ 40) is one
limit level above and record-tight: the corpus records no attempt.

### Follow-up checks on the three suggestions (this turn)

1. **Prior-art sweep (negative, strengthened).**  Greps over all channels
   and the wiki with the alternate phrasings (epsilon one, e1 level,
   least fixed point, address notation, PrSS, hardy hierarchy tapes)
   surface no ε₁-level machine and no attempt above ε₀ anywhere.  The 40
   in the ladder's ω^ω row is the least-m-at-f_α(3)/(f_α(10)) record, and
   that row links no transitions page in the snapshot; there is no
   dedicated PrSS/BMS wiki page in the corpus at all, so its list→ordinal
   decoding is not extractable from text.

2. **The ω^ω comparison (structural only).**  The wiki's record for
   f_{ω^ω}(3)+(10) is 40 states and for f_{ω^ω}(2) is 10; our engine is the
   34-state ω^ω rung with an 8-state advance module.  Without their row's
   transition table the extra states cannot be attributed line-by-line;
   plausible budget is exactly the advance/level machinery our +8 pays,
   measured honestly as a structural comparison, not a claim of ours
   being better or worse.

3. **The PrSS model check (`tools/eps1_prss.py`).**  The expansion rule is
   implemented verbatim and unit-tested green (successor-drop, decrement,
   segment-after-r copy).  The bridge search is NEGATIVE on the covered
   class: of three candidate orientations (leading-sentinel identity,
   reversed with trailing sentinel, bare), none reproduces `chain_fs`/
   `pred_chain` values for NUM-bottom chains; `reversed+trailing`'s 85 are value MISMATCHES, not partial matches
   (the corrected count: 0 matches for EVERY bridge).  The per-class
   breakdown now in `tools/eps1_prss.py` types every failure: the 85
   are the successor-class cases — the trailing-0 construction makes
   the rule fire its pred branch, which decodes back to the original
   chain and can never equal pred_chain's value; 61 more successors
   are not-expressible; all 154 limit chains are not-expressible.  The
   bare bridge cannot express the limit step at all: the rule's own
   canonicity (an element < c must exist) needs the sentinel.  Honest state of the idea: the Address
   Notation decoding needs Racheline's own correspondence (the c₀..c₄
   constants and the lexicographic reading), which is not in the corpus,
   so the index-free build remains open rather than blocked; the module
   is the standing harness to check the next candidate mechanically.

### The BB(51) champion as an artifact, and the decoding chase (this turn)

`machines/bb51_eps0_champion.txt` transcribes Racheline's 51-state row
set exactly from the corpus's original wiki text (Talk:Champions,
Sept 2024; claim Σ(51) > (f_ε₀)^8(f_ω^ω^3(a lot)) > f_{ε₀+1}(8); start
state 30, blank tape).  `tools/check_bb51_champion.py` is green: the
parse is exact (51 states, 101 rows — the halt pair (50, 1) encoded as
a missing pair), and a 10^7-step run from state 30 on a blank tape
reaches the cap with no halt, all 51 states used, span 5943 cells, 5606
ones at cap.  No level claim is added here; the recorded claim stays
the wiki's.  On the decoding: the corpus also records (general channel,
Nov 2024) that a member asked for a 'pointer version' and for a
description of what each part of the 51-state TM does — both requests
recorded UNANSWERED — with racheline adding only that 'the expansion
algorithms of address notation and PrSS are equivalent for PrSS-
standard sequences'.  So the list→ordinal decoding is genuinely not in
the public record; `tools/eps1_prss.py` stands as the harness for the
next candidate correspondence.
