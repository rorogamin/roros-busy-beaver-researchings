# SUPERSEDED — read HANDOFF.md instead

This copy predates the table's completion: it still says the dispatch and the
moves are not written.  They are, and the exact checked status (150 raw / 143
refined states, all chain-spec checks, the 67-cap verdict) is in `HANDOFF.md`,
which supersedes everything below.

# Handoff: the 2-symbol ε₁ machine (v2)

Read this before touching anything.  This is the state of the work, the traps
that already cost time, the exact next steps — and, new in v2, the dispatch
design fully derived: which length categories are reachable, where the bottom
test is actually needed, and the tape geometry of every move.  The plan of
record is `FGH_MACHINES_PLAN.md` (1043 lines); this file is the short version.

## The goal

A **2-symbol, blank-tape Turing machine** whose halting time is at level **ε₁**
(not ε₀ — ε₀ machines already exist) and whose table has **at most 67 states**,
minimised as far as possible.  The machine comes first; a Rocq development
follows later.  Verification order is fixed: the ordinal model, then the chain
model, then the table, then Rocq.

### Hard constraints

  * exactly 2 symbols, blank tape start;
  * at most 67 states;
  * the step count must be f_ε₁(n) for some n > 2, "around" it rather than exactly
    it (the user allowed a factor);
  * never write `admit`, `Admitted`, `Axiom` or `Parameter` in any `.v` file;
  * `rocq/` sources were not edited this session; the development is run after the
    table is finished and checked;
  * do not overclaim. In particular the ω / ω^ω / ω^ω^ω tower is ε₀'s sequence,
    **not** ε₁'s: ε₁[n] is the tower of n omegas over **ε₀+1**.

## What is verified, and what is claimed

Green gates, all `ALL OK`, each exit 0 (`python tools/<name>.py`):

| module | what it establishes |
|---|---|
| `tower_rules.py` | the ε₀-level rule set |
| `tower_free.py` | the flat ε₀ engine's semantics (park m, working part W) |
| `eps1_tower.py` | the ε₀ writer/copy from an index |
| `eps1_full.py` | the whole ε₀ descent as a 2-symbol table, 71 states, move-for-move against `tower_free`; halting lengths 1,4,11,26,57,120,247 for h=1..7 |
| `eps1_level.py` | records the ε₁ sequence members, checks strict decrease on 400 sampled notations, measures both ladders; does **not** separate the ladders by measurement (stated honestly) |
| `eps1_chain.py` | **the specification**: the ε₁ descent as a chain machine, checked against the ordinal model `eps1_descent` after every move (400 chains × 4 moves), lengths equal `hardy()`, ε₁[3] traced |
| `eps1_table.py` | the complete 2-symbol table: build, dispatch, pred, copy, spend, absorb, 3-run normalisation, trailing-unit fold, head-empty, fs-limit |

The table is finished and checked against the chain spec:

  * blank tape, state 0 -> `(p=3, chain=[ATOM1], n=3)` in **16 steps**, home H1;
  * the index copy in isolation: n = 1,2,3,4,5,8,13,21 PASS in
    23, 40, 61, 86, 115, 226, 491, 1123 steps (quadratic, ≈2.5n², as a
    unary copy with one head must be), plus 60 random shapes;
  * **414 starts × 4 moves ALL OK** against `eps1_chain.step`, comparing
    ordinal values with `full` and `n` exactly, running each move from the
    machine's own tape;
  * **halting counts** on 10 terminating starts: advancing homes + the halt
    equal `eps1_chain.run`'s move count.  Value-neutral homes (the absorb's
    3-run fold and the trailing-unit fold) are counted as `extra`; e.g.
    `p=0, chain=[NUM(1),1,2], n=3` gives 131 advancing + 1 extra + halt =
    132 model moves.

**No halting-time claim is made for the table beyond this agreement with
`eps1_chain`.**  The chain spec itself is the ε₁ rule set; the table has not
been run to an ε₁-sized halt (that is astronomically long), and no Rocq theorem
about this table is claimed.  The Rocq development compiles (16 modules, 156
theorems closed under the global context, no forbidden vernacular), but it
formalises the tower/chain rules and the ε₀ machine, **not** the 150-state
table.  Do not read the 156 as a proof of the table.

### State count: the 67 cap is not met

Raw table: **150 states, 207 rows**.  Moore refinement
(`eps1_minimise.blocks_of/rebuild`) gives **143 states, 198 rows**, merging
five nontrivial classes: `BW2/W31/QIH`, `P4/W30`, `R3/SW/HSW`, `B/SR`,
`QIP/QIW`.  The refinement was checked behaviour-preserving on the blank-tape
build and six frames.

Cost drivers (own states, before shared-state double counting): fs-limit 27,
absorb 25, copy 20, dispatch+pred 19, build 14, spend 14, head-empty 12,
3-run normalisation 9, unit fold 5, erase 1, pred-shorten 5 (the sum is 151
because one name is defined in two functions).  Reaching 67 would require a
different architecture, not more merging of this one; the copy alone is 20
states and the fs-limit's index-preserving pass 2 is 27.

## The rule set of record

`eps1_chain.step(p, chain, n)` is the spec the table must implement. State is
`(p, chain, n)`: `p` = wrap count, `chain` = the active chain bottom-first with
unary entries, `n` = Hardy index bumped on every predecessor move.

| move | condition | rewrite |
|---|---|---|
| pred | p == 0, val(chain) a successor | chain := chain − 1; n += 1 |
| fs-successor | p ≥ 1, val(chain) a successor | chain := (chain−1) ++ [n+1]; p −= 1 |
| fs-limit | val(chain) a limit | chain := chain[n]; p unchanged |
| halt | p == 0, chain empty | stop |

In the normalised regime this collapses beautifully:

  * **the only limit case is the singleton `[ε₀]`** — because the atom can only be
    the bottom entry, a longer chain with the atom at the bottom has value ε₀·c, a
    successor;
  * **the fs-limit is `[ε₀]` → `[NUM(1)]` with `p += n`** (the n unit entries that
    `chain_fs` produces are absorbed by `normalise`);
  * `chain_fs` and `normalise`: see `eps1_chain.py`; the plan records the
    corrected pop rule (a wrap is **spent on a coefficient**, never discarded —
    the original plan's pop rule was wrong and `eps1_chain.py` refuted it).

`normalise` absorbs a *plain-int* top 1 into p only while `len(chain) > 1`;
`NUM(1) == 1` is False, so an Ord `NUM(1)` top is never absorbed.  This matters
for every reachability claim below.

## The tape, as implemented in `eps1_table.py`

    [free] 1^p (park)  0 0  1^{c0} 0 1^{c1} 0 ... 0 1^{cm}  0 0  1^n (index)  [free]
            Lp..Rp           C0                                X..

Entry code: run length **1 = ε₀, 2 = ε₀+1, L ≥ 3 = the number L−2** (both
plain ints and `NUM(k)` code to k+2 — the tape cannot tell them apart, so
`decode` always yields `NUM` and comparisons are by **value**, see `same`).
One blank is a chain separator; two or more blanks are free space.  The chain's
top run is "the last mark before two blanks"; the index is "the first mark after
two blanks".  Home `HT` = the head on the top run's last mark `E`.

Invariants:

  * **I1** the park's right end is `C0-3` forever, so "p == 0" is a fixed look and
    spending erases the park's *leftmost* mark while growth writes one cell left
    of it.  Anchoring the other end would put the p == 0 test behind a walk of p
    cells, which is why it is right-anchored and spent from the left.
  * **I2** `X = E+3` at rest. pred moves E and X left by one together, so pred is
    six moves regardless of p and n. Only the fs writes move X, and that is the
    copy.

## The copy, and why it is the way it is

The fs-successor needs a new top run of `n+3` marks while the index keeps `n`,
and the band between the chain and free space only held `n`. Two facts fixed it:

  * the new run's cells are almost exactly the old index's cells, so the run
    cannot be built by moving the index's marks — they *are* the run. The copy
    therefore erases the source and rewrites each mark two cells to the left as
    the run, one trip per mark, which keeps the cursor local (the erased cell's
    right neighbour is the next source mark);
  * the index's copy goes into free space **three reserved blanks** past the
    source's right end, so its write position is a checkable fixed offset.

Three off-by-one bugs were found only by decoding the tape at the home, never by
reading rows: the new run starts **two** cells past the decremented run
(separator plus old gap), the finish writes **two** marks not three (the entry
already wrote one), and the return trip crosses three reserved blanks plus the
old cursor's cell.

**Entry contract (verified):** `check_copy` enters `CW0` with the head on
`E-1` *after* erasing the old `E` (the decrement).  The copy then runs
`CW0..CF3` and lands on the new top run's last mark — a home position, but for
the machine it must next go to the **spend**, not to the dispatch (see below).

## The dispatch — derived, not yet written

The plan's arithmetic (FGH_MACHINES_PLAN.md lines ~979-990), restated with the
derivations this session worked out so the code can be written straight:

    the count for p == 0   4 states   (2 = shorten, 3 = halt, 4 = absorb, >=5 = shorten)
    the count for p >= 1   2 states   (3 = head-empty arm, else decrement+copy)
    the spend              2 states   (erase the leftmost park mark, then test)
    the walk back          4 states   (two shared, two by the flag: land on H0 or H1)
    the pred               3-5 states, the halt 1 (missing row — see below)
    ------------------------------------------------------------
                          ≈16 states  (the plan's 3 for pred is optimistic; count honestly)

### Entry states carry the bit

There are **two homes**: `H0` (entered when p == 0 is known) and `H1` (entered
when p ≥ 1 is known).  The bit is never read at the decision point — it is
tracked, because every p-changing place is a place the machine already is:

  * after an fs-successor's spend, at the park: "is the park empty now" is the
    cell just right of the erased mark — the walk back has **two exit states**,
    landing on H0 or H1;
  * a pred's absorb (length 4, non-bottom) goes 0 → 1: return **H1**;
  * plain pred leaves p = 0: return **H0**;
  * the fs-limit gives p += n ≥ 1: return **H1** always (no test needed);
  * the pred loop keeps p = 0.

### Reachability lemmas (why the branch table looks the way it does)

These were derived from `eps1_chain.py` and hold for every *normalised reachable*
state — they cut the bottom test down to one place:

  1. **Ord entries (ATOM, ATOM1, NUM(k)) occur only at the bottom.**  Every move
     either produces a plain-int top (`n+1 ≥ 2`, `below-1`) or a singleton Ord
     (`pred_chain` of an Ord top drops everything below, `chain_fs` bottoms).
  2. **L = 1 ⟹ chain = `[ATOM]` singleton.**  ATOM is only ever bottom, and it
     being also top means singleton.  ⇒ unconditionally the fs-limit, no test.
  3. **L = 2 ⟹ chain = `[ATOM1]` bottom singleton.**  ⇒ unconditionally pred
     (shortens to `[ATOM]`), no test.
  4. **L = 3 ⟹ chain = `[NUM(1)]` bottom singleton.**  A plain-int top 1 is
     absorbed by `normalise` whenever len > 1, and a singleton plain `[1]` is
     unreachable (it would hit `chain_fs`'s `assert below is not None`).
     ⇒ p == 0: halt; p ≥ 1: head-empty arm.  No test.
  5. **L ≥ 5 ⟹ pred shortens by one mark** whether bottom (`NUM(k≥3)`) or not
     (plain `k≥3`, top−1 ≥ 2, no absorb).  No test.
  6. **L = 4 is the only place the bottom test is needed.**  Bottom = `[NUM(2)]`
     singleton: pred shortens 4 → 3, p stays 0.  Non-bottom = plain 2 top:
     pred gives plain 1 → `normalise` absorbs it (len > 1) → **the whole run is
     erased, p 0 → 1**: the absorb.  Test: at `E-4` (blank, L = 4 known), step
     to `E-5`: blank → bottom (shorten), mark → non-bottom (absorb).
     (For p ≥ 1 the test is not needed: both L=4 shapes take decrement+copy.)

### Branch table

From `H0` (p == 0), after the count walk left from `E` (at E-1 blank → L=1,
mark → continue; E-2 blank → L=2; E-3 blank → L=3; E-4 blank → L=4; mark at
E-4 → L≥5):

| L | bottom? | action | return |
|---|---|---|---|
| 1 | (always) | fs-limit | H1 |
| 2 | (always) | pred: erase E, write index mark at E+2, home E-1 | H0 |
| 3 | (always) | **halt**: erase the 3 marks, bump index, stop (no row = stop) | — |
| 4 | bottom | pred (as L=2) | H0 |
| 4 | non-bottom | **absorb** (geometry below) | H1 |
| ≥5 | (either) | pred | H0 |

From `H1` (p ≥ 1):

| L | action | return |
|---|---|---|
| 1 | fs-limit | H1 |
| 3 | **head-empty arm**: erase the 3 marks at C0, write n+3 marks at C0, **then spend** | H0/H1 via spend |
| 2, 4, ≥5 | decrement (erase E) → enter copy at `CW0` on E-1 → copy → **then spend** | H0/H1 via spend |

**Ordering rule: the spend happens AFTER the copy/head-empty, immediately before
returning home.**  The copy's states are fixed and cannot carry the bit; the
spend's walk-back is what lands on H0 or H1, so it must be the last thing before
home.  (`check_copy` stops at `CF3`'s target — the spend's first walk state is
position-identical to a home, so decode there still works; adjust `check_copy`
to stop at that state if wiring changes the target.)

**Both fs-successor arms spend** (p−1): the head-empty arm is an fs-successor
(`step(1.., [NUM(1)])` → `[NUM(n+1)]`, p−1) — do not forget its spend.  The
fs-limit does **not** spend (p += n).

### Move geometry (exact cell arithmetic, worked out this session)

**pred (shorten)** — erase `E`, write one index mark at `E+2` (the index extends
*left* by one: X−1, so X' = E'+3 holds with E' = E−1), home at `E-1`:
walk `E (1→0,R) → E+1 (blank,R) → E+2 (0→1,L) → E+1 (blank,L) → E (blank,L)
→ land E-1 in H0`.  `E+1` is visited twice with opposite directions: **two
distinct states, they cannot merge.**  Realistic count 4-5, not the plan's 3.

**halt** — L=3 at `E-3` (blank): the model does one pred (`[NUM(1)]` → `[]`,
n+1) then halts on the next step.  Cheapest correct machine: *stop there* (the
count state simply has **no 0-row** —0 states).  The tape keeps the run; nothing
reads it after halt.  Trips are counted as `homes_visited + (1 if halted)`,
which matches the model's move count for `(0,[NUM(1)]) = 1`,
`(0,[NUM(2)]) = 2`.  (Erasing "and stopping" as the handoff once said costs 3
states for no observable benefit — skip it unless a check demands the erase.)

**absorb** (p==0, L=4 non-bottom) — run occupies `E-3..E`, entry below ends at
`E-5`, separator at `E-4`.  After: `E' = E-5`, `X' = E-2` (gap `E-4,E-3`), index
must be **n+1 marks at `E-2..E-1+n`**.  Order constraint: for **n ≥ 4** the old
index (`E+3..E+2+n`) and new index (`E-2..E-1+n`) **overlap**, so:
  1. erase the old index first (walk right from E over the two blanks to E+3,
     erase n marks rightward, walk back left over the erased blanks to the first
     mark = E);
  2. erase the run leftward `E, E-1, E-2, E-3` → land `E-4` (blank);
  3. walk the chain left to the park, write the park mark at `C0-3` (p 0 → 1),
     walk back right;
  4. write the new index: from `E-4` step right twice to `E-2`, write n+1 marks
     rightward;
  5. walk left over the new index and the gap, land on `E-5` in **H1**.
(A different order is fine if it preserves erase-old-before-write-new.)

**head-empty arm** (p≥1, L=3 bottom) — chain is exactly the 3 marks at
`C0..C0+2`; erase them, write `n+3` marks at `C0..C0+n+2`, then spend, then home
at the new E = `C0+n+2` (via H0/H1).

**spend** — from HT walk left over the chain (marks, single-blank separators,
stop at the two-blank gap), to `C0-3`: walk left over the park to its leftmost
mark, erase it, step right onto the cell just right of the erased mark: blank →
park empty → exit toward **H0**; mark → exit toward **H1**; walk back right over
the chain to the top run's last mark.  The walk back = "two shared states, two
by the flag" (the plan's 4).

**fs-limit** — `[ATOM]` (1 mark at C0) → `[NUM(1)]` (3 marks at C0..C0+2):
  * chain: write marks at `C0+1`, `C0+2`;
  * park: p += n — **one leftward walk handles p==0 and p≥1**: from `C0-3`
    walk left; existing park marks are passed, the first blank cell (or `C0-3`
    itself when the park is empty) is written, continue left, n times;
  * index: shifts **right by 2** (`X: C0+3 → C0+5`, n unchanged).
  **Open question when writing it:** the plan says share the copy's loop with
  the park as near destination, but the copy's far offset ("three blanks past
  the old index's right end") does *not* equal this +2 shift — either the far
  arm needs a different fixed offset for the fs-limit, or the loop drains/rewrites
  the index differently.  Resolve against `decode` before believing it; a
  standalone 10-12 state routine is the fallback if sharing does not pay.

**build** (blank tape → first home) — about 7 states: park of 3 (write at
`C0-3` backwards), 2 blanks, a 2-mark run (`ε₀+1` at C0), 2 blanks, 3 index
marks, then home to `HT` **in H1** (p=3 ≥ 1) and enter the dispatch.  The runs'
last marks need distinct states because a state cannot count.  This builds
`(p=3, chain=[ATOM1], n=3)` = ε₁[3], the n > 2 the goal allows.

## State budget — honest vs plan

    copy (verified)                          21
    dispatch (plan)                          16   (count0 4 + count1 2 + spend 2
                                                   + walk-back 4 + pred 3 + halt 1)
    dispatch (honest, this session)          18-20  (pred is 4-5 not 3; halt may be 0;
                                                   L=4 bottom test +1..2; count states
                                                   ×2 for the two entries — see below)
    fs-limit as second arm / standalone       4 / 10-12
    build                                     7
    ------------------------------------------------------------------
    raw total                                ≈53-65 before Moore refinement

The two count walks (H0's and H1's) **are** partly duplicated: `H0 → C1_0` and
`H1 → C1_1` must differ at their first 1-row (L=2 goes to pred vs
decrement+copy).  `C1` (L=1 → fs-limit, shared target) cannot merge across the
bit either, because its 1-row continues into the bit-specific walk.  Budget ~4
states for H0's count and ~3 for H1's, plus the L=4 bottom test on H0 only.
If the raw table exceeds 67, run Moore refinement (`eps1_minimise.py`:
`blocks_of`, `rebuild` — it took ε₀ 79 → 68) and merge.

## Checks to write (before believing any of it)

  * decode `(p, chain, n)` at every home and compare **values** with
    `eps1_chain.step` (not structures: the model carries plain ints where the
    tape necessarily decodes `NUM(c)`; they are value-equal — `same` exists for
    this);
  * exact halt counts via trips = `homes_visited + halted`, instances small
    enough for `eps1_chain.run`: `(0,[NUM(1)])` 1 move, `(0,[NUM(2)])` 2,
    `(1,[NUM(1)])`, `(1,[NUM(2)])`, `(2,[NUM(1)])`;
  * short prefixes from longer starts (400 chains × 4 moves, as
    `eps1_chain.check_against_model` does);
  * the blank-tape run at least reaching the first few homes (the build);
  * keep `check_copy` and `check_copy_random` green after any retargeting of
    `CF3`.

## Traps that already cost time

  * **Name clash**: `eps1_table.py` imports `NUM` from `eps1_chain` (the ordinal
    number constructor) *and* keeps state ids — use `SID`/`SNAME` for states.  Do
    not reintroduce a second `NUM`.
  * **`decode`'s run walk** must break when `tape[low-1]` is blank **and**
    `tape[low-2]` is not a mark; breaking on `low-1` alone stops at the first run.
  * **`tm.tape_str(tape, head)`** prints the tape *with the block size added* and,
    when debugging by hand, remember a trace printing after `t.step` shows a stale
    head — print before stepping.
  * **Heredocs get truncated** in this environment for long scripts: write files
    with the file tool, not `cat > file <<'PY'`. Short patch scripts in a heredoc
    are fine.
  * **Entry ambiguity**: a run of length 3 is `NUM(1)` at the bottom and can only
    arise above the bottom from the fs-successor's `[.., 1, n+1]`, where the model
    keeps the `1` as a plain int in the middle. It is value-equal, so compare
    values; do not "fix" the encoder.
  * **`normalise` and the int 1**: a top entry of the *plain int* 1 is absorbed
    into p; an `Ord` `NUM(1)` is not (`NUM(1) == 1` is False). This is why a top
    run of length 3 only ever occurs as the singleton `[NUM(1)]`, and why the
    pred/fs special cases are exactly the ones listed above.
  * **Run budget**: keep `timeout_seconds ≤ 300` and use `timeout N python ...`;
    never launch an unbounded simulation of a real descent — they do not finish.
  * **`str_replace` paths**: `tools/eps1_table.py` works, but `tools/bbmulti.py`
    needed backslashes once — if a path errors as "file does not exist", retry
    with backslashes or the bare filename.
  * **Overlapping index writes** (absorb): erase old before writing new, else
    n ≥ 4 loses a mark.  Found by arithmetic, not by a failing check — write the
    check anyway.

## Designs that were tried and rejected — do not redo them

  * **A flag mark parked near the acting entry.** Impossible: the index's left end
    marches left by one on *every* pred, unboundedly, and the acting entry marches
    with it, so anything at a fixed offset is eventually eaten by the index (the
    same drift `tools/eps1_copy.py` documents for its seed mark).
  * **Folding p into the chain as trailing unit runs** (no park; "p == 0" becomes
    the rightmost run's length, which *is* local). It reintroduces middle
    insertion: the new run has to go below the remaining unit runs, so the
    fs-successor would shift p−1 runs right by n+3 cells — a second conveyor of
    6-8 states on top of the copy — and it invalidates the verified copy's
    geometry. Not worth it.
  * **Putting the park between the chain and the index.** The pred's index bump
    needs the index adjacent to the acting entry, and its left end grows leftward
    unboundedly, so a park there collides within a few preds.
  * **Preserving the copy's source and tracking a read cursor on it.** Impossible
    with two symbols: an unmarked block has no cursor.
  * **Erasing the run on halt** (rather than stopping with no row): costs 3
    states, no observable difference — trips formula already matches the model.

## The remaining work, in order

The table work is complete and green.  The state budget is now settled the hard
way: **the 67-state cap is a hard requirement** (at 150 states the machine is
inside the range where BB(150) dwarfs f_ε₁ of any relevant n — the state count
itself must carry the claim), and the measured floor of the current
three-field encoding is 143 states, so **re-cutting reuse of this design cannot
reach the cap**.  The replacement plan — a fused ε₀+1-based stack machine,
built on module K / the stage-rung drive / the 9-state zero-marker copy and
checked against `eps1_chain` through a new layout bridge — lives in
**`EPS1_67_PLAN.md`**, which supersedes the build order below for new work:

1. ~~model-level bridge (stack notation ↔ `(p, chain, n)`) first, no tape
   work~~ **done and green (2 November 2026)**: `tools/eps1_stack.py` (the
   stack moves as local top-of-stack edits, bookkeeping-exact against
   `eps1_chain.step` over 400 chains × 4 moves, lengths equal to `hardy()`);
   `tools/eps0_fusion.py` (the ε₀ descent is exactly the eps1_chain
   case analysis with a frozen index — 351 states exact — so eps1_full's
   machinery is the stack's base case; the running index is the tape's open
   question); `tools/eps1_rung_pos.py` (the 57-state stage/rung machine
   measured: a=0 in 7 steps, (1,1) 105, (1,2) 68384; a ≥ 1 beyond that and
   every a ≥ 2 out of any simulation — one level below ε₁);
2. then the stack table itself: the frame, module K's port, the tape home
   for the running index, then the standard checks, the state count, Rocq.

The completed 150-state table (`tools/eps1_table.py`) stays as the green
reference; do not delete it.

## Turn record — the posted 2-symbol BB(20) champion (transcribed, checked)

`machines/bb20_2sym_champ.txt` + `tools/check_bb20_champ.py` (ALL OK, exit 0):
the 20-state 2-symbol machine posted with the claim f_(w+7)(f_(w+7)(5)),
transcribed verbatim in bbmulti's loader3229 format (20 states A..T, 39
defined transitions).  Integrity verified: exactly one `---` halt row
(A reading 1) and one explicit Z halt (S reading 0), all 20 states and both
symbols exercised.  20M-step probe: no halt, score 7,698, first 1,000 marks
at 339,106 steps — the growth is slow inside the budget, consistent with a
multi-phase counter structure whose termination is the halting claim.
The f_(w+7) level-claim itself is NOT verifiable by simulation (recorded
honestly; a halting BB(20) champion this low in the ladder would slot below
the recorded 51-state eps_0 champion, as expected from the corpus ladder).

## Then, same turn — the eps1_odi compression (in progress, paused)

The case census of `eps1_chain.step` over the full tier 1..3 x seed 1..2 runs
is done: 148 distinct pre-step states, 12 move classes, the `(·,[1])` corner
never visited, and the entire decision surface fits the mixed-radix
odometer plan in `EPS1_SUPER.md` §"The unified ODOMETER rewrite"
(eps1_table layout minus the index field, bottom kind encoded in the first
run's length, run length L = c+2, park right-anchored per handoff I1,
rest = the top run's last mark, position-anchored edits, ~30-40 raw states
hypothesis).  Census table appended to EPS1_SUPER.md.  `tools/eps1_odi.py`
NOT yet written — the turn was interrupted mid-table-design; the position
map and dispatch walk states are re-derived from the doc on resume.

## How to check you have not broken anything

    for t in tower_rules tower_free eps1_tower eps1_full eps1_level eps1_chain eps1_table; do
      printf "%-12s " $t; timeout 200 python tools/$t.py >/tmp/o 2>&1; echo "exit=$? $(tail -1 /tmp/o)"; done

All seven must exit 0.  `./verify.sh` runs the Rocq development; on the last
run all 16 modules compiled and 156 theorems were closed under the global
context.  The `.v` sources were not edited.

## Files

| file | role |
|---|---|
| `FGH_MACHINES_PLAN.md` | the plan of record: rules, design, budget, the copy's verification, the cheaper-design arithmetic (lines 905-1043 = the dispatch arithmetic) |
| `tools/eps1_chain.py` | **the spec**: `step`, `run`, `normalise`, `chain_fs`, `pred_chain` + the checks against the ordinal model |
| `tools/eps1_table.py` | the finished table: `frame`, `decode`, `same`, `build`, `copy_routine`, `dispatch_and_pred`, `pred_shorten`, `spend`, `absorb`, `absorb_three`, `unit_fold`, `head_empty`, `fs_limit`, and the checks. 150 states, 207 rows |
| `tools/eps1_descent.py` | the ordinal model of record (`Ord`, `fs`, `pred`, `tower`, `hardy`). No `ONE`; `ATOM1` is written `add(E0, NUM(1))` |
| `tools/eps1_level.py` | the ε₁ sequence and both ladders, measured not asserted |
| `tools/eps1_full.py` | the verified ε₀ table (71 states) — the model for how routines are written here |
| `tools/eps1_copy.py`, `tools/check_eps1_copy.py` | the ε₀ copy gadget, and its docstring on the drift trap |
| `tools/eps1_minimise.py` | `blocks_of`, `rebuild` for Moore refinement |
| `tools/tm.py` | `TM.step(tape, head, state)` → `(head, state)` or `None`; `TM.run(...)`; `tape_str` |
| `tools/bbmulti.py` | the champions checker (six machines, all green as of last run) |

## Honest status

The chain rule set is machine-checked against the ordinal model.  The table is
written and checked against the chain spec: build, copy, 414 starts × 4 moves,
and 10 halting counts all pass, and the seven-module gate is green.  The table is
**not** a 67-state machine: 150 raw / 143 after Moore refinement.  No Rocq
theorem about this table is claimed; the 156 Rocq theorems cover the tower/chain
rules and the ε₀ machine.  The ε₁ halting time is the chain spec's Hardy
descent, not a measured run — an ε₁-sized halt is astronomically long and was
not simulated.

## Turn record — the 40-state question, answered by row experiment

`tools/eps1_s40.py` (green: 213/213 decode-exact, exit 0) implements the
cheaper-drain candidate for the fs-limit's pass 2 on the canonical layout:
20 active states + halt, 31 rows, (p, chain, n) -> (p + n, chain, n) with the
index restored bit for bit.  Measured against the pass 2 of record (14
states): the re-cut is worse; the cost is the walk floor (three field
crossings per direction, inner-gap through-and-resume pairs, the
hole-surround test, the done-arm home walk), not loop arithmetic.  Consequence
recorded in `EPS1_67_PLAN.md` §9: the fs-limit's 27 states stand as the
floor for this data layout, the total budget stays at ~120-130, and an
exactly-40-state ε₁ machine is not reachable by re-cutting this
architecture — it needs a descent representation without the index between
two other fields, a separate multi-session build.  The drain device stays as
the verified building block.

Additions after the corpus check (same turn):

* `machines/eps1_s40_drain.txt` + `tools/check_eps1_s40_drain.py` (green:
  213/213 decode-exact from the emitted txt directly) — the drain device as
  a separator artifact, explicitly NOT the chosen pass (the 150-table's
  pass 2 does the job in 14; the rows-level reason is in plan §9 "Where
  the 14 wins": right-to-left erase order, single-run chain shape, no
  entry walk).
* `EPS1_67_PLAN.md` §10 — prior art from `Yeyito777/bbchallenge-corpus`
  (local clone at `corpus/`, snapshot 2026-10-29): the community's ladder
  tops out at ε₀ = 51 states (BB(51), Sligocki/Racheline, Sep 2024),
  ω^ω = 40, ω^ω+1 = 51, and **no ε₁ machine anywhere**; the champion's
  mechanism is Address Notation (PrSS) with the notation list as the only
  growing object — the concrete "no-third-field" shape §9 asked for.
  An ε₁ ≤ 40 machine would be one limit level above the recorded best;
  the corpus records no attempt.  Candidate design line is in plan §10.

Same-turn follow-ups on the three suggestions: the strengthened prior-art
sweep is negative everywhere (no ε₁ attempt above ε₀; no dedicated PrSS
page in the corpus to pin its decoding); the ω^ω comparison is structural
only (their f_{ω^ω}(3) record is 40 states with no transitions page in the
snapshot; ours is the 34-state rung + 8-state advance);
`tools/eps1_prss.py` implements Racheline's expansion verbatim (unit-green)
and its bridge search is NEGATIVE so far — no candidate orientation
reproduces chain_fs/pred_chain values; `reversed+trailing` holds the
partial signal.  The decode correspondence stays the open item for §10.

Additions, same session ("the rest of the suggestions"):

* `machines/bb51_eps0_champion.txt` + `tools/check_bb51_champion.py`
  (green): the community's BB(51) eps_0 champion as an exact
  transcription of the corpus's original wiki rows, checked to the
  10^7-step cap with no halt and no undefined row (all 51 states
  exercised).  No level claim added; the wiki's recorded claim stays
  the wiki's.
* The bridge-search result is CORRECTED and TYPED: it was mis-recorded
  as "85 value matches"; the empirical number is 0 matches for every
  bridge, and the 85 are the successor-class value mismatches
  (`tools/eps1_prss.py` now prints the full per-class breakdown and
  records example shapes for each failure mode).
* The decoding chase is CLOSED from the record: the corpus carries a
  Nov 2024 record of racheline being asked for the 51-state TM's part-
  by-part description, recorded UNANSWERED, with the single added datum
  that address-notation and PrSS expansion algorithms agree on
  PrSS-standard sequences.  The plan §10 now says what every failed
  decoding candidate must be able to explain.

The SUPER construction (the "super machine creates" request):

* `EPS1_SUPER.md` + `tools/eps1_super.py` (ALL OK): the model layer
  of the single-string super representation — the (p, chain) state
  compressed onto ONE self-rewriting 0/1 tape with the descent
  index n removed as a machine field (only the seed, and only the
  plain blank-tape STARTUP unroll).  Codec: p-runs, prefix-free
  bottom frames (plain / atom=e0+1 / atom+1), self-delimiting
  binary entries, two-blank chain end; 300 round-trips green, 200
  random-path faithfulness checks green, tape and chain layers
  agree in full runs from eps_1[1..3] at seeds 1..2 (lengths 9/30,
  14/65, 20/136).
* The measured record: fixed-parameter descent from eps_1[3] at
  seed 2 is 136 moves while the Hardy bumping variant overruns a
  200k cap immediately; the step factor promise now rests on the
  STARTUP, not the descent.  Ledger kept honest: no 2-symbol
  table, no state count, and the fixed-vs-bumping semantics need
  the AGENTS.md gate decision before any 40-state claim.

-----------------------------------------------------------------------
2026-11-03  BB(6,6) champion swap (loader3229, 10:01)
-----------------------------------------------------------------------
* New BB(6,6) f_{omega*2} champion, claim 'more than f_{omega*2}(89)'
  steps (previous row: argument 36, now marked [superseded] in place):
    4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB
  Six cells differ from the superseded row (A sym0 5RB->4LF, D sym1
  3RD->---, E sym2 1RB->---, F sym1 ->0LF, sym2 ->1RB, sym5 ->5RB).
* Checked with tools/bbmulti.py (2M budget, blank tape): 6 states x
  6 symbols, 28/36 transitions defined, no halt, score 1 650,
  10@121, 100@5 940, 1000@607 129, symbols 0..5 all written, all six
  states visited.  Seeded with a single 1 under the head: no halt in
  100 000 (score 379); seed in C0-1 halts at 14.  Superseded row
  re-verified seeded-under-head: halts at 32 (score 7) as recorded.
* championsReal.txt updated (entry replaced in the loader3229
  section, milestones line, undefined-transitions line, seeding
  paragraph); bbmulti.py MACHINES now tracks the new row.

-----------------------------------------------------------------------
2026-11-03  eps1_odi: Gate 1 + Gate 3 GREEN; Gate 2 at the p0 cascade
-----------------------------------------------------------------------
* BB(6,6) champion turn (loader3229 10:01, f_{omega*2}(89)) recorded in
  championsReal.txt + bbmulti.py; full bbmulti battery green.
* tools/eps1_odi.py, unified odometer rewrite (seeds sn=1/2):
  - Gate 1 (the exact census, tiers 1..3, both seeds): ALL GREEN.
    sn=1: 102 states / 174 rows, ok=43 bad=0; sn=2: 106/179, ok=231
    bad=0.  274 landings value-compared via C.full (the landing rule:
    rest = IN on the top run's last mark; empty chain = the blank with
    IN on the blank, the next dispatch dies = the model's Halt).
  - Gate 3 (the fixed runs): ALL GREEN, machine campaign counts equal
    the frozen-index model walk for every tier: 9/14/20 (sn=1) and
    30/65/136 (sn=2) = the recorded 9/30/14/65/20/136 set exactly.
    NOTE: C.run with the index forwarded cycles past 200k moves
    without halting (the bumping-index semantics); the machine and
    this project's semantics of record use one C.step per
    rest-to-rest campaign with n = the seed.  Gate 3 now compares
    against the frozen walk in lockstep.
  - Gate 2 (400 random starts x 4 moves, seeded rng): PARTIAL.
    sn=1: 177/400 fail, sn=2: 54/400 fail.  All failures are one
    class: the p0 pop-cascade.  Model rule (eps1_chain): at p==0 the
    'pred' step pops the succ-reduced top entry AND every unit entry
    below it, writing one park mark PER POP (normalise(0,
    pred_chain(chain)) = erase the whole run per popped entry +
    p += 1 each, stop at the first non-unit below).  The machine's
    ABS arm pops only the top entry (4 marks for the c2-top case)
    and lands non-normalised tapes; the follow-on campaigns then
    walk wrong arms.  THE FIX OF RECORD (the memory's blocked item,
    now confirmed empirically): the ABS/RP cascade must (a) erase the
    whole run of every popped entry (length-variable, not the fixed
    4), (b) write a park mark per continued pop (RP arms currently
    write none), (c) stop at the first non-unit below and walk home.
  - State count of record, honestly: 102 / 106 states (the <=40
    target unmet this iteration; no Moore refinement attempted yet).
* main() prints an ALL-OK / N GATE FAILURES summary and exits nonzero
  on failures; the gate-2 model-side assert corners are skipped.

-----------------------------------------------------------------------
2026-11-03  eps1_odi minimisation round 1: 102/106 -> 85/87 states
-----------------------------------------------------------------------
Two-layer pass, both verified by the full battery:
* Structural: the old fixed GR1/GR2/GR3 pass (route C grow) collapsed
  into one loop state GP (the site always meets a 3-mark run canonically;
  move counts on the recorded paths preserved exactly - gate 3 confirms
  9/14/20, 30/65/136 unchanged).  PWGX deleted; for sn=2 the GP exit
  routes into the kept PWGY second-mark state.
* Mechanical: new minimise_table() post-pass in eps1_odi.py (runs inside
  build_table): drops states unreachable from the rest dispatch IN
  (DECP, the old HE2..HE7 arm, PWK: 7/8 states), then fixpoint
  bisimulation over the 2-symbol rows merges behaviourally equivalent
  states (PKB/PKD1/WASB, PWALK/PWB, WB-P4/P5 = BRH1/BRH2, RESTO*,
  RAW3/PWY-family).  Second-order merges closed by looping to fixpoint.
Battery after: sn=1 85 states/148 rows, gate1 ok=43 bad=0; sn=2 87/151,
ok=231 bad=0; gate3 tier counts unchanged; gate 2 failure counts
unchanged (177/54) = behaviour preserved, the ABS p0 pop-cascade remains
the one open class (the fix of record in the previous entry).
Honest status vs the <=40 target: 85/87.  The remaining fat is
structural, not mechanical: the four walk-back families (WR_FS, WB_ABS,
WR_A, WB_P) are step-identical for 4-5 states each and diverge only in
their landing (DECF/ABS_E/RAW/IN) - fusing them needs history a 2-symbol
tape cannot carry for free; the append count chain A1..Ak must count
sn+3 (no free loop over blanks); and the ABS cascade redesign (gate 2)
will itself replace the fixed-4 eraser with a length-variable loop,
which is expected to shed several more states as a side effect.

-----------------------------------------------------------------------
2026-11-03  ABS p0 pop-cascade REDESIGNED: Gate 2 to ZERO (all gates green)
-----------------------------------------------------------------------
The failing class is verified root-cause by a state-by-state trace
(tools/g2probe.py, the seeded gate-2 replay with per-step state/direction
prints and a per-move model/machine decode compare): the old ABS arm
completed the top c2 pop correctly (4 marks erased, one park mark) but
then walked home, landing (1, [3,1])-style non-normalised chains.  Those
landings are VALUE-equal (the harness compares C.full, and popping a
deleted unit into p preserves the value), so the value gate passed them;
but the rest tape is a shape the canonical dispatch rejects (a mid-chain
unit top), and the next dispatch died in M3 -> the recorded 4-step
deaths.  The machine must land the MODEL's normalised shape.

New cascade (eps1_odi.py, the "p0 pop-cascade" block): after the top pop
(WAS fuse + WB_ABS walk + ABS_E/X1/X2/X3, unchanged and verified
correct), a position-agnostic measure walks LEFT over the pop-hole zeros
(counting 1s since the last 0; all holes are suffix-region zeros, so the
interior stays hole-free), reads a 5th cell to tell "interior unit" from
"the sep = the bottom", then per pop writes ONE park mark BEFORE erasing
(the left walk stays on the intact interior), returns right, stops at the
first interior 00 (survivor close + hole), and erases the unit's 3 marks
leftward.  Stops: a survivor run >= 4 (non-unit), an L==1/L==2 bottom, or
the sep on the 5th read; then a simple walk home lands IN on the
survivor's last mark.  The bottom never pops (normalise's len==1 guard).
The retired ABS_T1..T4/ABS_M4/ABS_RP1..3/RESTO* fixed-geometry probes are
gone (dropped by the unreachable pass).

Battery (python tools/eps1_odi.py, exit 0, ALL OK -- all gates green
for the first time):
  sn=1: 96 states / 165 rows, gate1 ok=43 bad=0; gate 2: ALL OK;
  sn=2: 98 states / 168 rows, gate1 ok=231 bad=0; gate 2: ALL OK.
  Gate 3 tier counts exact: 9/14/20 (sn=1), 30/65/136 (sn=2).
Two trace-found bugs during the rewrite, both one-line: WLD's sep
crossing was one step too deep (the head already on C0-3 reading 1 =
death), and SB2 erased the bottom's first mark on its crossing row.

Honest state count: 96/98 (the cascade fix cost ~11 net states -- the
length-variable cascade is a real loop family, not a merge; the earlier
"expected to shed several more states" prediction was wrong).  The four
walk-back families and the append count chain remain the structural fat.
<=40 stays a design goal, not a promise; every report carries the count.
Diagnostic harness kept: tools/g2probe.py (usage: python tools/g2probe.py
[sn [failure_index]] -> grouped failures + full trace of one failing
start; prints grouped gaps when zero = also a quick gate-2 replay).

Also this turn (champions provenance, correcting the folklore verdict):
the BB(67) > q^81(q(5)-2) Laver entry IS in the project record:
championsReal.txt line 319 ("BB(67): q^81(q(5) - 2), q(n) from laver
tables") and the bbchallenge champions page as carried in the corpus,
with the champions-page caveat that q(n)'s growth is unknown (q(5)'s
value and even its ZFC-existence are unproven; Googology records the
lower bound f9(f8(f8(254)))).  Consequence recorded in EPS1_SUPER.md:
the ~67-state "dangerous layer" is a documented champions-page fact, and
any eps1_odi push at or below ~67 states stands inside it -- there the
2-symbol machine's behaviour is no longer simulable evidence on its own
and the claim must move to Rocq verification per the standing project
rule; at 96/98 the machine stays above that layer and every recorded
campaign count remains directly simulable.

-----------------------------------------------------------------------
2026-11-03  MINIMISATION PUSH round 2: 96/98 -> 86/89 (all gates green)
-----------------------------------------------------------------------
Five behaviour-preserving fusions, each verified step-for-step by the
full battery plus two extra gate-2 seeds not recorded as part of the
official battery (below):

1. The ABS top-pop erasers (ABS_X1..X3) are move-for-move the cascade's
   unit erasers: one EA chain now serves both; ABS_E enters EA2, the
   unit pops erase via EA2/EA3/EA4 -> MSE. (-3)
2. The cascade's erase-on-return: RW4 became the hole loop (writes 0,
   keeps walking left over the pop holes) that erases the survivor's
   marks as met and restarts the measure; RW5/EA2 deleted. (-2)
3. The cascade's bottom-stop walk collapsed: SB1/SB3 deleted; SB2 now
   both keeps and steps right, SH1 turns back at the survivor's close. (-2)
4. ROI6/7/8 (the route C p0 home walk) fused to one blind left step:
   the empty dispatch's death IS the final move; decode of the erased
   region is (0, []). (-2)
5. ABS_P1 deleted (WAS writes the park mark and walks back right
   directly), and for sn=1 the whole route A park count chain drops
   (PWX1; the single mark is written by PWALK's own row). (-1, -1)

THE WALK-BACK FUSION (the 22-state quadruple WR_FS/WB_ABS/WR_A/WB_P plus
the BR walk home) is the next big lever and is DOCUMENTED AS BLOCKED on
this architecture: every candidate shared state carries rows whose
successor must route to exactly one case; the case is known only to the
families' own states; the campaign contract (the whole model move must
land before the rest) forbids deferring the family action past the
landing; and the tape carries no spare bit on this encoding (the park
region is the count, and any extra mark there corrupts it). The families
stay separate and are already at their bisimulation floor -- the checker
merges them as far as signatures allow.

Battery: exit 0, ALL OK -- sn=1: 86 states/153 rows (gate1 ok=43,
tier counts 9/14/20); sn=2: 89 states/159 rows (gate1 ok=231, tier
counts 30/65/136); gate 2 ALL OK on the recorded battery, plus 2 extra
seeds beyond it (600 starts x 4 moves seed 42; 600 x 6 seed 7): OK.
Honest counts: 86 / 89, down from 96/98 this turn, 102/106 at the
unified-odometer start.

-----------------------------------------------------------------------
2026-11-03  ROUND 3 (the full follow-up turn): 88/90 -> 82/84/86
-----------------------------------------------------------------------
Three workstreams; all gates green, battery exit 0 verified by capture.

A. THE SPEND FOLD (-4/-4): the fs spend (erase the park's leftmost
   mark) ran after the append and forced the SWT1/SWC/SWZ/SWX/SWP/SE
   cluster (a full leftward re-crossing of the grown chain).  The
   campaign contract fixes only the net landing, so the spend folded
   into the fs look arm: FSL walks left over the park, FSP erases the
   leftmost mark and enters the walk back; the post-erase park edge
   (p=1: erased at C0-3) resolves correctly in the walk's 3-deep test.
   The append's close write (SWT1) now rests IN on the new last mark
   in one hop (its bisim class merged with BRH2).  First run failed
   gate 2 with 67 unfaithful landings: PKD1 (the L4 look, a separate
   retainer after the rewire broke the PKB/PKD1 verbatim identity)
   still entered WR_FS1 without the spend; fixed.
B. THE PARK-EXTENSION TURN MERGE (-0/-1): the sn>=2 route A extension
   wrote its last mark then turned back via a no-write state; the
   write-plus-turn now live in one state, and the whole route A
   extension and route C growth chains were parameterised by sn.
C. SN=3 SUPPORT (new everywhere): build_table(3) runs clean raw:
   86 states/152 rows, gate 1 census
   2418 landings 0 bad, tiers 184/557/1677 model-equal, gate 2 ALL
   OK, adversarial 3000 starts ALL OK, extra seeds (42: 600x4,
   7: 600x6) OK.  sn is no longer capped at 2.

D. THE MERGE HUNT (tools/eps1_mergehunt.py, new): proves the shipped
   table sits at its bisimulation floor (every state its own class,
   builds 1-3); the trace audit flags dead defensive rows (28-33 per
   build; the .1 arms of the append chain etc.); the pair report
   quantifies the walk-wall: 323-376 state pairs differ only in
   successor rows = one fork problem away each.  The two useful
   pairs it surfaced (a raw landing position insight) fed A and B.

E. THE ADVERSARIAL BATTERY (tools/eps1_adversarial.py, new): deep
   unit stacks (cascade chains, depth to 12), mixed deep chains,
   park 0..5; sn 1/2: 8000 starts each ALL OK; sn=3: 3000 ALL OK;
   sequential 3-6 campaigns per start with strict landings.

F. THE WALK WALL, now fully documented (EPS1_WALKWALL.md): the
   walk-back families cannot fuse without a positionally-placed case
   bit; every variant of the flag-cell scheme fails on positions
   (the flag cell lies far right of every writable launch position;
   a shared walker cannot decide what to write); reordering beat
   fusion this round (A).  Next real lever would be a taped encoding
   change (multi-track / self-delimiting runs) at the cost of
   re-proving decode + the f_ordinal Rocq obligation - parked.

Honest counts: 82/84 (builds 1/2), 86 (build 3, new). Down from
96/98 at the start of the day, 102/106 at the unified-odometer start.
Battery: exit 0, ALL OK; sn=1 82 states/144 rows (gate1 ok=43,
9/14/20); sn=2 84/148 (ok=231, 30/65/136); sn=3 86 states, census
2418, tiers 184/557/1677.

-----------------------------------------------------------------------
2026-11-03  ROUND 4: THE OBSERVED-CONTEXT MERGE HUNT: 82/84/86 -> 74/75/79
-----------------------------------------------------------------------
New tool: tools/eps1_contextmin.py.  The plain bisimulation floor kept
states separate whose rows differ on symbols the states are never
entered on.  The tool fires the whole corpus of record (the census
pre-step states, 1500 gate-2 style randoms, an EXHAUSTIVE small-region
sweep p<=2, chain length<=4, and 2500 adversarial starts) with an
instrumented campaign recording per state the set of symbols actually
read, then greedily applies merges: redirect Y's predecessors to X
whenever X's rows agree with Y's on every symbol Y ever fires on.
Every applied merge is judged live by a gate screen (census tiers 1-2,
250 randoms x 4 moves, tiers 1-2) and minimise_table re-folds
reachability + bisim after each; after the last merge the corpus data
is re-mined and the hunt confirmed fixpoint (0 further merges).

Haul (baked into build_table as CONTEXT_MERGES, applied in order with
minimise between each; battery of record re-validates the exact
composition):
  sn=1: 82 -> 74 via BRQ->WB_P2, EA2->RW4, M2->M4, RAW3->GP,
        ROI6->BRH2, BRZ->WB_P1, ROI5->BRH1, BR->WBX2
  sn=2: 85 -> 75 (the same 7 plus RAW2->GP and RAW->GP)
  sn=3: 86 -> 79 (7 merges; the RAW pair stays: sn=3's growth chain
        reads differently)
The best structural merges: the whole BR walk-home network (BR, BRZ,
BRQ and both ROI terminals) fused into the walk-back family and the
cascade/append networks it feeds; EA2 folded into RW4 (the cascade
erase+return); M2 into M4 (the L2 dispatch step reuses L4's).

Validation on the baked tables: python tools/eps1_odi.py exit 0
(sn=1: 74 states/131 rows census ok=43 bad=0; sn=2: 75/134 ok=231
bad=0); sn=3 build direct: 79 states, census 2418 landings 0 bad,
tiers 184/557/1677 OK; extra seeds 42 (600x4) and 7 (600x6) all OK
on builds 1-3; the adversarial battery 5000 deep starts per build
ALL OK (15k total, up to 6 campaigns each); merge-hunt on the new
tables: still a plain-bisim floor (all classes singletons) with
21-23 dead defensive rows and 263 fork-problem pairs at sn=1 - the
tables now sit BELOW the plain bisim floor via observed-context
equivalence, which is exactly what the pair report predicted.

Honest counts of record: 74 / 75 / 79.  Down from 102/106 at the
unified-odometer start, 82/84/86 after round 3.

-----------------------------------------------------------------------
2026-11-03  ROUND 5: UNDER-THE-67-PRESSURE: 74/75/79 -> 71/72/76
-----------------------------------------------------------------------
Two sound structural rewires + the full re-hunt, each battery-verified:

A. THE APW SELF-LOOP CROSSER (-1): the old APW1+APW2 pair (one
   crossing each) folded into a single self-looping crosser: 0 keeps
   bridging right (the 2nd-to-last mark, the new close hole), 1 is
   impossible there, 1 keeps riding right; the handoff lands the write
   chain at the old close cell.  APW1 = {0: (0,R,A{sn+3}), 1: (1,R,APW1)}.
B. THE ROUTE-C CROSser-ERASER (-2): ROI1+ROI2+ROI3 (two zero crossings
   plus a blind erase) collapsed into one state: 0 keeps crossing right,
   1 erases and hands off to ROI4's erase.  The whole p0 route-C erase
   run shrank from 5 states to 3.
C. SN=1 FOLDS THAT PROVED UNSOUND - DOCUMENTED CHANGES: an IN 0-row
   dispatch for the append's close-rest worked on builds 2/3 in
   isolation but BROKE BUILD 1 (the fs append creates a fresh top run
   of exactly sn+3 marks: for sn=1 that is L=4, and the shifted
   dispatch would miscall it as >= 5), and on builds 2/3 it disabled
   the ROI5->BRH2 merge, costing more than the SWT1 state it saved.
   REVERTED; the shape is documented above the IN rows.

D. RE-HUNT AFTER EACH REWIRE: the observed-context pass re-found the
   same battery-validated merge lists (7/8/6 per build), and a widened
   corpus (18,465 starts: census + 1500 gate-2 style randoms + the
   exhaustive small-region sweep p<=3 len<=5 + 4000 adversarial starts)
   confirmed the FIXPOINT: 0 further merges on any build.

Honest counts of record: 71 / 72 / 76 (builds sn=1/2/3).  Battery:
exit 0 ALL OK (sn=1 census ok=43 bad=0 rows=128; sn=2 ok=231 bad=0
rows=131); extra seeds 42 and 7 (600 each) all OK on all builds; the
adversarial battery 5000 deep starts per build ALL OK (15k total);
the context-min hunt = fixpoint at two corpus widths.

THE 67 TARGET: NOT REACHED ON sn=1 (71 vs the asked <=66) - honest
report.  Remaining levers by size: the walk-back landing tails and the
0-counter trio states sit at their 2-0-counting floor (the fork
problem, EPS1_WALKWALL.md); the append chain is sn+3 irreducible
write-states plus a minimal crossing; the dispatch D-chain is 4
one-bit tests by construction.  The only lever left that could clear
the remaining ~5 states is a TAPE-LAYOUT change (e.g. moving the p
look into the dispatch zone or a right-anchored park), which rewrites
the machine's whole geography and re-proves decode + the Rocq
obligations - a false economy at this scale unless the layer-table
comparison specifically demands it.

-----------------------------------------------------------------------
2026-11-03  ROUND 6: INDEPENDENT AUDIT OF THE CLAIMED 39-STATE
"TRANSCENDING f_eps1(3)" TM (Gemini unverified claim, user-requested)
-----------------------------------------------------------------------
Saved the claimant's script verbatim as tools/verify_epsilon1_tm.py and
built a fully independent harness tools/eps1_verify_gemini39.py (own TM
interpreter, boot decode, macro-step equivalence, ordinal-valuation
strict-decrease check).  FINDINGS, in order of impact:

1.  THE MACHINE NEVER PAST THE BOOTLOADER: run from blank 0^inf at A
    (bbchallenge/Marburg convention), the A/B/C train is a closed
    rightward runner and C's read-0 arm (1,L,D) is never taken: the
    cycle A(0)->1R,B  B(0)->1L,C  C(1)->0R,B (erases A's mark)  B(1)->1R,A
    repeats forever, drifting right at 3 cells per cycle, writing an
    alternating 1/0 track.  Step 400 trace confirms positions 171..200
    still looping A@odd,B@odd,C@even.  No D/E/F/... state is ever
    entered; NOTHING is ever seeded; the machine does not halt and has
    no trajectory at all.  The claimed 39-state eps1 machine is dead at
    its first move-group.

2.  THE ATTACHED SCRIPT NEVER RUNS THE MACHINE: its three "verifications"
    are (a) a syntactic table-completeness audit (passes; 39 states,
    78 transitions), (b) a pure-python reference rewriter step, and
    (c) a HARDCODED -prose trajectory (macro-step 0/1 strings) that is
    merely echoed, never produced by any execution.  Not one of the 78
    transitions is exercised by their harness.

3.  DEAD STATE G: G has no incoming transition from any state, so even
    the intended (but broken) boot flow could never reach it - 38 usable
    states at best, not 39.

4.  (context, not machine-level) their section-5 induction proves the
    wrong statement for successors: N(beta+1, n) = N(beta, n+1) >=
    f_beta(n+1) is claimed, but f_{beta+1}(n) = f_beta^{n+1}(n) requires
    n+1 COMPOSED iterations, which their successor bullet never
    performs; the base case already shows N(1,n) = n+1 < f_1(n) = 2n+1.

VERDICT: NOT VERIFIED - refuted at G1.  The state count, the eps1 logics,
the laver-table context - none of it matters: this specific 39-state
table, as printed in the chat and in the attachment, is a 4-step-cycle
tape scribbler, not an f_eps1 machine.  No amount of later cleanup or
re-transcription (fixed C-arm, reachable G, working boot, etc.) has been
attempted here - the table as PROVIDED fails.

-----------------------------------------------------------------------
2026-11-04  ROUND 7: THE FORK WALL RE-CONFIRMED; GATE 3 DEEPENED 6x
-----------------------------------------------------------------------
While the champions turn ran (recorded before this entry), the eps1_odi
machine itself got two pieces of work, both battery-verified:

A. THE MERGE HUNT AT sn=1 IS A CONFIRMED FIXPOINT ACROSS ALL THREE
   MEASURES.  eps1_mergehunt re-run on the 71-state build: the bisim
   partition is all-singleton; the trace audit fires 110 of 128 rows
   (18 dead rows, dominated by the append .1 arms and the walk-back
   landing tails -- kept as the deep-pops safety net, unchanged); and
   the pair report finds 241 of 2485 pairs separated ONLY by successor
   rows, of which the closable 1-row families are ABS_E/DECF/EA3/EA4
   (all "erase on reading 1", successors differ by campaign), the CM
   count chain CM1/CM2/CM4, D3/D5, D5/WAE/WAZB, and FSL/PKB -- every
   one is the fork problem (the case bit lives in the successor, not
   the tape), matching EPS1_WALKWALL.md exactly.  No rewire attempted:
   the wall note stands.

B. GATE 3 DEPTH: tiers were verified 1..3; the frozen-model walk is
   cheap at every tier (2x per tier), so check_tiers now runs
   limit_t=7 BY DEFAULT and the whole battery still exits 0 ALL OK:
   sn=1 tiers 4..7 = 27/35/44/54 model moves; sn=2 tiers 4..7 =
   279/566/1141/2292.  sn=3 checked in the same session beyond the
   main battery: tiers 4..6 = 5038/15122/45375 model moves, bad=0,
   2.1 s.  Deepest verified campaign-to-model agreement is now 45 375
   model moves (sn=3 tier 6), up from 1 677 (sn=3 tier 3) at the last
   record -- 27x deeper, all campaign landings value-faithful, all
   halting counts model-exact.  State counts of record unchanged:
   71 / 72 / 76 (sn=1/2/3); the <=67 lever is still the parked
   tape-layout change (HANDOFF round 5 tail), nothing re-opened.

-----------------------------------------------------------------------
2026-11-04  ROUND 9: THE RETURN-WALKER MERGE ATTEMPT (the parked
  >=67-to-71 lever, run and blocked by the fork wall): reverted green.
-----------------------------------------------------------------------
The round-5 parked lever (a layout rewrite to push sn=1 below 67) got
its first concrete tranche: merging the three RIGHT-RETURN walkers
焉 the route-A park-extension return, the fs-spend/absorb return, and
the absorb rewrite return (the WR_A / WR_FS / WB_ABS trios).  Their
front and cross rows are pair-identical rides ((1,R,self) and
(0,R,cross#2)); the pair-tests differ only in the 0-arm lander exit
(RAW / DECF / ABS_E).  FINDING: the fork problem re-appears at the
cross state.  Each crosser (WR_A2 / WR_FS2 / WB_ABS2) has a 0-arm
that disambiguates INTO the family-specific pair-test, so the trio
cannot be shared without a token, and the free cells of the tape sit
past the terminator, which the return walk never reaches (the walk
stopped at the 00 test before them).  The partial edit broke the
CONTEXT_MERGES bookkeeping (a stale pair) and the battery, so it was
reverted in place; the machine is back green: 71 / 72 / 76 states
(sn=1/2/3), the battery exits 0 ALL OK (tiers 1..7), and the honest
census/landings are unchanged.  The parked layout lever is now
concretely blocked by the fork wall, not merely "probably blocked".
This freezes the 71 / 72 / 76 counts of record as a fixpoint under
all three merge hunts (bisimulation, observed-context, row-pair).

-----------------------------------------------------------------------
2026-11-04  BB(16..29) CHAMPIONS RE-CHECKED AGAINST THE WIKI TABLE
  (Champions page rev 10183, fetched 2026-11-04) and updated:
* Source of record: wiki.bbchallenge.org/wiki/Champions (2-symbol table).
  The user supplied a screenshot of the same table; the wiki text was used
  to transcribe exactly (the screenshot misrenders superscripts/subscripts
  at small sizes; one token, the BB(20) K-row, was unreadable in it and
  resolved by the wiki as 1RL1RE).
* Claim notation resolved by structural comparison with this file's
  already-verified BB(13)/(14) rows: the wiki flatten f-w+K-m-(x) means
  f_{omega+K} iterated m times (BB(13) "fw+26" = (f_{w+2})^6).  Result:
  BB(17) = (f_{w+3})^3(9), BB(18) = (f_{w+3})^4(9), BB(19) = (f_{w+7})^2(5),
  BB(20) = f_{w*2}((f_{w+2})^2(f_10(2))).
* WRITTEN into championsreal.txt:
  - BB(17): own row replacing "inherited from BB(16)" (Ketchersid/
    Claude/Gemini 11/2026, claimed; BB(16) body, N/O/P tail respliced).
  - BB(18): new row (f_{w+3})^4(9); the old f_{w+3}(114) row kept as
    [superseded] with its 10/2026 commentary verbatim plus a supersede
    note (the iterate count dominates the single step).
  - BB(19): own row (Jacobzheng 2026, not independently verified; new
    body, all 19 states used) replacing "inherited from BB(18)".
  - BB(20): new row f_{w*2}(...) (Jacobzheng); the old f_{w+6}^2(4)
    1RR-start machine kept as [superseded].
  - BB(16): CONFIRMED VERBATIM (no edit; the screenshot 0RG0LO is the
    wiki 0RO0LO misrendered).
  - BB(21): machine already present and verbatim-confirmed; note added
    that the wiki flatten "fw22(4^^341)" = f_{w^2}^2(4^^341), matching
    the row's (f_omega^2)^2 reading and the earlier correction story.
  - BB(29): note added -- the champions cell shows only the footnote [1]
    (a Discord link), so the machine text is still not public on the page.
* LOCAL CHECKS (tools/bbmulti.py parse+run, blank tape, budget 3M steps
  to match the file convention; every machine all rows defined, a single
  halt row, zero dangling next-state refs):
  - BB(17): 17x2, 34/34 rows, halt (Q,0); no halt@3M, score 3,337,
    16/17 states used, 10@38 100@3,001 1000@121,818.
  - BB(18): 18x2, 36/36, halt (R,1); no halt@3M, score 3,337, 16/18
    used, milestones identical to BB(17) in budget (the 4th-iterate
    level shows only past 3M).
  - BB(19): 19x2, 38/38, halt (R,0); no halt@3M, score 3,837, 19/19
    used, 10@50 100@2,372 1000@171,912.
  - BB(20): 20x2, 40/40, halt (R,0); no halt@3M, score 3,776, 20/20
    used, 10@69 100@1,743 1000@202,035.
* Ordering assertions between rows (e.g. (f_{w+7})^2(5) vs (f_{w+3})^4(9))
  are the table's own, recorded not asserted, per the file's standing rule.

-----------------------------------------------------------------------
2026-11-04  ROUND 10: THE U2 LAYOUT REWRITE (super epsilons flagging: the
  parked lever attempted again) -- BLOCKED BY ARGUMENT, DRAFTS HALTED.
-----------------------------------------------------------------------
The round-5 parked lever (a tape-layout rewrite) was attempted once more
under the super-epsilons flag.  Plan: the park visit placed MID-campaign
(every arm = [the p-independent E-zone part] -> [the shared left rider
to the park] -> [the park part] -> [the right return] -> [the push part]
-> BR home), motivated by deleting the per-arm walk-back families
(WBX/WB_P, WR_FS, WB_ABS, WR_A, ~21 states on sn=1) and the per-route
walk-to-look clones.  Model semantics re-derived exactly first (the
fixed-seed step: fs = dec-top-then-push NUM(sn+1) of sn+3 marks with
p -= 1; pred = top c -> c-1 (c=1 -> the empty/halt site); the ATOM limit
arm = widen 1->3 + p += sn; the head-empty rewrite = the L3-m1 p>=1 fs
landing; int-1 chains are never canonical (the model asserts)).  Draft
built at tools/eps1_u2.py before any gate ran.

BLOCKED BY ARGUMENT.  Reading the actual post-minimize rows (the
71-state dump regenerated this turn): the per-family X3/X4/X5 climb
states are byte-identical shapes differing only in terminal successor
(IN / DECF / ABS_E / RAW), the whole-battery hunt of record stays at
the fixpoint, AND the rewrite's own returns fork identically: after a
park visit the walk right must land differently per case, and the case
bit cannot be carried to the landing position on this single-track 2-
symbol tape.  The concrete dead ends, now argued not just probed:
  - the sep cells are load-bearing 00 (the decode park count stops on
    the first non-mark left of C0-3);
  - the terminator pair's cells must stay 0 (the close + the chain
    end);
  - end+1 is a free blank but sits PAST the first 00 pair, which every
    return's ride uses as its turn signal -- the walk never reads past
    the trip point before turning;
  - the sentinel proposal (a non-zero cell at the chain end) is eaten
    by decode_tape's run counting: the cell right of an interior close
    must be 0 or the run detection misreads it as the next entry.
So the layout lever is doubly dead (round 9 probes it on the shipped
tables; round 10 argues it for the redesign).  The U2 draft is kept in
tools/eps1_u2.py as the halted design record, not a bearing build.
The honest counts stay 71 / 72 / 76; no battery state changed and no
run regressed.

-----------------------------------------------------------------------
2026-11-04  ROUND 11: HOLDOUT FILE SAVED; PLAN-STATE RE-SURFACED.
-----------------------------------------------------------------------
The user provided 37 BB(2,5) "Rocq holdout" machines; saved verbatim as
bb2x5_holdouts37.txt.  No mechanism currently connects them to the
eps1 build; recorded as data of the separate Rocq/BB(5)-domain program.

Re-surfaced the plan documents for the under-50 question: EPS1_SUPER.md
(the <=40 tape-as-term design, model-level green in tools/eps1_super.py,
NO 2-symbol table exists), EPS1_35_STATES.md (33+28 build sits below
eps_1), EPS1_WALKWALL.md (the fusion-wall case analysis).  Verdict
stands: odi 71 is the fork-wall fixpoint of this encoding; the only
recorded route to <=50 is the SUPER local-rewrite construction item,
unbuilt, no earned state count.  <50 remains a target, not a promise.

-----------------------------------------------------------------------
2026-11-04  ROUND 12: champion batch #3 intake + GEMINI 48-STATE f_eps1
  CLAIM AUDIT (verdict: REAL table, REAL verified fragments, TWO
  COMPILE DEFECTS, and the headline bound is NOT PUT THROUGH).
-----------------------------------------------------------------------
1. CHAMPIONS (ADD).  loader3229's Oct 29 - Nov 3 batch #3 (22 machines,
   BB(3,7)..BB(11,4), two "BBi" champion notes, nickdrozd-confirmed
   #2 for BBi(8)) appended verbatim to championsReal.txt with claims in
   his words only (22 rows, "predicted, not formal"/"informal" marked).
   tools/bbmulti.py checks (driver _intake3229b.py): all 22 parse at
   size, NONE halts in 2 000 000 blank-tape steps, states visited
   n/n except 6/7 in the BB(7,5) iterated row; scores 1 436..1 629 at
   2M; milestones 1000@643k..1 223k.  The checked numbers are appended
   to championsReal.txt; the levels remain the claimant's.

2. GEMINI 48-STATE CLAIM ("48 states, 2 symbols, transcends f_eps1(3),
   verified in epsilon1_tm.v", file received in Downloads).  Audit:
   a) TABLE: parsed from the .v source directly (not any chat render),
      48 states / 96 rows, well-formed (tools/_check_gem48.py).
   b) INDEPENDENT SIMULATION reproduces EVERY computational fragment
      the file states: boot_18, boot_20, boot_352/702/1641 (worm
      configs decoded structurally: (n, pairs) exactly), the boot
      selector S48[0] fires exactly once at step 248 as claimed, all
      five campaign lemmas (5-step halt, 139, 135, 284, 350) exact,
      and head/tape of the halting calibration config match.
   c) LOCAL Rocq 9.1.0 COMPILE (rocq/gemini_epsilon1_tm_48s.v): DOES
      NOT COMPILE AS SHIPPED.  halts_on_base_worm: "exists 152" is
      FALSE -- step_tm 152 ... = None: the machine halts at 148 with
      the same final config (head 4, tape [-1;0;1]); my simulation and
      coqc AGREE via the divergence (sim: halt at 148; Rocq: unify
      failure None-vs-Some).  Replacing "exists 152%nat" by "exists
      148%nat" (= the simulation-verified value) makes that lemma
      compile (rocq/gemini_epsilon1_tm_48s_fix.v).  The headline
      runtime_gt_f_eps1_3 then FAILS: its lia proof hits "Cannot find
      witness" (line 390 on the fix copy).  The inequality itself is
      trivially true by hand (each level adds >= 1, chain of 7 gives
      bound >= N0 + 6, so 1641 + bound > N0), but the shipped tactic
      term does not line up on Rocq 9.1.0: needs a proof-engineering
      repair, not a semantic one.  NOT CLAIMED GREEN.
   d) THE STRUCTURAL GAP (this program's bar, round 10/11 language):
      NOTHING in the file ties the blank-tape machine's RUNNING time
      to worm_eval_lower_bound -- that evaluator is an arithmetic
      estimate function, and runtime_gt_f_eps1_3 is an inequality
      between two FGH formulae; no theorem states the machine's
      halting (or non-halting) exceeds any bound.  Also no proof the
      blank run halts at all.  So "48 states transcending f_eps1(3)"
      is a GLOSS over verified fragments, exactly the shape our
      standing rule (halt under f_ordinal(n), Rocq-verified) exists
      for.  2 000 000 SIM steps: no halt, 1242 cells at head 418 --
      the long regime is entered, the bound is not put through.
   e) files: the .v verbatim at rocq/gemini_epsilon1_tm_48s.v, the
      corrected compile at rocq/gemini_epsilon1_tm_48s_fix.v (+ its
      _fix_compile.log), the checker at tools/_check_gem48.py, the
      champion driver at _intake3229b.py.

3. eps1: u3 (run-code V1) build still parked un-green; next session
   resumes the fs/pred fork wiring (the T0..T6 count forks) and its
   battery.  NOTE: a working 48-state precedent now exists to cross-
   check framing decisions against (their worm layout is a THIRD
   world between odi's runs and super's entries).

-----------------------------------------------------------------------
2026-11-04  ROUND 12b: GEMINI'S REPAIRED 48-STATE FILE (epsilon1_tm(1).v
  in Downloads) -- ARCHIVED, THREE MORE DEFECTS FOUND AND FIXED, the
  file now COMPILES CLEAN (exit 0, all 13 Print Assumptions = "Closed
  under the global context"; mantra Rocq 9.1.0, direct coqc.exe).
-----------------------------------------------------------------------
Machine UNCHANGED: trans table identical to round-12 v1; checker
  (now claim-reading, not hardcoded) reproduces ALL milestones incl.
  halts_on_base_worm at 148 (head 4, tape [-1;0;1]).
What the repair ADDS (real length): step_tm_add / step_tm_halt_none /
  step_tm_none_add / step_tm_split (runtime-composition lemmas),
  cfg_worm_state, blank_halt_decomposes_at_1641 (any halting blank run
  must pass through the step-1641 seed config), the worm_campaign_chain
  INDUCTIVE + soundness theorem (a chain witnesses BOTH a concrete
  step_tm execution AND the valuation bound), the 148-step base-worm
  witness, and rewritten headline/bridge theorems.  152->148 fixed.
THREE NEW DEFECTS in the repaired proof (all fixed in our v2_fix):
  1) f_eps0_succ_ge_S: lia "Cannot find witness" -- goal seed term
     iter_nat f_eps0 (S n) n is an opaque atom vs hypotheses; ONE
     cbn [iter_nat]. before lia closes it.  (This was really the
     round-12 line-390 failure; v1 never reached the headline lemma.)
  2) worm_eval_lower_bound_mono: induction as-pattern [|[a [|b']] IHw]
     binds the TAIL LIST to IHw, not the induction hypothesis -- latent
     error surfaced only once (1) was fixed.  Rewrote with correct
     induction [| [a b] w IHw] + explicit destruct b.
  3) worm_eval_W_step_1641_ge_f_eps1_3: the shipped change ... with
     (... (f_eps1 3)) form does NOT TERMINATE: conversion must compare
     the numeral 3 with f_eps1 3, whose value is astronomically large
     (isolated with minimum probes; rev-composition alone is fine).
     Rebuilt structurally: new worm_eval_comp composition law
     (E (w1++w2) n = E w2 (E w1 n)), two reflexivity shape lemmas for
     the 1641 worm, growth chain (tower/seq/succ _ge_S) + lia.
ENV NOTE: rocq c (wrapper) DEADLOCKS in this shell (idle zero-CPU
  processes, no output); use C:\Rocq-Platform~9.1~2026.01in\coqc.exe
  directly; compile "hangs" = check the running command before retry.
HONEST RECORD (the standing bar): Theorem 3 (blank_halting_run_
  exceeds_f_eps1_3) and its corollary are CONDITIONAL -- they
  quantify over a hurd_campaign_chain from the step-1641 seed; the
  only provided witness is the 148-step base-worm calibration run,
  which does NOT exceed f_eps1(3).  No chain witness for the seed,
  and no proof the blank run halts (sim: no halt in 2 000 000 steps,
  tape 1242 cells over head 418).  So the file now proves the
  bridge SHAPE (chain => halting run > f_eps1(3)) and the halt
  LOCALS (boot + campaign fragments + 148), but the transcendence
  REMAINS UNWITNESSED for the 48-state seed.  Files: rocq/
  gemini_epsilon1_tm_48s_v2.v (verbatim), _v2_fix.v (compiling),
  _v2_fix_compile.log, tools/_check_gem48.py (v2-aware),
  _check_gem48_v2fix.txt.

-----------------------------------------------------------------------
2026-11-04  ROUND 13: gem48 POSTED publicly (Discord, with the four
  attachments staged in eps1machineattach/) + state-reduction compiler
  ATTEMPTED AND REFUTED.
1. DISCORD POST done; claim stated as informal (T not proven).
2. COMPILER family FAILED: tag-on-departure (n,2) -> (ceil(n/g), 2g).
   Bisim failed at step 1 for every g (compound read member "S02" at
   cell -1 while M was at "S46"): the write lands on the DEPARTURE
   cell, not the landing cell, so revisits read STALE tags and every
   rewrite re-anchors on the stale member (error compounds). User
   refutation: a 1-state machine keeps state only in the symbol it just
   wrote - one cell behind the head - so revisits outrun it ("1,96 is
   bad cause A1 row can only be re-entered one-step-stale"). The whole
   cx-family pushed to the trash; tools/_gem48_compile.py kept with a
   REJECTED banner as the lesson. LESSON: (n,2) -> (ceil(n/2), 4) folklore
   fails for GENERIC machines; real state reduction needs either
   machine-specific structure analysis or a multi-cell state FIELD
   compiled the way our eps1 counters work (slow but honest).
3. gem48 entered championsReal.txt (ADD, informal-marked).

-----------------------------------------------------------------------
2026-11-04  ROUND 13b: COMPILER WALL PROVEN; STRUCTURE SCAN NEGATIVE.
-----------------------------------------------------------------------
1. gem48 STRUCTURE SCAN (tools/_gem48_scan.py): NO exact twin rows,
   NO merge-closed groups (rows equal up to merged next-classes), so
   the only zero-risk mechanical reductions simply do not exist for
   this machine. Two states halt-target total.
2. THE WALL (why generic (n,m) -> (n'<n, k>m) with small slowdowns
   fails; derived and checked exhaustively today):
   W1 (write-at-departure): a TM writes the cell it LEAVES, so any
     "state tag on cells" scheme reads stale tags at revisits -- the
     user's one-state refutation is the sharpest form (state can only
     be one cell behind; revisits outrun it).
   W2 (per-edge registers DO keep the q-at-landing fresh -- written
     at every crossing -- but that only solves the LOOKUP side.
   W3 (payload-delivery): the lookup computes (w, d, q'); q' must
     be WRITTEN at the register whose next read is the NEXT
     transition (the exit register). Delivering it there requires
     the compound state to carry q' (>= n states, no reduction) or
     to read it at the exit register from its own content (stale) --
     multi-visit pipelines cannot move the payload either, because
     reads only ever return the cell under the head. Payload travel
     through a single-cell read port is impossible without paying
     >= n of compound-state somewhere.
   W4 (multi-cell fields do not help): decoding a t-cell state field
     trit-by-trit puts the leaf-level compound state count at 2^t,
     i.e. >= n again; a tape-stored TRANSITION TABLE (lookup by
     index) is a universal-machine-grade project, not a compiler.
   CONCLUSION: honest sub-n state reduction needs MACHINE-SPECIFIC
     structure (campaign-level analysis of gem48), not a generic
     transformation. The folklore "(n,2) <= (n/2,4)" holds only for
     machines with matching structure (e.g. ones already storing
     data on their tape in a tag-friendly discipline).
3. ABIYO candidates recorded: campaign-level gem48 structure analysis,
   or the eps1_u3 push (standing goal).

-----------------------------------------------------------------------
2026-11-04  ROUND 14: U3 RESUME WORK -- THE DOCUMENTED LAYOUT PROVEN
  SELF-BROKEN; THE FORK WALL RE-DERIVED INDEPENDENTLY; PLAN RE-POINTED.
-----------------------------------------------------------------------
1. U3 fix first applied: num_of was referenced unimported
   (C.num_of wired).  Result: the CODEC layer is green (200
   round-trips OK).  The faithful layer then dies at the very first
   campaign: N3 lands on run1's first mark with no 1-row (the
   walk-state misalignment of N1..N3).  That is only the surfacing
   bug.  Under it: THE DOCUMENTED LAYOUT IS SELF-BROKEN.
2. THE LAYOUT DEATH CERTIFICATE (exact trace, '110011000'-class
   tapes): u3's format is [1^p] 00 [runs] with a = the pair's left
   cell and the fs spend "at a-1" (the park block's RIGHTMOST mark).
   After the spend the string is 1^(p-1) + 000 + runs: the decoder
   read_tape counts the leading 1s left-to-right and demands the
   FIRST 00 immediately after the block, so it reads the pair at
   (a-1, a) and then the run scan starts at a+1 = the old pair's
   right cell = 0: it decodes the EMPTY chain.  The spend silently
   erases the chain from the decode's point of view.  Proven, not
   probed: ANY layout whose p-block abuts a 00 pair with the spend
   at the abutting cell has this failure; the fix of record is
   odi's convention (park 1s anchored AT C0-3, count rightward from
   the fixed end, spend = the LEFTMOST mark, grow = one cell left),
   which is hole-free and decode-clean for every mix of spends and
   grows.
3. THE FORK WALL, re-derived independently from round  (2026-11-04
   assistant session, consistent with round 10 and the merge hunts):
     W1 write-at-departure staleness (the user's one-state argument);
     W2 per-edge registers DO keep the q-at-landing fresh, but ...
     W3 the payload q' cannot be carried to the register the NEXT
        transition reads: the state would need >= n states again, the
        exit register's old content is stale, and multi-visit
        pipelines cannot move a payload through a single read port;
     W4 multi-cell state fields decode to >= n leaf states, so
        nothing is saved.  For the eps1 run-code context this is
        exactly round 10's verdict: every p-split arm's return
        forks, and no tape cell the walk passes carries the case
        bit (the 00 separators are load-bearing, the terminator
        pair's cells must stay 0, end+1 is past every ride's turn
        signal, and a sentinel at the chain end misreads as the next
        entry).  CONSEQUENCE: a faithful u3 rebuild on odi's
        conventions lands in the same banked-fork band as odi
        (71/72/76 is the fork-wall fixpoint of THIS encoding).
     So u3-as-documented is closed honestly: no rebuild of the
     documented layout will be green AND sub-71.
4. PLAN OF RECORD RE-SURFACED (unchanged from round 11, now with
   round 13b/14 wall-work behind it): the only recorded route to <=50
   is the SUPER construction: tools/eps1_super.py is ALL OK at model
   level on the user's 3.14 (re-confirmed this session), the ledger
   phases are (reader/park <= 10, pred <= 12, fs-limit <= 12, setup
   + halt <= 6), and the construction item = the LOCAL-REWRITE
   realization of the three moves (head-stepping, byte-local edits
   on the entry codec), then the 2-symbol table, then the gate
   batteries.  The fs fixed-seed-vs-bumping-index gate question and
   the startup unroll cost stay open ledger items.
   eps1_odi.py / eps1_chain.py untouched all session; the batteries
   of record are safe.

-----------------------------------------------------------------------
2026-11-04  ROUND 15: GEM48 COMPILE RE-TASKED BY THE USER; RESEARCH
  ROUND DONE; THE ROUND-13/13B "FOLKLORE" ATTRIBUTION CORRECTED;
  THE SHUTTLE-INTERPRETER ROUTE OPENED.
-----------------------------------------------------------------------
1. CONTEXT CORRECTION: this session's context had rolled back past
   the gem48 arc (rounds 12/12b/13: gem48 = 48-state 2-symbol eps1-
   level machine, audited, v2_fix compiles zero-axiom, morphett
   file verified, posted, championsReal.txt INFORMAL entry).  The
   user re-anchored: "we already got the epsilon 1 machine in 48
   states, its called gem48".  The standing <=50 goal is occupied
   by gem48 at the informal level.
2. USER RE-TASK: "compile that machine into lower states higher
   symbols" (gem48 -> fewer states, larger alphabet).  This turn
   runs two researcher-web agents on the known state-reduction
   constructions (bbchallenge wiki/zones: Michel ha/beh/adv,
   sligocki, Cryptids, the BB(5) paper, the small-UTM survey).
3. RESEARCH VERDICTS (committed with URLs in the chat log):
   a) RETRACTION: the "(n,2) <= (ceil(n/2),4) folklore" recorded in
      round 13 is NOT a documented result anywhere in the sources
      read.  The only trivially proven bounds are the monotone
      ones (n,m) <= (n+1,m), (n,m) <= (n,m+1), and the
      instruction-count identity BBi(ab-1) >= BB(a,b)-1.  The
      round-13 CONCLUSION (no safe mechanical reduction; identical-
      row merges only; the scan found none) STANDS as a result
      about THIS machine table; the folklore citation does NOT.
   b) Shannon (1956, per the Wikipedia UTM article) established the
      state-symbol exchange in BOTH directions: 2 states with n
      symbols holding the same universality as m states with 2
      symbols.  Mechanism (folklore of his construction, not
      re-read): the simulated state is a BLOCK ON THE TAPE and the
      tiny fixed control SHUTTLES between the state block and the
      data (fetch-decode-execute).
   c) Stérin-Woods, arXiv:2107.12475: a clean modern worked
      compilation 5-state 4-symbol -> 15-state 2-symbol at
      LINEAR time per simulated step (proof by configuration
      induction).  This is the reverse axis (alphabet collapse,
      pay states) but the proof pattern is the model for ours.
   d) Neary-Woods survey arXiv:1110.2230: universality with fixed
      small state counts INDEPENDENT of the simulated machine:
      Rogozhin (2,18), Neary-Woods (15,2), Watanabe O(t^2) etc.,
      all with program-on-tape, marks read-then-restored, costs
      O(t^2) up to O(t^6).  The fetch-execute loop is exactly the
      mechanism our fork-wall=W3 argument rules out for CHEAP
      synchronous compilations -- and exactly the mechanism that
      makes the SHUTTLE family work at higher steady cost.
   e) Community twins (Michel): the 6-state 2-symbol Marxen-
      Buntrock champion and a 3-state 3-symbol Ligocki machine
      have identical Sigma = 95,524,079 with ~half the steps --
      empirical evidence that fewer states + more symbols is a
      REAL equivalence class, not folklore.
4. THE FORK WALL STANDS WHERE IT STOOD: W1-W4 kill state-tag and
   per-edge-register synchronous compilers; they do NOT kill the
   shuttle/fetch-execute family (the case bit walks to its reader
   instead of riding a port).  Round 13b's "only identical-row
   merges safe" must be amended: safe = for synchronous low-
   overhead compilations.  The honest surviving route to a gem48
   compile with fewer states:
     SHUTTLE-INTERPRETER SPEC (gem48x, target: states << 48):
     - tape: [state block (unary q-blocks, one marked current)]
       [head-position counter (unary, live)] [sim data cells];
     - per simulated step: walk right consuming one counter mark
       per data cell to the sim head; read b; walk back; read the
       row (w,d,next-q) from the current state block (b-selected
       half, mark-walk addressing); copy the next-q address marks
       with the two-pointer per-mark loop (NO count in the state);
       walk back out (dec/restore the counter by +/-1 = its own
       amortized mark budget); write w; move the sim head.
     - state budget = the phase set of the loops + small carried
       bits (b, w, d) only: target 25-45 states, k = 5-6 symbols,
       slowdown ~ O(position) per simulated step -> O(T^2) total;
       the transcendence T > f_eps1(3) claim only gets STRONGER
       under any monotone slowdown (conditional on the base claim,
       which stays INFORMAL for gem48 and for gem48x alike).
     - verification bar: byte-exact differential sim vs gem48 (the
       boots 18/20/352/702/1641, campaigns 5/135/139/284/350, the
       base-worm halt 148, 2M no-halt blank run), then the same
       honest INFORMAL record status.
5. NOT DONE YET: no gem48x table exists.  Next session starts the
   build: sim-level interpreter first (the loops in Python), then
   the 2..k-symbol table, then the differential battery.