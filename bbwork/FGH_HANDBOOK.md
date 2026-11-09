# FGH machines, dissected

### A working manual for reading, measuring and building 2-symbol Turing machines at transfinite levels of the fast-growing hierarchy

---

This file is about **how the machines in `championsReal.txt` are actually built**, read off their
transition tables and their tapes rather than off their claimed values. Every claimed value in
that ledger is a number somebody asserted; what follows separates three kinds of statement and
never lets one impersonate another.

| tag | meaning |
|---|---|
| **[claim]** | a value in `championsReal.txt`. Not verified here, often not verified anywhere ("claimed analysis ... never verified"). |
| **[measured]** | I parsed the 5-tuple string, normalised the start state, ran the machine on a blank tape, and report what happened. Reproducible with `tools/handbook_tables.py`. |
| **[proved]** | checked by Rocq 9.1, `Print Assumptions` reporting `Closed under the global context`. Only the four machines in `machines/` have anything proved about them. |

The measured window is **400 000 steps**, always from a blank tape, always with the start state
relabelled to 0 (free normalisation: renaming states changes nothing). Nothing here is a claim
that a machine has the level it is quoted with. The point is the opposite: to see what *shape*
sits under each quoted level and what the shapes have in common.

Section 1 fixes vocabulary, section 2 is the method, section 3 is the census, sections 4-7 take
the four families apart machine by machine, section 8 states the laws the census supports,
sections 9-10 turn that into theory and a construction kit for the ε/ζ/η target, section 11 is
the verification plan, section 12 is a log of things I asserted earlier in this project that
turned out to be wrong.

Appendix A is the measured table for all 21 machines, Appendix B every transition table of every
machine of 21 states or fewer (generated from the ledger's strings), Appendix C the transcribable
state patterns.

---

## 1. The object

### 1.1 Machines, tapes, and the three free normalisations

A 2-symbol machine is a partial map `δ : Q × {0,1} ⇀ {0,1} × {L,R} × Q`. The 5-tuple string
`1RB0RA_1LC1LF_...` lists, for each state in order, the two cells `read>write,dir,next`; `Z` or
`H` means halt. A cell `---` means the transition is undefined — reading it halts the machine.
Both conventions are used interchangeably in the ledger and in the machines here: a machine can
have several halt triggers at once.

Three normalisations are free and I apply them everywhere:

1. **Blank tape.** The tape starts all-`0` with the head at 0. A machine that needs a seed must
   write it itself; that is the boot phase. `BB(51)` is quoted with start state 30, everything
   else with start 0 — relabelling makes them comparable.
2. **State relabelling.** Any permutation of `Q` gives the same run. I relabel the start state
   to 0.
3. **Trimming.** Cells never read and states never entered do not exist as far as the run is
   concerned. Two ledger rows that differ only there behave identically (this is not the same as
   being the same table; see §4.3).

The two observables are `steps` (to halt, or to the end of the window) and `score` = the number
of `1`s on the tape at halt. A ledger row like "`> f_{w+1}((f_w)^4(6))`" is a lower bound on
**steps**. Score is usually smaller and much less studied. My own four machines are the other way
round: their scores are the hard-won number and their step counts are incidental.

### 1.2 What "level" is not

It is not a number on the tape, and it is not the size of the tape. It is not even a property of
the machine in isolation: it is a property of the machine's **descent structure**, i.e. of the
ranking function you can prove terminates the run.

Concretely, a run decomposes into *rounds*. A round is a stretch of steps that starts and ends at
the same phase of the tape's data structure, having transformed it. Write `T_i` for the tape at
the start of round `i`. If there is a function `ρ` from tapes to ordinals with

```
  ρ(T_{i+1}) < ρ(T_i)      for every round, and
  ρ(T) = 0                 only at the halting configuration,
```

then the run terminates, and the number of rounds is at most the length of the fundamental-
sequence descent from `ρ(T_0)`. The machine's *level* is the order type of the smallest such `ρ`
that works for its actual round structure. Nothing has to be written on the tape: `ρ` can be "the
multiset of block lengths, ordered lexicographically", a perfectly good ordinal notation living
in the analyst's head.

That is the single most important idea in this file, and it is what makes small machines at high
levels possible at all. A 19-state machine does not need to *represent* ε₀; it needs a round
structure whose descent is ε₀-shaped. The proof obligation then splits in two, and the halves are
independent:

* **dynamics layer** — "the run is a sequence of rounds" and "each round decreases `ρ`". Purely
  combinatorial, about tape layouts and local transitions.
* **value layer** — "a descent of length `L` from `ρ(T_0)` yields at least `N` ones / steps".
  This is where the fast-growing hierarchy appears, and where the ordinals live.

The ledger's claimed values are value-layer claims that skip the dynamics layer entirely. That is
why they can be enormous and still fit in a comment: nothing has been checked. My Rocq
development does the opposite: it checks the dynamics layer exhaustively for one specific run
(`vm_compute` over the actual steps) and states the value layer in terms of `tower`. Neither is a
proof of an FGH bound; §11 says what a real one needs.

### 1.3 The measure/expansion decomposition

Every machine in the census, without exception, has the same three-part round:

```
  SEEK      walk until a separator (or an end of block) is found
  EXPAND    write 1s into a region, for as long as the walk lasts
  BOOKKEEP  decide whether this was the last round; move to the next data field
```

The level is decided almost entirely by BOOKKEEP. SEEK and EXPAND are mechanical and cost the
same 2-3 states in every machine. BOOKKEEP is where a machine either decrements a block (level
ω), refills a fuel block from the output (level ω+1), pushes a new fuel block (level ω^ω), or
re-reads a block as a program (ε₀). This is measurable: the states carrying more than 5% of the
run are 2-4 SEEK/EXPAND states, and the BOOKKEEP states together carry 1-5% of the steps while
deciding 100% of the value (§8, L6).

---

## 2. Method

Everything in sections 3-8 comes from four instruments, 120 lines of Python in `tools/`. They are
crude on purpose: the point is to look at many machines the same way, not to analyse one deeply.

### 2.1 Parsing and role classification

`tools/extract.py` pulls `BB(n)` and `BB(n,m)` rows out of `championsReal.txt`, resolves the
alphabet size from the row label, and turns the 5-tuple string into a dict. It prefers the first
non-superseded row and skips rows marked `[superseded]`.

`analyse.classify` labels every state by what its two cells do:

* **write** — the state's job is to *produce* material: both cells write `1`, or it writes
  without moving back over the same neighbourhood.
* **sweep** — both cells move the head the same way: the state's job is to *travel*.
* **branch** — one cell goes left, the other right: the state's job is to *decide*, and it is the
  only place a `Z`/`---` halt can live.

The distinction is diagnostic rather than principled (a state that writes and travels at once is
classified by its dominant action), but it is stable and it separates the families cleanly. A
machine with **zero** write states is an interpreter: it never manufactures cells, only moves and
rewrites existing ones (§7).

### 2.2 Cycle extraction

`analyse.cycles` does a bounded BFS over the transition graph from each state, collecting short
return cycles. It is the cheapest way to see a round: `0-1-2-3` is a 4-phase round, `2-3-10-4-18`
is the 5-symbol engine's main loop, `2-3-9-4-17` its 7-symbol cousin.

### 2.3 Hot-state profiling

Run the machine for `N` steps, count visits per state, report the two or three states with the
largest share. This one number separates the design philosophies better than any other (§8, L1).

What it measures: visit counts are *steps*, so a state visited once per round but walked for a
million steps shows as hot, while a state visited a million times for one step each does not. That
is exactly what we want — where the time goes, not where the control flow goes.

### 2.4 Tape morphology

Run the machine, take a run-length encoding of the tape, and report `runs` (number of maximal
constant blocks), `max` (longest block), and the first 14 and last 4 runs. Reading a tape is the
skill this file is trying to teach, so here is the dictionary:

| pattern | reading |
|---|---|
| `1^a 0^b 1^c` | two numbers separated by a gap: a counter and a scratch area |
| `1^a 0 0 1^c` | two *fields*: the doubled blank is a separator (§10.2) |
| many runs of length 1-3 | a bit string: positional encoding, no field structure |
| `3^k 4 1^a 2^b` | a tagged record: `k` markers, a delimiter, two numeric fields |
| `1^a` alone | one counter; the machine is at most exponential |

The dictionary is descriptive, not normative: the same shape can serve several levels. What it
does pin down is the **addressing mode** — whether the machine finds a field by *counting runs*
(positional, needs states) or by *reading a marker* (direct, needs symbols).

### 2.5 What the instruments cannot see

A 400 000-step window on a machine whose claimed value is `f_ε0(10^352)` samples the boot phase
and nothing else. Every measured number here is therefore about *shape*, never about *scale*, and
the most misleading thing you can do with them is compare `ones` at 400k across machines and infer
a level ordering. §8 L2 shows the census refuting exactly that inference, and §4.3 shows the
ledger's own BB(8)/BB(9) pair agreeing to the step for 400 000 steps despite a four-iterate
difference in claimed value.

---

## 3. The census

Twenty-one rows, measured the same way. `w/s/b` is the role census (write/sweep/branch); `hot` is
the share of steps in the two most visited states; `runs`/`max` describe the tape at 400 000
steps. The quote column is the ledger's claim, reproduced without endorsement.

| machine | states | symbols | quote | w/s/b | hot | runs | max |
|---|---|---|---|---|---|---|---|
| BB(6,2) | 6 | 2 | 10^^10^^10^^8 | 2/1/3 | 25/25 | 127 | 739 |
| BB(7,2) | 7 | 2 | 3{20}3 | 2/3/2 | 49/49 | 44 | 993 |
| BB(8,2) | 8 | 2 | f_w^3(12) | 3/2/3 | 25/24 | 1313 | 3 |
| BB(9,2) | 9 | 2 | f_w^7(12) | 4/1/4 | 25/24 | 1313 | 3 |
| BB(10,2) | 10 | 2 | f_{w+1}(2{36}3) | 2/2/6 | 24/23 | 1471 | 2 |
| BB(11,2) | 11 | 2 | f_{w+1}((f_w)^2(5)) | 5/2/4 | 50/50 | 33 | 1010 |
| BB(18,2) | 18 | 2 | f_{w+3}(114) | 5/3/10 | 49/49 | 45 | 975 |
| BB(21,2) | 21 | 2 | (f_w)^22(4^^341) | 6/6/9 | 50/49 | 11 | 1151 |
| BB(40,2) | 40 | 2 | f_{w^w}(75500) | 15/11/14 | 48/48 | 341 | 1117 |
| BB(41,2) | 41 | 2 | (f_{w^w})^4(32) | 15/11/15 | 46/45 | 543 | 1062 |
| BB(51,2) | 51 | 2 | f_{eps0+1}(8) | 15/20/16 | 41/41 | 661 | 382 |
| BB(67,2) | 67 | 2 | Laver q^81(q(5)-2) | 25/21/21 | 19/18 | 298 | 31 |
| BB(19,5) | 19 | 5 | f_eps0(1.7e352) | 3/0/16 | 99/1 | 5 | 527 |
| BB(18,7) | 18 | 7 | same as 19,5 | 2/0/16 | 99/1 | 5 | 527 |
| BB(56,7) | 56 | 7 | (f_eps0)^F(k0), F from tape | 27/9/20 | 99/1 | 5 | 527 |
| BB(4,4) | 4 | 4 | > 2{509}3 | 0/0/4 | 53/44 | 56 | 447 |
| BB(6,4) | 6 | 4 | f_{w+1}(10^^65533) | 0/0/6 | 50/25 | 11 | 398 |
| BB(5,5) | 5 | 5 | > f_{w+1}((f_w)^4(6)) | 0/0/5 | 50/50 | 17 | 398 |
| BB(6,5) | 6 | 5 | > f_{w+2}(126) | 0/0/6 | 50/50 | 9 | 426 |
| BB(3,6) | 3 | 6 | f_w^3(15) | 0/0/3 | 50/50 | 34 | 398 |
| BB(2,8) | 2 | 8 | 10^^^5 (ten digits → 155) | 0/0/2 | 75/25 | 9 | 764 |

Four columns to notice before reading on.

**`hot` is bimodal.** Either two states carry 90-100% of the run, or the profile is spread over
four or more states at 20-25% each; almost nothing lands in between. The two-state machines are
*ping-pong engines*; the four-way ones are *bit-string scramblers*; BB(67) at 19/18 is a
*program* (§8 L1).

**`runs` spans five to fifteen hundred.** BB(19,5) and BB(51,2) claim adjacent levels after `+1`
and sit on tapes with 5 and 661 runs. Any theory that reads level off the tape must explain that;
§6.2 does, and the answer is direct versus positional addressing.

**`max` collapses when the alphabet grows.** Every 2-symbol machine that is not a bit-scrambler
holds a block of 700-1200 ones; every ≥4-symbol machine 400-800; the 2-symbol bit-scramblers 2-3.
A long block means the machine is *accumulating* rather than *encoding*.

**The role census is a fingerprint.** `0/0/*` means no state ever writes a zero into a blank on
its own initiative — every cell is rewritten in place, i.e. an interpreter (§7). The 2-symbol
machines run 2-6 write states against 3-21 sweeps. Nothing else in the census separates the
families as reliably.
---

## 4. Family I — the 2-symbol ladder (BB(6) … BB(41))

These are the machines everyone means by "small 2-symbol FGH machines". They share one skeleton,
and the skeleton is visible in the transitions before any dynamics are run.

### 4.1 The skeleton: two pumps and a bookkeeper

Take BB(7,2), claimed `3{20}3`. Its table is small enough to read whole:

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | sweep R | 1R1 | 0R6 |
| 1 | write R | 1R2 | **1R1** |
| 2 | sweep R | 0R3 | 1R**H** |
| 3 | write L | 0L4 | 0L3 |
| 4 | sweep L | 0L5 | **1L4** |
| 5 | branch | 1R0 | 1L5 |
| 6 | branch | 1L2 | 0R1 |

Two rows are self-loops that write a `1` and keep moving: state 1 on `1` → `1R1`, state 4 on `1` →
`1L4`. Everything else either moves the head without writing, or branches. The measured profile is
**state 1: 49%, state 4: 49%**, and all five other states share the remaining 2%.

That is the whole design. State 1 walks right through a block of ones, writing a `1` on every cell
it crosses — it *renews* the block it walks over; run it long enough and it extends the tape. State
4 walks back left doing the same. The five cold states decide where state 1 may start and what to
do when it hits a blank. In one sentence: **the pump is two states; the level is the five states
that say "again" or "stop".**

The same two rows exist in most 2-symbol machines in the census:

| machine | right pump | left pump | share of run in the pair | bookkeeping states |
|---|---|---|---|---|
| BB(7,2) | `1: 1R1` | `4: 1L4` | 97% | 5 |
| BB(8,2) | none — erase pump `6: 0R6` | none | 49% | 6 |
| BB(11,2) | `6: 1R6` | `7: 1L7` | 100% | 9 |
| BB(18,2) | `2: 1R2` | `0: 1L0` | 98% | 16 |
| BB(21,2) | `7: 1R7` | `5: 1L5` | 98% | 19 |
| BB(40,2) | `6: 1R6` | `39: 1L39` | 95% | 38 |
| BB(51,2) | none | `10: 0L` (erase walk) | 82% | 49 |

As the claimed level rises, the *pump* column barely changes and the column of states outside the
pair grows monotonically: 5, 6, 9, 16, 19, 38, 49. This is the first hard fact of the census: **levels are
not bought by better pumps. They are bought by more bookkeeping around the same pump.**

The two rows where the pattern breaks are the interesting ones. BB(8,2) has *no* pump that writes:
one of its four hottest states (6, `0 → 0R6`) walks right **erasing**. BB(51,2)'s hot pair is an erase-walk left
(`10: 0L20 / 0L17`, writes 0 on both symbols) and a pure travel right (`12: 0R13 / 1R13`). Both are
*material-destroying* machines: they are counting down a positional record, not accumulating. That
distinction — accumulate versus count down — is the same one as §6.2's direct versus positional
addressing, and it is visible directly in the hot rows.

### 4.2 BB(6,2) — a four-phase round, and why six states suffice

`1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE`, claimed `10^^10^^10^^8`.

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | write R | 1R1 | 1R0 |
| 1 | write R | 1R2 | 1R**H** |
| 2 | branch | 1L3 | 0R5 |
| 3 | branch | 1R0 | 0L4 |
| 4 | branch | 0L3 | 1R2 |
| 5 | sweep R | 1R0 | 0R4 |

No self-loop pump here, and the profile is not 50/50 either: **four states at 24-25%** (0, 2, 3, 4),
one at 3% (5), one at 0% (1). The round is a four-phase shuttle: 0 and 1 write the frontier, 2 and
3 choose a side, 4 and 5 erase and sweep. State 1 writes *and* tests: on `0` it lays a `1` and
continues, on `1` it halts (`1 → 1RH`). That single row is the machine's only halt trigger.

The tape at 400k is 127 runs with a 739-cell block — so the shuttle eventually produces a long run,
not a bit string. The four-way profile is what a *frontier* machine looks like: the head stays near
the boundary where material is created, and each phase costs about the same number of steps. It is
also why six states are enough for a tower: the value comes from the *rate* at which the frontier
advances, and a frontier shuttle doubles the block per pass without needing a counter at all. The
counter is the block itself.

### 4.3 BB(8,2) / BB(9,2) — bit scramblers, and a measurement that kills a natural inference

BB(8,2), claimed `f_w^3(12)`; BB(9,2), claimed `f_w^7(12)`. Their tables differ in exactly two
cells, and at 400 000 steps the two runs are **step-for-step identical**: same final state, same
674 ones, same 1331-cell extent, same 1313 runs, same longest block of 3.

| | BB(8,2) | BB(9,2) |
|---|---|---|
| state 4, read 0 | `1L7` | `0L7` |
| state 7 | `1R6`, `1RH` | `0L8`, `1RH` |

So a four-iterate difference in claimed value is invisible for 400 000 steps. That is not a
contradiction — `f_w(12)` is astronomically larger than 400 000, so both machines are inside their
first iterate — but it is the cleanest demonstration available of §2.5: **the window samples the
preamble, and the preamble is identical across levels.** Anyone comparing `ones` at 10^5 to rank
machines will get the wrong answer, and here is a controlled experiment showing it.

The morphology is the other lesson. 1313 runs with a longest block of 3 means the tape is a *bit
string*: `1 0 1 0 1 1 0 1 ...`. The machine is not accumulating material in a block; it is
rewriting a pattern in place, and its claimed level comes from how the pattern is *read*, not from
how big it is. Four states at 25/24/25/24 (1, 2, 5, 6) confirm a four-phase scrambler with no hot
pair. BB(9) differs by two cells and behaves identically, so its two extra states are doing work
that starts later.

### 4.4 BB(10,2) — where the tape becomes a bit string

`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC`, claimed
`f_{w+1}(2{36}3)`. Measured: **1471 runs, longest block 2** at 400k — the most fragmented tape in
the census. Profile 24/23/20/20 over states 1, 2, 7, 6: a four-phase scrambler, like BB(8)/BB(9),
with two more states of phase logic.

State 9 is the halt row: `0 → 1RH`. Note that the halt *writes a 1*: the machine's last act adds
one to the score. That idiom recurs (BB(11,2) state 5 is also `0 → 1RH`) and it is worth naming
because it shows the halt is a *transition*, not a missing entry: the analysis must account for the
final step like any other.

### 4.5 BB(11,2) — the cleanest two-state engine in the census

Claimed `f_{w+1}((f_w)^2(5))`, 11 states, and the profile is a perfect 50/50 between states 6 and 7:

| state | role | read 0 | read 1 |
|---|---|---|---|
| 5 | sweep R | 1R**H** | 0R6 |
| 6 | write R | 1R1 | **1R6** |
| 7 | write L | 1L0 | **1L7** |

Two self-loops, one in each direction, and nine states of bookkeeping. The tape at 400k is 33 runs
with a 1010-cell block: the pumps are building a long run, not scrambing bits. If you want to see
"two states do the work, nine states choose the level" in one table, this is the machine.

### 4.6 BB(18,2) / BB(21,2) — the ladder proper

BB(18,2), claimed `f_{w+3}(114)`: 16 bookkeeping states around the pump pair `2: 1R2` / `0: 1L0`,
98% of steps in the pair, 45 runs and a 975-cell block at 400k. The role census is 5/3/10 — the
first machine with ten branch states, i.e. the first one where the bookkeeping has real internal
structure (the cycle list contains `3-4-9-0-1-2`, `4-5-8`, `5-6-12`, `12-...`: at least four
distinct loops through the same pump).

BB(21,2), claimed `(f_w)^22(4^^341)`: 19 bookkeeping states, 98% in `7: 1R7` / `5: 1L5`, and at
400k only **11 runs** with a 1151-cell block. Eleven runs means the tape is a handful of very long
fields — the most "numeral-like" tape of the family. Its first runs are `1^2` then a 339-cell
field, i.e. a two-field layout being extended.

The pair is worth comparing: 18 states at `f_{w+3}` has 45 runs; 21 states at `(f_w)^22` has 11.
Both are `f_w`-iterates; the difference is that BB(21) keeps its data in *few fields*, and the
whole claim is about the iteration count read from one of them. Three extra states bought a much
higher iterate count and a much *simpler* tape. Level and tape complexity are not the same axis.

### 4.7 BB(40,2) / BB(41,2) — the pair that changes regime

Claimed `f_{w^w}(75500)` and `(f_{w^w})^4(32)`. These are the first 2-symbol machines in the
census whose profile is no longer a two-state ping-pong: 48/48 at BB(40) but with **341 runs**, and
46/45 at BB(41) with **543 runs**. The role census jumps to 15/11/14 and 15/11/15.

341 runs is the ω^ω signature: a *list* of counters. A fixed-arity numeral (BB(21), 11 runs)
cannot express ω^ω; a list whose length is itself a counter can, and a list of n counters has
O(n) runs on the tape. The measured jump from 11 runs (BB(21)) to 341 (BB(40)) through 45
(BB(18)) is the clearest tape-level correlate of a level jump in the whole census.

### 4.8 What each extra state buys

Deltas along the 2-symbol column, with the ledger's claim attached to each row:

| jump | states | claim delta | measured change |
|---|---|---|---|
| BB(6)→BB(7) | +1 | 10^^…→3{20}3 | profile 4-way → ping-pong |
| BB(7)→BB(8) | +1 | →f_w^3(12) | tape becomes a bit string (1313 runs) |
| BB(8)→BB(10) | +2 | →f_{w+1} | +2 phases, halt row moved inside the loop |
| BB(10)→BB(11) | +1 | →f_{w+1} with (f_w)^2 inside | ping-pong becomes clean, 33 runs |
| BB(11)→BB(18) | +7 | →f_{w+3} | 10 branch states, four loops through one pump |
| BB(18)→BB(21) | +3 | →(f_w)^22 | runs collapse 45 → 11 (fewer, bigger fields) |
| BB(21)→BB(40) | +19 | →f_{w^w} | runs explode 11 → 341 (list instead of fields) |
| BB(40)→BB(41) | +1 | →(f_{w^w})^4 | 543 runs, profile flattens |
| BB(41)→BB(51) | +10 | →f_{eps0+1} | 661 runs, 15/20/16 roles, 41/41 |

The pattern is not "+1 state = +1 level". It is: **a level costs a data structure, and a data
structure costs 10-20 states; single states buy *iterations* inside the current structure.** The
BB(18)→BB(21) row is the counter-example that proves the rule — three states bought iterations
without new structure, and the tape got *simpler*.

---

## 5. Family II — the tagged engines (BB(19,5), BB(18,7), BB(56,7))

### 5.1 Why five symbols change the game

A 2-symbol machine has one separator (the blank) and therefore one way to say "field boundary":
*position*, found by walking. A 5-symbol machine has four separators; it can say "this is field
2" by *writing a `2`*. The consequence is visible in the role census: BB(19,5) is **3 write / 0
sweep / 16 branch**. It has *no sweep states at all* — every state is a decision, and movement is
decided per cell. That is an interpreter, not a pump.

### 5.2 BB(19,5) — the canonical ε₀ engine

Claimed `f_eps0(1.7·10^352)`. Full table in Appendix B; the rows that matter:

| state | read 0 | read 1 | read 2 | read 3 | read 4 |
|---|---|---|---|---|---|
| 0 | 1R1 | 2L0 | 1R0 | 2L1 | 2L0 |
| 1 | 0L0 | 2R1 | 3R1 | 4R0 | 1L16 |
| 2 | **1R H** | 1R2 | 2L3 | — | — |
| 4 | — | — | 0R7 | 1L18 | 0R5 |
| 16 | 1R2 | 3R17 | 1R12 | 3L15 | 0R14 |

Measured over 400 000 steps: **99% of all steps are in state 0**; the tape is **5 runs** with a
527-cell longest block; `ones` = 886, extent = 887. Samples during the window:

```
  100k   1^1 3^147 4^1 1^185 2^104 0^1
  200k   2^1 3^280 2^346 0^1
  300k   2^1 3^79 4^1 1^499 2^147 0^1
  400k   3^527 4^1 1^52 2^306 0^1
```

Read that as a data structure. The tape is a **record of three numeric fields written in distinct
symbols**, with `4` acting as a delimiter: `3^a 4 1^b 2^c`. The fields are big (tens to hundreds of
cells) and their *shape* is stable: four to six runs, always. State 0 is a single-step walk that
increments along the record; the other 18 states are entered on the rare cells where a field
boundary or the delimiter appears. 99% in one state is the signature of a **linear scan over a
positional record** — the machine spends its life moving the head, and the decisions are the 1%.

This is the interpreter philosophy in its purest form: small, fixed-shape tape; almost all states
are dispatch; the level is in the dispatch table. Note what is *not* on the tape: no nesting, no
inheritance, no tower. Four or five runs, all flat. Whatever ε₀ means for this machine, it cannot
be read off the tape the way BB(40)'s list could be read off 341 runs — the ordinal is in the
state graph's interpretation of the fields, not in the fields themselves. That is exactly the
point of §1.2, and it is also why this machine is *19* states instead of *51*.

### 5.3 BB(18,7) — same engine, two spare symbols

Claimed identical to BB(19,5), and measured identical: 886 ones, 5 runs, 527-longest block, 99% in
state 0 at every sample. The 7-symbol table is the 5-symbol table with two extra columns, and
state 4 is `0>4L4 1>1L4 2>0R6 3>1L17 4>0R5 5>2L4 6>4L4` — i.e. symbols 5 and 6 are handled by
falling through to the same actions as others.

Two readings, both useful: (a) padding an alphabet is free — you can always add unused symbols and
the machine behaves the same; (b) therefore a "7-symbol ε₀ engine" and a "5-symbol ε₀ engine" can be
the same machine, and the 18 vs 19 states difference is noise. Anyone comparing across alphabets
must compare *used* symbols, not declared ones. The ledger's own BB(61,6) row ("same step count as
BB(94,5)") is the same phenomenon at a larger scale: a symbol lift that does not change behaviour.

### 5.4 BB(56,7) — the glue, and the one row that matters

Claimed `(f_eps0)^F(k0)` with **F read off the tape** ("the fuel is measured, not a constant"), 56
states, glue "kernel-checked (`LadderGlue.lean`, `native_decide`, no sorry)". The machine contains
the 18,7 engine as its states 0-17; states 18-55 are the ladder around it. My 400 000-step run
never leaves the inner engine (identical trace to BB(18,7): 886 ones, 5 runs), which is exactly
what "the outer ladder has not engaged yet" looks like: the first round is the engine's, and the
glue only runs between rounds.

This is the single most important entry for the target in §10, because it is the ledger's own
demonstration that **composition is cheaper than construction**: 37 extra states turn one ε₀ round
into an F-fold iterate, where F is a number on the tape. No new arithmetic, no new encoding — one
connector. And the proof obligation is split the same way (glue by case check, engine by hand),
which is the format §11 recommends.

---

## 6. Family III — the big 2-symbol engines (BB(51,2), BB(67,2))

### 6.1 BB(51,2) — ε₀+1 in two symbols, at 661 runs

Claimed `f_{eps0+1}(8)`, start state 30. Measured: roles 15/20/16, hot 41/41 (states 10 and 12),
**661 runs**, longest block 382, `ones` 1612, extent 1952 at 400k. Over the window the run count
grows 77 → 129 → 299 → 669 → 661 while the longest *zero* run stays pinned at 10.

That is the opposite morphology to BB(19,5), and it is what positional addressing costs. A
2-symbol machine cannot label a field, so it must find one by walking; and to walk to field k it
must count separators. With a fixed-length separator (here: no zero-run longer than 10) the walk
can be *bounded*, but the tape must then be a long, fine-grained list — 661 blocks — and the
machine must contain the states that count through it. The 32 extra states over BB(19,5) are
exactly that parser: 15 write + 20 sweep + 16 branch against 3/0/16.

The 41/41 hot pair is the two directional walks over that list. Note that 82% is *less* concentrated
than BB(18,2)'s 98%: as the list grows, the fraction of time spent in pure pumping drops, because
more time goes into finding fields. That is measurable and it is the cost model of §6.2.

### 6.2 The cost model: direct vs positional addressing

Two machines at adjacent claimed levels:

| | BB(19,5) | BB(51,2) |
|---|---|---|
| states | 19 | 51 |
| symbols | 5 | 2 |
| tape at 400k | 5 runs, max 527 | 661 runs, max 382 |
| hot share | 99% / 1% | 41% / 41% |
| role census | 3/0/16 | 15/20/16 |
| addressing | by symbol (direct) | by counting (positional) |

The ratio is 2.7× states for the same order of level. Where does the time go? A round on a
direct-addressed tape touches O(1) fields: walk to the field, act, walk back. A round on a
positional tape must find field k, which costs a walk of length proportional to the tape's extent,
so the round is O(extent) and the *state graph* needs states for each leg of the walk (that is what
the 20 sweeps are). This is the whole reason the 2-symbol column is expensive, and it is why the
same level appears at 19 states with 5 symbols and 51 with 2.

For the goal it matters in a precise way: **adding symbols is a state discount of roughly 2-3×,
but it does not reduce the number of *rungs*.** The rungs are set by the data structure, and the
data structure is set by the level, not by the alphabet.

### 6.3 BB(67,2) — a program, not a numeral

Claimed `q^81(q(5)−2)` from Laver tables — not an FGH claim at all, which makes it a useful
control. Measured: 25/21/21 roles, hot 19/18 over states 25 and 27, **298 runs**, longest block 31,
`ones` 1793, extent 1943.

Everything about this profile is different: no dominant pair (19% and 18%), no long block (31),
many short runs (298), and a role census that is nearly uniform (25/21/21). This is what a
*program* looks like: many phases of comparable cost, data spread over many small cells, no single
pump. It is the natural shape when the machine implements a recursive function on a structured
state rather than accumulating material in a block — and it is a warning for anyone who thinks
"more states = higher FGH level". BB(67) has more states than BB(51) and is not an FGH machine.

---

## 7. Family IV — the tiny high-symbol machines (BB(4,4), BB(6,4), BB(5,5), BB(6,5), BB(3,6), BB(2,8))

### 7.1 Every cell is a branch

The role census for all six is `0/0/n`: **zero write states, zero sweep states.** No state in these
machines both writes and moves as its job; every state decides based on the symbol read, and the
*action* is per-cell. With enough symbols, control flow is encoded directly in the alphabet, so a
single state can be a whole dispatch table.

BB(4,4), claimed `> 2{509}3`:

| state | read 0 | read 1 | read 2 | read 3 |
|---|---|---|---|---|
| 0 | 0L1 | 3L1 | 1R**H** | 2R0 |
| 1 | 1L3 | 3R1 | 1L2 | 2R0 |
| 2 | 3R1 | 1L1 | 3L2 | 2R2 |
| 3 | 0R3 | 2R2 | 2L1 | 0R0 |

Four states, sixteen defined cells, one halt row (`(0,2) → 1RH`). Measured: hot 53/44 (states 2
and 1), 56 runs, longest block 447, `ones` 539 at 400k. A 4-state machine with a 447-cell block:
the block is the number, and the symbols are the instruction bits that say what to do with it.

BB(2,8), claimed `10^^^5` (with the last ten digits replaced by 155):

| state | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| 0 | 1R1 | 3R1 | 4L0 | 1L1 | 5L0 | 6L1 | 5R0 | 1R**H** |
| 1 | 2L0 | 6R0 | 4R1 | 7R0 | 3L1 | 6L0 | 4R1 | 4R0 |

Two states, sixteen cells, and it is a five-arrow tower. Nothing in this machine looks like a
counter: it is a set of rewrites on seven distinct symbols, each of which acts as a state of its
own. This is the extreme of the exchange: **symbols are cheap, states are expensive, and a
2-state/8-symbol machine can be at 10^^^5.**

### 7.2 The trade surface

| states | symbols | machine | claim | measured shape |
|---|---|---|---|---|
| 2 | 8 | BB(2,8) | 10^^^5 | 75/25, 9 runs, max 764 |
| 3 | 6 | BB(3,6) | f_w^3(15) | 50/50, 34 runs, max 398 |
| 4 | 4 | BB(4,4) | > 2{509}3 | 53/44, 56 runs, max 447 |
| 5 | 5 | BB(5,5) | > f_{w+1}((f_w)^4(6)) | 50/50, 17 runs, max 398 |
| 6 | 4 | BB(6,4) | f_{w+1}(10^^65533) | 50/25, 11 runs, max 398 |
| 6 | 5 | BB(6,5) | > f_{w+2}(126) | 50/50, 9 runs, max 426 |
| 19 | 5 | BB(19,5) | f_eps0 | 99/1, 5 runs, max 527 |
| 51 | 2 | BB(51,2) | f_{eps0+1} | 41/41, 661 runs, max 382 |

Read down the first two columns: at fixed level, **one symbol is worth several states**, and at
fixed budget, symbols are the cheaper currency. BB(5,5) reaches ε₀+1-adjacent territory in 5 states;
BB(51,2) reaches the same order in 51. The state counts in the census are therefore not a measure
of difficulty — they are a measure of how much of the control flow had to be pushed into the state
graph because the alphabet could not hold it.

That is the answer to the question "why do these small machines reach the FGH at all": because the
tape is data and the alphabet is instruction, and a 5-state machine with 5 symbols already has ten
instructions. The hierarchy level lives in how those instructions compose over a descent, and
composition costs almost nothing in states.
---

## 8. The laws the census supports

These are regularities measured over 21 machines at one window, not theorems. They are stated
sharply because a sharp statement is testable; L7 says where each one could break.

### L1 — the profile is bimodal, and the regime changes at ~50 states

Sort the machines by the share of the run in their top two states:

```
  BB(11,2) 100    BB(19,5) 100    BB(5,5) 100    BB(3,6) 99    BB(18,2) 98    BB(21,2) 99
  BB(7,2)   97    BB(40,2) 95     BB(6,5) 100*   BB(6,4)  75   BB(2,8) 100*   BB(67,2) 37
  BB(41,2)  92    BB(51,2) 82     BB(8,2)  49    BB(10,2) 47   BB(6,2)  50
```

(*top-two sums of the rounded pair.) Two clusters: **≥82%** (one machine phase dominates) and
**≤75%** (several phases share the run). The cluster is a design fact, not a level fact — BB(2,8)
at `10^^^5` is as concentrated as BB(19,5) at ε₀, and BB(67,2) with more states than either is at
37%. Within the 2-symbol column the useful quantity is the **tail** (steps outside the top two
states), which grows with size:

| states | 2-symbol machine | top-two share | tail | what the hot pair is |
|---|---|---|---|---|
| 7 | BB(7,2) | 97% | 3% | pump R + pump L |
| 11 | BB(11,2) | 100% | 0% | pump R + pump L |
| 18 | BB(18,2) | 98% | 2% | pump R + pump L |
| 21 | BB(21,2) | 99% | 1% | pump R + pump L |
| 40 | BB(40,2) | 95% | 4% | pump R + pump L |
| 41 | BB(41,2) | 92% | 9% | pump R + pump L |
| 51 | BB(51,2) | 82% | 18% | erase-walk L + scan R |
| 67 | BB(67,2) | 37% | 63% | (no pair; six phases) |

Up to 41 states the hot pair is a pair of pumps and the tail is under 10%. At 51 the pair is still
there but it is *not* pumping — it is erasing and scanning (§4.1), i.e. counting a positional
record down — and the tail has grown to 18%. By 67 there is no pair at all, only six phases at
6-19%. That progression is the visible boundary between a *counter machine* and a *program*, and
it is the best single predictor of "is this machine an FGH machine" in the census.

### L2 — growth is back-loaded, so the window cannot rank machines

At 400 000 steps:

| machine | claim | ones at 400k | runs | max block |
|---|---|---|---|---|
| BB(6,2) | 10^^10^^10^^8 | 855 | 127 | 739 |
| BB(21,2) | (f_w)^22(4^^341) | 1548 | 11 | 1151 |
| BB(40,2) | f_{w^w}(75500) | 1291 | 341 | 1117 |
| BB(51,2) | f_{eps0+1}(8) | 1612 | 661 | 382 |
| BB(19,5) | f_eps0(1.7·10^352) | 886 | 5 | 527 |
| BB(2,8) | 10^^^5 | 864 | 9 | 764 |

Every machine on that list, from a tower to ε₀, produces **855-1612 ones** in the first 400 000
steps. The spread is a factor of two; the claimed levels span the whole hierarchy. There is no
signal here. The reason is structural: a run's value is dominated by its *last* round, and the
last round happens after a number of rounds that is itself enormous. The window sees only the
bootstrap.

The controlled version of the experiment is §4.3: BB(8,2) and BB(9,2) claim `f_w^3(12)` and
`f_w^7(12)` — four extra `f_w` iterates — and their runs agree to the step for the entire 400 000
steps. If a four-iterate gap is invisible, a tower-versus-ε₀ gap is hopeless.

Practical consequence: **you cannot rank, discover or verify a level by simulation.** Simulation
finds *shape* (this file) and confirms *small instances* (my Rocq machines). The level is always a
proof, and the only thing simulation contributes to it is the round structure you then prove.

### L3 — one symbol ≈ three states, at fixed level

| level (claimed) | 2 symbols | 5 symbols | 7 symbols |
|---|---|---|---|
| f_{w+1} | BB(11,2), 11 | BB(5,5), 5 | — |
| f_{w+2} | — | BB(6,5), 6 | — |
| f_eps0 | — | BB(19,5), 19 | BB(18,7), 18 |
| f_eps0+1 | BB(51,2), 51 | — | BB(56,7), 56 (glued) |

(The 2-symbol column has no `f_eps0` row in the census; BB(51) is one rung above, at `eps0+1`.)

The 19-versus-51 comparison is the clean one: same order of level, 2.7× the states. And the
18-versus-19 comparison shows that once the alphabet holds the structure, extra symbols are free
(BB(18,7) is BB(19,5) with two unused columns). L3 is the quantitative form of "symbols are the
cheap currency".

### L4 — tape morphology tracks the *encoding*, and the level shows up as a trend

Run count at 400k, 2-symbol column, in order of claimed level:

```
  BB(6) 127   BB(8) 1313   BB(10) 1471   BB(11) 33   BB(18) 45   BB(21) 11
  BB(40) 341  BB(41) 543   BB(51) 661
```

No monotone pattern — 1313 runs at BB(8) and 11 at BB(21), and BB(21) is the higher level. What
*does* correlate is the **trend within a machine as it runs**: BB(51)'s run count grows 77 → 299 →
661 → 661 while its longest zero-run stays pinned at 10 (§6.1), i.e. it is *building a list*;
BB(19,5)'s run count is 5 at every sample, i.e. it is *reusing a record*. Growth in run count with
bounded separator length is the signature of a list being constructed; constant run count with
growing blocks is a fixed-arity numeral.

So L4 should be stated as: **the arity of the tape's notation is the level, and arity shows up as
either a growing run count (positional) or a growing block (direct).** A single snapshot cannot
tell you the arity; a series can.

### L5 — level lifts are cheap in states and expensive in proof

Three measured examples of the same thing:

| lift | mechanism | cost |
|---|---|---|
| one round → `b` rounds | erasing fuel block, one cell per stage | +14 states (my connector) |
| `(f_w)^2` → `(f_w)^22` | more bookkeeping around the same pump | +3 states (BB(18)→BB(21)) |
| `f_{w+2}` → `f_{w+3}` | splice two states into the halt row | +2 states (ledger, BB(16)→BB(18)) |
| ε₀ round → `(f_eps0)^F` | glue, F read from tape | +37 states (BB(19,5)→BB(56,7)) |

The last one is the expensive case only because it carries a *new engine* as well as the glue; the
pure glue is one transition. The lesson for construction: **the marginal state cost of a rung is
2-14; the marginal state cost of a new data structure is 10-20.** Budget accordingly.

### L6 — the cold states decide the value

Every machine in Family I has 5-49 bookkeeping states and 2 pumps, and the bookkeeping collectively
runs under 5% of the steps. BB(11,2) is the extreme: 100% of the *steps* are in states 6 and 7,
and 0% of the *decisions* are — the halt row is state 5's `0 → 1RH`, the loop test is state 2/3,
and the whole hierarchy level is in the nine states that are never hot.

The same holds for the tagged engines: BB(19,5) spends 99% of its steps in state 0 and 1% in the
other 18 states, and those 18 states contain both halt triggers (`2` on `0`, and the undefined
cells at `(4,0)`, `(4,1)`). This is why profiling is a *pointer* and not an *analysis*: it tells
you where the engine is, and the engine is never where the level is.

### L7 — what would falsify these

L1 breaks if a machine exists at ≥50 states with a clean two-state pump and an FGH claim — the
ledger's BB(56,7) might be one (99% in state 0, but that is one state, not two, and it is an
interpreter). L3's ratio is a three-point fit; BB(67,2) shows it is not a law of nature. L4's
"growing run count" test needs a second window at 10^7 steps to confirm the trend continues; I
only have 400k. L5's per-rung cost is measured on my own builders, which are not optimised for
size. L6 is safe — it follows from the definition of the pump.

---

## 9. Why the levels are what they are

### 9.1 The structure ladder

The census, read as data structures, gives a table of what a machine must be able to *hold* at each
level. "Primitive" is the one new thing the machine needs over the row above.

| level | tape object | primitive needed | measured example |
|---|---|---|---|
| f₂/f₃ | one block | expand while consuming | my machines 1-3 (15-state engine, 34-38 states total) |
| ω | block + fuel | refill/consume a fuel block | my ladder (54 states, tower height b) |
| ω^k | k fuel blocks | borrow across k fields | ledger BB(18) `f_{w+3}` |
| ω^ω | growing list of fuels | push a new level | ledger BB(40) `f_{w^w}`, 341 runs |
| ε₀ | list whose elements are lists | re-read a field as a program | BB(19,5) / BB(51,2) at `eps0` / `eps0+1` |
| ε₁ | family indexed by a list | diagonalise the ε-list | none in the census |
| ζ₀ | family of families | the ε-family as one object | none in the census |
| η₀ | one more index | one more nesting | none in the census |

The right-hand column is the census's contribution: each row is a machine I ran, and the object
column is what its tape actually looked like. The table is a description of *what to build*, not a
theorem about what is possible.

### 9.2 Two ways to be at the same level

The two machines claiming ε₀-class levels (BB(19,5) and BB(51,2)) are not variants of each other;
they are two different designs.

**Numeral machines** (BB(51,2), BB(40,2), BB(18,2)) put the ordinal on the tape as a *numeral*: a
list of blocks whose lengths are digits, with the separator encoding the field structure. Progress
is one fundamental-sequence step per round: find the least significant non-empty field, decrement
it, normalise. The level is the strength of the numeral system, and the state count is the cost of
the parser. Morphology: many runs, few states per run, growing run count.

**Interpreter machines** (BB(19,5), BB(18,7), BB(56,7)) put a small *instruction* on the tape: a
record of three fields, one delimiter, and a state table that dispatches on the symbol read.
Progress is one instruction per round, and the level is the strength of the interpreter's
*dispatch*, not of its data. Morphology: few runs, huge blocks, 99% of steps in one state, and a
role census of almost all branches.

Neither is more "honest" than the other. But they have different failure modes: a numeral machine
fails by getting the borrow wrong (a normalisation bug — silently wrong value, still halts), and an
interpreter fails by having an unreachable dispatch case (silently wrong level, still halts). Both
fail silently, which is why §11's verification plan matters more than the construction.

### 9.3 Where the Veblen index enters, operationally

The standard definition: `φ(0,β) = ω^β`, `φ(1,0) = ε₀`, `φ(1,1) = ε₁`, `φ(2,0) = ζ₀`,
`φ(3,0) = η₀`, and `φ(α,·)` enumerates the common fixed points of `φ(β,·)` for `β < α`. The
operational content, in machine terms:

* `ε₀` = "a counter whose *height* is a counter". The machine must be able to grow a new field
  while counting down an old one. BB(19,5)'s record `3^a 4 1^b 2^c` has exactly this shape: `a` is
  the height, `b`/`c` are the value being counted. The tape never nests, because the *height is
  reused*, not materialised.
* `ε₁` = "a counter whose height is a *list* of heights". The machine must be able to index the
  ε-family: one extra field that says *which* ε-number, plus a rule that produces the fundamental
  sequence of `ε_{k+1}` from `ε_k`.
* `ζ₀` = the same one index further: the list of ε-numbers becomes a single object that can be
  counted down; `η₀` = one more turn.

Each step is one more level of "treat the previous object as a single cell". In tape terms that is
one more run-type or one more field; in state terms it is 2-14 states; in proof terms it is a whole
new ordinal notation.

### 9.4 Why my ladder is only f₃ while 19 states reaches ε₀

This is worth stating precisely because it is the most common confusion in this project, including
my own earlier messages.

A machine's rank (`ρ`) bounds the **number of rounds** from above. It does not by itself give a
lower bound on the value: a rank-ω machine that does one step per round is linear. What gives the
value is the **expansion factor** — how much material each round creates — times the number of
rounds.

My ladder has rank ω (the fuel block is consumed one cell per round) and a huge expansion (each
round replaces a counter of length n by a block of `5·2^(n-1)`). With `b` fuel cells it runs `b`
rounds, so the value is a tower of height `b` — that is `f_3(b)`, not `f_ω(b)`. The rank is ω, the
value class is f₃, and both statements are true: `f_3(b) ≤ f_ω(b)` because `f_ω(b) = f_b(b)`.

BB(19,5) has the same rank *shape* but its round count is **read from the tape** (`c` in
`3^a 4 1^b 2^c`), so the count grows with the value, and that self-reference is what turns `f_3`
into `f_ε0`. In the ledger's words for BB(56,7): "the fuel is measured, not a constant".

So the single structural difference between f₃ and ε₀ machines is **where the iteration count comes
from**: a constant in the boot (f₃), a block on the tape (f_ω and up), or a field that is itself
produced by the machine's own output (ε₀ and up). That is the whole game.

---

## 10. The construction kit

### 10.1 The five routines, with measured costs

All costs are states, measured in this repository's builders (`tools/mk_machines.py`,
`tools/ladder.py`) or designed here and marked so.

| routine | job | cost | status |
|---|---|---|---|
| boot | write `1^c 0 1^2 0 1` on blank, walk back | 1 per cell + 6 | built, [proved] |
| engine | one doubling pass on a counter block | 15 | built, [proved] |
| connector | find output, write fresh `U`,`W`, re-enter engine | 14 | built, [proved] |
| fuel handle | walk to fuel, erase one cell, test, return | 5 of the 14 | built |
| glue | one transition from engine halt pair into connector | 1 | built |
| copy | duplicate a block of unknown length | 9 | designed (§10.2), not built |
| push | extend a numeral by one field | 6 | designed, not built |

The point of the table: **everything except the copy/push pair is already built and proved**, and
those two are the difference between f₃ and everything above it.

### 10.2 The copy problem, and the two tricks

To grow a block you do not need to copy: consume the source and write two cells per cell (§1.3).
That is why the doubling engine is 15 states. To *refill fuel from the output* you need the output
to still be there after the fuel is written, and that is a genuine copy.

With two symbols there is no spare marker, so the only marker available is **a zero written into a
run of ones**. A single `0` inside `1^k` is unique, costs one unit of the block, and is restored on
the way back. That gives a copy in nine states:

```
  C0  at the mark:      1 → 0,R,C1        erase the cell you are carrying
  C1  walk right:       1 → 1,R,C1 ; 0 → 0,R,C2
  C2  second separator: 0 → 0,R,C3
  C3  walk over dest:   1 → 1,R,C3 ; 0 → 1,L,C4    write the copy
  C4  walk back:        1 → 1,L,C4 ; 0 → 0,L,C5
  C5  separator:        0 → 0,L,C6
  C6  second separator: 0 → 0,L,C7
  C7  over source:      1 → 1,L,C7 ; 0 → 1,R,C8    restore the mark
  C8  next cell:        1 → 1,R,C0 ; 0 → halt      done
```

The doubled blank between source and destination is not decoration: walking back you must be able
to tell the separator from the mark, and only the pair of blanks is distinguishable (C5/C6 consume
it, C7 stops at the first single blank, which is the mark). My own ladder's first bug was exactly
this separator landing one cell off, producing three blanks and merging two fields.

### 10.3 Blueprint A — growing stack, ω^ω, 40-50 states

Layout: `[F_k 00 F_{k-1} 00 ... 00 F_1 00 C]` where each `F_i` is a fuel block. A round does:

1. decrement `F_1` (borrow): if `F_1` is empty, clear it, decrement `F_2`, refill `F_1` from the
   output block (the copy primitive), and continue carrying left as long as the borrow propagates;
2. if the borrow runs off the left end, **push** a new `F_{k+1}` (six states) instead of halting;
3. run the engine one round on `C`.

The rank is the lexicographic order on the list, which is `ω^k` for fixed `k` and `ω^ω` once the
push is allowed. Cost: engine 15 + copy 9 + borrow 8 + push 6 + boot 6 ≈ 44 states, plus glue.
This rung is within reach of the 2-symbol budget and is the natural next build.

### 10.4 Blueprint B — ε₀ by glue, 54-56 states

The census's answer is not to build ε₀ from scratch but to **glue**: take an engine that already
does one ε₀ round, and add a connector that reads its iteration count from the tape. BB(56,7) is
exactly this (`+37` states over the 19-state engine, of which the connector proper is small and the
rest is the second copy of the engine's data layout).

In my own builder the same move costs 14 states, because the connector is generic: find the output,
write a fresh `U`,`W`, walk to the fuel, erase, return. The difference (37 versus 14) is that the
ledger's machine is 7-symbol and carries its own record format; mine is 2-symbol and uses the block
layout. On the 2-symbol side, `54 (ladder) + 9 (copy) = 63` states for a genuine `(f_eps0)^F`-style
machine, which fits under 67 with four to spare.

### 10.5 Blueprint C — ε₁, ζ₀, η₀, and where 67 binds

Now the arithmetic the target actually needs, with the measured rung costs:

| rung | what it needs beyond the row above | states |
|---|---|---|
| ε₀+1 (numeral form) | list whose elements are lists: borrow + push + re-read | 51 (the ledger's BB(51), measured at 661 runs) |
| ε₁ | diagonalise the ε-list: index the family, produce `ε_{k+1}[n]` from `ε_k` | +13 (borrow + push on a second axis) |
| ζ₀ | the ε-family as one object: one more borrow axis | +12 |
| η₀ | one more | +12 |

So the 2-symbol budget reads: **ε₁ ≈ 64 states (fits), ζ₀ ≈ 76 (does not), η₀ ≈ 88 (does not).**

> **Correction (census bounds, 10/2026).** The numbers in this subsection are the cost of
> *this* construction, not a lower bound on the rung. The census puts the rungs far lower:
> BB(29) > f_{ω^ω}(3), BB(31) > f_{ω↑↑4}(3), BB(33) > f_{ω↑↑6}(3) -- **two states per tetration
> level**. So ω↑↑3 is reachable near 30 states and ε₀ well under the 63 budgeted above:
> the surplus here is the cost of the glue this section describes, not of the ordinal. Any
> state-count claim in this handbook should be read as "achieved by this construction",
> never as "required by this rung".
>
> Two further corrections, both taken from the ledger itself. (i) `BB(51) = f_{ε₀+1}(8)` is a
> per-machine analysis from 2024 and the weakest number in the ledger: it has 18 more states than
> the f_{ω↑↑6} machine at BB(33), and the two-states-per-tetration-level scaling cannot carry 51
> states past ε₀ at all, since ω↑↑k < ε₀ for every finite k -- crossing into the ε-family is a
> change of data structure (well-founded lexicographic descent), not one more axis. So it says
> nothing about the ε₀ rung's true state cost. (ii) The working targets for this repository are
> lower still: **ε₁ ≤ 40, ζ₀ ≤ 45, ζ₁ ≤ 48, η₀ ≈ 50, η₁ ≈ 53 states**, each with a
> Rocq-checked halting theorem at the stated level. Those are targets, not results.

With 5-7 symbols the same rungs cost 19-25 states each (§L3), so all three fit comfortably under 67
in a larger alphabet — the ledger's own BB(19,5) is an ε₀ engine in 19 states, and BB(94,5) is at
`ψ₀(Ω₂)` in 94.

That is the honest form of the answer to "can we get ε₁/ζ₀/η₀ in <67 states, 2 symbols": **ε₁ yes,
ζ₀ and η₀ probably not — but 67 is a state bound, not a symbol bound, and symbols are the cheap
currency.** If the constraint really is 2 symbols, the target should be ε₁; if the constraint is
states only, all three are reachable at 6-8 symbols.

### 10.6 Scorecard: what exists, what is simulated, what is proved

| object | states | symbols | status |
|---|---|---|---|
| doubling engine (f₂/f₃) | 15 | 2 | [proved] score = `5·2^(n-1)` for n = 8,10,12 |
| 3 machine instances | 34/36/38 | 2 | [proved] ≥ `tower 3` ones, exactly 640/2560/10240 |
| ladder (tower height b) | 54 | 2 | [proved] 2563 ones at step 6 582 195 for b=2,c=2 |
| rung ω (core, two edits) | 26 | 2 | [simulated] no halt in 200 000 steps, marks 196 → 628 |
| rung ω^ω (level chain) | 34 | 2 | [simulated] levels 1→3→12→…, runtimes 29, 248, >3e6 |
| rung ω↑↑3 | ~30 (census) | 2 | not built here; census: BB(29) > f_{ω^ω}(3), BB(31) > f_{ω↑↑4}(3) |
| rung ω^d scaffolding (halts) | 41 | 2 | [simulated] d=1: 35 steps, d=2: 299 steps (halts, measured) |
| copy primitive | 9 | 2 | designed only |
| growing stack (ω^ω) | ~44 | 2 | designed only |
| ε₀ by glue | ~63 | 2 | designed only |
| ε₁ | ~64 | 2 | designed only |
| ζ₀ / η₀ | ~76 / ~88 | 2 | designed only |
| ζ₀ / η₀ | ~35-40 | 5-7 | designed only |

Nothing in this repository is at ε₀ or above, and the table is laid out so that this sentence
cannot be misread as a claim that it is.

The three simulated rungs are structural demonstrations, not BB records. They do start on
a blank tape and boot themselves, but two of them never halt and the halting one stops
after 35 / 299 steps, so none of them halts in f_alpha(n) steps; they sit below every row
of the census in the only sense that matters, which is the halting time.

---

## 11. What a proof would actually have to contain

### 11.1 The two layers, again

A defensible claim "machine M halts with score ≥ `f_α(n)`" is the conjunction of:

1. **Dynamics**: M's run decomposes into rounds of a specified shape, and the rank `ρ` decreases
   strictly at every round. This is the part that can be machine-checked against the table, and it
   is where every real BB analysis spends its pages.
2. **Value**: a descent of `L` rounds at rank `ρ` yields `≥ f_α(n)` ones. This is arithmetic on
   ordinals, independent of the machine.

The ledger's rows are (2) with (1) assumed. My Rocq development is (1) for one instance with (2)
replaced by a concrete number. Neither is the conjunction.

### 11.2 What `f_ε₁` needs in Rocq

To even *state* `score ≥ f_{ε₁}(3)` you need, in the proof assistant:

* a notation system for ordinals below `ε₁` (Veblen normal forms, or a well-ordering proof for the
  term language), because `ε₁ = φ(1,1)` is not a term you can write with `ω^` alone;
* fundamental sequences for that system, with the proofs that they are increasing and cofinal;
* the FGH itself, defined by well-founded recursion on the notation, plus the monotonicity lemmas
  needed to compare a computed value against `f_α(n)`.

That is a project, not a file. It is also *independent of the machine* — the same library would
serve every machine at that level, which is why it is the right thing to build once. The cheaper
alternative, and the one I used, is to state the value layer against a function you can define with
`nat` recursion alone (`tower`), and prove the machine beats it. That gives a true theorem with a
true (if low) level, and it is honest about which level it is.

### 11.3 The harness that does work today

`rocq/Bounds.v` defines `okb` — an executable checker that runs the machine for a given number of
steps and checks halt, step count and score — plus `okb_sound`, which turns any `true` result into
a real `run … = Some c'` with `halted`, `steps ≥ ns`, `score ≥ sc`. Each machine theorem then
closes with `vm_compute; reflexivity`, which is a kernel conversion check over the actual run, and
ends with `Print Assumptions` reporting `Closed under the global context`. Eight theorems, about 95
seconds, no axioms.

Its limit is measured, not guessed: `vm_compute` costs time linear in steps and memory linear in
tape length. 6.5M steps ≈ 6 s; 105M steps ≈ 82 s. Since the engine's step count is quadratic in its
output, certified scores cap out around 10⁴-10⁵ — which is where `f_3` lives. Anything above that
needs the parametric round lemma (§11.4), not more compute.

### 11.4 The lemma that would change everything

One statement:

```
  forall n, run M (K n) (mkConf q0 [] bl ...) = Some (halted config with score >= G n)
```

where `G` is the machine's round function written in closed form. Proved by induction on `n`, using
the nine sweep lemmas already in `rocq/Core.v` (`walk_F1`, `walk_F2`, `walk_F0`, `walk_R1`,
`walk_R3`, `walk_R5`, `walk_R4`, `walk_N0`, `walk_N1` — all [proved]). That converts "verified for
n = 8, 10, 12" into "verified for all n", and it is the single highest-value theorem this project
could contain. It is not in the repository. Everything in §10's blueprint is designed to be
provable *with* it, which is why the blueprints are worth building only after it exists.

---

## 12. Corrections log

Things I asserted earlier in this project that the ledger or the measurements contradict. Kept
because a document that only records successes is not usable as a reference.

1. **"No 2-symbol machine below 67 states has a proven ε₀ bound."** Wrong as phrased: the ledger's
   BB(51) row is a 2-symbol machine at `f_{ε₀+1}(8)`. What is true is that no such bound has been
   *independently verified*, and that I could not produce or certify one. The distinction between
   "does not exist" and "is not proved" matters and I collapsed it.

2. **"The ordinal has to be on the tape."** Wrong, and the user was right to push back. The ordinal
   is in the ranking function (§1.2). What *is* on the tape is a numeral or a record whose descent
   has that order type; the two are related by the analysis, not by an encoding.

3. **"Copying is the missing primitive."** Refined: the missing primitive is **refill** — feeding
   the output into the fuel field. Copy is one way to do it; glue with a measured fuel (BB(56,7)) is
   another and is cheaper. My ladder's connector already does a refill of sorts; what it lacks is
   that its fuel is fixed at boot, not read from the tape (§9.4).

4. **"BB(8,2) and BB(9,2) are the same machine with unreachable states."** Wrong: the tables differ
   in two cells, and I had only observed 400 000 identical steps. The correct statement is the one
   in §4.3 — identical *within the window*, divergence later — and it took the measurement to see
   the difference between "identical" and "identical so far".

5. **"My ladder machine has 53 states."** Off by one; the table's highest state is 53, so it has 54.
   Fixed in `README.md` and `tools/ladder.py`.

---

## 13. Reproducing everything

```
  cd tools
  python handbook_tables.py > handbook_appendix.md    # appendices A and B
  python report.py > analysis_out.txt                 # the per-machine digest
  cd ..
  ./verify.sh                                         # Rocq build + axiom audit
```

Appendix A is the table of §3 with more columns; Appendix B is every transition table up to 21
states; Appendix C is the cookbook of transcribable state patterns. `tools/analyse.py` has the
classifier, the cycle finder and the sampler if you want to point them at a machine of your own.

## Appendix A — measured profiles

All figures from a run of 400000 steps on a blank tape, start state normalised
to 0. "hot" is the share of all steps spent in the two most visited states;
"runs" and "max" describe the tape at the end of the window (run-length
encoding: runs = number of maximal constant blocks, max = longest block).

| machine | st | sy | roles (w/s/b) | hot states | ones | extent | runs | max block |
|---|---|---|---|---|---|---|---|---|
| BB(6,2) | 6 | 2 | 2/1/3 | 4:25%, 2:25% | 855 | 978 | 127 | 739 |
| BB(7,2) | 7 | 2 | 2/3/2 | 1:49%, 4:49% | 1146 | 1193 | 44 | 993 |
| BB(8,2) | 8 | 2 | 3/2/3 | 1:25%, 2:24% | 674 | 1331 | 1313 | 3 |
| BB(9,2) | 9 | 2 | 4/1/4 | 1:25%, 2:24% | 674 | 1331 | 1313 | 3 |
| BB(10,2) | 10 | 2 | 2/2/6 | 1:24%, 2:23% | 774 | 1509 | 1471 | 2 |
| BB(11,2) | 11 | 2 | 5/2/4 | 6:50%, 7:50% | 1171 | 1189 | 33 | 1010 |
| BB(18,2) | 18 | 2 | 5/3/10 | 2:49%, 0:49% | 1380 | 1405 | 45 | 975 |
| BB(21,2) | 21 | 2 | 6/6/9 | 7:50%, 5:49% | 1548 | 1554 | 11 | 1151 |
| BB(40,2) | 40 | 2 | 15/11/14 | 6:48%, 39:48% | 1291 | 1464 | 341 | 1117 |
| BB(41,2) | 41 | 2 | 15/11/15 | 6:46%, 39:45% | 1515 | 1790 | 543 | 1062 |
| BB(19,5) | 19 | 5 | 3/0/16 | 0:99%, 1:1% | 886 | 887 | 5 | 527 |
| BB(18,7) | 18 | 7 | 2/0/16 | 0:99%, 1:1% | 886 | 887 | 5 | 527 |
| BB(51,2) | 51 | 2 | 15/20/16 | 10:41%, 12:41% | 1612 | 1952 | 661 | 382 |
| BB(56,7) | 56 | 7 | 27/9/20 | 0:99%, 1:1% | 886 | 887 | 5 | 527 |
| BB(67,2) | 67 | 2 | 25/21/21 | 25:19%, 27:18% | 1793 | 1943 | 298 | 31 |
| BB(4,4) | 4 | 4 | 0/0/4 | 2:53%, 1:44% | 539 | 539 | 56 | 447 |
| BB(6,4) | 6 | 4 | 0/0/6 | 2:50%, 1:25% | 637 | 638 | 11 | 398 |
| BB(5,5) | 5 | 5 | 0/0/5 | 2:50%, 1:50% | 644 | 644 | 17 | 398 |
| BB(6,5) | 6 | 5 | 0/0/6 | 2:50%, 1:50% | 731 | 731 | 9 | 426 |
| BB(3,6) | 3 | 6 | 0/0/3 | 2:50%, 1:50% | 659 | 659 | 34 | 398 |
| BB(2,8) | 2 | 8 | 0/0/2 | 0:75%, 1:25% | 864 | 864 | 9 | 764 |

### Tape shapes at the end of the window

The first 14 runs, then the last 4 (`v^n` = n consecutive cells holding v).

- **BB(6,2)** (127 runs): `1^3 0^1 1^3 0^2 1^1 0^2 1^4 0^2 1^1 0^1 1^26 0^2 1^1 0^2 ... 0^2 1^7 0^1 1^739`
- **BB(7,2)** (44 runs): `1^993 0^2 1^72 0^2 1^44 0^4 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 ... 1^2 0^2 1^1 0^3`
- **BB(8,2)** (1313 runs): `1^3 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^2 0^1 1^1 0^1 1^1 0^1 ... 0^1 1^2 0^1 1^1`
- **BB(9,2)** (1313 runs): `1^3 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^2 0^1 1^1 0^1 1^1 0^1 ... 0^1 1^2 0^1 1^1`
- **BB(10,2)** (1471 runs): `1^1 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^2 0^1 1^1 0^1 1^1 0^1 ... 0^1 1^1 0^1 1^1`
- **BB(11,2)** (33 runs): `1^1010 0^1 1^28 0^1 1^116 0^1 1^2 0^1 1^2 0^1 1^1 0^1 1^1 0^1 ... 0^1 1^1 0^1 1^2`
- **BB(18,2)** (45 runs): `1^975 0^1 1^39 0^1 1^116 0^1 1^4 0^3 1^3 0^1 1^1 0^1 1^1 0^1 ... 0^1 1^1 0^2 1^226`
- **BB(21,2)** (11 runs): `1^1151 0^1 1^54 0^1 1^1 0^1 1^340 0^1 1^1 0^2 1^1 ... 0^1 1^1 0^2 1^1`
- **BB(40,2)** (341 runs): `1^1117 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^1 0^1 ... 0^1 1^1 0^4 1^1`
- **BB(41,2)** (543 runs): `1^1062 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^1 0^1 1^1 0^1 ... 0^1 1^1 0^5 1^1`
- **BB(19,5)** (5 runs): `3^527 4^1 1^52 2^306 0^1 ... 4^1 1^52 2^306 0^1`
- **BB(18,7)** (5 runs): `3^527 4^1 1^52 2^306 0^1 ... 4^1 1^52 2^306 0^1`
- **BB(51,2)** (661 runs): `1^382 0^2 1^2 0^1 1^248 0^1 1^5 0^1 1^5 0^1 1^5 0^1 1^3 0^1 ... 0^1 1^5 0^10 1^1`
- **BB(56,7)** (5 runs): `3^527 4^1 1^52 2^306 0^1 ... 4^1 1^52 2^306 0^1`
- **BB(67,2)** (298 runs): `1^1 0^1 1^13 0^1 1^8 0^1 1^29 0^1 1^13 0^1 1^22 0^1 1^22 0^1 ... 1^1 0^1 1^4 0^1`
- **BB(4,4)** (56 runs): `3^1 2^38 3^447 1^1 3^1 1^1 3^1 1^1 3^1 1^1 3^1 1^1 3^1 1^1 ... 3^1 2^1 1^1 3^1`
- **BB(6,4)** (11 runs): `2^42 1^183 2^1 1^398 2^1 1^6 2^2 1^1 2^1 0^1 1^2 ... 1^1 2^1 0^1 1^2`
- **BB(5,5)** (17 runs): `3^59 2^1 1^164 3^1 1^398 3^1 1^6 3^2 1^1 3^1 1^1 3^1 1^1 3^1 ... 3^1 1^1 4^4 3^1`
- **BB(6,5)** (9 runs): `3^120 1^49 3^1 1^426 3^1 1^6 3^1 4^1 3^126 ... 1^6 3^1 4^1 3^126`
- **BB(3,6)** (34 runs): `3^212 2^1 1^11 3^1 1^398 3^1 1^6 3^2 1^1 3^1 1^1 3^1 1^1 3^1 ... 1^1 3^1 1^2 2^1`
- **BB(2,8)** (9 runs): `1^1 4^1 6^1 5^67 6^23 5^5 6^1 5^764 2^1 ... 5^5 6^1 5^764 2^1`

## Appendix B — full transition tables

Generated from the 5-tuple strings in `championsReal.txt`. A cell `---`
means no transition (the machine halts if it ever reads it). `H` is an
explicit halt row. Rows with all cells defined are complete machines.

### BB(6,2) (6 states, 2 symbols, start 0)

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | write R | `1R1` | `1R0` |
| 1 | write R | `1R2` | `1RH` |
| 2 | branch L/R | `1L3` | `0R5` |
| 3 | branch L/R | `1R0` | `0L4` |
| 4 | branch L/R | `0L3` | `1R2` |
| 5 | sweep R | `1R0` | `0R4` |

### BB(7,2) (7 states, 2 symbols, start 0)

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | sweep R | `1R1` | `0R6` |
| 1 | write R | `1R2` | `1R1` |
| 2 | sweep R | `0R3` | `1RH` |
| 3 | write L | `0L4` | `0L3` |
| 4 | sweep L | `0L5` | `1L4` |
| 5 | branch L/R | `1R0` | `1L5` |
| 6 | branch L/R | `1L2` | `0R1` |

### BB(8,2) (8 states, 2 symbols, start 0)

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | sweep R | `1R1` | `0R0` |
| 1 | write L | `1L2` | `1L5` |
| 2 | branch L/R | `1R3` | `0L1` |
| 3 | branch L/R | `1R0` | `1L4` |
| 4 | sweep L | `1L7` | `0L2` |
| 5 | branch L/R | `1R6` | `1L3` |
| 6 | write R | `0R6` | `0R5` |
| 7 | write R | `1R6` | `1RH` |

### BB(9,2) (9 states, 2 symbols, start 0)

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | sweep R | `1R1` | `0R0` |
| 1 | write L | `1L2` | `1L5` |
| 2 | branch L/R | `1R3` | `0L1` |
| 3 | branch L/R | `1R0` | `1L4` |
| 4 | write L | `0L7` | `0L2` |
| 5 | branch L/R | `1R6` | `1L3` |
| 6 | write R | `0R6` | `0R5` |
| 7 | branch L/R | `0L8` | `1RH` |
| 8 | write R | `1R8` | `1R2` |

### BB(10,2) (10 states, 2 symbols, start 0)

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | sweep R | `1R1` | `0R0` |
| 1 | write L | `1L2` | `1L5` |
| 2 | branch L/R | `1R3` | `0L1` |
| 3 | branch L/R | `1R0` | `1L4` |
| 4 | sweep L | `1L8` | `0L2` |
| 5 | branch L/R | `0R6` | `1L3` |
| 6 | branch L/R | `1R7` | `1L6` |
| 7 | branch L/R | `1L2` | `0R6` |
| 8 | write L | `0L9` | `0L8` |
| 9 | branch L/R | `1RH` | `0L2` |

### BB(11,2) (11 states, 2 symbols, start 0)

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | branch L/R | `1R6` | `0L7` |
| 1 | write R | `1R10` | `1R2` |
| 2 | sweep L | `0L3` | `1L0` |
| 3 | branch L/R | `0R4` | `1L3` |
| 4 | branch L/R | `0L8` | `1R5` |
| 5 | sweep R | `1RH` | `0R6` |
| 6 | write R | `1R1` | `1R6` |
| 7 | write L | `1L0` | `1L7` |
| 8 | write L | `0L10` | `0L9` |
| 9 | write L | `1L7` | `1L8` |
| 10 | branch L/R | `1L9` | `1R4` |

### BB(18,2) (18 states, 2 symbols, start 0)

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | write L | `1L1` | `1L0` |
| 1 | branch L/R | `1R2` | `0L0` |
| 2 | write R | `1R3` | `1R2` |
| 3 | write R | `1R4` | `1R10` |
| 4 | branch L/R | `1R5` | `0L9` |
| 5 | branch L/R | `1L6` | `1R8` |
| 6 | branch L/R | `1R12` | `0L12` |
| 7 | branch L/R | `1L6` | `0R2` |
| 8 | branch L/R | `1R13` | `0L4` |
| 9 | write L | `1L0` | `1L4` |
| 10 | sweep L | `0L11` | `1L1` |
| 11 | branch L/R | `0R12` | `1L11` |
| 12 | branch L/R | `1L5` | `1R7` |
| 13 | write R | `0R16` | `0R6` |
| 14 | sweep L | `0L6` | `1L15` |
| 15 | sweep L | `0L14` | `1L15` |
| 16 | branch L/R | `1L16` | `0R17` |
| 17 | branch L/R | `1RH` | `0L15` |

### BB(21,2) (21 states, 2 symbols, start 0)

| state | role | read 0 | read 1 |
|---|---|---|---|
| 0 | write L | `0L8` | `0L5` |
| 1 | sweep R | `0R9` | `1R6` |
| 2 | branch L/R | `0R3` | `1L2` |
| 3 | write R | `1R7` | `1R4` |
| 4 | branch L/R | `1L14` | `0R7` |
| 5 | write L | `1L0` | `1L5` |
| 6 | sweep L | `0L2` | `1L0` |
| 7 | write R | `1R1` | `1R7` |
| 8 | branch L/R | `1R3` | `0L5` |
| 9 | branch L/R | `1L15` | `0R10` |
| 10 | sweep L | `0L12` | `1L11` |
| 11 | sweep L | `0L11` | `1L12` |
| 12 | write L | `1L4` | `1L13` |
| 13 | branch L/R | `0R16` | `0L12` |
| 14 | branch L/R | `0R15` | `1L14` |
| 15 | branch L/R | `1L17` | `0R7` |
| 16 | branch L/R | `1L5` | `1R16` |
| 17 | branch L/R | `1RH` | `0L18` |
| 18 | sweep L | `1L7` | `0L19` |
| 19 | write L | `1L7` | `1L20` |
| 20 | sweep L | `0L4` | `1L17` |

### BB(40,2) (40 states, 2 symbols)

Too wide to print here; see `championsReal.txt`. Role census: write 15, sweep 11, branch 14.

### BB(41,2) (41 states, 2 symbols)

Too wide to print here; see `championsReal.txt`. Role census: write 15, sweep 11, branch 15.

### BB(19,5) (19 states, 5 symbols, start 0)

| state | role | read 0 | read 1 | read 2 | read 3 | read 4 |
|---|---|---|---|---|---|---|
| 0 | branch L/R | `1R1` | `2L0` | `1R0` | `2L1` | `2L0` |
| 1 | branch L/R | `0L0` | `2R1` | `3R1` | `4R0` | `1L16` |
| 2 | branch L/R | `1RH` | `1R2` | `2L3` | `---` | `---` |
| 3 | branch L/R | `0L10` | `3R3` | `2R3` | `2R3` | `4R3` |
| 4 | branch L/R | `---` | `---` | `0R7` | `1L18` | `0R5` |
| 5 | branch L/R | `1L6` | `1R5` | `2R5` | `---` | `4R5` |
| 6 | write L | `4L4` | `1L6` | `2L6` | `---` | `4L6` |
| 7 | branch L/R | `0L8` | `1R7` | `2R7` | `---` | `4R7` |
| 8 | branch L/R | `0R10` | `0L9` | `---` | `---` | `4R10` |
| 9 | write L | `2L4` | `1L9` | `2L9` | `---` | `4L9` |
| 10 | branch L/R | `4R15` | `---` | `0L4` | `---` | `0L10` |
| 11 | branch L/R | `2R16` | `---` | `2L11` | `---` | `4L11` |
| 12 | branch L/R | `2L13` | `---` | `2R12` | `3R12` | `4R12` |
| 13 | branch L/R | `4R16` | `2R16` | `2L13` | `3L13` | `4L13` |
| 14 | branch L/R | `4L13` | `---` | `2R14` | `3R14` | `4R14` |
| 15 | write L | `3L11` | `1L15` | `2L15` | `1L16` | `4L15` |
| 16 | branch L/R | `1R2` | `3R17` | `1R12` | `3L15` | `0R14` |
| 17 | branch L/R | `3L11` | `1R17` | `2R17` | `0R17` | `4R17` |
| 18 | branch L/R | `1R2` | `1L18` | `2L18` | `1L18` | `4L18` |

### BB(18,7) (18 states, 7 symbols, start 0)

| state | role | read 0 | read 1 | read 2 | read 3 | read 4 | read 5 | read 6 |
|---|---|---|---|---|---|---|---|---|
| 0 | branch L/R | `1R1` | `2L0` | `1R0` | `2L1` | `2L0` | `---` | `---` |
| 1 | branch L/R | `0L0` | `2R1` | `3R1` | `4R0` | `1L15` | `---` | `---` |
| 2 | branch L/R | `0RH` | `1R2` | `2L3` | `---` | `---` | `---` | `---` |
| 3 | branch L/R | `0L9` | `3R3` | `2R3` | `2R3` | `4R3` | `---` | `---` |
| 4 | branch L/R | `4L4` | `1L4` | `0R6` | `1L17` | `0R5` | `2L4` | `4L4` |
| 5 | branch L/R | `1L4` | `1R5` | `5R5` | `---` | `6R5` | `---` | `---` |
| 6 | branch L/R | `0L7` | `1R6` | `2R6` | `---` | `4R6` | `---` | `---` |
| 7 | branch L/R | `0R9` | `0L8` | `---` | `---` | `4R9` | `---` | `---` |
| 8 | write L | `2L4` | `1L8` | `2L8` | `---` | `4L8` | `---` | `---` |
| 9 | branch L/R | `4R14` | `---` | `0L4` | `---` | `0L9` | `---` | `---` |
| 10 | branch L/R | `2R15` | `---` | `2L10` | `---` | `4L10` | `---` | `---` |
| 11 | branch L/R | `2L12` | `---` | `2R11` | `3R11` | `4R11` | `---` | `---` |
| 12 | branch L/R | `4R15` | `2R15` | `2L12` | `3L12` | `4L12` | `---` | `---` |
| 13 | branch L/R | `4L12` | `---` | `2R13` | `3R13` | `4R13` | `---` | `---` |
| 14 | write L | `3L10` | `1L14` | `2L14` | `1L15` | `4L14` | `---` | `---` |
| 15 | branch L/R | `1R2` | `3R16` | `1R11` | `3L14` | `0R13` | `---` | `---` |
| 16 | branch L/R | `3L10` | `1R16` | `2R16` | `0R16` | `4R16` | `---` | `---` |
| 17 | branch L/R | `1R2` | `1L17` | `2L17` | `1L17` | `4L17` | `---` | `---` |

### BB(51,2) (51 states, 2 symbols)

Too wide to print here; see `championsReal.txt`. Role census: write 15, sweep 20, branch 16.

### BB(56,7) (56 states, 7 symbols)

Too wide to print here; see `championsReal.txt`. Role census: write 27, sweep 9, branch 20.

### BB(67,2) (67 states, 2 symbols)

Too wide to print here; see `championsReal.txt`. Role census: write 25, sweep 21, branch 21.

### BB(4,4) (4 states, 4 symbols, start 0)

| state | role | read 0 | read 1 | read 2 | read 3 |
|---|---|---|---|---|---|
| 0 | branch L/R | `0L1` | `3L1` | `1RH` | `2R0` |
| 1 | branch L/R | `1L3` | `3R1` | `1L2` | `2R0` |
| 2 | branch L/R | `3R1` | `1L1` | `3L2` | `2R2` |
| 3 | branch L/R | `0R3` | `2R2` | `2L1` | `0R0` |

### BB(6,4) (6 states, 4 symbols, start 0)

| state | role | read 0 | read 1 | read 2 | read 3 |
|---|---|---|---|---|---|
| 0 | branch L/R | `1L5` | `2R0` | `3R1` | `---` |
| 1 | branch L/R | `3R3` | `2L1` | `3R1` | `1L2` |
| 2 | branch L/R | `2R0` | `1L1` | `3R2` | `2L2` |
| 3 | branch L/R | `1L3` | `2R4` | `0L0` | `1L3` |
| 4 | branch L/R | `1RH` | `0L4` | `1L5` | `---` |
| 5 | branch L/R | `2R0` | `---` | `2L5` | `2L5` |

### BB(5,5) (5 states, 5 symbols, start 0)

| state | role | read 0 | read 1 | read 2 | read 3 | read 4 |
|---|---|---|---|---|---|---|
| 0 | branch L/R | `1L1` | `3L1` | `4L2` | `2R0` | `4L1` |
| 1 | branch L/R | `3L4` | `3R1` | `1L2` | `2R0` | `4R3` |
| 2 | branch L/R | `3R1` | `1L1` | `3L2` | `2R2` | `4L2` |
| 3 | branch L/R | `1RH` | `---` | `---` | `4L3` | `4L4` |
| 4 | branch L/R | `3R1` | `---` | `---` | `4L4` | `3L2` |

### BB(6,5) (6 states, 5 symbols, start 0)

| state | role | read 0 | read 1 | read 2 | read 3 | read 4 |
|---|---|---|---|---|---|---|
| 0 | branch L/R | `0L1` | `3L1` | `4L2` | `2R0` | `4L1` |
| 1 | branch L/R | `1L5` | `3R1` | `1L2` | `2R0` | `4R3` |
| 2 | branch L/R | `3R1` | `1L1` | `3L2` | `2R2` | `4L2` |
| 3 | branch L/R | `1RH` | `---` | `---` | `4L3` | `4L4` |
| 4 | branch L/R | `3R1` | `---` | `---` | `4L4` | `3L2` |
| 5 | branch L/R | `4R5` | `3R4` | `---` | `0R0` | `3L2` |

### BB(3,6) (3 states, 6 symbols, start 0)

| state | role | read 0 | read 1 | read 2 | read 3 | read 4 | read 5 |
|---|---|---|---|---|---|---|---|
| 0 | branch L/R | `1R1` | `3L1` | `4L2` | `2R0` | `4L1` | `5L1` |
| 1 | branch L/R | `2L2` | `3R1` | `1L2` | `2R0` | `5L2` | `1RH` |
| 2 | branch L/R | `3R1` | `1L1` | `3L2` | `2R2` | `4L2` | `5L2` |

### BB(2,8) (2 states, 8 symbols, start 0)

| state | role | read 0 | read 1 | read 2 | read 3 | read 4 | read 5 | read 6 | read 7 |
|---|---|---|---|---|---|---|---|---|---|
| 0 | branch L/R | `1R1` | `3R1` | `4L0` | `1L1` | `5L0` | `6L1` | `5R0` | `1RH` |
| 1 | branch L/R | `2L0` | `6R0` | `4R1` | `7R0` | `3L1` | `6L0` | `4R1` | `4R0` |

---

## Appendix C — Cookbook: transcribable state patterns

Every pattern below is taken from code in `tools/` that runs and has been tested;
the state numbers are free, the *shapes* are what matter. `1` = mark, `0` = blank,
`R`/`L` = direction, `H` = halt (leave the pair undefined).

**C1. Boot writer.** One state per pattern cell, chained left to right; then a
walk-back that leaves the head on `C`'s first cell.

```
0: on 0 -> write 0, R, 15          ; jump entry (state 0 on blank)
15+i: on 0 -> write pat[i], R, 15+i+1     ; one state per cell, i = 0..n-1
15+n: on 0 -> write 0, L, p1       ; p1..p5 walk back: skip 1s, skip 0s
p1: 1 -> 1,L,p1 ; 0 -> 0,L,p2
p2: 0 -> 0,L,p2 ; 1 -> 1,L,p3
p3: 1 -> 1,L,p3 ; 0 -> 0,L,p4
p4: 0 -> 0,L,p4 ; 1 -> 1,L,p5
p5: 1 -> 1,L,p5 ; 0 -> 0,R,<engine entry>
```

**C2. Find a block, find its end, place a separator.** Two states, plus the
write state that *also* writes the separator (this is the off-by-one fix):

```
S0: 0 -> 0,R,S0 ; 1 -> 1,R,S1     ; skip blanks, stop on first 1
S1: 1 -> 1,R,S1 ; 0 -> 0,R,S2     ; skip the block, arrive at the blank after it
S2: 0 -> 1,R,S3                   ; first written cell (marker/U), etc.
```

**C3. Erase-to-mark and return.** Used for the copy primitive and for any
"remember this cell" instruction:

```
M0: 1 -> 0,R,M1                   ; leave a unique 0 behind
M1: ... (do work elsewhere) ...
M2: walk left until 0 -> 1,R,M3    ; the only 0 in the run is the mark
M3: continue, or 1 -> 1,R,M0 to iterate
```

**C4. Doubling pass (the 15-state engine).** `A` erases a cell of `U`, `T` tests
whether `U` has more, `F1`/`F0`/`F2` sweep right over `U`/gaps/`W`, `F2` writes a
`1` on the blank after `W` and `G1` writes the second one, then `R1`–`R5` sweep
back left over `W`, `U`, gaps and the counter `C`, and `A2`/`T2` erase one cell of
`C`. The 2-cells-per-cell append is the growth engine; `N0`/`N1` re-enter the pass.
Full table: `machines/machine_1_omega.txt`, states 0–14.

**C5. Fuel erase, test, and return.** From `tools/ladder.py`:

```
FK: 0 -> 0,L,FK ; 1 -> 1,L,FL     ; skip the gap to the fuel
FL: 1 -> 1,L,FL ; 0 -> 0,R,FD     ; go to the fuel's left end
FD: 1 -> 0,R,FT                   ; erase the leftmost fuel cell
FT: 1 -> 1,R,FG ; (0 undefined = halt)   ; fuel remains?
FG: 1 -> 1,R,FG ; 0 -> 0,R,FR     ; skip the rest of the fuel
FR: 0 -> 0,R,FR ; 1 -> 1,R,<engine entry>  ; walk back to the new counter
```

**C6. Copy primitive.** Nine states, `C0`-`C8`, listed in §10.2.

**C7. Glue.** A composition needs exactly one transition: the engine's halt pair
maps into the connector's entry, e.g. `(12, 0) -> (0, R, SCAN)`. Everything else
is disjoint state ranges. This is why glue proofs are cheap and engine proofs are
not.
