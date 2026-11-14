# Summary of changes for run d4631eef-4a5e-44a6-ba73-3d788fcc4a24
Agreed, there are no outliers, so the project stays as it is.

From the clean rebuild I just ran:
- `lake build RequestProject` succeeds with no errors or warnings.
- No file under `RequestProject/` contains `sorry` or `admit`.
- All 14 non-halting theorems in `RequestProject/BB25/Check.lean` (the 13 family members plus the `…4RB0LB` sibling) use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each project file takes 15–56 seconds to build, and about 15–18 seconds of that is just loading Mathlib. When I profiled the two slowest files, no single proof step took more than about 5 seconds.

I didn't change anything this time.

# Summary of changes for run 9ea8a5b8-d82e-48a0-878a-8598d0b888d9
I re-checked all 14 machines in the pruned project: the 13 family members and the sibling `1RB2LA0RB1LB---_1LA3RA1RA4RB0LB` (B3 = 4RB). All 14 are proved never to halt from the blank tape.

**What I checked**
- **Clean rebuild:** I deleted the project's compiled output and rebuilt everything from scratch. `lake build RequestProject` finished successfully with no errors or warnings.
- **No gaps:** a search of `RequestProject/` found no `sorry` or `admit`.
- **Axioms:** each of the 14 theorems in `RequestProject/BB25/Check.lean` (`not_halts_2LB`, `2RB`, `1LB`, `1RB`, `0LB`, `0RB`, `3RA`, `2LA`, `2RA`, `1LA`, `1RA`, `0LA`, `0RA`, `not_halts_sibling`) relies only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Right machines:** each theorem is stated as `¬ Halts (fromStd "<bbchallenge string>") init`. `fromStd` decodes the machine from its bbchallenge string, and the file checks cell by cell that the decoded table matches the one used in the proof.

**Sibling proof**
- The main result is `BB25.Sibling.not_halts_sibling`, in `RequestProject/BB25/Sibling/Final.lean`.
- It reuses the `0RB` proof: the same checkpoints, the same 156-step start and the same shared branch lemmas.
- The one part that differs is where the sibling's B3 = 4RB rule changes the behaviour; that is proved separately in `Sibling/Pop.lean`.

**Project after pruning**
- It went from about 21,600 lines in 71 files to about 15,200 lines in 55 files.
- `PROOF_OVERVIEW.md` maps the proof. `ANALYSIS.md` keeps the historical notes and adds sections on the sibling and the cleanup.

**Caveat on the Properties table:** I fixed the sibling entry's comment, which pointed at a file that no longer exists. Older entries from earlier sessions may still point at files deleted in the pruning; I couldn't review the full table, so some of those may be out of date.

# Summary of changes for run 46d73dd8-531b-4797-bce9-5601fdca67c2
**`0LB` is now proved non-halting in Lean, so all thirteen family members are formally settled.**

The main theorem is `BB25.Prefix.not_halts_0LB : ¬ Halts (M b4_0LB) init`, in `RequestProject/BB25/Prefix/LB0/Final.lean`, for `1RB2LA0RB1LB---_1LA3RA1RA4LB0LB`. It contains no `sorry` and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The whole library builds. The only build warning is an unused variable in `Prefix/Except.lean`, a file I didn't touch.

**What I used from the three folders**
- **New `0LB` package (`PROOF_0LB.md`):** this is the argument I formalized. It uses a single-return invariant at checkpoints of the form `L c Z <B1 22^r 1`. I followed it section by section and found no errors.
- **Old `0RB` folder (`PROGRESS_0LB.md`):** this is the part you suspected might be useless, and it wasn't needed. It reduced `0LB` to an unproved statement that a "`ZZZ`-rooted" shape comes back after one or two returns; the new invariant makes that unnecessary. Only its idea of an "energy" for the four-decrement pops carries over.
- **Old `1LA` and `0RB` work:** I reused Lean pieces already in the project, such as the paid reset stack, repeated decrements, the drain digits and the exact drain lemma, plus the general bound `trun_ge_qgain`.

**New files, in `RequestProject/BB25/Prefix/LB0/`**
- `Energy.lean`: the energy calculation on words (`X ↦ ⌊e/2⌋ − 3`) and **Lemma 3.1**, the energy version of the expanding-close bound.
- `Clock.lean`: the clock-buffer energy `4e − 2`, the `6(2^t − 1)` energy threshold for a run of pops, and the two density bounds of **Corollary 3.2**.
- `Scan.lean`: the `<B1` sweep at machine level. A pop costs four decrements (`W <B1 → D⁴ <B1 22`, through the `101`/`201` blocks), and the reverse-debt table of §6 is proved with the energy guaranteeing each decrement is available.
- `Return.lean`: the invariant `ZInv` and the return theorem `zinv_return` (§4–8, both stopping cases). From any checkpoint satisfying the invariant, the machine runs a positive number of steps to another one.
- `Final.lean`: the blank tape reaches `L ZXZZX Z <B1 22^7 1` at step 931, checked by direct computation. That checkpoint satisfies the invariant (§9), and repeating the return theorem gives the result.

**Two small differences from the written proof**
- It never needs the stack energy of §2 or Lemma 2.1. Every core is kept in the form `D^k(T w)` for an explicit reset word `w`, so all supply arguments are done on words.
- The invariant uses the actual height `h` instead of the decoded height `H` in the bound `23·2^h ≤ 24(b+1)`. That is a weaker assumption, and it is still re-established at each new checkpoint.

**The `4RB/0LB` sibling (not proved)**
- `1RB2LA0RB1LB---_1LA3RA1RA4RB0LB` is not one of the thirteen: its B3 is `4RB`, not `4LB`.
- Its local lemma file now compiles as `RequestProject/BB25/Sibling/Local.lean`. It checks the new marker rules, the ordinary rules for the new table, how one pop episode fits together, the spinouts, and the 156-step seed.
- **Its non-halting is not formalized.** Every block-level lemma in the project assumes B3 = `4LB`, and the `W <B1` rule is false for the sibling. Transferring the `0RB` proof would mean re-deriving those lemmas for a machine with B3 left open.

`ANALYSIS.md` has a new §26 recording all of this. The properties table lists `not_halts_0LB`, `zinv_return` and Lemma 3.1 as proved, along with the definition of `ZInv`.

# Summary of changes for run 8f34a2cd-c861-488f-aa59-ffcc886f9793
The `0RB` member of the BB(2,5) family, `1RB2LA0RB1LB---_1LA3RA1RA4LB0RB`, is now fully formalized as non-halting.

**Main result.** `BB25.Prefix.not_halts_0RB : ¬ Halts (M b4_0RB) init`, in `RequestProject/BB25/Prefix/RB/Final.lean`. It is unconditional — both `01` branches of the `<B1` sweep (`zodd`, `zeven`) are discharged — depends on no `sorry`, and uses only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. The whole library builds cleanly (all 8087 jobs) and a search for `sorry`/`admit` over `RequestProject/` returns nothing.

**What was finished this session.**
- Verified and committed the last in-flight cleanup (removal of unused `CStack` hypotheses from `paid_stack_facts` and, additionally, from `paid_stack_mod_eight`, with all call sites updated); the build is now also free of linter warnings.
- Confirmed the completed even-branch chain end to end: Lemma A (`gen_scan_stops`, via the leading-run criterion plus the six exceptional families in `RB/Families.lean`), Lemma B (`Prefix/Slack.lean`: the general expanding-close bound `trun_ge_qgain`, the upper bound `rrun_le_two_pow`, and the dyadic-slack statement `trun_gt_of_pow`, lifted to stacks as `slack_early`), the debt gap `gen_scan_gap` (`RB/Gap.lean`), the refined drain reading `ready_chi_ref` and Lemma C (`RB/Clock.lean`), the small clock `lemma_seven`, and the case split `zeven` (`RB/Even.lean`).
- Documented all of this in a new Section 25 of `ANALYSIS.md` ("`0RB` is settled"), which supersedes the earlier §24.3 list of open obligations; `ARISTOTLE_SUMMARY.md` was read but not modified.
- Registered `BB25.Prefix.not_halts_0RB` in the properties table with status *proved*.

Twelve of the thirteen family members are now proved non-halting in this development; `0LB` remains open.

# Summary of changes for run cca1cab2-cc25-4f81-a477-1020f2c6effb
**`1LA` is now proved non-halting, unconditionally.**  The previous state of the project reduced `1RB2LA0RB1LB---_1LA3RA1RA4LB1LA` to a single open statement, `ZReady` — that the member-independent `01` branch of the `<B1` sweep always returns to a checkpoint whose own scan succeeds.  That statement is now proved, so `RequestProject/BB25/Prefix/LA/Final.lean` contains `not_halts_1LA : ¬ Halts (M b4_1LA) init`, sorry-free and using only `propext`, `Classical.choice` and `Quot.sound`.  The whole library builds with no `sorry` anywhere.

The new development is four files under `RequestProject/BB25/Prefix/LA/`.  `Debt.lean` formalises the reverse-debt interpreter: a scan of a paid reset stack already charged with `n` decrements is read as a debt travelling right to left through the reset word, where a final one bit stops it when the debt is even, a final zero bit when it is odd, and a final pop costs the two decrements of the `1LA` rule, turning `n` into `2n+4` and requiring `2n+4` below it.  Same file: the dual-credit lemma — for a good stack `c`, the scan of `D^n(T(P(c)))` is safe as soon as `2n+2 ≤ cval c`.  Instead of the submitted proof's maximal-run peeling, the Lean proof carries a disjunction whose second alternative (`n` even, `n+4 ≤ 2·cval`, `n+2 ≤ bval`) is exactly the state of the scan inside a run of pops and is inductive on its own.  `Chi.lean` defines the drain digits `chi m` and proves the two crossing inequalities of the submitted Section 6 (`n+4 ≤ 4m`, and `n+9 ≤ 2m` for odd `n`), plus `chi (2^k m) = X^k chi m`, which identifies the document's `X^(q-1)` buffer as the head of the drain digits.  `Exact.lean` redoes the drain of the shared machinery keeping the reset word, so the checkpoint the machine actually reaches is the paid stack of `P(σ) Y^r V chi(2^(r-1)(cval σ + 1)) V` — the exact word (A) of the submission.  `Direct.lean` proves that word is always ready, and `Final.lean` does the case split of Section 7 (a counter of at least two drains; an exhausted counter overflows early, with the clean reset ready for free and the exceptional one landing in a drain with at least three `22` blocks) and concludes.

No error was found in the submitted `1LA` argument; two of its steps turned out to be avoidable and this is recorded in the notes: applying the dual-credit lemma after the pop rather than before removes the parity split on the residual digit, and the buffer needs no separate construction.  `ANALYSIS.md` has a new section 23 describing all of the above; `RequestProject/BB25/Prefix/LA.lean` was left in place with its header updated to point at the completed proof.  Eleven of the thirteen members are now verified; `0RB` and `0LB` remain, and nothing in the project claims otherwise.

# Summary of changes for run 2831d7a4-84d1-4b9a-a13f-dfb475b3327c
I picked up where the last session stopped, finished the remaining member of the previous submission, and made a start on the new one.

**`1RB` is now proved non-halting from the blank tape** (`RequestProject/BB25/Prefix/Main.lean`, `not_halts_1RB`), sorry-free and using only the standard axioms. This is the tenth of the thirteen members: `3RA`, `2LA`, `1RA`, `0LA`, `2LB`, `0RA`, `2RB`, `1LB`, `2RA`, `1RB`. The new development is `RequestProject/BB25/Prefix/JOne.lean`. `1RB` pushes the marker block `013`, so the local episode above the marker is the one already verified for `0RA`/`2RB`; the difference is that when the head returns to the marker the block disappears *without leaving a bit behind* and the head keeps going left, with a `11` block, a pending `2>` and the deposited word in front of it. With a counter of at least two below, the head pays the two decrements, pops, and the word is reset over the resulting good stack; with a counter of zero or one the head runs off the left end, the decoded word is reset first and the two pending digits then cancel, so the deposited word is read in the counter phase instead. The three deposited words are each handled explicitly, and for the long-sweep word the key point is that it is balanced: read in the counter phase it gives the counter back and multiplies the decoded value by 2^(2n+2). The checkpoint invariant was strengthened to carry the general even margin and the height bound, both supplied by goodness at the checkpoint; the four earlier members were re-proved against the strengthened invariant. I found no error in the submitted `1RB` argument.

**`1LA` is started, not finished.** It is the one member whose `A> 241` rule sends the head back into the `<B1` sweep, so the sweep can consume several pops in a row and goodness of the checkpoint is not sufficient — exactly as the submitted document says. `RequestProject/BB25/Prefix/LA.lean` formalises the part of that argument that does not need its new comparison lemma: the scan predicate `Ready`, the theorem that the sweep from a ready good checkpoint is safe and ends either in the known left-end spinout or at the member-independent `01` branch (`scan_1LA`), that the blank-tape seed checkpoint is ready, and hence non-halting of `1LA` granted one explicit hypothesis, `ZReady` — that the `01` branch returns to a checkpoint that is ready again (Sections 5–7 of the document: the exact return word, the reverse-debt interpreter and the dual-credit comparison). `ZReady` is a hypothesis of the theorem, never an axiom, so nothing claims `1LA` has been decided; what its proof still needs is recorded in the notes.

The notes were brought up to date, since the previous session did not update them: `ANALYSIS.md` now has §20 recording the four members verified then (`0RA`, `2RB`, `2RA`, `1LB`), §21 for `1RB`, and §22 for the `1LA` reduction and the precise remaining gap. The whole library builds with no `sorry`, and all the theorems mentioned use only `propext`, `Classical.choice` and `Quot.sound`. Nothing here touches `0RB` or `0LB`, whose material you said is still to come.

# Summary of changes for run b98e8fcb-5bd4-4c81-8fc0-e5dc07eb6516
Verified the three remaining claimed members in Lean. RequestProject/BB25/Prefix/Main.lean now proves not_halts_1RA, not_halts_0LA and not_halts_2LB (blank-tape non-halting), alongside the earlier not_halts_3RA and not_halts_2LA, all sorry-free and using only the standard axioms. The checkpoint sweep is proved once for every member in Return.lean via a WCase abstraction of the member-specific "A> 241" branch, which is then established in Bit.lean (1RA), Zero.lean (0LA) and Two.lean (2LB). For 0LA and 2LB the stack invariant genuinely fails at one exceptional checkpoint; the repair follows the machine one sweep further, using goodness-free forms of the tail lemmas together with new word-level bounds (Expand.lean, Except.lean): a decoded word of height at least two whose value is even, respectively divisible by four, must contain one, respectively two, expanding closes, so its transduced value is at least 11, respectively 43. These are exactly the two small-value barriers the submitted argument needs, proved structurally with no finite search. A full library build succeeds and no sorry remains. ANALYSIS.md has a new section 19 recording what is machine-checked, the file layout, and the simplifications relative to the prose argument, notably two sub-cases for 2LB that turn out to be vacuous. No error was found in the submitted argument; eight members of the family remain open.

# Summary of changes for run 3908ed15-4550-412a-b764-66b4258e00cf
Verified the submitted prefix-safety proof for the two BB(2,5) family members with B4 = 3RA and B4 = 2LA by formalizing its argument in Lean; both are now proved non-halting from the blank tape, sorry-free and with standard axioms only. The development is in RequestProject/BB25/Prefix (Word, Stack, Reset, Return, Main): the reset arithmetic and transducer, the admissibility/goodness invariant, the paid reset stack and its machine correspondence, the return theorem with all early-overflow cases and the left-end spinout, and the 156-step blank-tape seed checkpoint (counter 56, decoded value 63), giving not_halts_3RA and not_halts_2LA. Section 18 of ANALYSIS.md contains the verification report: no error was found in the submitted argument, and the two presentational deviations of the Lean route are documented there. Ready for the remaining files whenever you send them.

# Summary of changes for run b0ff94fc-9d4b-4f31-afa8-47f75f4f1786
I picked up where the previous run stopped, finished the `FValue.lean` development, got it compiling, and added a second new file that checks its criterion against the runs of all 13 members inside the Lean kernel. The whole project builds with no `sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`; the two kernel computations use `propext` only).

**`RequestProject/BB25/FValue.lean` — the rebuilt counter `f` and what invariant of it can decide halting.**
- The two exact run laws: a run of `22` blocks doubles `f + 1` per block (`rmapFrom_Yrun`); a run of `21` blocks doubles `f − 1` per block (`rmapFrom_Vrun`), because after a `21` the phase is `1>` and every further block first decrements.
- This explains the empirical `f ≡ 1 (mod 8)` — a trailing run of `n` blocks `21` forces `f ≡ 1 (mod 2^n)` (`rmapFrom_Vrun_mod`) — and disqualifies it: the dangerous value `f = 1` is fixed by such a run (`rmapFrom_Vrun_eq_one_iff`). **No congruence on `f` can certify non-halting; a lower bound is needed.**
- The quantity that works is the deficit `2^e − (f+1)`, equivalently the normalised value `(f+1)/2^e`: a bit block doubles the deficit, a shift block at least halves it, a decrement adds one (`deficit_push`/`deficit_pop`/`deficit_dec`, and the `tval_*` versions). So the normalised value only ever falls, and only at decrements, by `2^−e` each.
- Hence the criterion `rmap_f_lower`: a reset word of total cost at most `1/2` rebuilds a counter with its top bit set, `2^(e−1) ≤ f + 1` — a non-modular invariant. With `e ≥ 3` this gives `f ≥ 3` and, for the five members whose `A> 241` bounces, survival of a whole cycle (`reset_cycle_of_f_ge_two`, `reset_cycle_of_cost`); `danger_iff_f_le_one` is the converse reading.
- Two decidable forms of the criterion, since rational arithmetic does not reduce in the kernel: the integer cost at a fixed scale (`rcost_le_half_of_nat`, `reset_cycle_of_ncost`) and a coarser counting form (`rcost_le_half_of_deep`: at most `2^(m−1)` decrements, all at digit count at least `m`). The counting form is sufficient but not necessary — one of `2LB`'s reset words is cheap without passing it.

**`RequestProject/BB25/FTrace.lean` — the criterion checked against the runs.** `ovCfgs` records the overflow configurations of the accelerated block simulation, and every one of them is proved to really occur in the run (`ovCfgs_reachable`). Kernel-checked (`overflow_words_safe`): within 4000 accelerated block steps every one of the 13 members reaches at least seven overflows (in fact 9 to 12), and at every overflow from the fourth on the tape ahead of the head is a plain word of digit blocks, needs no borrow, builds at least three digits, and is cheap. Two consequences follow from the criterion rather than from inspection of the values: the counter rebuilt at each of those overflows has its top bit set and satisfies `f ≥ 3` (`overflow_top_bit`), and for the five bouncing members (`2LB`, `1LB`, `3RA`, `2LA`, `0LA`) every one of those overflow events is provably survived, ending with a well-formed counter stack and no `141`/`241` block on the tape (`bouncing_overflows_survived`).

**Status.** No member of the family is decided, and nothing in the project claims otherwise. What is now settled is the shape of the argument: for a bouncing member, non-halting follows from the single statement "every reset word is cheap", and the finite certificate above covers the first nine to twelve overflows of every member. Proving that cheapness propagates from one overflow to the next requires controlling the word the overflow deposits, which remains open. `ANALYSIS.md` §17 records all of this, separating the machine-checked statements from the exploratory measurements (e.g. the measured costs of `2LB`'s reset words, `0.25, 0.094, 0.184, 0.064, 0.0073, …`, well below the `1/2` threshold).

# Summary of changes for run 8e5dcb10-ed00-45e2-a31b-9280f183da03
## What I did

I analysed the **overflow** and **reset** events of the family, and answered the double-counter question. Everything below is machine-checked Lean (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only) unless explicitly marked exploratory. New prose is `ANALYSIS.md` §16; new Lean is in `RequestProject/BB25/Phase.lean`, `Overflow.lean` and the new `Trace.lean`.

## Your second question first: yes, it is a two-sided counter, and no, the old rule did not capture it

The earlier `cval` was the **left** counter only. The right-hand word of digit blocks now has a value of its own, and — exactly as you expected — **a different digit representation on each side/phase**: `21` is a shift in the counter phase but a bit in the reset phase, and `12` the other way round (`digit_roles_swap`; the worked example `digit_counts_differ` shows the same word `21 21 22` being `1` over one digit in one reading and `7` over three in the other).

Because of that, the right counter is carried not by a number but by a **shift map** `⟨c,d,e,f⟩`, `v ↦ ((v−c)/2^d)·2^e + f`: `f` is the right counter's value in the representation the current phase uses, `e` its digit count, `d` how many digits of the left counter it eats, `c` the **exact** overflow threshold. `cmap`/`rmap` compute it; `brun_count_dichotomy`/`brun_reset_dichotomy` prove the machine either finishes the word with the predicted value and pending digit, or overflows — precisely when `v < c`. Two structural consequences: the two sides are **one pool of blocks** (`brun_cstackRun`: `|lt'| = |lt| + |w|`), and the growth exponent is `e − d = #bits − #shifts` (`cmap_digit_count`).

## Overflows and resets

* `cdec` — the decrement as a stack operation (the borrow): `01 s ↦ 11 s`, `11 s ↦ 01 (cdec s)`, `03 s ↦ 03 (cdec (cdec s))` — a shift digit costs **two** decrements; the borrow crosses exactly the trailing zeros (`cdec_run_of_zeros`).
* `ofw` — the word the overflow deposits: the left counter re-encoded block for block into right-hand digits (`11 ↦ 22`; `03 ↦ 11` or `21`).
* `brun_overflow_reset_cycle` — one full turn of the cycle in closed form; `reset_value_bound` bounds the rebuilt counter by `2^(#blocks)`, and `overflow_reset_of_zero_bits` shows it is sharp (`n` zero bits come back as the full counter `2^n − 1`).

## Your follow-up: does the reset go differently depending on a counter value (mod k)?

* **Inside a phase, no.** `countRun_no_residue_dependence` / `resetRun_no_residue_dependence`: a phase depends on the counter only through `⌊(v−c)/2^d⌋` and the all-or-nothing test `v ≥ c`. Residues mod `2^d` are discarded, never tested.
* **At the overflow, yes — but locally.** The word handed to the reset is not a function of the stack shape alone: at each shift block the deposit is `11` or `21` according to whether the sub-counter below is exhausted, i.e. its **low bit** when it is `0`/`1` (`ofw_W_low_bit`). `overflow_word_value_dependent` gives two stacks of equal length, equal blocks and equal value `0` that deposit different words and rebuild `1` versus `3`. So the value dependence is digit-local, not a global "reset branches on `v mod k`".

## Family-wide facts, checked in the kernel (`Trace.lean`)

Running the accelerated block simulator from the blank tape inside Lean:
* `shared_overflow_prefix` — **all 13 members share their first five overflows**, with reset maps `⟨0,0,0,0⟩, ⟨1,0,1,1⟩, ⟨0,0,3,5⟩, ⟨0,0,6,57⟩, ⟨0,0,6,53⟩`.
* `reset_maps_clean` — within 4000 accelerated block steps every member reaches ≥ 7 overflows, and every reset word after the second has `c = 0` and `d = 0`: the reset never borrows and deletes no counter digit, so on that stretch the closed-form cycle applies unconditionally.

## Exploratory (simulator only, not machine-checked)

`tools/phases.py` + `tools/sweep_phases.py`, output saved in `tools/phases_sweep.txt`: the two facts above persist to the 14th overflow of every member; the rebuilt counter is odd from the 2nd overflow and `≡ 1 (mod 8)` later; members diverge from the 6th overflow. At the `<B1` events the counter is even in every logged event **except** `1LA`, which reaches a `<B1` with `cval = 25` — so "even at every `<B1`" is false for the family. Five members have `<B1` events where the left stack is not a pure counter stack at all. No member has been decided.


# Summary of changes for run 16443340-2628-4fea-8a6c-c8f20e7b1399
## What I did

Picking up from the earlier formalisation, I attacked the halting question itself with the counter structure as the ground. **No member of the family has been decided** — nothing in the project claims otherwise — but the analysis is now machine-checked down to a single arithmetical question, and two members turn out to be the same problem.

**The counter, proved (`RequestProject/BB25/Counter.lean`).** Reading the left stack from the head down, `11` is the bit 0 (`v ↦ 2v`), `01` the bit 1 (`v ↦ 2v+1`) and `03` a shift digit (`v ↦ v/2`) — a mixed-digit counter in the literal sense. Two theorems make it a counter: one head excursion into the stack decrements it by exactly one (`cval_decrement`), and if it is 0 the head instead runs off the bottom and reaches the left end (`cval_overflow`). So "the counter is 0" *is* "the head reaches the left end".

**Yes — your phases are exactly my phases, and yes, that is what I am doing with the overflow prediction.** The pending digit `1>`/`2>` is the parsing offset:
- *counter phase* (`countStep`, `brun_count`): fixed parse, `22 ↦ 2v+1`, `21 ↦ v/2`, and `11`, `12` also turn the head around, costing one decrement (`(v−1)/2`, `2(v−1)+1`);
- *reset phase* (`resetStep`, `brun_reset`): the pending digit created by the overflow marches right and re-parses the tape, which exchanges the roles of `21` and `12` — this is where the counter regains digits.

Because both phases are pure arithmetic, the overflow is predicted rather than simulated: `brun_drain` with `2 ^ drainCycles v ≤ v + 2` (at most `log₂(v+2)` round trips), and `countRun`/`resetRun` evaluate a whole word of blocks in one go. The dichotomy is complete — when a phase's arithmetic fails, the machine does not get stuck, it overflows to the left end (`brun_count_overflow`, `brun_reset_overflow`) — so a run is exactly an alternation of counter and reset phases punctuated by `<B1` events, and only the overflow/reset ends need to be looked at.

**The single danger point, sharply.** For the five members whose `A> 241` bounces (`2LB, 1LB, 3RA, 2LA, 0LA`), a `<B1` sweep started with a nonzero counter is survived *completely* — sweep, creation of the `141`, its conversion to `241` and its consumption — leaving a well-formed counter stack with no `141`/`241` anywhere (`brun_Bt_clear`, packaged as `brun_count_cycle` and `brun_reset_cycle`). Hence: if the counter is never 0 when a `<B1` sweep starts, the member never halts. I checked and corrected the converse: a zero counter there may instead run off the left end (spinout, never halts), so it is the only *chance* of halting, not a guarantee.

**Two of the thirteen are one machine (`RequestProject/BB25/Twins.lean`).** `2RB` writes `023` on the left stack, `0RA` writes `011`; the two blocks behave identically in every block rule, and renaming `023 ↦ 011` is proved to be an isomorphism of the two block simulations, so their analyses are literally the same computation and non-halting transfers either way.

**Your Fibonacci question (`ANALYSIS.md` §14).** It is a coincidence of the growth rate, not a rule. `D` (bits minus shifts at each overflow) grows geometrically; where the ratio sits near `φ ≈ 1.618` one automatically gets `D_{n−1}+D_n ≈ D_{n+1}`, since `φ² = φ+1`. For `2LB` the ratios drift upward (`1.40, 1.71, 1.66, 1.59, 1.69, 1.67, 1.77, 1.83, 1.84`) and the defect `D_{n−1}+D_n−D_{n+1}` runs `0, −6, −6, 2, −12, −28, −106, −288, −576`; other members grow at quite different rates (`2RB`/`0RA` faster than doubling per overflow). So: geometric growth with a member-dependent rate that happens to pass through `φ`.

**Why it stops there.** The words the reset phase re-parses look pseudo-random; their letter counts at successive overflows are not related by any fixed linear map (so no substitution/closed-form acceleration applies), and a search for exact linear conserved quantities found only trivial ones. Exploratory (not machine-checked): all 13 members survive 60 000 accelerated block steps with no danger, halt or spinout; `D` is positive and growing at every overflow, and is always even from the fourth overflow on. That is evidence, not a proof. Per your note I did not pursue a FAR/CTL solution.

Everything builds with no `sorry` and uses only the standard axioms; new tools are `tools/leftwords.py` (overflow-event log), `tools/dgrow.py` and `tools/one.py`. `ANALYSIS.md` has new sections §12–§15; `ARISTOTLE_SUMMARY.md` was left untouched.


# Summary of changes for run 20eb9327-ac1d-4372-988e-d948208cc798
I picked up the BB(2,5) `1RB2LA0RB1LB---_1LA3RA1RA4LB---` project and pushed the longitudinal analysis further, in two new Lean files, plus documentation and a new exploration tool. Everything builds with no `sorry` and uses only the standard axioms.

**`RequestProject/BB25/Sweep.lean` — the three sweeps (all 13 members).**
- Multi-step block runs `BRun b4 c c' k` (from `c` to `c'` at a cost of exactly `k` base steps), with soundness and transfer of halting/non-halting.
- The `<B1` sweep, the only source of the dangerous `141` block, is fully classified by the first non-`11` block of the left stack: `03` creates the `141`; `01` defuses the head into a harmless `<A 11 2>`; nothing (the left end) sends the machine into the spinout, so it never halts. This is exactly the criterion you described, now machine-checked.
- New: for the members that push `023`/`013`/`003` onto the left stack, a later `<B1` sweep reaching such a block **halts** the machine (3, 3, 5 steps).
- The `<A` sweep (turns around at the first `01`, otherwise reaches `^11` and creates a pending `2>`), and the rightward sweep of a pending `2>` (which crosses `22`/`12` unharmed). This sharpens the earlier halting criterion: the `141` need not sit next to the left end, only `22`/`12` blocks need separate it.
- New halting criterion: if the `03` that creates the `141` has nothing but `11` blocks below it, the machine halts.
- The counter step of your notes, verified with its exact cost: `11^m 01 <A 11 ⟶ 01^m 11 <A 21` in `4m+4` base steps — one excursion spends one `01`, the return leg can mint several.

**`RequestProject/BB25/Invariant.lean` — an inductive invariant for the tractable members.** For the five members whose `A> 241` bounces the head left without creating new left blocks (`2LB`, `1LB`, `3RA`, `2LA`, `0LA` — "tame"), well-formedness of the block configuration (left stack of `03`/`11`/`01` over `^11`; right stack in the shared alphabet; **at most one `141`/`241` present**, and **none while the head is `<B1`**) is proved to be an inductive invariant. Its payoff is a classification of every way the analysis can break down: a well-formed stuck configuration is either a pending `2>` in front of a `141`/`241` (which halts in 3 steps) or the head at the left end in state `<B1` (which never halts). Hence the sharpened criterion `not_halts_of_no_danger`: a tame member never halts as soon as its block simulation never puts a pending `2>` in front of a `141`/`241`.

**A caveat on the "budget" idea.** The plan of keeping enough `01`s below a pending `141` cannot work as a local invariant: I verified that the left stack `03 01 ^11` below the creating `03` also kills the machine (20 base steps), so having a `01` below is not sufficient. The fate of a `141` depends on the whole region between the left end and the block; `tools/arena.py` explores that region exhaustively for short left stacks (exploratory, not machine-checked: 831 survive, 133 halt, 129 undecided out of the 1093 stacks of length ≤ 6).

**Other work.** The block simulator gained two verified rules (`A> 1> 141 → <A 2> 141` and the `241` version — a pending `1` is harmless), which removes them from the list of breakdowns; the reference simulator in `tools/blocksim.py` was kept in sync. The whole development, including the kernel-checked running-time bounds, was rebuilt; the accelerated simulation of all 13 members again survives 20 000 block steps (base counts of order 10^123 … 10^228). `ANALYSIS.md` now has sections 9–11 recording the new verified results and stating precisely what remains open; no member has been decided, and I have not claimed otherwise.