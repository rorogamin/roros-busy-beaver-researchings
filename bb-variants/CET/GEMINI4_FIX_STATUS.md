# Gemini 4 repair status

Date: 2026-11-12

This is a work-in-progress repair, not a verification. No CET/FGH record was
changed. The original submissions remain in `gemini4_incoming/`.

## Working copies

`gemini4_fixed/` contains:

- `CET4_R8.v` — two induction-argument errors patched; full compile not
  finished.
- `CET23_R8.v` — mechanical errors patched through the prefix/decoupling
  region; full compile still fails in `run_N_decouple_deferred`.
- `Eps1Complete.v` — unchanged; its `rung_halts_gen` statement is false.
- `Eps1Counter.v` — compiled Rocq counterexample to `rung_halts_gen`.

## Eps1Complete.v: false statement

`rung_halts_gen` claims, for `m = 0`, `b = 0`, `V = []`:

    TM.run Eps1Tape.tbl 3
      (mkConf ENTRY (zeros 1 ++ on :: zeros 0) on []) =
    Some (mkConf G2 (zeros 0) on (zeros 2 ++ on :: [])).

The verified computation in `Eps1Counter.v` gives:

    TM.run Eps1Tape.tbl 3
      (mkConf ENTRY (zeros 1 ++ on :: zeros 0) on []) =
    Some (mkConf G2 [] bl [bl; bl; on]).

The claimed current symbol `on` and right tape are wrong; the actual halt is
`bl` at the head with `[bl;bl;on]` to the right. The submitted file's first
error at line 63 is therefore not a mere tactic error; the generalized rung
statement must be corrected before any proof can be accepted. This also means
the later FGH claims that depend on this statement are not established.

`Eps1Counter.v` compiles with:

    rocq compile -Q CET_ARTIFACT_BUNDLE/rocq Top gemini4_fixed/Eps1Counter.v

## CET4_R8.v: partial

Patched:

- `fast_run_outside_zero`: `apply IHn` -> `apply (IHn lo hi fc)`.
- `check_range_bool_sound`: `apply IHlen` -> `apply (IHlen (lo + 1) t)`.

The compile then proceeds much further but was still running at
`rewrite Hfc` in `prefix_5730_ok` after more than two minutes, with no `.vo`.
No completed Rocq verification of `cet4_r8_halts` is claimed.

## CET23_R8.v: partial

Mechanical repairs made include:

- `bt_interp_set` orientation;
- argument inference in `check_range_844_sound` and `fast_run_outside_zero`;
- record destructuring of `cfg_run_sound`;
- `c0 = fc_to_cfg fc0` definition alignment;
- `exp_844` range lemma;
- `Z.lt_ge_cases` replacements for unavailable `Z.gt_le_dec`;
- a series of `write_tape` case splits in the single-agent agreement and
  decoupling proofs.

The compile still fails in `run_N_decouple_deferred` at the branch where
`k_split = N.succ m` and `z` is the agent-2 position. The remaining goal
requires relating `stape (srun_N a1 m sc1) z` to the post-step tape, but the
available `Hmid` hypothesis relates the latter to the initial `sc1`, not to
`srun_N a1 m sc1`. This branch needs a proof redesign, not another tactic
patch.

No `.vo` and no `cet23_r8_halts` verification.

## Bottom line

The three submitted files cannot all be made into verified proofs by mechanical
repair:

- CET(4): still unverified until the compile completes and the theorem is
  checked.
- CET(2,3): still unverified; a decoupling branch needs a real proof.
- ε1: the stated generalized rung lemma is false, so the file must change its
  claim (and then its downstream FGH theorem) rather than merely its tactics.
