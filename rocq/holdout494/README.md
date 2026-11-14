# BB(3,3) holdout 494 — Rocq 9.1 port

Machine:

```text
1RB2LA0LA_2LC---2RA_0RA2RC1LC
```

The compiled theorem is:

```text
nonhalt : ~ halts tm c0
```

`Check494.v` also runs `Print Assumptions nonhalt`; on Rocq 9.1 it reports:

```text
Closed under the global context
```

## Provenance

This is not a new proof. It is a compatibility port of the complete proof in
`bbwork/vendor/busycoq/verify/BB33_494.v`, whose header credits Jason Yuen for
the Coq proof and Matthew House for the proof sketch. The mathematical argument
is unchanged.

The port:

- replaces old `From Coq Require` imports with `From Stdlib Require`;
- maps the removed `Lists.Streams` module to `Streams.Streams`;
- maps `Bool.Sumbool` to `Init.Sumbool`;
- replaces TLC's unused `Axiom inj_pair2` with
  `Eqdep.EqdepTheory.inj_pairT2`;
- keeps only the dependency closure needed by `BB33_494.v`.

The last change removes the only `Axiom` in the port. `Print Assumptions` is
still closed, so the theorem does not depend on it.

## Build

```bash
cd rocq/holdout494
bash build.sh
```

The default `coqc` must be Rocq 9.1 (or a compatible version providing
`Stdlib.Streams.Streams` and `Stdlib.Logic.Eqdep`).
