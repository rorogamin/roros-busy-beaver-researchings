# BB(2,5) prefix-safety proof package

Read PROOF.md first. It gives a mathematical nonhalting argument for the 3RA
and 2LA members of the supplied 13-machine family. The new argument has not
been Lean-kernel checked in this session.

Files:

- PROOF.md: complete mathematical argument and case analysis.
- FORMALIZATION.md: detailed map into the supplied Aristotle Lean project.
- PrefixSafetySeed.lean: proposed small Lean seed/spinout lemmas, not compiled
  here; no main nonhalting theorem is represented by an axiom or sorry.
- verify_prefix_safety.py: finite independent consistency checks of the new
  definitions and constructive return lemma against the supplied simulator.
- verification_results.json and verification_log.txt: recorded test run.
- check_components.py and component_results.json: separate reset-bridge and
  matched-group finite tests.
- reference_tools/: three unchanged scripts from the supplied Aristotle
  archive, used as a separate reference implementation.

Run with Python 3.10 or newer, from this directory:

```
python verify_prefix_safety.py --max-length 10 --random 200
python check_components.py
```

No third-party Python dependencies are required. The test suite is not a
formal certificate and is not the reason the infinite-run claim follows;
the universal lemmas and return proof in PROOF.md are the reason.

To try the small Lean file, copy it to
`RequestProject/BB25/PrefixSafetySeed.lean` inside the supplied project and run
its usual Lean/Lake environment. See FORMALIZATION.md for the main proof.
