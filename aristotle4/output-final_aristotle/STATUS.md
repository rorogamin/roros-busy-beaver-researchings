# Project status

The uploaded archive (`66a5222e-...-aristotle.tar.gz`) has been unpacked:

- `RequestProject/` — the archived Lean development for the machine
  `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA` (`Machine`, `Counter`, `Macro`, `RoundTrip`,
  `Binary`, `Pass`, `Shield`, `Frontier`, `Main`). Builds with no `sorry`.
  `not_halted_before_hundred_million` (Machine.lean) and one check in Pass.lean use
  `native_decide`, i.e. they trust the Lean compiler.
- `aristotle_archive/` — the archived `ANALYSIS.md`, earlier run summaries and the
  source of the helper tools (simulation code, not verified; compiled binaries omitted).

`lakefile.toml` now also declares the `RequestProject` library, so the
`import RequestProject.Macro` in both drafts resolves.

## The two drafts

`tm_mixed_radix_result/RequestProject/MixedRadix.lean` and
`tm_overflow_progress/RequestProject/Overflow.lean` now **compile**, with no
`sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
Only one kind of fix was needed: in five `have` steps (MixedRadix lines 41, 55;
Overflow lines 40, 52, 73), `cases u ++ r <;> rfl` was preceded by
`simp only [List.cons_append]`, so that `u ++ r` appears as a subterm. No
statement was changed.

What these files prove: local, context-independent excursion rules and their
composition (`mrAdd_single_sound`, `mrAdd_value`, `fresh_overflow`,
`productive_return`, ...). They do **not** prove halting or non-halting from the
blank tape, and they do not show that the blank-tape run reaches the
"productive" family. The step counts \(10^{100}\) and \(10^{1000}\) in the READMEs
come from the Python/C++ tools and are **not** checked in Lean. The largest
Lean-checked bound is still \(10^8\) steps.
