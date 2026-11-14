# Machine 14 closure audit

Target: `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`

Source language: mxdys, 2025-11-07, `corpus/knowledge/discord/bb2x5/chat/2025-08-09--2025-11-20.md`.

## Literal pair-language test

I tested the literal pair-based reading

- left: `0 11 (01|11|03)*`
- head: `<A` or `A>`
- right: `(22|14|24|21)* 0`

with the head marker at the boundary and the machine's normal `(write, direction, next state)` semantics from `bb.py`.

### `A>` fragment

Enumerated all left-pair suffixes of length 0..6 and right-pair suffixes of length 0..6:

- 2,985,984 configurations checked
- 0 A-state escapes
- 2,239,488 transitions into B

This is a bounded audit, not a proof of closure.

### `<A` fragment

The literal pair language is not closed. The first escape is:

```
input:  01101010101<A222222220
        (left = 01101010101, current symbol = 1, right = 222222220)

A1 -> 2LA
        write 2, move left, stay A

output: 0110101010<A2222222220
        left = 0110101010 ends in 0, so it is not
        a legal `0 11 (01|11|03)*` word
```

This is a language escape, not a halt: the next transition is `A0 -> 1RB`.

## Why this is not yet a disproof

The 2025 note also contains the separate contexts

```
(01|11|03|1)* A>
01|11|03|1 <A|A> 1|2|4
```

so a lone `1` before the head is explicitly allowed. The literal pair-only regex used above omits those rules. Therefore the escape above may be an artefact of the incomplete transcription rather than a real reachable configuration.

The 2026 correction ("nearly closed"; only halt route is `2>` meeting `21$`) was supplied by the user on 2026-11-06 as two images. It is transcribed in `machine14_2026_rules.md`, together with the later `A = [<A^-1 A>]` table. Those tables have not yet been checked against the raw machine or encoded in Rocq; their `A`/`2>` head-composition semantics remain to be fixed.

## Status

- No Rocq theorem for machine 14 exists.
- No ledger entry was added.
- `championsReal.txt`: 1,185 lines, SHA-256 `222631753464966fe8ecc14229970eae5930c9556e216cc6cb0edc1508eacbd4`.

To complete the audit, the missing 2026 rule table (and the 2025 accompanying image, if it contains the full context table) must be transcribed or supplied.
