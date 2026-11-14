# BB(2,5) 37 — bouncers structural pass

Date: 2026-11-07

## Completed result

Decider: `vendor/bouncers/bouncers.exe` (structural bouncer certificate finder).

Input: `h25_37.txt` (37 machines; same list as the formal 37).

Command:

```sh
cd vendor/bouncers
./bouncers.exe -n 1000000 -pm=1 -cores 8 < ../../h25_37.txt
```

Result:

- exit status: `0`
- wall time: 44 s
- stdout: 0 lines, therefore **0 bouncer certificates**
- stderr: empty, therefore no parse failures or panics
- all 37 input lines were read by the driver

Positive control: the same binary produced a valid short certificate for
`1RB---_0LB0LC_1LD0RE_0RE0LA_1RC1RD` at `-n 10000 -pm=1`, so the empty result
is not a broken-invocation artifact.

## What this does and does not establish

At the 1,000,000-step scan cap, the structural bouncer decider found **no
bouncer certificate** among the 37 machines. This is a completed finite decider
pass, not a nonhalting proof for any of the 37.

## Excluded attempts

- A 10,000,000-step run did not complete within the command window; its process
  was stopped with empty stdout/stderr. It is not reported as a result.
- The existing FAR binary aborts on these inputs at
  `MAX_WORD_LENGTH=32` (`main25.cpp:327`), so no completed FAR result is
  claimed.
