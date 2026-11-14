# Target A3/B1 context findings

Dump produced by `a3context.c`:

```bash
./a3context.exe 10000000000 logs/a3context_1e10.csv
```

At `10^10` steps the dump contains **540 A3 births** and **315 B1 visits**.
The CSV records the nearest-first left tape (up to 80 cells), the distance to
the nearest `4` (`d4`) and nearest `1` (`d1`), and the same prefix for B1.

## A3 births

- `no4=0`: every A3 has a `4` in the scanned left context.
- `no1=0`: every A3 also has a `1` in the scanned window; the frontier is
  present.
- `deep_fail=0`: every nearest `4` has a nonempty used-tape context farther
  left.  This independently confirms the sharpened `A3ShieldDeep` on the dump.
- `d1 <= d4` violations: **0**.
- Maximum `d4`: **76** at step `937249590` (`d1=89`).  The distance is not
  bounded by a small radius in this prefix.
- `d1-d4` margin counts below 13: `1:68, 4:2, 5:35, 6:15, 10:2, 12:14`.
- All 68 margin-1 events have the pattern `4 1` at the frontier.  Across all
  A3 events, the cell immediately beyond the nearest `4` is `0` (472 events)
  or `1` (68 events), never `2`, `3`, or `4`.
- The dominant nearest-first prefixes are `3020…` and `0202…`; length-8
  prefixes are still highly regular:
  `30202020` (128), `02020202` (126), then `02302020` (22), `33020202` (20),
  `34020202` (20), `40202020` (19), `41240202` (15).

Interpretation: the A3 shield is structurally real, but it is not a fixed
radius-8/local property.  The near misses are exactly the `4 1` boundary
pattern, which is the useful shape for a preservation proof.

## B1 visits

- **0** B1 visits have a leading `1` in the left prefix; this is consistent
  with `B1Safe`.
- **281/315** B1 prefixes have a `4` before any `1` within the 80-cell window.
- **34/315** have no `4` anywhere in that window (e.g. `00000000`,
  `20202020`-type prefixes).

Therefore a single uniform “every left mover has a 4 before any 1” invariant
is false.  `B1Safe` must remain a separate immediate-left condition.  This is a
negative structural result, not a failure of the finite check: no B1 leading
`1` was observed.

## 10^11 extension

`./a3context.exe 100000000000 logs/a3context_1e11.csv` completed with:

- 657 A3 births: `no4=0`, `no1=0`, `deep_fail=0`, max `d4=76`;
- 70 margin-1 events (all still the `4 1` boundary pattern);
- 377 B1 visits: 0 leading `1`, 341 with a `4` before a `1` in the window,
  36 with no `4` in the window.

The independent archive tools at the same bound:

- `fours 100000000000`: 358 cascade births, minimum 1 four between frontier
  and head; `1:30, 2:16, 3:17, 4:55, 5:107, 6:18, 7+:115`.
- `cantor 100000000000`: 84 cascades, 0 Cantor-compatible, 84 blocked by a
  digit `1`, 0 blocked only by `22`.

## Margin-1 successor check

`./a3margin.exe 10000000000` follows each of the 68 margin-1 events to the
next A3.  All **68/68** successor A3s are deep (there is a cell beyond the
nearest `4`); 52 successors are themselves margin-1.  The earlier `deep=0`
counts for seven events used an incorrect `d4 >= 2` test; with the correct
`d4 >= 1` plus a genuine cell beyond the `4`, there are no exceptions.

This supports the local preservation picture, but it is a finite check, not
a proof that the next A3 is always deep.

## Reproduce

```bash
cd bbwork
gcc -O3 -o a3context.exe a3context.c
./a3context.exe 10000000000 logs/a3context_1e10.csv
py -3.14 analyze_a3.py logs/a3context_1e10.csv
py -3.14 margin_a3.py logs/a3context_1e10.csv
py -3.14 analyze_b1.py logs/a3context_1e10.csv
```
