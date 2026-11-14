# Exploration tools

These are the (unverified) scripts used to produce the empirical observations
of `ANALYSIS.md` §4.  They all simulate the machine
`1RB---3RA2LA2RB_2LB3LA4LB4RA0RA` from the blank tape; nothing here is part of
the formal development in `RequestProject/`, which stands on its own.

| file | what it does |
|---|---|
| `sim.c` | fast C simulator; prints one line per epoch (frontier move) with the epoch length, the tape width and the closest approach of a cascade to the frontier. `gcc -O2 -o sim sim.c && ./sim 200000000000` |
| `cascade_predictor.py` | finds every long cascade and compares its actual stopping cell with the one predicted by the two-mode (`P`/`Q`) cascade automaton of §4.1 |
| `visit_profile.py` | prints the number of head visits to each cell during one epoch (the profile that exhibits the two counters) |
| `line_crossings.py` | records the head's crossings of a fixed line and the time spent on each side (this is where the `2k+1` increment costs are visible) |
| `two_counter_view.py` | decodes the region right of a fixed line as a binary counter in two-cell blocks (`2 4 ↦ 0`, `4 4 ↦ 1`) and prints its value at every entry of the head |

Usage of the Python scripts: `python3 <script> <step-limit> <epoch> [<line offset from the frontier>] [<count>]`.

Tools added for §6 (the binary region counter):

| file | what it does |
|---|---|
| `markerstats.c` | counts the marker events (`B3 → 4RA`), how many of them satisfy the hypothesis of the proved rule `marker_increment`, how many machine steps those cover, and the histogram of carry lengths. `gcc -O2 -o markerstats markerstats.c && ./markerstats 2000000000` |
| `tripstats.c` | per-round-trip statistics: how far right of the counter the head gets and how long each trip takes, with a histogram and a record list. `gcc -O2 -o tripstats tripstats.c && ./tripstats 2000000000` |
| `tripstats.py` | the same in Python, printing one line per trip |
| `roundtrip.py` | prints the full zig-zag of one round trip (all local extrema of the head position) |
| `bincounter.py` | reads the cells right of a marker as binary digits in two-cell blocks and prints the value at every marker event |

Tools added for §7 (the pass function and the cascade shield):

| file | what it does |
|---|---|
| `shield.c` | classifies every cascade death: the stopping symbol, the mode, the length of the cascade, and — for a stopping `4` — which transition wrote it (`B2`, the sweep, or `B3`, a marker event). `gcc -O2 -o shield shield.c && ./shield 20000000000` |
| `shape.c` | prints the whole used tape at every local minimum of the head position |
| `shape2.c` | prints the tape each time the head leaves the cell next to the frontier |
| `shape3.c` | one line per round trip: the tape at the turning point, with the leftmost and rightmost cell of the trip relative to the frontier |
| `fours.c` | counts the cells holding `4` between the frontier and the head, and reports their distribution at every cascade birth. `gcc -O2 -o fours fours.c && ./fours 20000000000` |

Tools added for §8 (is the ternary counter ever Cantor-compatible at a cascade?):

| file | what it does |
|---|---|
| `cantor.c` | at every cascade birth, reads the ternary counter word next to the frontier and reports its value, its number of digits `1` and whether it satisfies the Cantor criterion of `cross_digits_iff` (no digit `1`, no two consecutive digits `2`). A cascade is delimited properly here: its end is detected at the three stopping patterns, so one long cascade is counted once. `gcc -O2 -o cantor cantor.c && ./cantor 20000000000` |
