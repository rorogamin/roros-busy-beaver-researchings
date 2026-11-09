## Appendix A - measured profiles

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

## Appendix B - full transition tables

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

