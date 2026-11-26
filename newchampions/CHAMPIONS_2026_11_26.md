# New Busy Beaver Champions & `roro+1` Core (2026-11-26)

## 1. New `BB(4,4)` Champion (`> f_omega^12(2{31}4) > f_{omega+1}(12)`)

- **Strict TNF**: `1RB1LA1RZ3LA_1RC3RB2LC1LB_1RD3RD1RC2LB_2LA3RD1LC0RA`
- **Core-labeled form** (`{B, C, D}` = `Core-B`, wrapper = `A`): `3RC1RZ2LA3LA_3RD3RB1LC2RD_3RB1LB3LC2RC_1LA3LB0RA2RD`
- **Lower bound**: `S > f_omega^12(2{31}4) > f_{omega+1}(12)` (13 full Ackermann passes, 31 nested calls to `F(B_i, .)`)
- **Verifier**: `verify_bb44_fw12_and_roro_plus1.py`

### Proof Summary (Core-Labeled Form)
1. **Blank-tape bootstrap** (1,380 raw steps):
   `0^inf [A:0] 0^inf --(1380 steps)--> 0^inf 3^1 2^32 [D:1] 0^inf` (`a_1 = 1, B_1 = 32, r_1 = 1`; all 4 states & 4 symbols visited).
2. **Core-B macro-rule (`{B, C, D}`)**:
   `0^inf 3^a 2^B [D:1] 1^{r-1} 0^inf ---> 0^inf 3^N 2^B [D:0] 0^inf`
   where `N = F^r(B, a) >= (2 ↑^{B-1} (a+3)) - 3` and `N === -3 (mod 2^{65536})` for all `B >= 4`.
3. **Exact Period-4 (`5/4` Collatz-shift) A-wrapper** (`B = 4q + rem`, `q >= 1, N >= 1`):
   - `rem = 0`: `---> 0^inf 3^1 2^{N + 5q - 1} [D:1] 1^2 0^inf` (`r = 3`)
   - `rem = 1`: `---> 0^inf 3^1 2^{N + 5q + 1} [D:1] 1^1 0^inf` (`r = 2`)
   - `rem = 2`: `---> 0^inf 3^1 2^{N + 5q + 3} [D:1]     0^inf` (`r = 1`)
   - `rem = 3`: `---> HALT` (via `A1 = 1RZ`)
4. **Exact 2-adic orbit from `B_1 = 32`**:
   `32 -> 36 -> 41 -> 48 -> 56 -> 66 -> 80 -> 96 -> 116 -> 141 -> 173 -> 213 -> 263 === 3 (mod 4) -> HALT` on Pass 13.

---

## 2. New `roro+1` (`4x4`, `nd = 14`) $f_{\omega+1}$ Cores

Built by wrapping roromachine14's 9-instruction `3x4` `f_omega` core (`3LB3RA2RB1LA_---2RA3LB1LC_------3RB1LC`) with 1 counter-decrementing state `D` (`14` defined transitions, leaving **2 free slots** for an outer wrapper/exit!).

### Primary `roro+1` Core (Linear Single-Pass, `csym = 2`, `nd = 14`)
- **Partial TM**: `3LB3RA2RB1LA_---2RA3LB1LC_---1LD3RB1LC_3RA2RD1RD3RD`
- **Free slots**: `B0` (clean exit when `c = 0`), `C0` (completely unused!)
- **Input tape**: `0^inf 2^c 1 2^k 3^B [A:0] 0^inf` (`c >= 0, k >= 2, B >= 3`)
- **Macro-rule**:
  - For `c >= 1`: `(c, k, B) ---> (c - 1, B, N + 2)` where `N = F_roro(k, B) >= f_omega(B)` (wrapper executes in `B + N + 4` steps!).
  - For `c = 0`: exits cleanly at `[B:0]` with final Ackermann output `> f_omega^c(B) ~ f_{omega+1}(c)`.

### Variant B (`csym = 2`, `nd = 14`, 4-step exit)
- **Partial TM**: `3LB3RA2RB1LA_---2RA3LB1LC_---1LD3RB1LC_0LA2RD1RD3RD`
- **Free slots**: `B0` (4-step clean exit when `c = 0`), `C0` (unused)
- **Macro-rule**: `(c, k, B) ---> (c - 1, B + 1, N)` for `c >= 1`; exits at `[B:0]` in 4 steps when `c = 0`.

### Variant A (`csym = 3`, `nd = 14`, 4-step exit)
- **Partial TM**: `3LB3RA2RB1LA_0RD2RA3LB1LC_1LD0LD3RB1LC_1RB------0RA`
- **Free slots**: `D1` (4-step clean exit when `c = 0`), `D2` (unused)
- **Input tape**: `0^inf 3^c 1 2^k 3^B [A:0] 0^inf`
- **Macro-rule**: `(c, k, B) ---> (c - 1, 2, N + B)` for `c >= 1`; exits at `[D:1]` in 4 steps when `c = 0`.
