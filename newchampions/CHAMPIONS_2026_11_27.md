# New `BB(3,5)` Champion (`> f_omega^4(2{4}4)`) — 2026-11-27

## New `BB(3,5)` Champion (`5` Full Ackermann Passes, `> f_omega^4(2{4}4)`)

- **Strict TNF**: `1RB2RA1LA3LA4LB_2LB2RC4LA2LA1RB_1RZ2RC3RB2LB1LB`
- **`roro`-labeled form**: `3LB3RA2RB1LA4RA_1RB2RA3LB1LC1RA_1RZ4LB3RB1LC1RB`
- **`Core-B`-labeled dual**: `3RB1LB3LA2RA4LA_2LB3RB1LA2RC2LA_1RZ3LB4RB2RC2LB` (exact TNF-isomorphic!)
- **Lower bound**: `S > f_omega^4(2{4}4)` (5 full `roro` Ackermann passes with `B_{i+1} = B_i + N_i - 1`, strictly beating the 2024 `BB(3,5)` champion `1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC` of `~f_omega^2(16)` by 3 full $f_\omega$ iterations!)
- **Irreducibility**: All 15/15 transitions used.
- **Verifier**: [verify_bb35_fw4.py](file:///E:/Projects/st/bbwork/newchampions/verify_bb35_fw4.py)

### Proof Summary (`roro`-Labeled Form)
1. **Blank-tape bootstrap** (139 raw steps):
   `0^inf [A:0] 0^inf --(139 steps)--> 0^inf 113 1 2^2 3^5 [A:0] 0^inf` (`L_1 = '113'`, `k_1 = 2`, `B_1 = 5`).
2. **`roro` core macro-rule** (`L` untouched on the left):
   `0^inf L 1 2^k 3^B [A:0] 0^inf ---> 0^inf L [C:1] 1^{B+1} 3^N 0^inf`
   where `N = F_roro(B, k)` (`B=1 -> 2k+1`, `B=2 -> 2^{k+2}-3`, `B=5, k=2 -> N_1 > 2{4}4`, and `N > f_omega(B)` for all `B >= 5, k >= 2`).
3. **Unconditional Left-Counter Wrapper** (for ALL `B >= 2, N >= 1`, independent of modular residues!):
   - `L_1 = '113'`: `113 [C:1] 1^{B+1} 3^N 0^inf ---> 243 1 2^2 3^{B+N-1} [A:0] 0^inf`
   - `L_2 = '243'`: `243 [C:1] 1^{B+1} 3^N 0^inf ---> 212 1 2^2 3^{B+N-1} [A:0] 0^inf`
   - `L_3 = '212'`: `212 [C:1] 1^{B+1} 3^N 0^inf ---> 222 1 2^2 3^{B+N-1} [A:0] 0^inf`
   - `L_4 = '222'`: `222 [C:1] 1^{B+1} 3^N 0^inf ---> 33333 1 2^2 3^{B+N-1} [A:0] 0^inf`
   - `L_5 = '33333'`: `33333 [C:1] 1^{B+1} 3^N 0^inf ---> HALT` in 7 steps (via `C1=4LB`, `B3=1LC`, `C3=1LC` across `33333`, `C0=1RZ`).
4. **Exhaustive Search Coverage in `BB(3,5)`**:
   - Exhaustive all-$P$ (`P in {2..16}`) over `Core-B [A:0/2/4]` and `roro [C:1]` (600 roots): 0 engines $\ge 5$ passes.
   - Exhaustive blank-tape-first lazy-DFS over all 6 free slots of `Core-B` (2.81M nodes), `roro` (2.78M nodes), and 10-instr 1-detour `3x5` cores (`CoreB-4DET`, `roro-4DET`, 498k nodes): global ceiling = **5 true $f_\omega$ reloads (`> f_omega^4(2{4}4)`)**.
