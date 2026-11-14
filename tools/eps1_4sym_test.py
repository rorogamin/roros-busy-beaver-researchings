"""Prototype 4-symbol {_, a, b, c} 2-row PSS TM + optimal 4->2 binary compiler + Moore minimizer."""

SYM4 = ['_', 'a', 'b', 'c']
SYM2_ENC = {'_': (0, 0), 'a': (0, 1), 'b': (1, 0), 'c': (1, 1)}


def build_4sym_tm():
    # States are named strings; transitions: (state, sym4) -> (write4, dir ('L'/'R'), next_state or None for HALT)
    T = {}

    def add(st, rules):
        for syms, (w, d, nxt) in rules.items():
            for s in syms:
                T[(st, s)] = (w if w != '=' else s, d, nxt)

    # Boot from blank tape: write "a a a a _ b c b b c c b b c c" (n=4, S=[(0,0),(1,1),(1,1)])
    # Leave head at blank '_' right of S, transition to POP_CHK (moving L).
    boot_str = 'aaaa_bcbbccbbcc'
    for i, ch in enumerate(boot_str):
        nxt = f'BOOT_{i+1}' if i + 1 < len(boot_str) else 'POP_C'
        T[(f'BOOT_{i}', '_')] = (ch, 'R' if i + 1 < len(boot_str) else 'R', nxt)
    # After writing last 'c', one step R hits '_' then L to POP_C:
    T[('POP_C_FROM_R', '_')] = ('_', 'L', 'POP_C')
    # Fix last boot step to step onto '_' and goto POP_C: wait if last boot writes 'c' and moves L, it's ALREADY on last 'c' -> POP_C!
    T[(f'BOOT_{len(boot_str)-1}', '_')] = (boot_str[-1], 'R', 'GO_END_WAIT')
    T[('GO_END_WAIT', '_')] = ('_', 'L', 'POP_C')

    # --- Dispatch rightmost entry (head on rightmost char of S, should be 'c') ---
    T[('POP_C', 'c')] = ('c', 'L', 'POP_2')
    T[('POP_2', 'c')] = ('c', 'R', 'CMP_START')   # (d, 1) -> CMP
    T[('POP_2', 'b')] = ('b', 'L', 'POP_3')       # (d, 0) -> check d==0 vs d>0
    T[('POP_3', 'b')] = ('b', 'R', 'CMP_START')   # d >= 1 -> CMP

    # (0, 0) pop: currently on 'c' or '_' immediately left of 'b c _'
    T[('POP_3', 'c')] = ('c', 'R', 'ERASE_0_B')
    T[('POP_3', '_')] = ('_', 'R', 'ERASE_0_LAST_B')
    T[('ERASE_0_B', 'b')] = ('_', 'R', 'ERASE_0_C')
    T[('ERASE_0_C', 'c')] = ('_', 'L', 'ERASE_0_SKIP')
    T[('ERASE_0_SKIP', '_')] = ('_', 'L', 'INC_N_SCAN_S')
    T[('ERASE_0_LAST_B', 'b')] = ('_', 'R', 'ERASE_0_LAST_C')
    T[('ERASE_0_LAST_C', 'c')] = ('_', 'L', None)  # HALT when S becomes empty! (or inc_n then halt; halting here is valid too!)

    # Increment n on left end of a^n and return to POP_C
    add('INC_N_SCAN_S', {'bc': ('=', 'L', 'INC_N_SCAN_S'), '_': ('_', 'L', 'INC_N_GAP')})
    add('INC_N_GAP', {'_': ('_', 'L', 'INC_N_GAP'), 'a': ('a', 'L', 'INC_N_ADD')})
    add('INC_N_ADD', {'a': ('a', 'L', 'INC_N_ADD'), '_': ('a', 'R', 'RET_FROM_N')})
    add('RET_FROM_N', {'a': ('a', 'R', 'RET_FROM_N'), '_': ('_', 'R', 'RET_SKIP_GAP')})
    add('RET_SKIP_GAP', {'_': ('_', 'R', 'RET_SKIP_GAP'), 'bc': ('=', 'R', 'GO_END')})
    add('GO_END', {'bc': ('=', 'R', 'GO_END'), '_': ('_', 'L', 'POP_C')})

    # --- Compare S[j] < T ---
    # Entered at POP_2('c') -> R (on second 'c' of T) or POP_3('b') -> R (on second-to-last 'b' of T)
    # CMP_START: move R to '_', or move L until hitting 'c' before T!
    # Wait: POP_2('c') moved R onto last 'c' of T; POP_3('b') moved R onto rightmost 'b' of T.
    # Let CMP_START walk R to '_', wait or walk L skipping 'c' then skipping 'b' until 'c' of S[k-2]!
    add('CMP_START', {'c': ('c', 'R', 'CMP_START'), '_': ('_', 'L', 'CMP_TO_J'), 'b': ('b', 'R', 'CMP_START')})
    # CMP_TO_J: start at rightmost char of T ('c'), skip 'c' L, then skip 'b' L until 'c' (end of S[k-2])
    add('CMP_TO_J', {'c': ('c', 'L', 'CMP_TO_J'), 'b': ('b', 'L', 'CMP_SKIP_TB')})
    add('CMP_SKIP_TB', {'b': ('b', 'L', 'CMP_SKIP_TB'), 'c': ('c', 'L', 'CMP_FIND_B')})

    # Head is inside S[j] (just left of S[j]'s trailing 'c's, or on second 'c' of S[j]!).
    # Wait: S[j] may end in 'c' or 'c c'! So CMP_FIND_B skips 'c' and 'a' L!
    add('CMP_FIND_B', {'ca': ('=', 'L', 'CMP_FIND_B')})
    T[('CMP_FIND_B', 'b')] = ('a', 'R', 'CMP_GO_T')
    T[('CMP_FIND_B', '_')] = ('_', 'R', 'FOUND_R')  # j == 0 matched! Wait: what if S[j] ended, hitting previous 'c'?
    # WAIT! In CMP_FIND_B, if we skip 'c', we skip over S[j-1]'s 'c's WITHOUT stopping at boundary!
    # FIX: Keep TWO states: CMP_SKIP_JC (skip trailing 'c' of S[j]) -> then in S[j]'s b/a body, 'c' means S[j] < T!!
    del T[('CMP_FIND_B', 'c')]
    T[('CMP_SKIP_JC', 'c')] = ('c', 'L', 'CMP_SKIP_JC')
    T[('CMP_SKIP_JC', 'a')] = ('a', 'L', 'CMP_FIND_B_IN')
    T[('CMP_SKIP_JC', 'b')] = ('a', 'R', 'CMP_GO_T')
    # Fix CMP_SKIP_TB on 'c' -> goto CMP_SKIP_JC!
    T[('CMP_SKIP_TB', 'c')] = ('c', 'L', 'CMP_SKIP_JC')
    # Inside CMP_FIND_B_IN: we ALREADY saw >=1 'a' in S[j]! Skip 'a' L. If 'b', mark 'a'. If 'c' or '_', S[j] < T!!
    T[('CMP_FIND_B_IN', 'a')] = ('a', 'L', 'CMP_FIND_B_IN')
    T[('CMP_FIND_B_IN', 'b')] = ('a', 'R', 'CMP_GO_T')
    T[('CMP_FIND_B_IN', 'c')] = ('c', 'R', 'FOUND_R')
    T[('CMP_FIND_B_IN', '_')] = ('_', 'R', 'FOUND_R')

    # CMP_GO_T: walk R over {a, b, c} to '_' (right of T)
    add('CMP_GO_T', {'abc': ('=', 'R', 'CMP_GO_T'), '_': ('_', 'L', 'CMP_T_SKIPC')})
    # Skip T's trailing 'c's and 'a's L
    T[('CMP_T_SKIPC', 'c')] = ('c', 'L', 'CMP_T_SKIPC')
    T[('CMP_T_SKIPC', 'a')] = ('a', 'L', 'CMP_T_SKIPA')
    T[('CMP_T_SKIPC', 'b')] = ('a', 'L', 'CMP_BACK_J')
    T[('CMP_T_SKIPA', 'a')] = ('a', 'L', 'CMP_T_SKIPA')
    T[('CMP_T_SKIPA', 'b')] = ('a', 'L', 'CMP_BACK_J')
    # If CMP_T_SKIPA hits 'c' -> T had NO 'b' left -> S[j] >= T!
    T[('CMP_T_SKIPA', 'c')] = ('c', 'R', 'CMP_RESTORE_T')

    # Restore T (a -> b, c -> c) going R until '_'
    add('CMP_RESTORE_T', {'a': ('b', 'R', 'CMP_RESTORE_T'), 'c': ('c', 'R', 'CMP_RESTORE_T'), '_': ('_', 'L', 'CMP_FIND_J_A')})
    # Walk L over {b, c} to S[j]'s 'a's
    add('CMP_FIND_J_A', {'bc': ('=', 'L', 'CMP_FIND_J_A'), 'a': ('b', 'L', 'CMP_RESTORE_J')})
    # Restore remaining 'a's of S[j] -> 'b', until hitting 'c' (end of S[j-1]) -> CMP_SKIP_JC!
    add('CMP_RESTORE_J', {'a': ('b', 'L', 'CMP_RESTORE_J'), 'c': ('c', 'L', 'CMP_SKIP_JC')})

    # Walk L from marked 'b'->'a' in T across T's 'b's and S[j+1..k-2] ({b, c}) until S[j]'s 'a's
    add('CMP_BACK_J', {'bc': ('=', 'L', 'CMP_BACK_J'), 'a': ('a', 'L', 'CMP_FIND_B_IN')})

    # --- FOUND_R: currently on S[r]'s FIRST cell (which is 'a'!). Keep it 'a' (a_start), restore rest of S[r] 'a'->'b', go erase T ---
    T[('FOUND_R', 'a')] = ('a', 'R', 'FOUND_RESTORE_R')
    add('FOUND_RESTORE_R', {'a': ('b', 'R', 'FOUND_RESTORE_R'), 'bc': ('=', 'R', 'FOUND_GO_T'), '_': ('_', 'L', 'ERASE_T_CHK')})
    add('FOUND_GO_T', {'abc': ('=', 'R', 'FOUND_GO_T'), '_': ('_', 'L', 'ERASE_T_CHK')})

    # Erase T from right end ('c' -> '_', peek next: 'c' => shift=1, 'ab' => shift=0)
    T[('ERASE_T_CHK', 'c')] = ('_', 'L', 'ERASE_T_TAG')
    T[('ERASE_T_TAG', 'c')] = ('_', 'L', 'ERASE_T_BODY_1')
    T[('ERASE_T_TAG', 'a')] = ('_', 'L', 'ERASE_T_BODY_0')
    T[('ERASE_T_TAG', 'b')] = ('_', 'L', 'ERASE_T_BODY_0')
    add('ERASE_T_BODY_0', {'ab': ('_', 'L', 'ERASE_T_BODY_0'), 'c': ('c', 'L', 'GO_ASTART_0')})
    add('ERASE_T_BODY_1', {'ab': ('_', 'L', 'ERASE_T_BODY_1'), 'c': ('c', 'L', 'GO_ASTART_1')})

    # Wait: let's avoid duplicating COPY across shift=0 and shift=1 by keeping a single COPY or tiny 2-branch!
    # Wait: how tiny IS duplicating ONLY the first-cell/after-c emit vs storing shift on tape?
    # Let's test BOTH! Here let's test the cleanest version first: store shift on LEFT of a^n?
    # No, let's check state count with separate COPY_0 and COPY_1 (sharing RET/DEC/CLOSE!) first!
    add('GO_ASTART_0', {'bc': ('=', 'L', 'GO_ASTART_0'), 'a': ('a', 'R', 'CP0_INIT_W')})
    add('GO_ASTART_1', {'bc': ('=', 'L', 'GO_ASTART_1'), 'a': ('a', 'R', 'CP1_INIT_W')})

    # Pass 1st cell: X_1 is a_start (= 'b'). For shift=0, copy 'b' past '_'; for shift=1, copy 'bb' past '_'.
    # Wait: first write of Pass creates '_' gap between X_m and dest!
    # Wait: after ERASE_T, right of X_m is ALL '_'!
    # Let's define shared CARRY helpers:
    # Carry 'b' into dest after ONE '_', writing 'b' (or 'bb') at first '_' after '_', then return L to a_start or a_cur!
    # Wait: on i == 1, head moves R across X_2..X_m, hits '_' (end of src), steps R onto '_' (start of dest!), writes 'b' (or 'bb'), returns L across '_' to X_m..X_2 until a_start!
    # For i >= 2: we overwrite X_i with 'a' (`a_cur`) so returning L stops at `a_cur` instead of `a_start`!
    # Look: i == 1 stops at `a_start` (only 1 'a' in slice right now!), and i >= 2 stops at `a_cur` (the first 'a' hit going L)!
    # THEY USE THE EXACT SAME `CARRY` STATES!!
    # Check!! At i == 1, `a_start` IS the rightmost 'a' in slice! Step R from `a_start`: write nothing on `a_start`, carry 'b' right!
    # When `CARRY_B` returns L across `_`, it hits the FIRST `a`:
    # Wait: on i == 1 that first `a` is `a_start` (leave it `a` and step R to `X_2`!), whereas on i >= 2 that first `a` is `a_cur` (restore `X_i` and step R to `X_{i+1}`)!!
    # So we just pass `ret_mode` (`RET_FIRST` vs `RET_B` vs `RET_C`) — or even simpler, for i==1 (`X_1`), use dedicated 1-step skip (`CARRY_FIRST_0` / `CARRY_FIRST_1`) OR share `CARRY_RET`!
    # Trace carefully:
    # Step 1 (X_1 = 'b'):
    add('CP0_INIT_W', {'bc': ('=', 'R', 'CP0_INIT_W'), '_': ('_', 'R', 'CP0_W1_B')})
    T[('CP0_W1_B', '_')] = ('b', 'L', 'CP0_RET_FIRST')
    add('CP0_RET_FIRST', {'_bc': ('=', 'L', 'CP0_RET_FIRST'), 'a': ('a', 'R', 'CP0_NEXT')})
    # Actually Wait: in CP0_RET_FIRST, there's only ONE '_' between dest('b') and src! Safe!

    add('CP1_INIT_W', {'bc': ('=', 'R', 'CP1_INIT_W'), '_': ('_', 'R', 'CP1_W1_B1')})
    T[('CP1_W1_B1', '_')] = ('b', 'R', 'CP1_W1_B2')
    T[('CP1_W1_B2', '_')] = ('b', 'L', 'CP1_RET_FIRST')
    add('CP1_RET_FIRST', {'bc_': ('=', 'L', 'CP1_RET_FIRST'), 'a': ('a', 'R', 'CP1_NEXT_NC')})

    # --- Loop X_2 .. X_m for shift = 0 ---
    T[('CP0_NEXT', 'b')] = ('a', 'R', 'CP0_CARRY_B')
    T[('CP0_NEXT', 'c')] = ('a', 'R', 'CP0_CARRY_C')
    T[('CP0_NEXT', '_')] = ('_', 'L', 'PASS_DONE_0')  # hit '_' after X_m -> pass finished!

    add('CP0_CARRY_B', {'bc': ('=', 'R', 'CP0_CARRY_B'), '_': ('_', 'R', 'CP0_DEST_B')})
    add('CP0_DEST_B', {'bc': ('=', 'R', 'CP0_DEST_B'), '_': ('b', 'L', 'CP0_RET_B_D')})
    add('CP0_RET_B_D', {'bc': ('=', 'L', 'CP0_RET_B_D'), '_': ('_', 'L', 'CP0_RET_B_S')})
    add('CP0_RET_B_S', {'bc': ('=', 'L', 'CP0_RET_B_S'), 'a': ('b', 'R', 'CP0_NEXT')})

    add('CP0_CARRY_C', {'bc': ('=', 'R', 'CP0_CARRY_C'), '_': ('_', 'R', 'CP0_DEST_C')})
    add('CP0_DEST_C', {'bc': ('=', 'R', 'CP0_DEST_C'), '_': ('c', 'L', 'CP0_RET_C_D')})
    add('CP0_RET_C_D', {'bc': ('=', 'L', 'CP0_RET_C_D'), '_': ('_', 'L', 'CP0_RET_C_S')})
    add('CP0_RET_C_S', {'bc': ('=', 'L', 'CP0_RET_C_S'), 'a': ('c', 'R', 'CP0_NEXT')})

    # --- Loop X_2 .. X_m for shift = 1 ---
    # Track prev_was_c: NC (not c) vs WC (was c). If WC and current=='b', emit 'bb'!
    T[('CP1_NEXT_NC', 'b')] = ('a', 'R', 'CP1_CARRY_B_NC')
    T[('CP1_NEXT_NC', 'c')] = ('a', 'R', 'CP1_CARRY_C')
    T[('CP1_NEXT_NC', '_')] = ('_', 'L', 'PASS_DONE_1')
    T[('CP1_NEXT_WC', 'b')] = ('a', 'R', 'CP1_CARRY_BB')
    T[('CP1_NEXT_WC', 'c')] = ('a', 'R', 'CP1_CARRY_C')
    T[('CP1_NEXT_WC', '_')] = ('_', 'L', 'PASS_DONE_1')

    add('CP1_CARRY_B_NC', {'bc': ('=', 'R', 'CP1_CARRY_B_NC'), '_': ('_', 'R', 'CP1_DEST_B')})
    add('CP1_DEST_B', {'bc': ('=', 'R', 'CP1_DEST_B'), '_': ('b', 'L', 'CP1_RET_B_D')})
    add('CP1_RET_B_D', {'bc': ('=', 'L', 'CP1_RET_B_D'), '_': ('_', 'L', 'CP1_RET_B_S')})
    add('CP1_RET_B_S', {'bc': ('=', 'L', 'CP1_RET_B_S'), 'a': ('b', 'R', 'CP1_NEXT_NC')})

    add('CP1_CARRY_BB', {'bc': ('=', 'R', 'CP1_CARRY_BB'), '_': ('_', 'R', 'CP1_DEST_BB')})
    add('CP1_DEST_BB', {'bc': ('=', 'R', 'CP1_DEST_BB'), '_': ('b', 'R', 'CP1_DEST_B')})

    add('CP1_CARRY_C', {'bc': ('=', 'R', 'CP1_CARRY_C'), '_': ('_', 'R', 'CP1_DEST_C')})
    add('CP1_DEST_C', {'bc': ('=', 'R', 'CP1_DEST_C'), '_': ('c', 'L', 'CP1_RET_C_D')})
    add('CP1_RET_C_D', {'bc': ('=', 'L', 'CP1_RET_C_D'), '_': ('_', 'L', 'CP1_RET_C_S')})
    add('CP1_RET_C_S', {'bc': ('=', 'L', 'CP1_RET_C_S'), 'a': ('c', 'R', 'CP1_NEXT_WC')})

    # --- Pass Done: walk L to counter, dec n, branch to CLOSE_GAP (more copies or finish) ---
    for sh in (0, 1):
        # Scan L across src to a_start, then across prefix to '_' gap, across '_'s to counter!
        add(f'PASS_DONE_{sh}', {'bc': ('=', 'L', f'PASS_DONE_{sh}'), 'a': ('a', 'L', f'DEC_GO_GAP_{sh}')})
        add(f'DEC_GO_GAP_{sh}', {'bc': ('=', 'L', f'DEC_GO_GAP_{sh}'), '_': ('_', 'L', f'DEC_SKIP_GAP_{sh}')})
        add(f'DEC_SKIP_GAP_{sh}', {'_': ('_', 'L', f'DEC_SKIP_GAP_{sh}'), 'c': ('c', 'L', f'DEC_SKIP_C_{sh}'), 'a': ('c', 'R', f'DEC_MORE_{sh}')})
        add(f'DEC_SKIP_C_{sh}', {'c': ('c', 'L', f'DEC_SKIP_C_{sh}'), 'a': ('c', 'R', f'DEC_MORE_{sh}'), '_': ('_', 'R', f'DEC_RESTORE_N')})
        # If more copies remain (`a -> c` succeeded): walk R across counter, gap, prefix to a_start -> restore a_start->'b', mark Copy1[0] as 'a', close '_' gap!
        add(f'DEC_MORE_{sh}', {'c': ('c', 'R', f'DEC_MORE_{sh}'), '_': ('_', 'R', f'DEC_MORE_GAP_{sh}')})
        add(f'DEC_MORE_GAP_{sh}', {'_': ('_', 'R', f'DEC_MORE_GAP_{sh}'), 'bc': ('=', 'R', f'DEC_MORE_PRE_{sh}'), 'a': ('b', 'R', f'MARK_NEXT_FIND_{sh}')})
        add(f'DEC_MORE_PRE_{sh}', {'bc': ('=', 'R', f'DEC_MORE_PRE_{sh}'), 'a': ('b', 'R', f'MARK_NEXT_FIND_{sh}')})
        add(f'MARK_NEXT_FIND_{sh}', {'bc': ('=', 'R', f'MARK_NEXT_FIND_{sh}'), '_': ('_', 'R', f'MARK_NEXT_SET_{sh}')})
        T[(f'MARK_NEXT_SET_{sh}', 'b')] = ('a', 'L', f'CLOSE_START_{sh}')
        # Close '_' gap between X_m and Copy_1 (`a`) by shifting [prefix .. X_m] R by 1 cell!
        # Step L from '_' onto X_m (`b` or `c`), swap '_' left across [prefix .. X_m] until hitting '_' gap before prefix!
        T[(f'CLOSE_START_{sh}', '_')] = ('_', 'L', f'SH_PICK_{sh}')
        T[(f'SH_PICK_{sh}', 'b')] = ('_', 'R', f'SH_PUT_B_{sh}')
        T[(f'SH_PICK_{sh}', 'c')] = ('_', 'R', f'SH_PUT_C_{sh}')
        T[(f'SH_PICK_{sh}', '_')] = ('_', 'R', f'SH_DONE_FIND_A_{sh}')  # hit counter gap!
        T[(f'SH_PUT_B_{sh}', '_')] = ('b', 'L', f'SH_BACK_{sh}')
        T[(f'SH_PUT_C_{sh}', '_')] = ('c', 'L', f'SH_BACK_{sh}')
        T[(f'SH_BACK_{sh}', '_')] = ('_', 'L', f'SH_PICK_{sh}')
        # Done shifting! Scan R across '_', b, c until hitting 'a' (which is Copy_1[0]!), then start pass!
        add(f'SH_DONE_FIND_A_{sh}', {'_bc': ('=', 'R', f'SH_DONE_FIND_A_{sh}'), 'a': ('a', 'R', f'CP{sh}_INIT_W')})

    # Note: DEC_MORE_GAP_0/1 if `a_start` was FIRST cell (`r == 0`, no prefix!): handled cleanly above (`'a': ('b', 'R', ...)`)!
    # Wait: what about MARK_NEXT_FIND if `src` was empty? Not possible since every entry has length >= 2 (`b c`).
    # Finish (all n copies done!): restore `c -> a` in counter, walk R to `a_start`, set `a_start -> 'b'`, close '_' gap ONCE, then GO_END -> POP_C!
    T[('DEC_RESTORE_N', 'c')] = ('a', 'R', 'DEC_RESTORE_N')
    T[('DEC_RESTORE_N', '_')] = ('_', 'R', 'FIN_GAP')
    add('FIN_GAP', {'_': ('_', 'R', 'FIN_GAP'), 'bc': ('=', 'R', 'FIN_PRE'), 'a': ('b', 'R', 'FIN_FIND_GAP')})
    add('FIN_PRE', {'bc': ('=', 'R', 'FIN_PRE'), 'a': ('b', 'R', 'FIN_FIND_GAP')})
    add('FIN_FIND_GAP', {'bc': ('=', 'R', 'FIN_FIND_GAP'), '_': ('_', 'L', 'FSH_PICK')})
    T[('FSH_PICK', 'b')] = ('_', 'R', 'FSH_PUT_B')
    T[('FSH_PICK', 'c')] = ('_', 'R', 'FSH_PUT_C')
    T[('FSH_PICK', '_')] = ('_', 'R', 'GO_END_FIN')
    T[('FSH_PUT_B', '_')] = ('b', 'L', 'FSH_BACK')
    T[('FSH_PUT_C', '_')] = ('c', 'L', 'FSH_BACK')
    T[('FSH_BACK', '_')] = ('_', 'L', 'FSH_PICK')
    add('GO_END_FIN', {'_bc': ('=', 'R', 'GO_END_FIN')})
    # Wait: after closing `_` gap in FIN_FIND_GAP, ALL of `[S]` has ZERO `_` inside!
    # Wait: FSH_PICK hits '_' on the LEFT of `[prefix]` (the counter gap)! So GO_END_FIN skips `_` first, then `bc` to far-right `_`!
    del T[('GO_END_FIN', '_')]
    T[('GO_END_FIN', '_')] = ('_', 'R', 'GO_END_FIN')
    add('GO_END_FIN', {'bc': ('=', 'R', 'GO_END')})
    # Fix `SH_DONE_FIND_A` too! SH_PICK hit `_` on LEFT of `[prefix]`, so skip `_`s then `{b, c}` until `a`!
    # Check: SH_DONE_FIND_A already has `{'_bc': ...}` which skips `_` and `b, c` until `a`! Safe!

    return T


def decode_4sym_tape(tape):
    lo, hi = min(tape), max(tape)
    s = ''.join(tape.get(i, '_') for i in range(lo, hi + 1)).strip('_')
    # Format: a^n _+ seq
    i = 0
    while i < len(s) and s[i] == 'a':
        i += 1
    n = i
    while i < len(s) and s[i] == '_':
        i += 1
    rest = s[i:]
    seq = []
    j = 0
    while j < len(rest):
        bcnt = 0
        while j < len(rest) and rest[j] == 'b':
            bcnt += 1
            j += 1
        assert j < len(rest) and rest[j] == 'c', f"bad decode at {j}: {s}"
        j += 1
        tag = 0
        if j < len(rest) and rest[j] == 'c':
            tag = 1
            j += 1
        seq.append((bcnt - 1, tag))
    return n, seq


def sim_4sym(T, start_tape=None, start_st='BOOT_0', max_steps=100000):
    tape = dict(start_tape) if start_tape else {}
    h = 0
    st = start_st
    trace = []
    for step in range(max_steps):
        if st is None:
            return step, tape, trace
        sym = tape.get(h, '_')
        if (st, sym) not in T:
            raise RuntimeError(f"Missing transition ({st}, {sym!r}) at step {step}")
        w, d, nxt = T[(st, sym)]
        if w == '_':
            tape.pop(h, None)
        else:
            tape[h] = w
        h += 1 if d == 'R' else -1
        st = nxt
        if st == 'POP_C':
            trace.append((step + 1, decode_4sym_tape(tape)))
    return max_steps, tape, trace


def step_pss2(S, n):
    a_last, b_last = S[-1]
    if a_last == 0 and b_last == 0:
        return S[:-1], n + 1
    r = max(i for i in range(len(S) - 1) if S[i][0] < a_last)
    if b_last == 0:
        return S[:-1] + S[r:-1] * n, n
    d = a_last - S[r][0]
    res = list(S[:-1])
    for t in range(1, n + 1):
        res.extend((a + t * d, b) for (a, b) in S[r:-1])
    return res, n


def compile_4to2_and_minimize(T4, start4='BOOT_0'):
    # Compile 4-symbol TM (cells aligned at even 2*k, 2*k+1) to 2-symbol TM with shared gadgets + Moore minimization.
    # For each state q in reachable 4-sym states:
    #   q: at bit 0 (2*i). Reads b0 -> move R to (q, 'b1', b0).
    #   (q, 'b1', b0): at bit 1 (2*i+1). Reads b1 -> sym4 = (b0, b1).
    #     Let (w, d, nxt) = T4[(q, sym4)].
    #     If nxt is None: write w1, R or stop! Actually HALT -> missing transition at (q, 'b1', b0) on b1!
    #     Else let (w0, w1) = SYM2_ENC[w].
    #     If w0 == b0 and d == 'R': write w1, R -> nxt! (0 extra states!)
    #     Else: write w1, L -> gadget ('W0', w0, d, nxt) which is on bit 0!
    #   Wait: gadget ('W0', w0, d, nxt) ignores current bit (since both 0/1 write w0 and move d to ('SKIP', d, nxt))!
    #     Wait: if w0 == b0 and d == 'L', we can jump to ('SKIP', 'L', nxt) WITHOUT writing w0 -> Wait: ('W0', b0, 'L', nxt) ALSO preserves b0!
    #     ('SKIP', 'R', nxt): ignores current bit (both 0/1 leave sym unchanged, move R to nxt)!
    #     ('SKIP', 'L', nxt): ignores current bit (both 0/1 leave sym unchanged, move L to nxt)!
    B = {}
    reachable4 = {start4}
    work = [start4]
    while work:
        q = work.pop()
        for s in SYM4:
            if (q, s) in T4:
                nxt = T4[(q, s)][2]
                if nxt is not None and nxt not in reachable4:
                    reachable4.add(nxt)
                    work.append(nxt)

    for q in reachable4:
        B[(q, 0)] = (0, 'R', (q, 'b1', 0))
        B[(q, 1)] = (1, 'R', (q, 'b1', 1))
        for b0 in (0, 1):
            for b1 in (0, 1):
                s4 = SYM4[(b0 << 1) | b1]
                if (q, s4) not in T4:
                    continue
                w, d, nxt = T4[(q, s4)]
                if nxt is None:
                    # halt cleanly by leaving transition undefined (Wait: write w1/w0 if needed; here HALT happens at ERASE_0_LAST_C where halting is sufficient!)
                    continue
                w0, w1 = SYM2_ENC[w]
                if w0 == b0 and d == 'R':
                    B[((q, 'b1', b0), b1)] = (w1, 'R', nxt)
                else:
                    B[((q, 'b1', b0), b1)] = (w1, 'L', ('W0', w0, d, nxt))
                    for cur0 in (0, 1):
                        B[(('W0', w0, d, nxt), cur0)] = (w0, d, ('SKIP', d, nxt))
                    for cur in (0, 1):
                        B[(('SKIP', d, nxt), cur)] = (cur, d, nxt)

    # Reachability from start4
    seen = {start4}
    stack = [start4]
    while stack:
        s = stack.pop()
        for sym in (0, 1):
            row = B.get((s, sym))
            if row and row[2] not in seen:
                seen.add(row[2])
                stack.append(row[2])

    # Moore minimization
    part = {s: 0 for s in seen}
    while True:
        sig = {}
        for s in seen:
            row_sig = []
            for sym in (0, 1):
                r = B.get((s, sym))
                if r is None:
                    row_sig.append(('H',))
                else:
                    row_sig.append(('T', r[0], r[1], part[r[2]]))
            sig[s] = tuple(row_sig)
        groups = {}
        for s in seen:
            groups.setdefault(sig[s], []).append(s)
        new_part = {}
        for idx, members in enumerate(sorted(groups.values(), key=lambda g: str(min(g, key=str)))):
            for m in members:
                new_part[m] = idx
        if new_part == part:
            break
        part = new_part
    return len(seen), len(set(part.values())), len(reachable4)


if __name__ == '__main__':
    T4 = build_4sym_tm()
    # Test 1: [(0,0), (1,0)] with n=2
    t1 = {i: ch for i, ch in enumerate('aa_bcbbc')}
    steps1, tape1, tr1 = sim_4sym(T4, start_tape=t1, start_st='RET_FROM_N', max_steps=10000)
    # Compare with step_pss2
    S, n = [(0, 0), (1, 0)], 2
    ref = []
    while S:
        ref.append((n, list(S)))
        S, n = step_pss2(S, n)
    got = [x[1] for x in tr1]
    print('Test 1 [(0,0),(1,0)] n=2 match:', got == ref, f'4sym steps={steps1}, ref len={len(ref)}')

    # Test 2: [(0,0), (1,1)] with n=1
    t2 = {i: ch for i, ch in enumerate('a_bcbbcc')}
    steps2, tape2, tr2 = sim_4sym(T4, start_tape=t2, start_st='RET_FROM_N', max_steps=10000)
    S, n = [(0, 0), (1, 1)], 1
    ref2 = []
    while S:
        ref2.append((n, list(S)))
        S, n = step_pss2(S, n)
    got2 = [x[1] for x in tr2]
    print('Test 2 [(0,0),(1,1)] n=1 match:', got2 == ref2, f'4sym steps={steps2}, ref len={len(ref2)}')

    # Test 3: [(0,0), (1,1), (1,1)] n=2 -> check first 5 macro-steps!
    t3 = {i: ch for i, ch in enumerate('aa_bcbbccbbcc')}
    steps3, tape3, tr3 = sim_4sym(T4, start_tape=t3, start_st='RET_FROM_N', max_steps=5000)
    S, n = [(0, 0), (1, 1), (1, 1)], 2
    ref3 = []
    for _ in range(len(tr3)):
        ref3.append((n, list(S)))
        S, n = step_pss2(S, n)
    got3 = [x[1] for x in tr3]
    print('Test 3 [(0,0),(1,1),(1,1)] n=2 first', len(got3), 'macro-steps match:', got3 == ref3)
    if got3 != ref3:
        for k in range(len(got3)):
            if got3[k] != ref3[k]:
                print('  mismatch at', k, 'got=', got3[k], 'ref=', ref3[k])
                break

    # Test 4: Boot from blank tape (first 5 macro-steps)
    steps4, tape4, tr4 = sim_4sym(T4, start_tape={}, start_st='BOOT_0', max_steps=5000)
    print('Boot test first', len(tr4), 'macro-steps:', tr4[:2])

    raw2, min2, r4 = compile_4to2_and_minimize(T4, 'BOOT_0')
    print(f'4-sym reachable states: {r4}, 2-sym raw: {raw2}, 2-sym Moore-min: {min2}')
