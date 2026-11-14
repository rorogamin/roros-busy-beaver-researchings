/* Fast multi-threaded Turing Machine decider & holdout screener.
 * Supports arbitrary standard specs (up to 16 states, 8 symbols).
 * Exact sound deciders:
 *   1. UNREACH_HALT  - Backward reasoning (up to depth 10) proves all undefined cells unreachable.
 *   2. HALT          - Direct simulation reaches an undefined transition (reports steps & nonzeros).
 *   3. CYCLER        - Bounded tape + exact (state, pos, tape[min..max]) configuration repeat.
 *   4. TC_R / TC_L   - Verified right/left translated cycler (exact slice + min-excursion replay check).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

#define MAX_S 16
#define MAX_K 8
#define TAPE_SIZE 262144
#define TAPE_MID 131072
#define BR_DEPTH 10
#define BR_WIN 32
#define BR_MAX_STATES 4096

typedef struct {
    int8_t out;   /* 0..7 */
    int8_t dir;   /* -1 or +1 */
    int8_t nxt;   /* -1 = halt, else 0..15 */
} Trans;

typedef struct {
    int n_states;
    int n_syms;
    Trans t[MAX_S][MAX_K];
} TM;

static int parse_tm(const char *s, TM *tm) {
    memset(tm, 0, sizeof(*tm));
    int st = 0, sym = 0, max_sym = 0;
    const char *p = s;
    while (*p && (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')) p++;
    if (!*p) return 0;
    while (*p) {
        if (*p == '_') {
            if (sym > max_sym) max_sym = sym;
            st++;
            sym = 0;
            p++;
            if (st >= MAX_S) return 0;
            continue;
        }
        if (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') break;
        if (!p[0] || !p[1] || !p[2]) return 0;
        if (sym >= MAX_K) return 0;
        if (p[0] == '-' && p[1] == '-' && p[2] == '-') {
            tm->t[st][sym].nxt = -1;
            tm->t[st][sym].out = 0;
            tm->t[st][sym].dir = 1;
        } else {
            int o = p[0] - '0';
            int d = (p[1] == 'R') ? 1 : ((p[1] == 'L') ? -1 : 0);
            int n = p[2] - 'A';
            if (o < 0 || o >= MAX_K || d == 0 || n < 0 || n >= MAX_S) return 0;
            tm->t[st][sym].out = (int8_t)o;
            tm->t[st][sym].dir = (int8_t)d;
            tm->t[st][sym].nxt = (int8_t)n;
        }
        sym++;
        p += 3;
    }
    if (sym > max_sym) max_sym = sym;
    tm->n_states = st + 1;
    tm->n_syms = max_sym;
    if (tm->n_states <= 0 || tm->n_syms <= 0) return 0;
    return 1;
}

/* Exact Backward Reasoning:
 * Back-node represents partial constraints on tape[0..BR_WIN-1] with head at pos in [0..BR_WIN-1].
 * cell[i] == -1 means unknown ('*'), else 0..K-1.
 * Reverse step from state s, pos p:
 *   Choose transition (s_prev, r) -> (w, d, s):
 *   If p - d out of [0..BR_WIN-1], treat as cutoff (cannot prove unreachable).
 *   In forward direction, at p_prev = p - d, head saw r, wrote w, moved d to p.
 *   In reverse, at p_prev: before reverse-step (= AFTER forward-step), tape[p_prev] MUST agree with w (or -1).
 *   Wait: after reversing that step, tape[p_prev] becomes r, and head is at p_prev, state s_prev.
 */
typedef struct {
    int8_t cells[BR_WIN];
    int8_t st;
    int8_t pos;
    int8_t depth;
} BRNode;

static int backward_unreachable(const TM *tm) {
    /* Quick state-level forward reachability ignoring tape */
    int reach[MAX_S];
    memset(reach, 0, sizeof(reach));
    reach[0] = 1;
    int chg = 1;
    while (chg) {
        chg = 0;
        for (int s = 0; s < tm->n_states; s++) if (reach[s]) {
            for (int k = 0; k < tm->n_syms; k++) {
                int ns = tm->t[s][k].nxt;
                if (ns >= 0 && !reach[ns]) { reach[ns] = 1; chg = 1; }
            }
        }
    }

    /* Check EVERY reachable undefined transition; if ANY could be reachable within BR_DEPTH, return 0 */
    BRNode *stk = (BRNode *)malloc(sizeof(BRNode) * BR_MAX_STATES);
    if (!stk) return 0;
    for (int hs = 0; hs < tm->n_states; hs++) {
        if (!reach[hs]) continue;
        for (int hk = 0; hk < tm->n_syms; hk++) {
            if (tm->t[hs][hk].nxt != -1) continue;
            int sp = 0;
            BRNode root;
            memset(root.cells, -1, BR_WIN);
            root.pos = BR_WIN / 2;
            root.cells[root.pos] = (int8_t)hk;
            root.st = (int8_t)hs;
            root.depth = 0;
            stk[sp++] = root;
            int nodes = 1;
            int maybe_reach = 0;
            while (sp > 0) {
                BRNode cur = stk[--sp];
                /* Check if compatible with initial blank tape in state 0 */
                if (cur.st == 0) {
                    int all0 = 1;
                    for (int i = 0; i < BR_WIN; i++) {
                        if (cur.cells[i] > 0) { all0 = 0; break; }
                    }
                    if (all0) { maybe_reach = 1; break; }
                }
                if (cur.depth >= BR_DEPTH) { maybe_reach = 1; break; }
                for (int ps = 0; ps < tm->n_states && !maybe_reach; ps++) {
                    if (!reach[ps]) continue;
                    for (int pk = 0; pk < tm->n_syms && !maybe_reach; pk++) {
                        Trans tr = tm->t[ps][pk];
                        if (tr.nxt != cur.st) continue;
                        int ppos = cur.pos - tr.dir;
                        if (ppos < 0 || ppos >= BR_WIN) { maybe_reach = 1; break; }
                        int8_t seen = cur.cells[ppos];
                        if (seen != -1 && seen != tr.out) continue;
                        if (sp >= BR_MAX_STATES - 1 || nodes >= BR_MAX_STATES * 4) {
                            maybe_reach = 1; break;
                        }
                        BRNode nxt = cur;
                        nxt.st = (int8_t)ps;
                        nxt.pos = (int8_t)ppos;
                        nxt.cells[ppos] = (int8_t)pk;
                        nxt.depth = (int8_t)(cur.depth + 1);
                        stk[sp++] = nxt;
                        nodes++;
                    }
                }
                if (maybe_reach) break;
            }
            if (maybe_reach) {
                free(stk);
                return 0;
            }
        }
    }
    free(stk);
    return 1;
}

typedef struct {
    int type;       /* 0=UNDECIDED, 1=HALT, 2=UNREACH_HALT, 3=CYCLER, 4=TC_R, 5=TC_L */
    uint64_t steps; /* for HALT: executed transitions (quicksim steps = steps+1); for cycles: detection step */
    int halt_st;
    int halt_sym;
    uint64_t nonzeros;
    int period;
    int shift;
} Result;

/* Verify a candidate right-translated cycler (dir=+1) or left-translated cycler (dir=-1)
 * by exact independent simulation on a clean copy of the critical window.
 */
static int verify_tc_replay(
    const TM *tm, const uint8_t *tape_cur, int p_cur, int st_cur,
    int period, int shift, int W, int dir_sign /* +1 right, -1 left */
) {
    /* Copy critical window [p_cur - W .. p_cur] if dir=+1 else [p_cur .. p_cur + W] */
    if (W < 0 || W > 4096 || period <= 0 || period > 200000 || shift <= 0) return 0;
    int span = W + shift + 8;
    if (span > 16384) return 0;
    uint8_t buf[16384];
    memset(buf, 0, span);
    int head0;
    if (dir_sign > 0) {
        /* critical [0..W] corresponds to [p_cur - W .. p_cur], head at W, right of W is blank 0 */
        for (int i = 0; i <= W; i++) buf[i] = tape_cur[p_cur - W + i];
        head0 = W;
    } else {
        /* critical [shift .. shift+W] corresponds to [p_cur .. p_cur + W], head at shift, left is blank 0 */
        for (int i = 0; i <= W; i++) buf[span - 1 - W + i] = tape_cur[p_cur + i];
        head0 = span - 1 - W;
    }
    int h = head0;
    int st = st_cur;
    int min_h = h, max_h = h;
    for (int k = 0; k < period; k++) {
        if (h < 0 || h >= span) return 0;
        if (h < min_h) min_h = h;
        if (h > max_h) max_h = h;
        uint8_t sym = buf[h];
        Trans tr = tm->t[st][sym];
        if (tr.nxt < 0) return 0;
        buf[h] = (uint8_t)tr.out;
        h += tr.dir;
        st = tr.nxt;
    }
    if (st != st_cur) return 0;
    if (dir_sign > 0) {
        if (h != head0 + shift) return 0;
        if (min_h < 0) return 0;
        if (max_h > h) return 0; /* wait: strict check that nothing > h was touched (all > h stays 0) */
        for (int i = 0; i <= W; i++) {
            if (buf[h - W + i] != tape_cur[p_cur - W + i]) return 0;
        }
        /* Also confirm tape strictly right of h stayed blank 0 */
        for (int i = h + 1; i < span; i++) if (buf[i] != 0) return 0;
        return 1;
    } else {
        if (h != head0 - shift) return 0;
        if (max_h >= span) return 0;
        if (min_h < h) return 0;
        for (int i = 0; i <= W; i++) {
            if (buf[h + i] != tape_cur[p_cur + i]) return 0;
        }
        for (int i = 0; i < h; i++) if (buf[i] != 0) return 0;
        return 1;
    }
}

/* Record snapshot for TC detection */
#define MAX_REC 32
typedef struct {
    uint64_t step;
    int pos;
    int min_since; /* min pos since this record (for R), or max pos since (for L) */
    uint64_t hash;
    int valid;
} RecSnap;

static uint64_t hash_window(const uint8_t *ptr, int len) {
    uint64_t h = 14695981039346656037ULL;
    for (int i = 0; i < len; i++) {
        h ^= ptr[i] + 1;
        h *= 1099511628211ULL;
    }
    return h;
}

/* Cycler hash entry (for bounded tape <= 1024) */
#define CYC_HT_SZ 16384
typedef struct {
    uint64_t hash;
    int st;
    int rel_pos;
    int span;
    uint64_t step;
    uint8_t used;
} CycEntry;

static int verify_cycler_replay(const TM *tm, const uint8_t *tape, int min_p, int max_p, int pos, int st, int period) {
    int span = max_p - min_p + 1;
    if (span <= 0 || span > 2048 || period <= 0 || period > 200000) return 0;
    uint8_t buf[2048];
    memcpy(buf, tape + min_p, span);
    int h = pos - min_p;
    int s = st;
    for (int k = 0; k < period; k++) {
        if (h < 0 || h >= span) return 0;
        Trans tr = tm->t[s][buf[h]];
        if (tr.nxt < 0) return 0;
        buf[h] = (uint8_t)tr.out;
        h += tr.dir;
        s = tr.nxt;
    }
    if (s != st || h != pos - min_p) return 0;
    return memcmp(buf, tape + min_p, span) == 0;
}

/* Two-phase fast decider:
 * 1) backward_unreachable (BR_DEPTH=10)
 * 2) ultra-fast raw sim up to 50,000 steps (catches short halts cleanly with zero overhead)
 * 3) if still running at 50k: run from step 0..min(max_steps, 250,000) with exact Cycler + TC_R + TC_L checks
 * 4) if still running: fast raw sim up to max_steps
 */
static Result raw_sim_fast(const TM *tm, uint64_t limit, uint8_t *tape) {
    Result res;
    memset(&res, 0, sizeof(res));
    int pos = TAPE_MID, min_p = TAPE_MID, max_p = TAPE_MID;
    int cl_lo = TAPE_MID - 256, cl_hi = TAPE_MID + 255;
    memset(tape + cl_lo, 0, cl_hi - cl_lo + 1);
    int st = 0;
    uint64_t step = 0;
    while (step < limit) {
        if (__builtin_expect(pos <= cl_lo + 4 || pos >= cl_hi - 4, 0)) {
            if (pos - 1024 < 8 || pos + 1024 >= TAPE_SIZE - 8) {
                res.type = 0; res.steps = step; return res;
            }
            if (pos <= cl_lo + 4) {
                int new_lo = cl_lo - 4096; if (new_lo < 0) new_lo = 0;
                memset(tape + new_lo, 0, cl_lo - new_lo);
                cl_lo = new_lo;
            }
            if (pos >= cl_hi - 4) {
                int new_hi = cl_hi + 4096; if (new_hi >= TAPE_SIZE) new_hi = TAPE_SIZE - 1;
                memset(tape + cl_hi + 1, 0, new_hi - cl_hi);
                cl_hi = new_hi;
            }
        }
        uint8_t sym = tape[pos];
        Trans tr = tm->t[st][sym];
        if (__builtin_expect(tr.nxt < 0, 0)) {
            uint64_t nz = 0;
            for (int i = min_p; i <= max_p; i++) if (tape[i]) nz++;
            res.type = 1; res.steps = step; res.halt_st = st; res.halt_sym = sym; res.nonzeros = nz;
            return res;
        }
        tape[pos] = (uint8_t)tr.out;
        pos += tr.dir;
        if (pos > max_p) max_p = pos;
        else if (pos < min_p) min_p = pos;
        st = tr.nxt;
        step++;
    }
    res.type = 0; res.steps = step;
    return res;
}

static Result decide_one(const TM *tm, uint64_t max_steps, uint8_t *tape, CycEntry *ht) {
    Result res;
    memset(&res, 0, sizeof(res));

    if (backward_unreachable(tm)) {
        res.type = 2;
        return res;
    }

    uint64_t pre = max_steps < 50000 ? max_steps : 50000;
    res = raw_sim_fast(tm, pre, tape);
    if (res.type != 0 || max_steps <= pre) return res;

    int pos = TAPE_MID, min_p = TAPE_MID, max_p = TAPE_MID;
    memset(tape + TAPE_MID - 256, 0, 512);
    int cl_lo = TAPE_MID - 256, cl_hi = TAPE_MID + 255;

    RecSnap r_snaps[MAX_S][MAX_REC];
    RecSnap l_snaps[MAX_S][MAX_REC];
    int r_idx[MAX_S], l_idx[MAX_S];
    memset(r_snaps, 0, sizeof(r_snaps));
    memset(l_snaps, 0, sizeof(l_snaps));
    memset(r_idx, 0, sizeof(r_idx));
    memset(l_idx, 0, sizeof(l_idx));
    memset(ht, 0, sizeof(CycEntry) * CYC_HT_SZ);

    int st = 0;
    uint64_t step = 0;
    uint64_t tc_limit = max_steps < 250000 ? max_steps : 250000;
    int max_cyc_check_step = 20000;

    while (step < tc_limit) {
        if (__builtin_expect(pos <= cl_lo + 4 || pos >= cl_hi - 4, 0)) {
            if (pos - 1024 < 8 || pos + 1024 >= TAPE_SIZE - 8) {
                res.type = 0; res.steps = step; return res;
            }
            if (pos <= cl_lo + 4) {
                int new_lo = cl_lo - 4096; if (new_lo < 0) new_lo = 0;
                memset(tape + new_lo, 0, cl_lo - new_lo);
                cl_lo = new_lo;
            }
            if (pos >= cl_hi - 4) {
                int new_hi = cl_hi + 4096; if (new_hi >= TAPE_SIZE) new_hi = TAPE_SIZE - 1;
                memset(tape + cl_hi + 1, 0, new_hi - cl_hi);
                cl_hi = new_hi;
            }
        }

        uint8_t sym = tape[pos];
        Trans tr = tm->t[st][sym];
        if (__builtin_expect(tr.nxt < 0, 0)) {
            uint64_t nz = 0;
            for (int i = min_p; i <= max_p; i++) if (tape[i]) nz++;
            res.type = 1; res.steps = step; res.halt_st = st; res.halt_sym = sym; res.nonzeros = nz;
            return res;
        }
        tape[pos] = (uint8_t)tr.out;
        pos += tr.dir;
        st = tr.nxt;
        step++;

        for (int s = 0; s < tm->n_states; s++) {
            for (int r = 0; r < MAX_REC; r++) {
                if (r_snaps[s][r].valid && pos < r_snaps[s][r].min_since) r_snaps[s][r].min_since = pos;
                if (l_snaps[s][r].valid && pos > l_snaps[s][r].min_since) l_snaps[s][r].min_since = pos;
            }
        }

        if (pos > max_p) {
            max_p = pos;
            for (int r = 0; r < MAX_REC; r++) {
                if (!r_snaps[st][r].valid) continue;
                int p1 = r_snaps[st][r].pos;
                int W = p1 - r_snaps[st][r].min_since;
                int d = pos - p1;
                int P = (int)(step - r_snaps[st][r].step);
                if (d > 0 && W >= 0 && W <= 512 && P <= 50000) {
                    if (verify_tc_replay(tm, tape, pos, st, P, d, W, 1)) {
                        res.type = 4; res.steps = step; res.period = P; res.shift = d;
                        return res;
                    }
                }
            }
            int idx = r_idx[st] % MAX_REC;
            r_idx[st]++;
            r_snaps[st][idx].step = step;
            r_snaps[st][idx].pos = pos;
            r_snaps[st][idx].min_since = pos;
            r_snaps[st][idx].valid = 1;
        } else if (pos < min_p) {
            min_p = pos;
            for (int r = 0; r < MAX_REC; r++) {
                if (!l_snaps[st][r].valid) continue;
                int p1 = l_snaps[st][r].pos;
                int W = l_snaps[st][r].min_since - p1;
                int d = p1 - pos;
                int P = (int)(step - l_snaps[st][r].step);
                if (d > 0 && W >= 0 && W <= 512 && P <= 50000) {
                    if (verify_tc_replay(tm, tape, pos, st, P, d, W, -1)) {
                        res.type = 5; res.steps = step; res.period = P; res.shift = d;
                        return res;
                    }
                }
            }
            int idx = l_idx[st] % MAX_REC;
            l_idx[st]++;
            l_snaps[st][idx].step = step;
            l_snaps[st][idx].pos = pos;
            l_snaps[st][idx].min_since = pos;
            l_snaps[st][idx].valid = 1;
        }

        if (step <= (uint64_t)max_cyc_check_step && (max_p - min_p + 1) <= 512) {
            int span = max_p - min_p + 1;
            uint64_t h = hash_window(tape + min_p, span);
            h ^= (uint64_t)st * 0x9e3779b97f4a7c15ULL;
            h ^= (uint64_t)(pos - min_p) * 0xbf58476d1ce4e5b9ULL;
            uint32_t slot = (uint32_t)(h & (CYC_HT_SZ - 1));
            for (int probe = 0; probe < 8; probe++) {
                uint32_t idx = (slot + probe) & (CYC_HT_SZ - 1);
                if (!ht[idx].used) {
                    ht[idx].used = 1; ht[idx].hash = h; ht[idx].st = st;
                    ht[idx].rel_pos = pos - min_p; ht[idx].span = span; ht[idx].step = step;
                    break;
                } else if (ht[idx].hash == h && ht[idx].st == st &&
                           ht[idx].rel_pos == pos - min_p && ht[idx].span == span) {
                    int P = (int)(step - ht[idx].step);
                    if (verify_cycler_replay(tm, tape, min_p, max_p, pos, st, P)) {
                        res.type = 3; res.steps = step; res.period = P;
                        return res;
                    }
                }
            }
        }
    }

    if (max_steps > tc_limit) {
        return raw_sim_fast(tm, max_steps, tape);
    }
    res.type = 0;
    res.steps = step;
    return res;
}

int main(int argc, char **argv) {
    uint64_t max_steps = 200000;
    const char *in_path = NULL;
    const char *out_path = NULL;
    int threads = 8;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--steps") && i + 1 < argc) max_steps = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--in") && i + 1 < argc) in_path = argv[++i];
        else if (!strcmp(argv[i], "--out") && i + 1 < argc) out_path = argv[++i];
        else if (!strcmp(argv[i], "--threads") && i + 1 < argc) threads = atoi(argv[++i]);
    }
    FILE *fin = in_path ? fopen(in_path, "r") : stdin;
    FILE *fout = out_path ? fopen(out_path, "w") : stdout;
    if (!fin || !fout) { fprintf(stderr, "file open error\n"); return 1; }

    /* Stream in batches of 50000 TMs so even 17M TMs use tiny RAM */
    const int BATCH = 50000;
    char **lines = (char **)malloc(sizeof(char *) * BATCH);
    TM *tms = (TM *)malloc(sizeof(TM) * BATCH);
    Result *results = (Result *)malloc(sizeof(Result) * BATCH);
    for (int i = 0; i < BATCH; i++) lines[i] = (char *)malloc(256);

    uint64_t total = 0;
    uint64_t cnt[8] = {0};
    char buf[512];
    omp_set_num_threads(threads);

    while (1) {
        int n = 0;
        while (n < BATCH && fgets(buf, sizeof(buf), fin)) {
            int len = (int)strlen(buf);
            while (len > 0 && (buf[len - 1] == '\n' || buf[len - 1] == '\r' || buf[len - 1] == ' '))
                buf[--len] = '\0';
            if (len == 0) continue;
            /* Support "id spec" or "spec" */
            char *sp = strrchr(buf, ' ');
            const char *spec = sp ? (sp + 1) : buf;
            if (strlen(spec) >= 250) continue;
            if (!parse_tm(spec, &tms[n])) continue;
            strcpy(lines[n], spec);
            n++;
        }
        if (n == 0) break;

        #pragma omp parallel
        {
            uint8_t *tape = (uint8_t *)malloc(TAPE_SIZE);
            CycEntry *ht = (CycEntry *)malloc(sizeof(CycEntry) * CYC_HT_SZ);
            #pragma omp for schedule(dynamic, 64)
            for (int i = 0; i < n; i++) {
                results[i] = decide_one(&tms[i], max_steps, tape, ht);
            }
            free(tape);
            free(ht);
        }

        for (int i = 0; i < n; i++) {
            uint64_t idx = total + i;
            Result r = results[i];
            cnt[r.type]++;
            if (r.type == 1) {
                fprintf(fout, "%llu\tHALT\t%s\tsteps=%llu\tnz=%llu\tst=%d\tsym=%d\n",
                        (unsigned long long)idx, lines[i],
                        (unsigned long long)r.steps, (unsigned long long)r.nonzeros,
                        r.halt_st, r.halt_sym);
            } else if (r.type == 2) {
                fprintf(fout, "%llu\tUNREACH_HALT\t%s\n", (unsigned long long)idx, lines[i]);
            } else if (r.type == 3) {
                fprintf(fout, "%llu\tCYCLER\t%s\tstep=%llu\tP=%d\n",
                        (unsigned long long)idx, lines[i], (unsigned long long)r.steps, r.period);
            } else if (r.type == 4) {
                fprintf(fout, "%llu\tTC_R\t%s\tstep=%llu\tP=%d\td=%d\n",
                        (unsigned long long)idx, lines[i], (unsigned long long)r.steps, r.period, r.shift);
            } else if (r.type == 5) {
                fprintf(fout, "%llu\tTC_L\t%s\tstep=%llu\tP=%d\td=%d\n",
                        (unsigned long long)idx, lines[i], (unsigned long long)r.steps, r.period, r.shift);
            }
        }
        total += n;
        fflush(fout);
    }

    fprintf(stderr, "DONE total=%llu UNDEC=%llu HALT=%llu UNREACH=%llu CYC=%llu TC_R=%llu TC_L=%llu\n",
            (unsigned long long)total, (unsigned long long)cnt[0],
            (unsigned long long)cnt[1], (unsigned long long)cnt[2],
            (unsigned long long)cnt[3], (unsigned long long)cnt[4], (unsigned long long)cnt[5]);
    if (in_path) fclose(fin);
    if (out_path) fclose(fout);
    for (int i = 0; i < BATCH; i++) free(lines[i]);
    free(lines); free(tms); free(results);
    return 0;
}
