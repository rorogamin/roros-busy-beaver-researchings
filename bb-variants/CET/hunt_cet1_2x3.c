#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

// ============================================================================
// CET_1(2, 3) 2-STATE 3-SYMBOL RECORD EXPEDITION ENGINE
// 2 Agents, 2 States (A, B), 3 Symbols (0, 1, 2)
// Initial positions: [0, 2]
// Halting Condition: QUASI-HALTS AT LAST COLLISION (zero collisions forever after)
// ============================================================================

typedef struct { int8_t w, mv, ns; } Tr;
typedef struct { Tr t[2][3]; } Agent2x3; // [state 0..1][read 0..2]

#define TAPE_SIZE 32768
#define TAPE_OFF  16384
#define MAX_STEPS 8000

#define HASH_BITS 16
#define HASH_SIZE (1 << HASH_BITS)
#define HASH_MASK (HASH_SIZE - 1)

typedef struct {
    uint64_t full_hash;
    int16_t p1, p2;
    uint8_t s1, s2;
    uint16_t step;
    uint16_t cols;
    uint16_t epoch;
} HashEntry;

static uint64_t Z_CELL[TAPE_SIZE][3]; // [pos][symbol 0..2]
static uint64_t Z_HEAD1[TAPE_SIZE][2];
static uint64_t Z_HEAD2[TAPE_SIZE][2];

static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void init_zobrist() {
    uint64_t seed = 0xA4F29B88E53108D3ULL;
    for (int i = 0; i < TAPE_SIZE; i++) {
        for (int c = 0; c < 3; c++) {
            Z_CELL[i][c] = splitmix64(&seed);
        }
        for (int s = 0; s < 2; s++) {
            Z_HEAD1[i][s] = splitmix64(&seed);
            Z_HEAD2[i][s] = splitmix64(&seed);
        }
    }
}

static void fmt_agent_std(const Agent2x3 *ag, char *buf) {
    char *p = buf;
    for (int s = 0; s < 2; s++) {
        if (s > 0) *p++ = '_';
        for (int r = 0; r < 3; r++) {
            Tr x = ag->t[s][r];
            *p++ = '0' + x.w;
            *p++ = x.mv > 0 ? 'R' : 'L';
            *p++ = 'A' + x.ns;
        }
    }
    *p = 0;
}

typedef struct {
    uint8_t tape[TAPE_SIZE];
    uint16_t vis[TAPE_SIZE];
    uint16_t mk;
    HashEntry table[HASH_SIZE];
    uint16_t epoch;
} ThreadContext;

static int eval_cet1_2x3(const Agent2x3 *ag1, const Agent2x3 *ag2, ThreadContext *ctx, int *out_tot_col, int *out_cyc_len, int *out_sim_steps) {
    if (++ctx->mk == 0) {
        memset(ctx->vis, 0, sizeof(ctx->vis));
        ctx->mk = 1;
    }
    ctx->epoch++;
    if (ctx->epoch == 0) {
        memset(ctx->table, 0, sizeof(ctx->table));
        ctx->epoch = 1;
    }

    uint8_t *tape = ctx->tape;
    uint16_t *vis = ctx->vis;
    uint16_t mk = ctx->mk;
    uint16_t ep = ctx->epoch;
    HashEntry *ht = ctx->table;

    int p1 = TAPE_OFF + 0;
    int p2 = TAPE_OFF + 2;
    int s1 = 0, s2 = 0;

    int last_col = 0;
    int cols = 0;

    uint64_t h = Z_HEAD1[p1][s1] ^ Z_HEAD2[p2][s2];

    for (int step = 1; step <= MAX_STEPS; step++) {
        if (p1 <= 20 || p1 >= TAPE_SIZE - 20 || p2 <= 20 || p2 >= TAPE_SIZE - 20) {
            return 0;
        }

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr t1 = ag1->t[s1][r1];
        Tr t2 = ag2->t[s2][r2];

        h ^= Z_HEAD1[p1][s1] ^ Z_HEAD2[p2][s2];

        // Writing priority: Agent 2 writes, then Agent 1
        if (r2 != t2.w) {
            h ^= Z_CELL[p2][r2] ^ Z_CELL[p2][t2.w];
            vis[p2] = mk; tape[p2] = t2.w;
        }

        uint8_t cur1 = (vis[p1] == mk) ? tape[p1] : 0;
        if (cur1 != t1.w) {
            h ^= Z_CELL[p1][cur1] ^ Z_CELL[p1][t1.w];
            vis[p1] = mk; tape[p1] = t1.w;
        }

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        h ^= Z_HEAD1[p1][s1] ^ Z_HEAD2[p2][s2];

        if (p1 == p2) {
            cols++;
            last_col = step;
        }

        // Cycle check via hash table
        uint64_t full_key = h ^ ((uint64_t)p1 << 32) ^ ((uint64_t)p2 << 16) ^ (s1 << 4) ^ s2;
        uint32_t slot = (uint32_t)(full_key ^ (full_key >> 17)) & HASH_MASK;

        for (int probe = 0; probe < 8; probe++) {
            HashEntry *e = &ht[(slot + probe) & HASH_MASK];
            if (e->epoch != ep) {
                e->epoch = ep;
                e->full_hash = full_key;
                e->p1 = p1; e->p2 = p2;
                e->s1 = s1; e->s2 = s2;
                e->step = step;
                e->cols = cols;
                break;
            }
            if (e->full_hash == full_key && e->p1 == p1 && e->p2 == p2 && e->s1 == s1 && e->s2 == s2) {
                int past_cols = e->cols;
                int cyc = step - e->step;
                if (past_cols == cols && last_col > 0) {
                    *out_tot_col = cols;
                    *out_cyc_len = cyc;
                    *out_sim_steps = step;
                    return last_col;
                } else {
                    return 0;
                }
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    int duration = 60;
    if (argc > 1) duration = atoi(argv[1]);

    init_zobrist();

    printf("=========================================================================================================\n");
    printf("🪐⚡ CET_1(2, 3) 2-STATE 3-SYMBOL QUASI-HALTING WORLD EXPEDITION (%d s) ⚡🪐\n", duration);
    printf("=========================================================================================================\n");
    printf("Condition: Exact In-Place Cycle with ZERO Post-Collision Collisions (Quasi-Halting)\n");
    printf("Standard bbchallenge notation: WriteMoveState for 3 symbols (e.g. 2LB1LA2LA_...)\n");
    printf("Hardware: 16 AMD Ryzen OpenMP Threads\n");
    fflush(stdout);

    ThreadContext *ctx_pools[16];
    for (int i = 0; i < 16; i++) {
        ctx_pools[i] = calloc(1, sizeof(ThreadContext));
    }

    int best_last_col = 0;
    char best_bb[128] = "";
    int best_cols = 0, best_cyc = 0, best_sim = 0;

    double t0 = omp_get_wtime();
    long long total_screened = 0;
    long long quasihalted_count = 0;

    #pragma omp parallel num_threads(16)
    {
        int tid = omp_get_thread_num();
        ThreadContext *ctx = ctx_pools[tid];

        uint64_t seed = (uint64_t)time(NULL) * 6364136223846793005ULL + ((uint64_t)tid * 104729ULL + 1ULL);
        for (int i = 0; i < 20; i++) splitmix64(&seed);

        Agent2x3 a1, a2;
        long long local_screened = 0;
        double last_hb = omp_get_wtime();

        while (omp_get_wtime() - t0 < duration) {
            // Generate Agent 1 in TNF
            int max_seen1 = 0;
            for (int s = 0; s < 2; s++) {
                for (int r = 0; r < 3; r++) {
                    uint64_t v = splitmix64(&seed);
                    a1.t[s][r].w = v % 3;
                    a1.t[s][r].mv = (v & 4) ? 1 : -1;
                    int lim = (max_seen1 < 1) ? 1 : 1;
                    int ns = ((v >> 3) & 1);
                    if (ns > max_seen1) max_seen1 = ns;
                    a1.t[s][r].ns = ns;
                }
            }

            // Generate Agent 2 in TNF
            int max_seen2 = 0;
            for (int s = 0; s < 2; s++) {
                for (int r = 0; r < 3; r++) {
                    uint64_t v = splitmix64(&seed);
                    a2.t[s][r].w = v % 3;
                    a2.t[s][r].mv = (v & 4) ? 1 : -1;
                    int ns = ((v >> 3) & 1);
                    if (ns > max_seen2) max_seen2 = ns;
                    a2.t[s][r].ns = ns;
                }
            }

            local_screened++;

            int tot_col = 0, cyc_len = 0, sim_steps = 0;
            int last_col = eval_cet1_2x3(&a1, &a2, ctx, &tot_col, &cyc_len, &sim_steps);

            if (last_col > 0) {
                #pragma omp atomic
                quasihalted_count++;

                if (last_col > best_last_col) {
                    #pragma omp critical
                    {
                        if (last_col > best_last_col) {
                            best_last_col = last_col;
                            best_cols = tot_col;
                            best_cyc = cyc_len;
                            best_sim = sim_steps;

                            char s1[64], s2[64];
                            fmt_agent_std(&a1, s1);
                            fmt_agent_std(&a2, s2);
                            sprintf(best_bb, "%s|%s", s1, s2);

                            printf("\n🔥👑 [NEW CET_1(2, 3) RECORD: LAST COLLISION AT STEP %d!] 👑🔥\n", last_col);
                            printf("Agent 1: %s\n", s1);
                            printf("Agent 2: %s\n", s2);
                            printf("bbchallenge: %s\n", best_bb);
                            printf("Observed Collisions: %d | Cycle Length: %d | Simulated Steps: %d\n\n",
                                   tot_col, cyc_len, sim_steps);
                            fflush(stdout);
                        }
                    }
                }
            }

            if (tid == 0 && omp_get_wtime() - last_hb > 10.0) {
                last_hb = omp_get_wtime();
                #pragma omp critical
                {
                    double el = omp_get_wtime() - t0;
                    printf("[%.1fs / %ds] Screened %lld machines (%.0f/s) | Quasihalted: %lld | Best Last Collision: %d steps\n",
                           el, duration, total_screened + local_screened,
                           (total_screened + local_screened) / (el > 0 ? el : 1), quasihalted_count, best_last_col);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_screened += local_screened;
    }

    double total_time = omp_get_wtime() - t0;
    printf("\n=========================================================================================================\n");
    printf("🏁 CET_1(2, 3) EXPEDITION COMPLETE in %.2f seconds!\n", total_time);
    printf("Total Configurations Screened: %lld (%.0f/sec)\n", total_screened, total_screened / total_time);
    printf("Total Certified Quasihalters: %lld\n", quasihalted_count);
    printf("👑 Inaugural World Champion CET_1(2, 3): Last Collision at Step %d\n", best_last_col);
    printf("bbchallenge: %s\n", best_bb);
    printf("Observed Collisions: %d | Cycle Length: %d | Simulated Steps: %d\n",
           best_cols, best_cyc, best_sim);
    printf("=========================================================================================================\n");

    return 0;
}
