#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 65536
#define TAPE_OFFSET 32768
#define STAGE1_CUTOFF 30000
#define DEEP_CEILING 50000000ULL

typedef struct { int8_t w, mv, ns; } Tr;
typedef struct { Tr t[2][3][2]; } M;

static void fmt(const M *m, char *b) {
    char *p = b;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                Tr x = m->t[a][s][r];
                *p++ = '0' + x.w; *p++ = x.mv > 0 ? 'R' : 'L'; *p++ = 'A' + x.ns;
            }
        }
    }
    *p = 0;
}

static inline uint32_t xorshift32(uint32_t *s) {
    uint32_t x = *s;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    return *s = x;
}

// Stage 1: Ultra-fast branchless simulator on stack / tiny L1 cache tape
static inline int eval_fast(const M *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;

    for (int step = 1; step <= STAGE1_CUTOFF; step++) {
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1];
        Tr b = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv;
        p2 += b.mv;
        s1 = a.ns;
        s2 = b.ns;

        if (p1 == p2) {
            *pos = p1 - TAPE_OFFSET;
            return step;
        }

        int d = p2 - p1;
        if (d < 0) d = -d;
        if (d > 120) return -1; // diverged

        int l = p1 < p2 ? p1 : p2;
        int h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }

        if (step > 6000 && (step - last_exp > 6000)) return -3; // stationary cycle
    }
    return -2; // Holdout past STAGE1_CUTOFF!
}

// Stage 2: Deep simulator for rare surviving candidates
static int eval_deep(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = 8388608, p2 = 8388610;
    int s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;

    for (uint64_t step = 1; step <= DEEP_CEILING; step++) {
        if (p1 <= 200 || p1 >= 16777000 || p2 <= 200 || p2 >= 16777000) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1];
        Tr b = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv;
        p2 += b.mv;
        s1 = a.ns;
        s2 = b.ns;

        if (p1 == p2) {
            *pos = p1 - 8388608;
            return (int)step;
        }

        int d = p2 - p1;
        if (d < 0) d = -d;
        if (d > 4000) return -1;

        int l = p1 < p2 ? p1 : p2;
        int h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = (int)step; }
        if (h > hi) { hi = h; last_exp = (int)step; }

        if (step > 500000 && ((int)step - last_exp > 500000)) return -3;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 60;
    if (argc > 1) duration = atoi(argv[1]);

    printf("========================================================================\n");
    printf("⚡⚡⚡ HYPER-SPEED CET(3) OMEGA ENGINE (%d s) ⚡⚡⚡\n", duration);
    printf("========================================================================\n");
    printf("16 Threads | L1 Cache residency | Target: >3,746,207 Steps\n");
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long total_evaluated = 0;
    long long total_deep = 0;
    int global_best = 3746207;
    int global_best_pos = -9;
    char global_best_bb[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    #pragma omp parallel
    {
        uint8_t *tape1 = calloc(TAPE_SIZE, 1);
        uint16_t *vis1 = calloc(TAPE_SIZE, 2);
        uint16_t mk1 = 0;

        uint8_t *tape2 = calloc(16777216, 1);
        uint32_t *vis2 = calloc(16777216, 4);
        uint32_t mk2 = 0;

        uint32_t seed = (uint32_t)time(NULL) * 2654435761u ^ ((omp_get_thread_num() + 1) * 40503u);
        for (int i = 0; i < 10; i++) xorshift32(&seed);

        M c;
        long long local_eval = 0;
        long long local_deep = 0;
        double last_hb = omp_get_wtime();

        while (omp_get_wtime() - t0 < duration) {
            // Generate full machine
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        uint32_t v = xorshift32(&seed);
                        c.t[a][s][r].w = v & 1;
                        c.t[a][s][r].mv = (v & 2) ? 1 : -1;
                        c.t[a][s][r].ns = (v >> 2) % 3;
                    }
                }
            }

            // Reject trivial divergent start
            if (c.t[0][0][0].mv == -1 && c.t[1][0][0].mv == 1 && c.t[0][0][0].w == 0 && c.t[1][0][0].w == 0) continue;

            local_eval++;

            if (++mk1 == 0) { memset(vis1, 0, TAPE_SIZE * 2); mk1 = 1; }
            int pos = 0;
            int s = eval_fast(&c, tape1, vis1, mk1, &pos);

            if (s == -2 || s > 25000) {
                local_deep++;
                if (++mk2 == 0) { memset(vis2, 0, 16777216 * 4); mk2 = 1; }
                s = eval_deep(&c, tape2, vis2, mk2, &pos);

                if (s > global_best) {
                    #pragma omp critical
                    {
                        if (s > global_best) {
                            global_best = s;
                            global_best_pos = pos;
                            fmt(&c, global_best_bb);
                            printf("\n🔥🎯🏆 NEW ALL-TIME RECORD: %d STEPS at cell %d! 🏆🎯🔥\n", s, pos);
                            printf("bbchallenge: %s\n", global_best_bb);
                            fflush(stdout);
                        }
                    }
                } else if (s > 1000000) {
                    #pragma omp critical
                    {
                        char bb[128]; fmt(&c, bb);
                        printf("  [Holdout >1M]: %d steps at cell %d | %s\n", s, pos, bb);
                        fflush(stdout);
                    }
                }
            }

            if (omp_get_thread_num() == 0 && omp_get_wtime() - last_hb > 10.0) {
                last_hb = omp_get_wtime();
                #pragma omp critical
                {
                    printf("[T+%.0fs] Screened %lld fresh machines | Deep checks: %lld | Champion: %d\n",
                           omp_get_wtime() - t0, total_evaluated, total_deep, global_best);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_evaluated += local_eval;
        #pragma omp atomic
        total_deep += local_deep;

        free(tape1); free(vis1);
        free(tape2); free(vis2);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 HYPER SEARCH COMPLETE in %.1fs\n", elapsed);
    printf("Total Fresh Machines Screened: %lld (%.0f machines/sec)\n", total_evaluated, total_evaluated / elapsed);
    printf("Deep Candidates Evaluated: %lld\n", total_deep);
    printf("Best CET(3) Champion: %d steps at cell %d\n", global_best, global_best_pos);
    printf("bbchallenge: %s\n", global_best_bb);
    printf("========================================================================\n");

    return 0;
}
