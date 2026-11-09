#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

// Ultra-compact fast memory representation
#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define FAST_CUTOFF 50000
#define DEEP_CEILING 100000000ULL // 100M Steps!
#define MAX_DIST 4000

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

// Stage 1 inline filter: runs first 50k steps at ~1,000,000 checks/sec
static inline int filter_stage1(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_expand = 0;

    for (int step = 1; step <= FAST_CUTOFF; step++) {
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;

        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return step; }

        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 220) return -1; // Fast divergence prune

        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_expand = step; }
        if (h > hi) { hi = h; last_expand = step; }

        if (step > 15000 && (step - last_expand > 15000)) return -3; // Bounded cycler prune
    }
    return -2; // Promising holdout!
}

// Stage 2: Deep 100M step evaluator
int simulate_super_deep(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_expand = 0;

    for (uint64_t step = 1; step <= DEEP_CEILING; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;

        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return (int)step; }

        int d = p2 - p1; if (d < 0) d = -d;
        if (d > MAX_DIST) return -1;

        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_expand = (int)step; }
        if (h > hi) { hi = h; last_expand = (int)step; }

        if (step > 500000 && ((int)step - last_expand > 500000)) return -3;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 300; // 5 minutes default
    if (argc > 1) duration = atoi(argv[1]);

    printf("========================================================================\n");
    printf("⚡⚡⚡ SUPER OMEGA HARD CET(3) RECORD SEARCH ENGINE (%d s) ⚡⚡⚡\n", duration);
    printf("========================================================================\n");
    printf("Threads: 16 AMD Ryzen 7 3800XT | Ceiling: 100,000,000 Steps\n");
    printf("Current Champion to Beat: 3,746,207 Steps\n");
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long total_evaluated = 0;
    int global_best = 3746207;
    int global_best_pos = -9;
    char global_best_bb[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint32_t seed = (uint32_t)time(NULL) * 2654435761u ^ ((omp_get_thread_num() + 1) * 40503u);
        for (int i = 0; i < 10; i++) xorshift32(&seed);

        M c;
        long long local_evaluated = 0;
        double last_heartbeat = omp_get_wtime();

        while (omp_get_wtime() - t0 < duration) {
            // Fast unrolled generation
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

            // Quick step 1 divergence check
            if (c.t[0][0][0].mv == -1 && c.t[1][0][0].mv == 1 && c.t[0][0][0].w == 0 && c.t[1][0][0].w == 0) continue;

            local_evaluated++;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            int s = filter_stage1(&c, tape, vis, mk, &pos);

            if (s > 100000 || s == -2) {
                // Survived fast stage: execute super deep evaluation
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = simulate_super_deep(&c, tape, vis, mk, &pos);

                if (s > global_best) {
                    #pragma omp critical
                    {
                        if (s > global_best) {
                            global_best = s;
                            global_best_pos = pos;
                            fmt(&c, global_best_bb);
                            printf("\n🔥🔥🔥 >>> NEW SUPER OMEGA RECORD: %d STEPS at cell %d! <<< 🔥🔥🔥\n", s, pos);
                            printf("bbchallenge: %s\n", global_best_bb);
                            fflush(stdout);
                        }
                    }
                } else if (s > 1000000) {
                    #pragma omp critical
                    {
                        char bb[128]; fmt(&c, bb);
                        printf("  [Mega-Halt >1M]: %d steps at cell %d | %s\n", s, pos, bb);
                        fflush(stdout);
                    }
                }
            }

            if (omp_get_thread_num() == 0 && omp_get_wtime() - last_heartbeat > 20.0) {
                last_heartbeat = omp_get_wtime();
                #pragma omp critical
                {
                    printf("[T+%.0fs] Evaluated ~%lldM machines across 16 threads | Current Best: %d steps\n",
                           omp_get_wtime() - t0, total_evaluated / 1000000, global_best);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_evaluated += local_evaluated;

        free(tape); free(vis);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 SUPER OMEGA SEARCH COMPLETE in %.1fs\n", elapsed);
    printf("Total Fresh Machines Screened: %lld (%.0f machines/sec)\n", total_evaluated, total_evaluated / elapsed);
    printf("Best CET(3) Champion: %d steps at cell %d\n", global_best, global_best_pos);
    printf("bbchallenge: %s\n", global_best_bb);
    printf("========================================================================\n");

    return 0;
}
