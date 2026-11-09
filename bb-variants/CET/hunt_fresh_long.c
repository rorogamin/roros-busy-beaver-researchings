#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define MAX_STEPS 10000000ULL
#define MAX_DIST 5000

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

static inline uint32_t rnd(uint32_t *s) {
    uint32_t x = *s; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *s = x;
}

/* >0 halt step; -1 diverged/OOB; -2 cutoff; -3 glider/stalled (pruned) */
static inline int run(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_expand = 0;
    for (int step = 1; step <= (int)MAX_STEPS; step++) {
        uint8_t r1 = vis[p1] == mk ? tape[p1] : 0;
        uint8_t r2 = vis[p2] == mk ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > MAX_DIST) return -1;
        if (p1 < 1000 || p1 > TAPE_SIZE - 1000 || p2 < 1000 || p2 > TAPE_SIZE - 1000) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_expand = step; }
        if (h > hi) { hi = h; last_expand = step; }
        /* prune: stalled (no new cell for 300k steps) => bounded cycler */
        if (step - last_expand > 300000) return -3;
        /* prune: glider => span grows linearly (> 0.2/step) after 100k steps */
        if (step == 100000 && (hi - lo) > 20000) return -3;
        if (step == 1000000 && (hi - lo) > 200000) return -3;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 900; // 15 minutes default
    if (argc > 1) duration = atoi(argv[1]);

    printf("========================================================================\n");
    printf("⚡ LONG-RUN 16-THREAD FRESH CET(3) RECORD SEARCH (%d SECONDS / %.1f MIN)\n", duration, duration / 60.0);
    printf("========================================================================\n");
    printf("Target: > 3,746,207 Steps | Step ceiling: 10,000,000 | Threads: %d\n", omp_get_max_threads());
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long global_tested = 0;
    int best = 3746207;
    int best_pos = -9;
    char bestbb[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint32_t seed = (uint32_t)time(NULL) * 2654435761u ^ ((omp_get_thread_num() + 1) * 40503u);
        for (int i = 0; i < 10; i++) rnd(&seed);

        long long local_tested = 0;
        double last_report = omp_get_wtime();

        while (omp_get_wtime() - t0 < duration) {
            M c;
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        c.t[a][s][r].w = rnd(&seed) & 1;
                        c.t[a][s][r].mv = (rnd(&seed) & 1) ? 1 : -1;
                        c.t[a][s][r].ns = rnd(&seed) % 3;
                    }
                }
            }

            if (c.t[0][0][0].mv == 1 && c.t[1][0][0].mv == -1) continue;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            int st = run(&c, tape, vis, mk, &pos);
            local_tested++;

            if (st > 500000) {
                #pragma omp critical
                {
                    if (st > best) {
                        best = st;
                        best_pos = pos;
                        fmt(&c, bestbb);
                        printf("\n💥💥💥 >>> NEW ALL-TIME CET(3) WORLD RECORD: %d STEPS at cell %d! <<< 💥💥💥\n", st, pos);
                        printf("bbchallenge: %s\n", bestbb);
                        fflush(stdout);
                    } else if (st > 1000000) {
                        char bb[128]; fmt(&c, bb);
                        printf("  [Notable >1M discovery]: %d steps at cell %d | %s\n", st, pos, bb);
                        fflush(stdout);
                    }
                }
            }

            if (omp_get_thread_num() == 0 && omp_get_wtime() - last_report > 30.0) {
                last_report = omp_get_wtime();
                #pragma omp critical
                {
                    printf("[T+%.0fs] Progress: running across %d threads | best: %d steps\n",
                           omp_get_wtime() - t0, omp_get_max_threads(), best);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        global_tested += local_tested;

        free(tape); free(vis);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 Screened %lld completely fresh random machines in %.1fs (%.0f machines/sec)\n",
           global_tested, elapsed, global_tested / elapsed);
    printf("Final Best CET(3): %d steps at cell %d | %s\n", best, best_pos, bestbb);
    printf("========================================================================\n");

    return 0;
}
