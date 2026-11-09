#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define CUTOFF_FAST 150000
#define CUTOFF_DEEP 20000000ULL
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

static inline uint32_t rnd(uint32_t *s) {
    uint32_t x = *s; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *s = x;
}

// Stage 1 filter: runs 150k steps with quick bounding
static inline int simulate_stage1(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_expand = 0;

    for (int step = 1; step <= CUTOFF_FAST; step++) {
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;

        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return step; }

        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 300) return -1; // Fast divergence bailout

        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_expand = step; }
        if (h > hi) { hi = h; last_expand = step; }

        if (step > 30000 && (step - last_expand > 30000)) return -3; // Bounded cycler
    }
    return -2; // Holdout past 150k steps!
}

// Stage 2: Deep 20,000,000 step verification
int simulate_stage2(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    for (uint64_t step = 1; step <= CUTOFF_DEEP; step++) {
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
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 60;
    if (argc > 1) duration = atoi(argv[1]);

    printf("========================================================================\n");
    printf("⚡ HIGH-THROUGHPUT PIPELINED CET(3) RECORD SEARCH (%d s)\n", duration);
    printf("========================================================================\n");
    printf("Baseline: 3,746,207 steps | 16 threads | Target: >3.74M\n");
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long total_searched = 0;
    int global_best = 3746207;
    int global_best_pos = -9;
    char global_best_bb[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint32_t seed = (uint32_t)time(NULL) * 2654435761u ^ (omp_get_thread_num() + 1) * 40503u;

        M m;
        long long local_count = 0;

        while (omp_get_wtime() - t0 < duration) {
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        m.t[a][s][r].w = rnd(&seed) & 1;
                        m.t[a][s][r].mv = (rnd(&seed) & 1) ? 1 : -1;
                        m.t[a][s][r].ns = rnd(&seed) % 3;
                    }
                }
            }

            local_count++;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            int s = simulate_stage1(&m, tape, vis, mk, &pos);
            if (s > 200000 || s == -2) {
                // Survived fast stage: run deep simulation
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = simulate_stage2(&m, tape, vis, mk, &pos);
                if (s > global_best) {
                    #pragma omp critical
                    {
                        if (s > global_best) {
                            global_best = s;
                            global_best_pos = pos;
                            fmt(&m, global_best_bb);
                            printf("\n💥💥💥 >>> NEW CET(3) WORLD RECORD HALT: %d STEPS at cell %d! <<< 💥💥💥\n", s, pos);
                            printf("bbchallenge: %s\n", global_best_bb);
                            fflush(stdout);
                        }
                    }
                } else if (s > 300000) {
                    char bb[128]; fmt(&m, bb);
                    printf("  Notable high runner: %d steps at cell %d | %s\n", s, pos, bb);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_searched += local_count;

        free(tape); free(vis);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 Screened %lld machines in %.1fs (%.0f machines/sec)\n", total_searched, elapsed, total_searched / elapsed);
    printf("Final Best CET(3): %d steps at cell %d\n", global_best, global_best_pos);
    printf("bbchallenge: %s\n", global_best_bb);
    printf("========================================================================\n");

    return 0;
}
