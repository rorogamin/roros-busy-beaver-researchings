#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 33554432
#define TAPE_OFFSET 16777216
#define SCREEN_STEPS 60000
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

static inline uint32_t rnd(uint32_t *s) {
    uint32_t x = *s; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *s = x;
}

// Stage 1: Ultra-fast behavioral classifier (60,000 steps)
// Targets ONLY systems that oscillate with high direction reversals and non-trivial tape span
static inline int screen_bouncer(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int min_touched = p1, max_touched = p2;
    int rev1 = 0, rev2 = 0;
    int prev_m1 = 0, prev_m2 = 0;

    for (int step = 1; step <= SCREEN_STEPS; step++) {
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;

        if (a.mv != prev_m1) { rev1++; prev_m1 = a.mv; }
        if (b.mv != prev_m2) { rev2++; prev_m2 = b.mv; }

        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return step; }

        int dist = p2 - p1; if (dist < 0) dist = -dist;
        // Bouncer constraint: distance must stay within dynamic interaction corridor
        if (dist > 350) return -1; // Fast prune of divergent pairs

        if (p1 < min_touched) min_touched = p1;
        if (p1 > max_touched) max_touched = p1;
        if (p2 < min_touched) min_touched = p2;
        if (p2 > max_touched) max_touched = p2;
    }

    // After 60,000 steps:
    // If one agent barely reversed (< 10 times), it is a unidirectional escapee
    if (rev1 < 10 && rev2 < 10) return -3;

    int span = max_touched - min_touched;
    // Tiny periodic cyclers stay within < 10 cells
    if (span < 12) return -3;

    // Passed filter: Genuine expanding ping-pong bouncer holdout!
    return -2;
}

// Stage 2: Deep 50,000,000 step verification
int simulate_deep_bouncer(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
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
        if (d > 5000) return -1;

        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_expand = (int)step; }
        if (h > hi) { hi = h; last_expand = (int)step; }

        if (step > 500000 && ((int)step - last_expand > 500000)) return -3; // Bounded
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 90;
    if (argc > 1) duration = atoi(argv[1]);

    printf("========================================================================\n");
    printf("🎯 CET(3) HIGH-EFFICIENCY BOUNCER & SHUTTLE HUNTER (%d s)\n", duration);
    printf("========================================================================\n");
    printf("Targeting: Multi-million step ping-pong & bouncer class | Threads: %d\n", omp_get_max_threads());
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long total_searched = 0;
    long long bouncer_candidates = 0;
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

        M c;
        long long local_count = 0;

        while (omp_get_wtime() - t0 < duration) {
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        c.t[a][s][r].w = rnd(&seed) & 1;
                        c.t[a][s][r].mv = (rnd(&seed) & 1) ? 1 : -1;
                        c.t[a][s][r].ns = rnd(&seed) % 3;
                    }
                }
            }

            // Reject instant step 1 escape
            if (c.t[0][0][0].mv == -1 && c.t[1][0][0].mv == 1 && c.t[0][0][0].w == 0 && c.t[1][0][0].w == 0) continue;

            local_count++;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            int s = screen_bouncer(&c, tape, vis, mk, &pos);

            if (s > 100000 || s == -2) {
                #pragma omp atomic
                bouncer_candidates++;

                // Stage 2 deep run up to 50,000,000 steps
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = simulate_deep_bouncer(&c, tape, vis, mk, &pos);

                if (s > best) {
                    #pragma omp critical
                    {
                        if (s > best) {
                            best = s;
                            best_pos = pos;
                            fmt(&c, bestbb);
                            printf("\n💥💥💥 >>> NEW ALL-TIME CET(3) RECORD HALT: %d STEPS at cell %d! <<< 💥💥💥\n", s, pos);
                            printf("bbchallenge: %s\n", bestbb);
                            fflush(stdout);
                        }
                    }
                } else if (s > 500000) {
                    #pragma omp critical
                    {
                        char bb[128]; fmt(&c, bb);
                        printf("  [Notable >500k Halt]: %d steps at cell %d | %s\n", s, pos, bb);
                        fflush(stdout);
                    }
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
    printf("Promising Bouncer Candidates Filtered: %lld\n", bouncer_candidates);
    printf("Final Best CET(3): %d steps at cell %d | %s\n", best, best_pos, bestbb);
    printf("========================================================================\n");

    return 0;
}
