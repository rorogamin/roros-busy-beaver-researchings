#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define MAX_STEPS 10000000
#define MAX_DIST 6000

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
static int run(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_expand = 0;
    for (int step = 1; step <= MAX_STEPS; step++) {
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
        /* prune: stalled (no new cell for 400k steps) => bounded cycler */
        if (step - last_expand > 400000) return -3;
        /* prune: glider => span grows linearly (> 0.25/step) after 100k steps */
        if (step == 100000 && (hi - lo) > 25000) return -3;
        if (step == 1000000 && (hi - lo) > 250000) return -3;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 90;
    if (argc > 1) duration = atoi(argv[1]);

    printf("=== High-Power CET(3,2) Hunt for >3,746,207 Steps (%d s) | threads=%d ===\n", duration, omp_get_max_threads());
    fflush(stdout);
    double t0 = omp_get_wtime();
    long long tested = 0, halts = 0, pruned = 0, cutoffs = 0;
    int best = 3746207;
    int done = 0;
    char bestbb[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint32_t seed = (uint32_t)time(NULL) * 2654435761u ^ (omp_get_thread_num() + 1) * 40503u;
        for (int i = 0; i < 10; i++) rnd(&seed);

        while (!done && (omp_get_wtime() - t0 < duration)) {
            M c;
            for (int a = 0; a < 2; a++) for (int s = 0; s < 3; s++) for (int r = 0; r < 2; r++) {
                c.t[a][s][r].w = rnd(&seed) & 1;
                c.t[a][s][r].mv = (rnd(&seed) & 1) ? 1 : -1;
                c.t[a][s][r].ns = rnd(&seed) % 3;
            }
            if (c.t[0][0][0].mv == 1 && c.t[1][0][0].mv == -1) continue;
            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0; int st = run(&c, tape, vis, mk, &pos);
            #pragma omp critical(stat)
            {
                tested++;
                if (st > 0) halts++; else if (st == -3) pruned++; else if (st == -2) cutoffs++;
                if (st > best) {
                    best = st; fmt(&c, bestbb);
                    printf("\n*** >>> NEW CET(3,2) RECORD: %d steps | %s | cell %d <<< ***\n", st, bestbb, pos);
                    fflush(stdout);
                } else if (st > 250000) {
                    char bb[128]; fmt(&c, bb);
                    printf("  notable halt %d | %s\n", st, bb); fflush(stdout);
                }
                if (tested % 1000000 == 0) {
                    printf("[%.0fs] tested %lldM | halts %lld | pruned %lld | cutoff %lld | best %d\n",
                           omp_get_wtime() - t0, tested / 1000000, halts, pruned, cutoffs, best);
                    fflush(stdout);
                }
            }
        }
        free(tape); free(vis);
    }
    printf("\nFinished hunt in %.1f s. Tested %lld machines.\n", omp_get_wtime() - t0, tested);
    printf("Final Best CET(3,2): %d steps | %s\n", best, bestbb);
    return 0;
}
