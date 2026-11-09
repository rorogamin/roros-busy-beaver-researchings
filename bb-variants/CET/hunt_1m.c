#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 8388608
#define TAPE_OFFSET 4194304
#define MAX_STEPS 6000000
#define MAX_DIST 4000
#define POP 64

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

static M parse(const char *s) {
    M m; const char *p = s;
    for (int a = 0; a < 2; a++) {
        for (int st = 0; st < 3; st++) {
            for (int r = 0; r < 2; r++) {
                m.t[a][st][r].w = p[0] - '0';
                m.t[a][st][r].mv = p[1] == 'R' ? 1 : -1;
                m.t[a][st][r].ns = p[2] - 'A';
                p += 3;
            }
            if (*p == '_' || *p == '|') p++;
        }
    }
    return m;
}

static inline uint32_t rnd(uint32_t *s) {
    uint32_t x = *s; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *s = x;
}

/* returns halt step, or -1 (diverged/out of bounds), -2 (cutoff) */
static int run(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
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
    }
    return -2;
}

static M pop[POP]; static int popsteps[POP]; static int popn = 0;
static int best = 0; static char bestbb[128];

int main(void) {
    const char *seeds[] = {
        "0LB1LA_0LC0LB_1RB1RC|1LC0RC_1RA1LB_0LB1RC",
        "0LC1LA_0LC0LB_1RB1RC|1RC0RC_1RA1LB_0LB1RC"
    };
    for (int i = 0; i < 2; i++) { pop[popn] = parse(seeds[i]); popsteps[popn++] = i == 0 ? 717751 : 265383; }
    best = 717751; fmt(&pop[0], bestbb);
    printf("Hunting >1,000,000 steps; seeds loaded; threads=%d\n", omp_get_max_threads());
    fflush(stdout);
    double t0 = omp_get_wtime();
    long long tested = 0; int done = 0;

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint32_t seed = (uint32_t)time(NULL) * 2654435761u ^ (omp_get_thread_num() + 1) * 40503u;
        while (!done) {
            M c; int mode = rnd(&seed) % 10;
            if (mode == 0) {
                for (int a = 0; a < 2; a++) for (int s = 0; s < 3; s++) for (int r = 0; r < 2; r++) {
                    c.t[a][s][r].w = rnd(&seed) & 1; c.t[a][s][r].mv = (rnd(&seed) & 1) ? 1 : -1; c.t[a][s][r].ns = rnd(&seed) % 3;
                }
            } else {
                int idx; 
                #pragma omp critical(popl)
                { idx = rnd(&seed) % popn; c = pop[idx]; }
                int nm = 1 + rnd(&seed) % 3;
                for (int i = 0; i < nm; i++) {
                    int a = rnd(&seed) % 2, s = rnd(&seed) % 3, r = rnd(&seed) % 2;
                    c.t[a][s][r].w = rnd(&seed) & 1; c.t[a][s][r].mv = (rnd(&seed) & 1) ? 1 : -1; c.t[a][s][r].ns = rnd(&seed) % 3;
                }
            }
            if (c.t[0][0][0].mv == 1 && c.t[1][0][0].mv == -1) continue;
            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0; int st = run(&c, tape, vis, mk, &pos);
            #pragma omp critical(popl)
            {
                tested++;
                if (st > 200000) {
                    int dup = 0;
                    for (int i = 0; i < popn; i++) if (popsteps[i] == st) dup = 1;
                    if (!dup) {
                        int slot = popn < POP ? popn++ : 2;
                        /* replace worst (keep index 0,1 seeds) */
                        if (popn == POP) { int w = 2; for (int i = 2; i < POP; i++) if (popsteps[i] < popsteps[w]) w = i; slot = w; }
                        if (slot >= 0 && (slot >= popn - 0 || st > popsteps[slot] || 1)) { pop[slot] = c; popsteps[slot] = st; }
                    }
                }
                if (st > best) {
                    best = st; fmt(&c, bestbb);
                    printf("\n*** NEW RECORD %d steps | %s | collision cell %d ***\n", st, bestbb, pos);
                    if (st >= 1000000) { printf(">>> 1,000,000+ ACHIEVED <<<\n"); done = 1; }
                    fflush(stdout);
                }
                if (tested % 200000 == 0) {
                    printf("[%.0fs] tested %lldk | best %d | pop %d\n", omp_get_wtime() - t0, tested / 1000, best, popn);
                    fflush(stdout);
                }
            }
        }
        free(tape); free(vis);
    }
    printf("Final best: %d | %s\n", best, bestbb);
    return 0;
}
