#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 33554432
#define TAPE_OFFSET 16777216
#define MAX_STEPS 30000000ULL

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

static int run_bidirectional(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_expand = 0;

    for (uint64_t step = 1; step <= MAX_STEPS; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) return -1;
        uint8_t r1 = vis[p1] == mk ? tape[p1] : 0;
        uint8_t r2 = vis[p2] == mk ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;

        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return (int)step; }

        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 4500) return -1;

        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_expand = (int)step; }
        if (h > hi) { hi = h; last_expand = (int)step; }

        if (step > 400000 && ((int)step - last_expand > 400000)) return -3;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 60;
    if (argc > 1) duration = atoi(argv[1]);

    const char *seeds[] = {
        "0LB1LA_0LC0LB_1RB1RC|1LC0RC_1RA1LB_0LB1RC", // 717k Nath-family
        "0LC1LA_0LC0LB_1RB1RC|1RC0RC_1RA1LB_0LB1RC", // 265k Nath-family
        "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB"  // 3.74M champ
    };

    M pop[3];
    for (int i = 0; i < 3; i++) pop[i] = parse(seeds[i]);

    printf("========================================================================\n");
    printf("🧬 HYBRID MULTI-SEED GENETIC CET(3) RECORD SEARCH (%d s)\n", duration);
    printf("========================================================================\n");
    printf("Seeds loaded: 717k, 265k, 3.74M | threads=%d | Goal: >3,746,207 steps\n", omp_get_max_threads());
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long total_tested = 0;
    int global_best = 3746207;
    int global_best_pos = -9;
    char global_best_bb[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint32_t seed_rng = (uint32_t)time(NULL) * 2654435761u ^ (omp_get_thread_num() + 1) * 40503u;

        M cand;
        long long local_tested = 0;

        while (omp_get_wtime() - t0 < duration) {
            int mode = rnd(&seed_rng) % 10;
            if (mode < 8) {
                // Mutate one of the top seeds
                int pidx = rnd(&seed_rng) % 3;
                cand = pop[pidx];
                int nmut = 1 + (rnd(&seed_rng) % 2);
                for (int i = 0; i < nmut; i++) {
                    int a = rnd(&seed_rng) % 2;
                    int s = rnd(&seed_rng) % 3;
                    int r = rnd(&seed_rng) % 2;
                    int type = rnd(&seed_rng) % 3;
                    if (type == 0) cand.t[a][s][r].w = rnd(&seed_rng) & 1;
                    else if (type == 1) cand.t[a][s][r].mv = (rnd(&seed_rng) & 1) ? 1 : -1;
                    else cand.t[a][s][r].ns = rnd(&seed_rng) % 3;
                }
            } else {
                // Fresh random
                for (int a = 0; a < 2; a++) for (int s = 0; s < 3; s++) for (int r = 0; r < 2; r++) {
                    cand.t[a][s][r].w = rnd(&seed_rng) & 1;
                    cand.t[a][s][r].mv = (rnd(&seed_rng) & 1) ? 1 : -1;
                    cand.t[a][s][r].ns = rnd(&seed_rng) % 3;
                }
            }
            local_tested++;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            int s = run_bidirectional(&cand, tape, vis, mk, &pos);

            if (s > global_best) {
                #pragma omp critical
                {
                    if (s > global_best) {
                        global_best = s;
                        global_best_pos = pos;
                        fmt(&cand, global_best_bb);
                        printf("\n💥💥💥 >>> NEW CET(3) RECORD HALT: %d STEPS at cell %d! <<< 💥💥💥\n", s, pos);
                        printf("bbchallenge: %s\n", global_best_bb);
                        fflush(stdout);
                    }
                }
            } else if (s > 700000) {
                #pragma omp critical
                {
                    char bb[128]; fmt(&cand, bb);
                    printf("  Notable high runner: %d steps at cell %d | %s\n", s, pos, bb);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_tested += local_tested;

        free(tape); free(vis);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 Evaluated %lld machines in %.1fs (%.0f machines/sec)\n", total_tested, elapsed, total_tested / elapsed);
    printf("Final Best CET(3): %d steps at cell %d\n", global_best, global_best_pos);
    printf("bbchallenge: %s\n", global_best_bb);
    printf("========================================================================\n");

    return 0;
}
