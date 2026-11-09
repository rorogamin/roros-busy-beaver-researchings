#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 67108864
#define TAPE_OFFSET 33554432
#define MAX_STEPS 600000000ULL

typedef struct {
    uint8_t w;
    int8_t d;
    uint8_t ns;
} Trans4;

typedef struct {
    Trans4 t[2][4][2];
} Machine4;

void format_bb4(const Machine4 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 4; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 2; sym++) {
                Trans4 tr = m->t[a][s][sym];
                *p++ = '0' + tr.w;
                *p++ = tr.d > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.ns;
            }
        }
    }
    *p = '\0';
}

static Machine4 parse_bb4(const char *s) {
    Machine4 m;
    const char *p = s;
    for (int a = 0; a < 2; a++) {
        for (int st = 0; st < 4; st++) {
            for (int sym = 0; sym < 2; sym++) {
                m.t[a][st][sym].w = p[0] - '0';
                m.t[a][st][sym].d = p[1] == 'R' ? 1 : -1;
                m.t[a][st][sym].ns = p[2] - 'A';
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

int simulate_candidate(const Machine4 *m, uint8_t *tape, uint32_t *vis, uint32_t mk, uint64_t max_steps, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (uint64_t step = 1; step <= max_steps; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Trans4 tr1 = m->t[0][s1][r1];
        Trans4 tr2 = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = tr2.w;
        vis[p1] = mk; tape[p1] = tr1.w;

        p1 += tr1.d;
        p2 += tr2.d;

        s1 = tr1.ns;
        s2 = tr2.ns;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            return (int)(step > 2147483647 ? 2147483647 : step);
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        if (dist > 800) return -1;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 60;
    if (argc > 1) duration = atoi(argv[1]);

    const char *seed_bb = "0LB0LC_0LD0RA_0RA0RA_0RA0RA|1RB1LD_1RC1RB_1LC1LA_0RC0RD";
    Machine4 seed = parse_bb4(seed_bb);

    printf("=== CET(4) 500M Neighborhood & Macro-Hunter (%d s) ===\n", duration);
    printf("Seed: 49,184,559 step champion (%s)\n", seed_bb);
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long tested = 0;
    int best = 49184559;
    char best_bb[256];
    strcpy(best_bb, seed_bb);

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint32_t seed_rng = (uint32_t)time(NULL) * 2654435761u ^ (omp_get_thread_num() + 1) * 40503u;

        Machine4 cand;

        while (omp_get_wtime() - t0 < duration) {
            cand = seed;
            int num_mut = 1 + (rnd(&seed_rng) % 2); // 1 or 2 mutations
            for (int i = 0; i < num_mut; i++) {
                int a = rnd(&seed_rng) % 2;
                int s = rnd(&seed_rng) % 4;
                int sym = rnd(&seed_rng) % 2;
                int type = rnd(&seed_rng) % 3;
                if (type == 0) cand.t[a][s][sym].w = rnd(&seed_rng) & 1;
                else if (type == 1) cand.t[a][s][sym].d = (rnd(&seed_rng) & 1) ? 1 : -1;
                else cand.t[a][s][sym].ns = rnd(&seed_rng) & 3;
            }

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            // Quick check 100k
            int s = simulate_candidate(&cand, tape, vis, mk, 100000, &pos);
            if (s == -2) {
                // Holdout! Deep test to 500M
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = simulate_candidate(&cand, tape, vis, mk, 500000000ULL, &pos);
                if (s > best) {
                    #pragma omp critical
                    {
                        if (s > best) {
                            best = s;
                            format_bb4(&cand, best_bb);
                            printf("\n*** >>> NEW CET(4) LATE COLLISION: %d STEPS at cell %d! <<< ***\n", s, pos);
                            printf("bbchallenge: %s\n", best_bb);
                            fflush(stdout);
                        }
                    }
                }
            }

            #pragma omp atomic
            tested++;
        }
        free(tape); free(vis);
    }

    printf("\nFinished in %.1f s. Tested %lld mutations around 49.1M champion.\n", omp_get_wtime() - t0, tested);
    printf("Best CET(4): %d steps | %s\n", best, best_bb);
    return 0;
}
