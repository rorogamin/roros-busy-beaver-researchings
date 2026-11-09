#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 67108864
#define TAPE_OFFSET 33554432
#define CUTOFF_FILTER 500000000ULL // 500 million step target

typedef struct {
    uint8_t w;      // write symbol (0 or 1)
    int8_t d;       // direction (-1 for LEFT, +1 for RIGHT)
    uint8_t ns;     // next state (0..3)
} Trans4;

typedef struct {
    Trans4 t[2][4][2]; // [agent 0..1][state 0..3][symbol 0..1]
} Machine4;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

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

static inline uint32_t rnd(uint32_t *s) {
    uint32_t x = *s; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *s = x;
}

// Stage 1: Fast filter up to 100,000 steps with strict distance bounds
int simulate_cet4_fast(const Machine4 *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int max_steps, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= max_steps; step++) {
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
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        int rem = max_steps - step;
        if (dist > 2 * rem || dist > 250) return -1;
    }
    return -2; // Timed out (genuine holdout / long collision candidate!)
}

// Stage 2: Deep simulation up to 100,000,000 steps
int simulate_cet4_deep(const Machine4 *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int max_steps, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= max_steps; step++) {
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
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        if (dist > 800) return -1;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 90;
    if (argc > 1) duration = atoi(argv[1]);

    printf("========================================================================\n");
    printf("🚀 CET(4) ULTRA LATE-COLLISION MASS SEARCH (>49,184,559 STEPS)\n");
    printf("========================================================================\n");
    printf("Baseline to beat: 49,184,559 steps (colliding at x = -16,394,853)\n");
    printf("Target ceiling: 100,000,000 to 500,000,000 steps | threads=%d | duration=%ds\n", omp_get_max_threads(), duration);
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long tested = 0;
    long long fast_filtered = 0;
    int global_best = 49184559;
    int global_best_pos = -16394853;
    char global_best_bb[256] = "0LB0LC_0LD0RA_0RA0RA_0RA0RA|1RB1LD_1RC1RB_1LC1LA_0RC0RD";

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *vis = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t mk = 0;
        uint32_t seed = (uint32_t)time(NULL) * 2654435761u ^ (omp_get_thread_num() + 1) * 40503u;

        Machine4 m;
        long long local_tested = 0;

        while (omp_get_wtime() - t0 < duration) {
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 4; s++) {
                    for (int sym = 0; sym < 2; sym++) {
                        m.t[a][s][sym].w = rnd(&seed) & 1;
                        m.t[a][s][sym].d = (rnd(&seed) & 1) ? 1 : -1;
                        m.t[a][s][sym].ns = rnd(&seed) & 3;
                    }
                }
            }
            local_tested++;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;

            // Stage 1: 50,000 steps
            int s = simulate_cet4_fast(&m, tape, vis, mk, 50000, &pos);
            if (s == -2) {
                // Survived Stage 1! Run Stage 2 up to 100,000,000 steps
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = simulate_cet4_deep(&m, tape, vis, mk, 100000000, &pos);

                if (s > global_best) {
                    #pragma omp critical
                    {
                        if (s > global_best) {
                            global_best = s;
                            global_best_pos = pos;
                            format_bb4(&m, global_best_bb);
                            printf("\n************************************************************************\n");
                            printf("🎉 NEW CET(4) WORLD RECORD HALT: %d STEPS at cell %d!\n", s, pos);
                            printf("bbchallenge: %s\n", global_best_bb);
                            printf("************************************************************************\n");
                            fflush(stdout);
                        }
                    }
                } else if (s == -2) {
                    #pragma omp critical
                    {
                        char bb[256];
                        format_bb4(&m, bb);
                        printf("\n[HOLDOUT SURVIVED 100M STEPS]: %s\n", bb);
                        fflush(stdout);
                    }
                }
            }
        }

        #pragma omp atomic
        tested += local_tested;

        free(tape);
        free(vis);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 Search completed in %.2f s. Total machines evaluated: %lld (%.0f/sec)\n", elapsed, tested, tested / elapsed);
    printf("Current Champion: %d steps at cell %d\n", global_best, global_best_pos);
    printf("bbchallenge: %s\n", global_best_bb);
    printf("========================================================================\n");

    return 0;
}
