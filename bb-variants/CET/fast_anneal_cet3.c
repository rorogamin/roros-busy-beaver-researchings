#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <omp.h>

#define N 3
#define TAPE_SIZE 20000000
#define TAPE_CENTER 10000000
#define CHAMPION_STEPS 4657368LL
#define MAX_SIM_MULT 1.15
#define MAX_SIM_ADD 10000
#define ITERATIONS 10000

typedef struct {
    int8_t ns, w, d;
} Tr;

static const Tr CHAMPION_TA[3][2] = {
    { {1, 0, -1}, {1, 0, -1} },
    { {2, 0,  1}, {0, 1, -1} },
    { {1, 1, -1}, {2, 1,  1} }
};

static const Tr CHAMPION_TB[3][2] = {
    { {1, 0,  1}, {2, 1,  1} },
    { {2, 1,  1}, {0, 0,  1} },
    { {2, 1, -1}, {1, 0, -1} }
};

// Fast XorShift128+ PRNG per thread
typedef struct {
    uint64_t s[2];
} Rng;

static inline uint64_t xorshift128p(Rng *rng) {
    uint64_t s1 = rng->s[0];
    const uint64_t s0 = rng->s[1];
    rng->s[0] = s0;
    s1 ^= s1 << 23;
    rng->s[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rng->s[1] + s0;
}

static inline double rng_double(Rng *rng) {
    return (xorshift128p(rng) >> 11) * (1.0 / 9007199254740992.0);
}

static inline int rng_int(Rng *rng, int n) {
    return (int)(xorshift128p(rng) % n);
}

long long run_machine_fast(const Tr tA[3][2], const Tr tB[3][2], long long max_steps,
                           int8_t *tape, int prune, int check_interval, int streak_threshold) {
    int pA = TAPE_CENTER;
    int pB = TAPE_CENTER + 2;
    int sA = 0, sB = 0;
    int min_pos = pA, max_pos = pB;
    int last_dist = 2;
    int streak = 0;
    long long result = max_steps;

    for (long long step = 0; step < max_steps; step++) {
        if (pA == pB) {
            result = step;
            break;
        }
        int8_t symA = tape[pA];
        int8_t symB = tape[pB];

        Tr trA = tA[sA][symA];
        Tr trB = tB[sB][symB];

        tape[pA] = trA.w;
        tape[pB] = trB.w;

        pA += trA.d;
        pB += trB.d;
        sA = trA.ns;
        sB = trB.ns;

        if (pA < min_pos) min_pos = pA; if (pA > max_pos) max_pos = pA;
        if (pB < min_pos) min_pos = pB; if (pB > max_pos) max_pos = pB;

        if (pA < 0 || pA >= TAPE_SIZE || pB < 0 || pB >= TAPE_SIZE) {
            result = -1; // OOB
            break;
        }

        if (prune && step > 0 && step % check_interval == 0) {
            int new_dist = pB - pA;
            int delta = new_dist - last_dist;
            if (abs(delta) >= check_interval * 0.9) {
                streak++;
                if (streak >= streak_threshold) {
                    result = max_steps;
                    break;
                }
            } else {
                streak = 0;
            }
            last_dist = new_dist;
        }
    }

    // Clean tape footprint
    for (int i = min_pos; i <= max_pos; i++) {
        tape[i] = 0;
    }
    return result;
}

void mutate(const Tr inA[3][2], const Tr inB[3][2], Tr outA[3][2], Tr outB[3][2], int k, Rng *rng) {
    memcpy(outA, inA, sizeof(Tr) * 6);
    memcpy(outB, inB, sizeof(Tr) * 6);

    for (int i = 0; i < k; i++) {
        Tr (*target)[2] = (rng_double(rng) < 0.5) ? outA : outB;
        int s = rng_int(rng, N);
        int sym = rng_int(rng, 2);
        target[s][sym].ns = rng_int(rng, N);
        target[s][sym].w = rng_int(rng, 2);
        target[s][sym].d = (rng_double(rng) < 0.5) ? -1 : 1;
    }
}

void fmt_table(const Tr t[3][2], char *buf) {
    char *p = buf;
    for (int s = 0; s < 3; s++) {
        if (s > 0) *p++ = '_';
        for (int sym = 0; sym < 2; sym++) {
            *p++ = '0' + t[s][sym].w;
            *p++ = t[s][sym].d > 0 ? 'R' : 'L';
            *p++ = 'A' + t[s][sym].ns;
        }
    }
    *p = 0;
}

int main() {
    printf("Simulated Annealing High-Performance Engine for CET(3)\n");
    int num_threads = omp_get_max_threads();
    printf("Spawning %d OpenMP workers...\n", num_threads);
    fflush(stdout);

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        Rng rng;
        rng.s[0] = 0x12345678ULL ^ (uint64_t)tid * 0x9e3779b97f4a7c15ULL ^ (uint64_t)time(NULL);
        rng.s[1] = 0x87654321ULL ^ (uint64_t)tid * 0xbf58476d1ce4e5b9ULL;

        int8_t *tape = (int8_t *)calloc(TAPE_SIZE, 1);

        Tr cur_tA[3][2], cur_tB[3][2];
        memcpy(cur_tA, CHAMPION_TA, sizeof(cur_tA));
        memcpy(cur_tB, CHAMPION_TB, sizeof(cur_tB));

        long long cur_steps = run_machine_fast(cur_tA, cur_tB, (long long)(CHAMPION_STEPS * 1.5), tape, 1, 5000, 3);
        Tr best_tA[3][2], best_tB[3][2];
        memcpy(best_tA, cur_tA, sizeof(best_tA));
        memcpy(best_tB, cur_tB, sizeof(best_tB));
        long long best_steps = cur_steps;

        #pragma omp critical
        {
            printf("[Worker %d] Started with base steps: %lld\n", tid, cur_steps);
            fflush(stdout);
        }

        for (int iter = 0; iter < ITERATIONS; iter++) {
            long long max_sim = (long long)(best_steps * MAX_SIM_MULT) + MAX_SIM_ADD;
            Tr newA[3][2], newB[3][2];
            mutate(cur_tA, cur_tB, newA, newB, 1, &rng);

            long long new_steps = run_machine_fast(newA, newB, max_sim, tape, 1, 5000, 3);
            if (new_steps < 0) continue; // OOB

            double T = fmax(1.0, best_steps * 0.01 * (1.0 - (double)iter / ITERATIONS));
            double delta = (double)(new_steps - cur_steps);

            if (delta >= 0 || rng_double(&rng) < exp(delta / T)) {
                memcpy(cur_tA, newA, sizeof(newA));
                memcpy(cur_tB, newB, sizeof(newB));
                cur_steps = new_steps;

                if (new_steps > best_steps && new_steps < max_sim) {
                    best_steps = new_steps;
                    memcpy(best_tA, newA, sizeof(newA));
                    memcpy(best_tB, newB, sizeof(newB));

                    char strA[32], strB[32];
                    fmt_table(best_tA, strA);
                    fmt_table(best_tB, strB);

                    #pragma omp critical
                    {
                        printf("★ [Worker %d][iter %d] NEW RECORD: %lld steps | %s|%s\n",
                               tid, iter, best_steps, strA, strB);
                        fflush(stdout);
                        FILE *fp = fopen("anneal_records.txt", "a");
                        if (fp) {
                            fprintf(fp, "%lld | %s|%s\n", best_steps, strA, strB);
                            fclose(fp);
                        }
                    }
                }
            }
        }
        free(tape);
    }

    printf("Annealing search completed.\n");
    return 0;
}
