#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 4194304
#define TAPE_OFFSET 2097152

typedef struct {
    uint8_t write;
    int8_t move;
    uint8_t next_state;
} Transition;

typedef struct {
    Transition t[3][3][2]; // [agent][state][read]
} Machine3;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void parse_bb(Machine3 *m, const char *bb) {
    const char *p = bb;
    for (int a = 0; a < 3; a++) {
        for (int s = 0; s < 3; s++) {
            for (int r = 0; r < 2; r++) {
                while (*p == '_' || *p == '|') p++;
                m->t[a][s][r].write = *p++ - '0';
                m->t[a][s][r].move = (*p++ == 'R') ? 1 : -1;
                m->t[a][s][r].next_state = *p++ - 'A';
            }
        }
    }
}

void random_machine(Machine3 *m, uint64_t *rng) {
    for (int a = 0; a < 3; a++) {
        for (int s = 0; s < 3; s++) {
            for (int r = 0; r < 2; r++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][r].write = v & 1;
                m->t[a][s][r].move = ((v >> 1) & 1) ? 1 : -1;
                m->t[a][s][r].next_state = (v >> 2) % 3;
            }
        }
    }
}

void mutate(Machine3 *dst, const Machine3 *src, uint64_t *rng, int mutations) {
    *dst = *src;
    for (int i = 0; i < mutations; i++) {
        int a = splitmix64(rng) % 3;
        int s = splitmix64(rng) % 3;
        int r = splitmix64(rng) % 2;
        int pick = splitmix64(rng) % 3;
        if (pick == 0) dst->t[a][s][r].write = splitmix64(rng) & 1;
        else if (pick == 1) dst->t[a][s][r].move = (splitmix64(rng) & 1) ? 1 : -1;
        else dst->t[a][s][r].next_state = splitmix64(rng) % 3;
    }
}

int simulate_mcet3(const Machine3 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int p3 = TAPE_OFFSET + 4;
    int s1 = 0, s2 = 0, s3 = 0;

    for (int step = 1; step <= max_steps; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;
        uint8_t r3 = (visited[p3] == marker) ? tape[p3] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];
        Transition tr3 = m->t[2][s3][r3];

        visited[p3] = marker; tape[p3] = tr3.write;
        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;
        p3 += tr3.move;

        s1 = tr1.next_state;
        s2 = tr2.next_state;
        s3 = tr3.next_state;

        if (p1 == p2 && p2 == p3) {
            *out_pos = p1 - TAPE_OFFSET;
            return step;
        }

        int min_p = p1 < p2 ? (p1 < p3 ? p1 : p3) : (p2 < p3 ? p2 : p3);
        int max_p = p1 > p2 ? (p1 > p3 ? p1 : p3) : (p2 > p3 ? p2 : p3);
        int rem = max_steps - step;
        if ((max_p - min_p) > (2 * rem)) return -1;
    }
    return -2;
}

void format_bbchallenge(const Machine3 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 3; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s > 0) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                Transition tr = m->t[a][s][r];
                *p++ = '0' + tr.write;
                *p++ = tr.move > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.next_state;
            }
        }
    }
    *p = '\0';
}

#define POOL_SIZE 256

int main(int argc, char **argv) {
    int duration = 40;
    if (argc > 1) duration = atoi(argv[1]);

    const char *nath_bb = "1RC0RB_1RC1LB_1LA0LC|0RA0RC_0LC1LA_1LB0RB|1LA0RC_1LB1LA_0LA1RB";
    Machine3 nath_m;
    parse_bb(&nath_m, nath_bb);

    printf("====================================================================\n");
    printf("   DEEP MCET(3) HUNTER: EXPLORING BEYOND NATH76 (12,733 STEPS)\n");
    printf("====================================================================\n");

    int global_max_steps = 12733;
    Machine3 global_best_m = nath_m;
    int global_best_pos = -6363;
    long long total_sims = 0;

    double start_time = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 0xcafebabe12345678ULL ^ ((uint64_t)omp_get_thread_num() * 0x9e3779b97f4a7c15ULL) + (uint64_t)time(NULL);

        Machine3 pool[POOL_SIZE];
        int pool_scores[POOL_SIZE];

        pool[0] = nath_m;
        pool_scores[0] = 12733;
        for (int i = 1; i < POOL_SIZE; i++) {
            if (i < 80) mutate(&pool[i], &nath_m, &rng, 1 + (i % 4));
            else random_machine(&pool[i], &rng);
            marker++;
            int out_pos = 0;
            int s = simulate_mcet3(&pool[i], 15000, tape, visited, marker, &out_pos);
            pool_scores[i] = (s > 0) ? s : 0;
        }

        long long local_sims = POOL_SIZE;

        while (omp_get_wtime() - start_time < duration) {
            int p1 = splitmix64(&rng) % POOL_SIZE;
            int p2 = splitmix64(&rng) % POOL_SIZE;
            int parent_idx = (pool_scores[p1] >= pool_scores[p2]) ? p1 : p2;

            Machine3 cand;
            if (splitmix64(&rng) % 6 == 0) {
                random_machine(&cand, &rng);
            } else {
                int n_mut = (splitmix64(&rng) % 10 == 0) ? 2 : 1;
                mutate(&cand, &pool[parent_idx], &rng, n_mut);
            }
            local_sims++;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int out_pos = 0;
            int s = simulate_mcet3(&cand, 15000, tape, visited, marker, &out_pos);
            if (s > 10000 || s == -2) {
                marker++;
                if (marker == 0) {
                    memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                    marker = 1;
                }
                s = simulate_mcet3(&cand, 5000000, tape, visited, marker, &out_pos);
            }

            if (s > 0) {
                int r = splitmix64(&rng) % POOL_SIZE;
                if (s >= pool_scores[r]) {
                    pool[r] = cand;
                    pool_scores[r] = s;
                }

                if (s > 12733) {
                    #pragma omp critical
                    {
                        if (s > global_max_steps) {
                            global_max_steps = s;
                            global_best_m = cand;
                            global_best_pos = out_pos;
                            char bb[256];
                            format_bbchallenge(&cand, bb);
                            printf(">>> NEW MCET(3) RECORD FOUND: %d steps at cell %d! <<<\n", s, out_pos);
                            printf("bbchallenge: %s\n\n", bb);
                            fflush(stdout);
                        }
                    }
                }
            }
        }

        #pragma omp atomic
        total_sims += local_sims;

        free(tape);
        free(visited);
    }

    double elapsed = omp_get_wtime() - start_time;
    printf("\nFinished hunt! Tested %lld machines in %.2f s (%.1f sims/sec)\n", total_sims, elapsed, total_sims / elapsed);
    char bb[256];
    format_bbchallenge(&global_best_m, bb);
    printf("FINAL MCET(3) RECORD: %d steps (at cell %d)\n", global_max_steps, global_best_pos);
    printf("bbchallenge: %s\n", bb);

    return 0;
}
