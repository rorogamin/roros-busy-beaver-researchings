#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define POP_SIZE 64

typedef struct {
    uint8_t write; // 0, 1, 2
    int8_t move;   // -1 or +1
    uint8_t next_state; // 0 or 1
} Transition;

typedef struct {
    Transition t[2][2][3]; // [agent][state][symbol]
} Machine2_3;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void format_bb_3sym(const Machine2_3 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 2; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 3; sym++) {
                Transition tr = m->t[a][s][sym];
                *p++ = '0' + tr.write;
                *p++ = tr.move > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.next_state;
            }
        }
    }
    *p = '\0';
}

static Machine2_3 parse_bb_3sym(const char *s) {
    Machine2_3 m;
    const char *p = s;
    for (int a = 0; a < 2; a++) {
        for (int st = 0; st < 2; st++) {
            for (int sym = 0; sym < 3; sym++) {
                m.t[a][st][sym].write = p[0] - '0';
                m.t[a][st][sym].move = (p[1] == 'R') ? 1 : -1;
                m.t[a][st][sym].next_state = p[2] - 'A';
                p += 3;
            }
            if (*p == '_' || *p == '|') p++;
        }
    }
    return m;
}

// Unrestricted simulation up to 10,000,000 steps with wide distance tolerance
int simulate_cet2_3(const Machine2_3 *m, int max_steps, uint8_t *tape, uint32_t *vis, uint32_t mk, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= max_steps; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = tr2.write;
        vis[p1] = mk; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        int rem = max_steps - step;
        if (dist > 2 * rem || dist > 3500) return -1;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 60;
    if (argc > 1) duration = atoi(argv[1]);

    const char *seed_bb = "2LB1LA2LA_2RB0LA0LB|1RB0LB1LB_2LA2LA1RA";
    Machine2_3 seed = parse_bb_3sym(seed_bb);

    printf("========================================================================\n");
    printf("🌈 CET(2,3) HYBRID GENETIC & WIDE-SEARCH HUNTER (%d s)\n", duration);
    printf("========================================================================\n");
    printf("Seed: 8,786 step champion (%s)\n", seed_bb);
    printf("Threads: %d | Goal: Smashes 8,786 steps into tens of thousands!\n", omp_get_max_threads());
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long total_tested = 0;
    int global_best = 8786;
    int global_best_pos = -192;
    char global_best_bb[256];
    strcpy(global_best_bb, seed_bb);

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint64_t rng = (uint64_t)time(NULL) * 2654435761ULL ^ ((uint64_t)omp_get_thread_num() + 1) * 40503ULL;

        Machine2_3 cand;
        long long local_count = 0;

        while (omp_get_wtime() - t0 < duration) {
            uint64_t r = splitmix64(&rng);
            if ((r % 100) < 60) {
                // Mutate around best
                cand = seed;
                int nmut = 1 + (r % 2);
                for (int i = 0; i < nmut; i++) {
                    uint64_t v = splitmix64(&rng);
                    int a = v % 2;
                    int s = (v >> 1) % 2;
                    int sym = (v >> 2) % 3;
                    int type = (v >> 4) % 3;
                    if (type == 0) cand.t[a][s][sym].write = (v >> 6) % 3;
                    else if (type == 1) cand.t[a][s][sym].move = ((v >> 8) & 1) ? 1 : -1;
                    else cand.t[a][s][sym].next_state = ((v >> 9) & 1);
                }
            } else {
                // Fresh random
                for (int a = 0; a < 2; a++) {
                    for (int s = 0; s < 2; s++) {
                        for (int sym = 0; sym < 3; sym++) {
                            uint64_t v = splitmix64(&rng);
                            cand.t[a][s][sym].write = v % 3;
                            cand.t[a][s][sym].move = ((v >> 4) & 1) ? 1 : -1;
                            cand.t[a][s][sym].next_state = (v >> 5) % 2;
                        }
                    }
                }
            }
            local_count++;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            // Quick 25,000 steps
            int s = simulate_cet2_3(&cand, 25000, tape, vis, mk, &pos);
            if (s > 8786 || s == -2) {
                // Deep 2,000,000 steps
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = simulate_cet2_3(&cand, 2000000, tape, vis, mk, &pos);
                if (s > global_best) {
                    #pragma omp critical
                    {
                        if (s > global_best) {
                            global_best = s;
                            global_best_pos = pos;
                            seed = cand; // update seed to new champion!
                            format_bb_3sym(&cand, global_best_bb);
                            printf("\n🌟🌟🌟 >>> NEW CET(2,3) WORLD RECORD: %d STEPS at cell %d! <<< 🌟🌟🌟\n", s, pos);
                            printf("bbchallenge: %s\n", global_best_bb);
                            fflush(stdout);
                        }
                    }
                }
            }
        }

        #pragma omp atomic
        total_tested += local_count;

        free(tape); free(vis);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 Tested %lld machines in %.1fs (%.0f machines/sec)\n", total_tested, elapsed, total_tested / elapsed);
    printf("Final Best CET(2,3): %d steps | %s\n", global_best, global_best_bb);
    printf("========================================================================\n");

    return 0;
}
