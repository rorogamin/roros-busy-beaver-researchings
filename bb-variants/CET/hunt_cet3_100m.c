#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

typedef struct {
    uint8_t w;
    int8_t d;
    uint8_t ns;
} Trans;

typedef struct {
    Trans t[3][2];
} Agent3Table;

#define TAPE_SIZE 262144
#define TAPE_OFFSET 131072

static inline uint64_t xorshift128p(uint64_t state[2]) {
    uint64_t s1 = state[0];
    const uint64_t s0 = state[1];
    state[0] = s0;
    s1 ^= s1 << 23;
    state[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
    return state[1] + s0;
}

static inline void random_table(Agent3Table* tbl, uint64_t rng[2]) {
    for (int s = 0; s < 3; s++) {
        for (int sym = 0; sym < 2; sym++) {
            uint64_t r = xorshift128p(rng);
            tbl->t[s][sym].w = r & 1;
            tbl->t[s][sym].d = (r & 2) ? 1 : -1;
            tbl->t[s][sym].ns = (r >> 2) % 3;
        }
    }
}

static inline void mutate_table(Agent3Table* dst, const Agent3Table* src, uint64_t rng[2], int num_mutations) {
    *dst = *src;
    for (int m = 0; m < num_mutations; m++) {
        uint64_t r = xorshift128p(rng);
        int s = r % 3;
        int sym = (r >> 2) & 1;
        int choice = (r >> 3) % 3;
        if (choice == 0) {
            dst->t[s][sym].w ^= 1;
        } else if (choice == 1) {
            dst->t[s][sym].d = -dst->t[s][sym].d;
        } else {
            dst->t[s][sym].ns = ((r >> 5) % 2 + dst->t[s][sym].ns + 1) % 3;
        }
    }
}

static inline void crossover_tables(Agent3Table* dst, const Agent3Table* p1, const Agent3Table* p2, uint64_t rng[2]) {
    uint64_t r = xorshift128p(rng);
    for (int s = 0; s < 3; s++) {
        for (int sym = 0; sym < 2; sym++) {
            dst->t[s][sym] = ((r >> (s * 2 + sym)) & 1) ? p1->t[s][sym] : p2->t[s][sym];
        }
    }
}

int simulate3_fast(const Agent3Table* a1, const Agent3Table* a2, int max_steps, uint8_t* tape, int* visited, int* pMarker, int* out_pos, int* out_ones) {
    (*pMarker)++;
    int marker = *pMarker;

    int pos1 = 0 + TAPE_OFFSET;
    int pos2 = 2 + TAPE_OFFSET;
    uint8_t state1 = 0;
    uint8_t state2 = 0;

    int min_mod = TAPE_OFFSET;
    int max_mod = TAPE_OFFSET + 2;

    for (int step = 0; step < max_steps; step++) {
        if (pos1 == pos2) {
            *out_pos = pos1 - TAPE_OFFSET;
            if (out_ones) {
                int ones = 0;
                for (int p = min_mod; p <= max_mod; p++) {
                    if (visited[p] == marker && tape[p] == 1) ones++;
                }
                *out_ones = ones;
            }
            return step;
        }

        int dist = abs(pos1 - pos2);
        int rem = max_steps - step;
        if (dist > 2 * rem) return -1;

        if (pos1 < min_mod && pos1 < pos2) {
            Trans tr0 = a1->t[state1][0];
            if (tr0.d == -1 && tr0.ns == state1 && tr0.w == 0) return -1;
        }
        if (pos2 > max_mod && pos2 > pos1) {
            Trans tr0 = a2->t[state2][0];
            if (tr0.d == 1 && tr0.ns == state2 && tr0.w == 0) return -1;
        }

        if (pos1 < 200 || pos1 >= TAPE_SIZE - 200 || pos2 < 200 || pos2 >= TAPE_SIZE - 200) return -1;

        uint8_t sym1 = (visited[pos1] == marker) ? tape[pos1] : 0;
        uint8_t sym2 = (visited[pos2] == marker) ? tape[pos2] : 0;

        Trans tr1 = a1->t[state1][sym1];
        Trans tr2 = a2->t[state2][sym2];

        visited[pos1] = marker;
        tape[pos1] = tr1.w;
        if (tr1.w != 0) {
            if (pos1 < min_mod) min_mod = pos1;
            if (pos1 > max_mod) max_mod = pos1;
        }

        visited[pos2] = marker;
        tape[pos2] = tr2.w;
        if (tr2.w != 0) {
            if (pos2 < min_mod) min_mod = pos2;
            if (pos2 > max_mod) max_mod = pos2;
        }

        pos1 += tr1.d;
        state1 = tr1.ns;

        pos2 += tr2.d;
        state2 = tr2.ns;
    }

    if (pos1 == pos2) {
        *out_pos = pos1 - TAPE_OFFSET;
        return max_steps;
    }
    return -2;
}

void print_champion(const Agent3Table* a1, const Agent3Table* a2, int steps, int pos, int ones) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════════════╗\n");
    printf("║  🌟 NEW CET(3) RECORD CHAMPION: %7d STEPS (Collision x=%6d, %5d 1s)  ║\n", steps, pos, ones);
    printf("╚══════════════════════════════════════════════════════════════════════════════╝\n");

    printf("bbchallenge format: ");
    for (int a = 0; a < 2; a++) {
        const Agent3Table* tbl = (a == 0) ? a1 : a2;
        for (int s = 0; s < 3; s++) {
            for (int sym = 0; sym < 2; sym++) {
                Trans tr = tbl->t[s][sym];
                printf("%d%c%c", tr.w, tr.d == 1 ? 'R' : 'L', (char)('A' + tr.ns));
            }
            if (s < 2) printf("_");
        }
        if (a == 0) printf("|");
    }
    printf("\n");

    printf("Agent 1: ");
    for (int s = 0; s < 3; s++) {
        for (int sym = 0; sym < 2; sym++) {
            Trans tr = a1->t[s][sym];
            printf("(%d, %s, %d)%s", tr.w, tr.d == 1 ? "RIGHT" : "LEFT", tr.ns,
                   (s == 2 && sym == 1) ? "" : ", ");
        }
    }
    printf("\nAgent 2: ");
    for (int s = 0; s < 3; s++) {
        for (int sym = 0; sym < 2; sym++) {
            Trans tr = a2->t[s][sym];
            printf("(%d, %s, %d)%s", tr.w, tr.d == 1 ? "RIGHT" : "LEFT", tr.ns,
                   (s == 2 && sym == 1) ? "" : ", ");
        }
    }
    printf("\n\n");
    fflush(stdout);
}

int g_best_steps = 6065;
long long g_total_machines = 0;

int main(int argc, char** argv) {
    long long target_machines = 100000000LL; // 100 Million machines!
    if (argc > 1) target_machines = atoll(argv[1]);

    int num_threads = omp_get_max_threads();
    printf("========================================================================\n");
    printf("🚀 CET(3) 100,000,000 MACHINE GRAND SEARCH (16 Threads)\n");
    printf("========================================================================\n");
    printf("Threads: %d | Target: %lld machines | Baseline: 6,065 steps\n", num_threads, target_machines);
    printf("Searching across 100M distinct configurations...\n\n");
    fflush(stdout);

    Agent3Table seed_a1 = {
        .t = {
            {{1, -1, 2}, {1, 1, 1}},
            {{1, -1, 0}, {0, -1, 1}},
            {{1, 1, 0},  {1, 1, 0}}
        }
    };
    Agent3Table seed_a2 = {
        .t = {
            {{1, 1, 2},  {1, -1, 0}},
            {{1, -1, 1}, {0, 1, 1}},
            {{0, 1, 1},  {0, -1, 2}}
        }
    };

    double start_time = omp_get_wtime();
    int running = 1;

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        uint64_t rng[2] = {
            (uint64_t)time(NULL) ^ ((uint64_t)tid * 0x9e3779b97f4a7c15ULL),
            0xd1b54a32d192ed03ULL ^ ((uint64_t)tid * 0x517cc1b727220a95ULL)
        };

        uint8_t* tape = (uint8_t*)malloc(TAPE_SIZE);
        int* visited = (int*)malloc(TAPE_SIZE * sizeof(int));
        memset(visited, 0, TAPE_SIZE * sizeof(int));
        int marker = 0;

        Agent3Table current_a1, current_a2;
        int local_best = 0;

        // Diversified thread portfolios:
        // Threads 0-3: Mutate around 6065 seed with variable mutation rates
        // Threads 4-7: Crossover and structural perturbations
        // Threads 8-15: Pure random evolutionary islands
        if (tid < 4) {
            current_a1 = seed_a1;
            current_a2 = seed_a2;
            local_best = 6065;
        } else if (tid < 8) {
            mutate_table(&current_a1, &seed_a1, rng, 2 + (tid % 3));
            mutate_table(&current_a2, &seed_a2, rng, 2 + (tid % 3));
            local_best = 0;
        } else {
            random_table(&current_a1, rng);
            random_table(&current_a2, rng);
            local_best = 0;
        }

        long long local_count = 0;

        while (running) {
            local_count++;

            Agent3Table cand_a1, cand_a2;

            if (local_best > 30 && (xorshift128p(rng) % 100 < 86)) {
                int num_mut = (xorshift128p(rng) % 100 < 70) ? 1 : 2;
                if (xorshift128p(rng) & 1) {
                    mutate_table(&cand_a1, &current_a1, rng, num_mut);
                    cand_a2 = current_a2;
                } else {
                    cand_a1 = current_a1;
                    mutate_table(&cand_a2, &current_a2, rng, num_mut);
                }
            } else {
                random_table(&cand_a1, rng);
                random_table(&cand_a2, rng);
            }

            int out_pos = 0;
            // Stage 1: Fast filter 7,000 steps
            int steps = simulate3_fast(&cand_a1, &cand_a2, 7000, tape, visited, &marker, &out_pos, NULL);

            if (steps == -2) {
                // Stage 2: Deep check up to 1,000,000 steps
                int out_ones = 0;
                int deep_steps = simulate3_fast(&cand_a1, &cand_a2, 1000000, tape, visited, &marker, &out_pos, &out_ones);

                if (deep_steps > 0) {
                    if (deep_steps > local_best) {
                        local_best = deep_steps;
                        current_a1 = cand_a1;
                        current_a2 = cand_a2;
                    }

                    if (deep_steps > g_best_steps) {
                        #pragma omp critical
                        {
                            if (deep_steps > g_best_steps) {
                                g_best_steps = deep_steps;
                                print_champion(&cand_a1, &cand_a2, deep_steps, out_pos, out_ones);
                            }
                        }
                    }
                }
            } else if (steps > 0) {
                if (steps > local_best) {
                    local_best = steps;
                    current_a1 = cand_a1;
                    current_a2 = cand_a2;
                }
                if (steps > g_best_steps) {
                    #pragma omp critical
                    {
                        if (steps > g_best_steps) {
                            g_best_steps = steps;
                            print_champion(&cand_a1, &cand_a2, steps, out_pos, 0);
                        }
                    }
                }
            }

            // Periodic progress reporting every 10M machines
            if ((local_count & 0x1FFFF) == 0) {
                #pragma omp atomic
                g_total_machines += 0x20000;

                if (tid == 0) {
                    long long curr_total = g_total_machines;
                    double curr_elapsed = omp_get_wtime() - start_time;
                    double rate = curr_total / curr_elapsed;
                    printf("Progress: %5.1fM / %lldM machines (%.0f machines/sec) | Best: %d steps\n",
                           curr_total / 1000000.0, target_machines / 1000000LL, rate, g_best_steps);
                    fflush(stdout);

                    if (curr_total >= target_machines) {
                        running = 0;
                    }
                }
            }
        }

        free(tape);
        free(visited);
    }

    double elapsed = omp_get_wtime() - start_time;
    printf("\n========================================================================\n");
    printf("🏁 100,000,000 MACHINE GRAND SEARCH FINISHED in %.2f s (%.2f min)!\n", elapsed, elapsed / 60.0);
    printf("Total Scanned: %lld machines (~%.0f machines/sec)\n", g_total_machines, g_total_machines / elapsed);
    printf("Final Highest CET(3) Step Count: %d steps!\n", g_best_steps);
    printf("========================================================================\n");

    return 0;
}
