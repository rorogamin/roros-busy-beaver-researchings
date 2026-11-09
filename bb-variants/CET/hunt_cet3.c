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
    Trans t[3][2]; // [state 0..2][sym 0..1]
} Agent3Table;

typedef struct {
    Agent3Table a1;
    Agent3Table a2;
    int steps;
    int col_pos;
} MachineCandidate;

#define TAPE_SIZE 65536
#define TAPE_OFFSET 32768

// Fast random number generator per thread
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

static inline void mutate_table(Agent3Table* dst, const Agent3Table* src, uint64_t rng[2]) {
    *dst = *src;
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

int simulate3(const Agent3Table* a1, const Agent3Table* a2, int max_steps, uint8_t* tape, int* visited, int* pMarker, int* out_pos) {
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
            return step;
        }

        int dist = abs(pos1 - pos2);
        int rem = max_steps - step;
        if (dist > 2 * rem) {
            return -1; // Cannot catch up
        }

        // Infinite escape prune on blank tape
        if (pos1 < min_mod && pos1 < pos2) {
            Trans tr0 = a1->t[state1][0];
            if (tr0.d == -1 && tr0.ns == state1 && tr0.w == 0) {
                return -1;
            }
        }
        if (pos2 > max_mod && pos2 > pos1) {
            Trans tr0 = a2->t[state2][0];
            if (tr0.d == 1 && tr0.ns == state2 && tr0.w == 0) {
                return -1;
            }
        }

        if (pos1 < 100 || pos1 >= TAPE_SIZE - 100 || pos2 < 100 || pos2 >= TAPE_SIZE - 100) {
            return -1;
        }

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
    return -1;
}

void print_machine(const Agent3Table* a1, const Agent3Table* a2, int steps, int pos) {
    printf("\n=======================================================\n");
    printf("🏆 NEW CET(3) RECORD: %d STEPS (Collision at x=%d)\n", steps, pos);
    printf("=======================================================\n");

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
    printf("\n=======================================================\n\n");
    fflush(stdout);
}

int g_best_steps = 6065;

int main(int argc, char** argv) {
    int max_time_sec = 25; // 25 seconds
    if (argc > 1) max_time_sec = atoi(argv[1]);

    int num_threads = omp_get_max_threads();
    printf("🚀 Launching CET(3) Deep Hunter with %d threads (baseline: 6065 steps)...\n", num_threads);
    fflush(stdout);

    // Baseline 6065 machine
    // Agent 1: (1, LEFT, 2), (1, RIGHT, 1), (1, LEFT, 0), (0, LEFT, 1), (1, RIGHT, 0), (1, RIGHT, 0)
    // Agent 2: (1, RIGHT, 2), (1, LEFT, 0), (1, LEFT, 1), (0, RIGHT, 1), (0, RIGHT, 1), (0, LEFT, 2)
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
    long long total_simulated = 0;

    #pragma omp parallel reduction(+:total_simulated)
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
        if (tid % 2 == 0) {
            current_a1 = seed_a1;
            current_a2 = seed_a2;
            local_best = 6065;
        } else {
            random_table(&current_a1, rng);
            random_table(&current_a2, rng);
            local_best = 0;
        }

        long long count = 0;

        while (omp_get_wtime() - start_time < max_time_sec) {
            count++;

            Agent3Table cand_a1, cand_a2;
            // 85% hill climb / mutate, 15% random restart
            if (local_best > 30 && (xorshift128p(rng) % 100 < 85)) {
                if (xorshift128p(rng) & 1) {
                    mutate_table(&cand_a1, &current_a1, rng);
                    cand_a2 = current_a2;
                } else {
                    cand_a1 = current_a1;
                    mutate_table(&cand_a2, &current_a2, rng);
                }
            } else {
                random_table(&cand_a1, rng);
                random_table(&cand_a2, rng);
            }

            int out_pos = 0;
            int steps = simulate3(&cand_a1, &cand_a2, 100000, tape, visited, &marker, &out_pos);

            if (steps > 0) {
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
                            print_machine(&cand_a1, &cand_a2, steps, out_pos);
                        }
                    }
                }
            }
        }

        free(tape);
        free(visited);
        total_simulated += count;
    }

    double elapsed = omp_get_wtime() - start_time;
    printf("\n🏁 Search completed in %.2f s! Total machines scanned: %lld (%.0f machines/sec)\n",
           elapsed, total_simulated, total_simulated / elapsed);
    printf("Highest CET(3) champion step count found: %d steps!\n", g_best_steps);

    return 0;
}
