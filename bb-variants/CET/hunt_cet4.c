#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

typedef struct {
    uint8_t w;      // write symbol (0 or 1)
    int8_t d;       // direction (-1 for LEFT, +1 for RIGHT)
    uint8_t ns;     // next state (0..3 for CET(4))
} Trans;

typedef struct {
    Trans t[4][2];  // [state 0..3][symbol 0..1]
} Agent4Table;

typedef struct {
    Agent4Table a1;
    Agent4Table a2;
    int steps;
    int col_pos;
} MachineRecord;

#define TAPE_SIZE 262144
#define TAPE_OFFSET 131072

// Fast xorshift128+ PRNG per thread
static inline uint64_t xorshift128p(uint64_t state[2]) {
    uint64_t s1 = state[0];
    const uint64_t s0 = state[1];
    state[0] = s0;
    s1 ^= s1 << 23;
    state[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
    return state[1] + s0;
}

// Generate fully random 4-state table
static inline void random_table(Agent4Table* tbl, uint64_t rng[2]) {
    for (int s = 0; s < 4; s++) {
        for (int sym = 0; sym < 2; sym++) {
            uint64_t r = xorshift128p(rng);
            tbl->t[s][sym].w = r & 1;
            tbl->t[s][sym].d = (r & 2) ? 1 : -1;
            tbl->t[s][sym].ns = (r >> 2) & 3; // 0..3
        }
    }
}

// Mutate table by flipping write, direction, or nextState
static inline void mutate_table(Agent4Table* dst, const Agent4Table* src, uint64_t rng[2], int num_mutations) {
    *dst = *src;
    for (int m = 0; m < num_mutations; m++) {
        uint64_t r = xorshift128p(rng);
        int s = r & 3;
        int sym = (r >> 2) & 1;
        int choice = (r >> 3) % 3;
        if (choice == 0) {
            dst->t[s][sym].w ^= 1;
        } else if (choice == 1) {
            dst->t[s][sym].d = -dst->t[s][sym].d;
        } else {
            dst->t[s][sym].ns = ((r >> 5) % 3 + dst->t[s][sym].ns + 1) & 3;
        }
    }
}

// Crossover two parent tables
static inline void crossover_tables(Agent4Table* dst, const Agent4Table* p1, const Agent4Table* p2, uint64_t rng[2]) {
    uint64_t mask = xorshift128p(rng);
    for (int s = 0; s < 4; s++) {
        for (int sym = 0; sym < 2; sym++) {
            int bit = (s * 2 + sym);
            dst->t[s][sym] = ((mask >> bit) & 1) ? p1->t[s][sym] : p2->t[s][sym];
        }
    }
}

// Fast simulation engine for 4-state 2-agent machines
int simulate4(const Agent4Table* a1, const Agent4Table* a2, int max_steps, uint8_t* tape, int* visited, int* pMarker, int* out_pos, int* out_ones) {
    (*pMarker)++;
    int marker = *pMarker;

    int pos1 = 0 + TAPE_OFFSET;
    int pos2 = 2 + TAPE_OFFSET;
    uint8_t state1 = 0;
    uint8_t state2 = 0;

    int min_mod = TAPE_OFFSET;
    int max_mod = TAPE_OFFSET + 2;

    for (int step = 0; step < max_steps; step++) {
        // Halting condition: collision on same cell
        if (pos1 == pos2) {
            *out_pos = pos1 - TAPE_OFFSET;
            int ones = 0;
            for (int p = min_mod; p <= max_mod; p++) {
                if (visited[p] == marker && tape[p] == 1) ones++;
            }
            *out_ones = ones;
            return step;
        }

        // Catch-up prune: max closing speed is 2 cells/step
        int dist = abs(pos1 - pos2);
        int rem = max_steps - step;
        if (dist > 2 * rem) {
            return -1; // Unreachable
        }

        // Infinite escape prune: running away on blank tape into same state and direction
        if (pos1 < min_mod && pos1 < pos2) {
            Trans tr0 = a1->t[state1][0];
            if (tr0.d == -1 && tr0.ns == state1 && tr0.w == 0) return -1;
        }
        if (pos2 > max_mod && pos2 > pos1) {
            Trans tr0 = a2->t[state2][0];
            if (tr0.d == 1 && tr0.ns == state2 && tr0.w == 0) return -1;
        }

        // Boundary guard
        if (pos1 < 200 || pos1 >= TAPE_SIZE - 200 || pos2 < 200 || pos2 >= TAPE_SIZE - 200) {
            return -1;
        }

        uint8_t sym1 = (visited[pos1] == marker) ? tape[pos1] : 0;
        uint8_t sym2 = (visited[pos2] == marker) ? tape[pos2] : 0;

        Trans tr1 = a1->t[state1][sym1];
        Trans tr2 = a2->t[state2][sym2];

        // Write
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

        // Move & transition
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

void print_record(const Agent4Table* a1, const Agent4Table* a2, int steps, int pos, int ones) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════════════╗\n");
    printf("║  🌟 NEW CET(4) RECORD CANDIDATE: %6d STEPS (Collision x=%5d, %4d ones)   ║\n", steps, pos, ones);
    printf("╚══════════════════════════════════════════════════════════════════════════════╝\n");

    printf("Agent 1: ");
    for (int s = 0; s < 4; s++) {
        for (int sym = 0; sym < 2; sym++) {
            Trans tr = a1->t[s][sym];
            printf("(%d, %s, %d)%s", tr.w, tr.d == 1 ? "RIGHT" : "LEFT", tr.ns,
                   (s == 3 && sym == 1) ? "" : ", ");
        }
    }
    printf("\nAgent 2: ");
    for (int s = 0; s < 4; s++) {
        for (int sym = 0; sym < 2; sym++) {
            Trans tr = a2->t[s][sym];
            printf("(%d, %s, %d)%s", tr.w, tr.d == 1 ? "RIGHT" : "LEFT", tr.ns,
                   (s == 3 && sym == 1) ? "" : ", ");
        }
    }
    printf("\n\n");
    fflush(stdout);
}

int g_best_steps = 6065; // Baseline from CET(3)

int main(int argc, char** argv) {
    int duration_sec = 25;
    int max_sim_steps = 200000;

    if (argc > 1) duration_sec = atoi(argv[1]);
    if (argc > 2) max_sim_steps = atoi(argv[2]);

    int num_threads = omp_get_max_threads();
    printf("========================================================================\n");
    printf("🚀 CET(4) 16-THREAD MASSIVELY PARALLEL BUSY BEAVER HUNTER\n");
    printf("========================================================================\n");
    printf("Threads: %d | Time Limit: %d seconds | Step Ceiling: %d\n", num_threads, duration_sec, max_sim_steps);
    printf("State Space per agent: 16^8 = 4,294,967,296 | Total Pair Space: 2^64 (~1.84e19)\n");
    printf("Initial Baseline: 6,065 steps (embedded from CET(3) champion)\n");
    printf("Searching...\n\n");
    fflush(stdout);

    // Embed CET(3) 6065-step champion into 4-state table (state 3 ready for activation)
    Agent4Table seed_a1 = {
        .t = {
            {{1, -1, 2}, {1, 1, 1}},
            {{1, -1, 0}, {0, -1, 1}},
            {{1, 1, 0},  {1, 1, 0}},
            {{1, -1, 3}, {0, 1, 0}} // State 3 default
        }
    };
    Agent4Table seed_a2 = {
        .t = {
            {{1, 1, 2},  {1, -1, 0}},
            {{1, -1, 1}, {0, 1, 1}},
            {{0, 1, 1},  {0, -1, 2}},
            {{0, 1, 3},  {1, -1, 1}} // State 3 default
        }
    };

    double start_time = omp_get_wtime();
    long long total_simulated = 0;
    int total_records_found = 0;

    #pragma omp parallel reduction(+:total_simulated, total_records_found)
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

        Agent4Table local_seed_a1, local_seed_a2;
        int local_best = 0;

        // Partition search strategy by thread ID:
        if (tid < 8) {
            // Seeded from CET(3) 6,065 baseline with state-3 activation
            local_seed_a1 = seed_a1;
            local_seed_a2 = seed_a2;
            local_best = 6065;
        } else {
            // Independent random evolutionary exploration
            random_table(&local_seed_a1, rng);
            random_table(&local_seed_a2, rng);
            local_best = 0;
        }

        long long count = 0;

        while (omp_get_wtime() - start_time < duration_sec) {
            count++;

            Agent4Table cand_a1, cand_a2;

            if (local_best > 50 && (xorshift128p(rng) % 100 < 88)) {
                // Hill-climbing mutation around best known
                int num_mut = (xorshift128p(rng) % 100 < 70) ? 1 : 2;
                if (xorshift128p(rng) & 1) {
                    mutate_table(&cand_a1, &local_seed_a1, rng, num_mut);
                    cand_a2 = local_seed_a2;
                } else {
                    cand_a1 = local_seed_a1;
                    mutate_table(&cand_a2, &local_seed_a2, rng, num_mut);
                }
            } else {
                // Random restart
                random_table(&cand_a1, rng);
                random_table(&cand_a2, rng);
            }

            int out_pos = 0;
            int out_ones = 0;
            int steps = simulate4(&cand_a1, &cand_a2, max_sim_steps, tape, visited, &marker, &out_pos, &out_ones);

            if (steps > 0) {
                if (steps > local_best) {
                    local_best = steps;
                    local_seed_a1 = cand_a1;
                    local_seed_a2 = cand_a2;
                }

                if (steps > g_best_steps) {
                    #pragma omp critical
                    {
                        if (steps > g_best_steps) {
                            g_best_steps = steps;
                            total_records_found++;
                            print_record(&cand_a1, &cand_a2, steps, out_pos, out_ones);
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
    printf("========================================================================\n");
    printf("🏁 CET(4) SEARCH FINISHED in %.2f seconds!\n", elapsed);
    printf("Total Machines Evaluated: %lld (~%.0f machines/sec)\n", total_simulated, total_simulated / elapsed);
    printf("Top CET(4) Step Count Achieved: %d steps!\n", g_best_steps);
    printf("========================================================================\n");

    return 0;
}
