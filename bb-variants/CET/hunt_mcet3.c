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
} AgentTable3;

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

static inline void random_table(AgentTable3* tbl, uint64_t rng[2]) {
    for (int s = 0; s < 3; s++) {
        for (int sym = 0; sym < 2; sym++) {
            uint64_t r = xorshift128p(rng);
            tbl->t[s][sym].w = r & 1;
            tbl->t[s][sym].d = (r & 2) ? 1 : -1;
            tbl->t[s][sym].ns = (r >> 2) % 3;
        }
    }
}

static inline void mutate_table(AgentTable3* dst, const AgentTable3* src, uint64_t rng[2], int num_mutations) {
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

// Fast simulation engine for MCET(3): 3 agents, 3 states, positions [0, 2, 4]
// With writing priority: Agent 1 > Agent 2 > Agent 3
int simulate_mcet3(const AgentTable3* a1, const AgentTable3* a2, const AgentTable3* a3,
                   int max_steps, uint8_t* tape, int* visited, int* pMarker,
                   int* out_pos, int* out_agents, int* out_ones) {
    (*pMarker)++;
    int marker = *pMarker;

    int p1 = 0 + TAPE_OFFSET;
    int p2 = 2 + TAPE_OFFSET;
    int p3 = 4 + TAPE_OFFSET;

    uint8_t s1 = 0, s2 = 0, s3 = 0;

    int min_mod = TAPE_OFFSET;
    int max_mod = TAPE_OFFSET + 4;

    for (int step = 0; step < max_steps; step++) {
        // Halting condition: pairwise collision
        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            *out_agents = 12; // A1 & A2
            if (out_ones) {
                int ones = 0;
                for (int p = min_mod; p <= max_mod; p++) {
                    if (visited[p] == marker && tape[p] == 1) ones++;
                }
                *out_ones = ones;
            }
            return step;
        }
        if (p2 == p3) {
            *out_pos = p2 - TAPE_OFFSET;
            *out_agents = 23; // A2 & A3
            if (out_ones) {
                int ones = 0;
                for (int p = min_mod; p <= max_mod; p++) {
                    if (visited[p] == marker && tape[p] == 1) ones++;
                }
                *out_ones = ones;
            }
            return step;
        }
        if (p1 == p3) {
            *out_pos = p1 - TAPE_OFFSET;
            *out_agents = 13; // A1 & A3
            if (out_ones) {
                int ones = 0;
                for (int p = min_mod; p <= max_mod; p++) {
                    if (visited[p] == marker && tape[p] == 1) ones++;
                }
                *out_ones = ones;
            }
            return step;
        }

        // Boundary guard
        if (p1 < 200 || p1 >= TAPE_SIZE - 200 ||
            p2 < 200 || p2 >= TAPE_SIZE - 200 ||
            p3 < 200 || p3 >= TAPE_SIZE - 200) {
            return -1;
        }

        // 1. Read
        uint8_t sym1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t sym2 = (visited[p2] == marker) ? tape[p2] : 0;
        uint8_t sym3 = (visited[p3] == marker) ? tape[p3] : 0;

        Trans tr1 = a1->t[s1][sym1];
        Trans tr2 = a2->t[s2][sym2];
        Trans tr3 = a3->t[s3][sym3];

        // 2. Write with Priority: Agent 1 > Agent 2 > Agent 3
        // Apply Agent 3 write first, then Agent 2 (overwrites A3 if p2==p3), then Agent 1 (overwrites A2/A3)
        visited[p3] = marker;
        tape[p3] = tr3.w;

        visited[p2] = marker;
        tape[p2] = tr2.w;

        visited[p1] = marker;
        tape[p1] = tr1.w;

        if (tr1.w != 0 || tr2.w != 0 || tr3.w != 0) {
            if (p1 < min_mod) min_mod = p1;
            if (p2 < min_mod) min_mod = p2;
            if (p3 < min_mod) min_mod = p3;

            if (p1 > max_mod) max_mod = p1;
            if (p2 > max_mod) max_mod = p2;
            if (p3 > max_mod) max_mod = p3;
        }

        // 3. Move & State
        p1 += tr1.d;
        s1 = tr1.ns;

        p2 += tr2.d;
        s2 = tr2.ns;

        p3 += tr3.d;
        s3 = tr3.ns;
    }

    // Check collision at max step
    if (p1 == p2 || p2 == p3 || p1 == p3) {
        *out_pos = (p1 == p2 || p1 == p3) ? (p1 - TAPE_OFFSET) : (p2 - TAPE_OFFSET);
        *out_agents = (p1 == p2) ? 12 : ((p2 == p3) ? 23 : 13);
        return max_steps;
    }

    return -2; // Still running
}

void print_mcet3_champion(const AgentTable3* a1, const AgentTable3* a2, const AgentTable3* a3,
                          int steps, int pos, int agents, int ones) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════════════╗\n");
    printf("║  🌟 NEW MCET(3) RECORD CHAMPION: %7d STEPS (Col x=%5d, Ag=%d, %4d 1s)║\n", steps, pos, agents, ones);
    printf("╚══════════════════════════════════════════════════════════════════════════════╝\n");

    printf("bbchallenge 3-agent format: ");
    for (int a = 0; a < 3; a++) {
        const AgentTable3* tbl = (a == 0) ? a1 : ((a == 1) ? a2 : a3);
        for (int s = 0; s < 3; s++) {
            for (int sym = 0; sym < 2; sym++) {
                Trans tr = tbl->t[s][sym];
                printf("%d%c%c", tr.w, tr.d == 1 ? 'R' : 'L', (char)('A' + tr.ns));
            }
            if (s < 2) printf("_");
        }
        if (a < 2) printf("|");
    }
    printf("\n");

    for (int a = 0; a < 3; a++) {
        const AgentTable3* tbl = (a == 0) ? a1 : ((a == 1) ? a2 : a3);
        printf("Agent %d: ", a + 1);
        for (int s = 0; s < 3; s++) {
            for (int sym = 0; sym < 2; sym++) {
                Trans tr = tbl->t[s][sym];
                printf("(%d, %s, %d)%s", tr.w, tr.d == 1 ? "RIGHT" : "LEFT", tr.ns,
                       (s == 2 && sym == 1) ? "" : ", ");
            }
        }
        printf("\n");
    }
    printf("\n");
    fflush(stdout);
}

int g_best_mcet3 = 36; // Baseline from initial preset

int main(int argc, char** argv) {
    int duration_sec = 35;
    if (argc > 1) duration_sec = atoi(argv[1]);

    int num_threads = omp_get_max_threads();
    printf("========================================================================\n");
    printf("🚀 MCET(3) MULTI-AGENT BUSY BEAVER HUNTER (16 Threads)\n");
    printf("========================================================================\n");
    printf("3 Agents (positions [0, 2, 4]) | 3 States | Priority: A1 > A2 > A3\n");
    printf("Threads: %d | Time Limit: %d seconds\n", num_threads, duration_sec);
    printf("Searching...\n\n");
    fflush(stdout);

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

        AgentTable3 curr_a1, curr_a2, curr_a3;
        random_table(&curr_a1, rng);
        random_table(&curr_a2, rng);
        random_table(&curr_a3, rng);
        int local_best = 0;

        long long count = 0;

        while (omp_get_wtime() - start_time < duration_sec) {
            count++;

            AgentTable3 cand_a1, cand_a2, cand_a3;

            if (local_best > 20 && (xorshift128p(rng) % 100 < 88)) {
                cand_a1 = curr_a1;
                cand_a2 = curr_a2;
                cand_a3 = curr_a3;

                int ag_choice = (xorshift128p(rng) >> 2) % 3;
                int num_mut = (xorshift128p(rng) % 100 < 75) ? 1 : 2;

                if (ag_choice == 0) mutate_table(&cand_a1, &curr_a1, rng, num_mut);
                else if (ag_choice == 1) mutate_table(&cand_a2, &curr_a2, rng, num_mut);
                else mutate_table(&cand_a3, &curr_a3, rng, num_mut);
            } else {
                random_table(&cand_a1, rng);
                random_table(&cand_a2, rng);
                random_table(&cand_a3, rng);
            }

            int out_pos = 0, out_agents = 0;
            // Stage 1 filter: 10,000 steps
            int steps = simulate_mcet3(&cand_a1, &cand_a2, &cand_a3, 10000, tape, visited, &marker, &out_pos, &out_agents, NULL);

            if (steps == -2) {
                // Survived 10k steps! Stage 2: Deep check up to 1,000,000 steps
                int out_ones = 0;
                int deep_steps = simulate_mcet3(&cand_a1, &cand_a2, &cand_a3, 1000000, tape, visited, &marker, &out_pos, &out_agents, &out_ones);

                if (deep_steps > 0) {
                    if (deep_steps > local_best) {
                        local_best = deep_steps;
                        curr_a1 = cand_a1;
                        curr_a2 = cand_a2;
                        curr_a3 = cand_a3;
                    }

                    if (deep_steps > g_best_mcet3) {
                        #pragma omp critical
                        {
                            if (deep_steps > g_best_mcet3) {
                                g_best_mcet3 = deep_steps;
                                print_mcet3_champion(&cand_a1, &cand_a2, &cand_a3, deep_steps, out_pos, out_agents, out_ones);
                            }
                        }
                    }
                }
            } else if (steps > 0) {
                if (steps > local_best) {
                    local_best = steps;
                    curr_a1 = cand_a1;
                    curr_a2 = cand_a2;
                    curr_a3 = cand_a3;
                }

                if (steps > g_best_mcet3) {
                    #pragma omp critical
                    {
                        if (steps > g_best_mcet3) {
                            g_best_mcet3 = steps;
                            print_mcet3_champion(&cand_a1, &cand_a2, &cand_a3, steps, out_pos, out_agents, 0);
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
    printf("🏁 MCET(3) Search finished in %.2f s! Total machines scanned: %lld (~%.0f/sec)\n",
           elapsed, total_simulated, total_simulated / elapsed);
    printf("Highest MCET(3) Step Count: %d steps!\n", g_best_mcet3);
    printf("========================================================================\n");

    return 0;
}
