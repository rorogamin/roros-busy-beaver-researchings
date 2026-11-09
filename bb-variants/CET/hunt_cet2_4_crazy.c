#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 8388608
#define TAPE_OFFSET 4194304

typedef struct {
    uint8_t write;
    int8_t move;
    uint8_t next_state;
} Transition;

typedef struct {
    Transition t[2][2][4]; // [agent][state][symbol]
} Machine2_4;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

// Generate a structural counter architecture:
// Agent 1 is a sweep writer / multiplier, Agent 2 is a decremeter / bounded bouncer
void generate_structured_machine(Machine2_4 *m, uint64_t *rng) {
    // Fill with random valid transitions
    for (int a = 0; a < 2; a++) {
        for (int s = 0; s < 2; s++) {
            for (int sym = 0; sym < 4; sym++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][sym].write = v & 3;
                m->t[a][s][sym].move = ((v >> 2) & 1) ? 1 : -1;
                m->t[a][s][sym].next_state = (v >> 3) & 1;
            }
        }
    }

    // Bias initial reads to move away or interact productively
    // Agent 1 at 0 reads 0 -> write non-zero, move left or right
    m->t[0][0][0].write = 1 + (splitmix64(rng) % 3); // write 1, 2, or 3
    // Agent 2 at 2 reads 0 -> write non-zero
    m->t[1][0][0].write = 1 + (splitmix64(rng) % 3);
}

void mutate_machine(Machine2_4 *dst, const Machine2_4 *src, uint64_t *rng, int mutations) {
    *dst = *src;
    for (int i = 0; i < mutations; i++) {
        int a = splitmix64(rng) % 2;
        int s = splitmix64(rng) % 2;
        int sym = splitmix64(rng) % 4;
        int pick = splitmix64(rng) % 3;
        if (pick == 0) dst->t[a][s][sym].write = splitmix64(rng) % 4;
        else if (pick == 1) dst->t[a][s][sym].move = (splitmix64(rng) & 1) ? 1 : -1;
        else dst->t[a][s][sym].next_state = splitmix64(rng) % 2;
    }
}

// Multi-stage evaluation:
// Returns step count if halts; -1 if provably escaped; -2 if timed out
int simulate_cet2_4(const Machine2_4 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos, int *max_span) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;
    int min_seen = p1, max_seen = p2;

    for (int step = 1; step <= max_steps; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];

        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        if (p1 < min_seen) min_seen = p1;
        if (p2 > max_seen) max_seen = p2;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            *max_span = max_seen - min_seen + 1;
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        int rem = max_steps - step;
        if (dist > 2 * rem) {
            *max_span = max_seen - min_seen + 1;
            return -1; // provably impossible to collide within max_steps
        }
    }
    *max_span = max_seen - min_seen + 1;
    return -2;
}

void format_bb_4sym(const Machine2_4 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 2; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 4; sym++) {
                Transition tr = m->t[a][s][sym];
                *p++ = '0' + tr.write;
                *p++ = tr.move > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.next_state;
            }
        }
    }
    *p = '\0';
}

#define ELITE_COUNT 256

int main(int argc, char **argv) {
    int duration = 30;
    if (argc > 1) duration = atoi(argv[1]);

    printf("====================================================================\n");
    printf("   CET(2,4) CRAZY SEARCH: MULTI-STAGE GENETIC & STRUCTURED EXPLORER\n");
    printf("====================================================================\n");
    printf("Searching for high-step champions (filter -> 20k -> 200k -> 5,000,000 steps)...\n\n");

    int global_max_steps = 9332;
    Machine2_4 global_best_m;
    int global_best_pos = 0;
    int global_best_span = 0;
    long long total_sims = 0;

    double start_time = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 0xdeadbeefcafebabeULL ^ ((uint64_t)omp_get_thread_num() * 0x7153a7b127a295ULL) + (uint64_t)time(NULL);

        Machine2_4 elite[ELITE_COUNT];
        int elite_scores[ELITE_COUNT];

        // Seed elites
        for (int i = 0; i < ELITE_COUNT; i++) {
            generate_structured_machine(&elite[i], &rng);
            marker++;
            int out_pos = 0, span = 0;
            int s = simulate_cet2_4(&elite[i], 10000, tape, visited, marker, &out_pos, &span);
            elite_scores[i] = (s > 0) ? s : 0;
        }

        long long local_sims = ELITE_COUNT;

        while (omp_get_wtime() - start_time < duration) {
            Machine2_4 cand;
            int parent_idx = splitmix64(&rng) % ELITE_COUNT;
            int p2_idx = splitmix64(&rng) % ELITE_COUNT;
            if (elite_scores[p2_idx] > elite_scores[parent_idx]) parent_idx = p2_idx;

            if (splitmix64(&rng) % 5 == 0) {
                generate_structured_machine(&cand, &rng);
            } else {
                int n_mut = (splitmix64(&rng) % 8 == 0) ? 2 : 1;
                mutate_machine(&cand, &elite[parent_idx], &rng, n_mut);
            }
            local_sims++;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int out_pos = 0, span = 0;
            // Stage 1: 15,000 steps
            int s = simulate_cet2_4(&cand, 15000, tape, visited, marker, &out_pos, &span);

            // Stage 2: If it runs to 15,000 or halted > 5,000, run deep up to 5,000,000 steps!
            if (s > 5000 || s == -2) {
                marker++;
                if (marker == 0) {
                    memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                    marker = 1;
                }
                s = simulate_cet2_4(&cand, 5000000, tape, visited, marker, &out_pos, &span);
            }

            if (s > 0) {
                int r = splitmix64(&rng) % ELITE_COUNT;
                if (s >= elite_scores[r]) {
                    elite[r] = cand;
                    elite_scores[r] = s;
                }

                if (s > 1000) {
                    #pragma omp critical
                    {
                        if (s > global_max_steps) {
                            global_max_steps = s;
                            global_best_m = cand;
                            global_best_pos = out_pos;
                            global_best_span = span;
                            char bb[256];
                            format_bb_4sym(&cand, bb);
                            printf(">>> NEW RECORD: %d steps | Tape Span: %d | Collision cell: %d <<<\n", s, span, out_pos);
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
    printf("\nFinished Crazy Search! Evaluated %lld machines in %.2f s (%.1f machines/sec)\n", total_sims, elapsed, total_sims / elapsed);
    if (global_max_steps > 9332) {
        char bb[256];
        format_bb_4sym(&global_best_m, bb);
        printf("\n====================================================================\n");
        printf("   CRAZY SEARCH CET(2,4) CHAMPION DISCOVERY: %d STEPS\n", global_max_steps);
        printf("====================================================================\n");
        printf("Collision at cell: %d | Active tape span: %d\n", global_best_pos, global_best_span);
        printf("bbchallenge: %s\n", bb);
    } else {
        printf("Previous 9,332 record stood firm during this pass.\n");
    }

    return 0;
}
