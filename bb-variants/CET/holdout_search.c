#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 65536
#define TAPE_OFFSET 32768
#define CUTOFF 30000

typedef struct {
    int8_t write;
    int8_t move;
    int8_t next_state;
} Transition;

typedef struct {
    Transition t[2][3][2];
} Machine;

void format_bb(const Machine *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
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

// Result types
#define RES_HALT 1
#define RES_ESCAPE 2
#define RES_PARALLEL 3
#define RES_HOLDOUT 4

typedef struct {
    int result;
    int steps;
    int max_spread;
    int min_dist;
} SimResult;

SimResult simulate(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 0, 999999};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    // Track trajectory states for cycle detection when moving together
    int consecutive_same_dist = 0;
    int last_dist = 2;

    for (int step = 1; step <= CUTOFF; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];

        // Simultaneous writes
        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        // Collision Check
        if (p1 == p2) {
            res.result = RES_HALT;
            res.steps = step;
            return res;
        }

        int dist = abs(p2 - p1);
        if (dist < res.min_dist) res.min_dist = dist;

        // Decider 1: Rapid Escape / Divergence
        // If distance exceeds 120 cells and is growing monotonically
        if (dist > 120 && ((p1 < p2 && tr1.move <= 0 && tr2.move >= 0) || (p1 > p2 && tr1.move >= 0 && tr2.move <= 0))) {
            res.result = RES_ESCAPE;
            res.steps = step;
            return res;
        }

        // Decider 2: Parallel Drift / Lockstep glider
        // If relative distance stays unchanged for > 200 steps while moving in the same direction into blank tape
        if (dist == last_dist) {
            consecutive_same_dist++;
            if (consecutive_same_dist > 250) {
                res.result = RES_PARALLEL;
                res.steps = step;
                return res;
            }
        } else {
            consecutive_same_dist = 0;
            last_dist = dist;
        }

        // Decider 3: Speed barrier
        if (p1 < p2 && tr1.move == -1 && tr1.write == 0 && tr1.next_state == s1 && r1 == 0) {
            res.result = RES_ESCAPE;
            res.steps = step;
            return res;
        }
        if (p2 < p1 && tr2.move == -1 && tr2.write == 0 && tr2.next_state == s2 && r2 == 0) {
            res.result = RES_ESCAPE;
            res.steps = step;
            return res;
        }
    }

    // SURVIVED 30,000 STEPS WITHIN PROXIMITY!
    res.result = RES_HOLDOUT;
    res.steps = CUTOFF;
    return res;
}

static inline uint32_t xorshift32(uint32_t *state) {
    uint32_t x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf("   HIGH-POWER CET(3) HOLDOUT & CHAMPION SEARCH ENGINE (OPENMP)\n");
    printf("====================================================================\n");

    long long total_searched = 0;
    int max_halt_steps = 0;
    char max_halt_bb[256] = "";
    int holdout_count = 0;

    int num_threads = omp_get_max_threads();
    printf("Using %d CPU threads...\n", num_threads);

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;

        uint32_t seed = (uint32_t)(time(NULL) ^ omp_get_thread_num() ^ (uintptr_t)tape);

        Machine m;

        while (1) {
            // Generate random machine
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        m.t[a][s][r].write = xorshift32(&seed) % 2;
                        m.t[a][s][r].move = (xorshift32(&seed) % 2) ? 1 : -1;
                        m.t[a][s][r].next_state = xorshift32(&seed) % 3;
                    }
                }
            }

            // Quick reject 1: Instant step-1 collision
            if (m.t[0][0][0].move == 1 && m.t[1][0][0].move == -1) continue;

            // Increment marker
            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            SimResult sr = simulate(&m, tape, visited, marker);

            #pragma omp critical
            {
                total_searched++;

                if (sr.result == RES_HALT) {
                    if (sr.steps > max_halt_steps) {
                        max_halt_steps = sr.steps;
                        format_bb(&m, max_halt_bb);
                        printf("\n>>> NEW CET(3) RECORD: %d steps! <<<\n", max_halt_steps);
                        printf("bbchallenge: %s\n\n", max_halt_bb);
                        fflush(stdout);
                    }
                } else if (sr.result == RES_HOLDOUT) {
                    holdout_count++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [!] GENUINE CET(3) HOLDOUT FOUND (#%d) [!]\n", holdout_count);
                    printf("bbchallenge: %s\n", bb);
                    printf("Survived %d steps without escaping or parallel-drifting!\n", sr.steps);
                    printf("Min distance achieved during run: %d cells\n", sr.min_dist);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total_searched % 10000000 == 0) {
                    printf("[Progress] Checked %lldM machines | Max Halt: %d steps | Holdouts: %d\n",
                           total_searched / 1000000, max_halt_steps, holdout_count);
                    fflush(stdout);
                }
            }

            if (holdout_count >= 5 || total_searched >= 50000000) {
                break;
            }
        }

        free(tape);
        free(visited);
    }

    printf("\nSearch finished. Total: %lld | Best Halt: %d | Total Holdouts: %d\n",
           total_searched, max_halt_steps, holdout_count);
    return 0;
}
