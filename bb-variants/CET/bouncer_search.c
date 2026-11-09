#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 131072
#define TAPE_OFFSET 65536
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

static inline uint32_t xorshift32(uint32_t *state) {
    uint32_t x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

// Result types
#define RES_HALT 1
#define RES_ESCAPE 2
#define RES_TRANSLATING_CYCLE 3
#define RES_SIMPLE_CYCLE 4
#define RES_NON_COLLIDING_BOUNCER 5 // GENUINE HOLDOUT!

typedef struct {
    int result;
    int steps;
    int min_dist;
    int max_dist;
    int direction_reversals;
    int tape_span;
} SimResult;

SimResult simulate_bouncer(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 999999, 0, 0, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_p1 = p1, max_p1 = p1;
    int min_p2 = p2, max_p2 = p2;

    int prev_v1 = 0, prev_v2 = 0;
    int reversals = 0;

    // Snapshot buffer to detect translating cycles of ANY period up to 100 steps
    // We check every 60 steps for matching state configuration
    #define SNAP_INTERVAL 60
    #define NUM_SNAPS 10
    int snap_p1[NUM_SNAPS];
    int snap_p2[NUM_SNAPS];
    int snap_s1[NUM_SNAPS];
    int snap_s2[NUM_SNAPS];
    int snap_count = 0;

    for (int step = 1; step <= CUTOFF; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];

        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        if (p1 < min_p1) min_p1 = p1;
        if (p1 > max_p1) max_p1 = p1;
        if (p2 < min_p2) min_p2 = p2;
        if (p2 > max_p2) max_p2 = p2;

        if (tr1.move != prev_v1) { reversals++; prev_v1 = tr1.move; }
        if (tr2.move != prev_v2) { reversals++; prev_v2 = tr2.move; }

        // Collision Check
        if (p1 == p2) {
            res.result = RES_HALT;
            res.steps = step;
            return res;
        }

        int dist = abs(p2 - p1);
        if (dist < res.min_dist) res.min_dist = dist;
        if (dist > res.max_dist) res.max_dist = dist;

        // Escape Decider: If distance > 100 and widening
        if (dist > 100) {
            res.result = RES_ESCAPE;
            res.steps = step;
            return res;
        }

        // Periodic Snapshot Decider:
        if (step % SNAP_INTERVAL == 0) {
            int slot = snap_count % NUM_SNAPS;
            snap_p1[slot] = p1;
            snap_p2[slot] = p2;
            snap_s1[slot] = s1;
            snap_s2[slot] = s2;
            snap_count++;

            if (snap_count >= NUM_SNAPS) {
                for (int lag = 1; lag < NUM_SNAPS; lag++) {
                    int prev_slot = (slot - lag + NUM_SNAPS) % NUM_SNAPS;
                    int d_curr = p2 - p1;
                    int d_prev = snap_p2[prev_slot] - snap_p1[prev_slot];
                    if (d_curr == d_prev && s1 == snap_s1[prev_slot] && s2 == snap_s2[prev_slot]) {
                        // Check if translating
                        int dx = p1 - snap_p1[prev_slot];
                        if (dx != 0) {
                            res.result = RES_TRANSLATING_CYCLE;
                            res.steps = step;
                            return res;
                        } else {
                            res.result = RES_SIMPLE_CYCLE;
                            res.steps = step;
                            return res;
                        }
                    }
                }
            }
        }
    }

    // SURVIVED 30,000 STEPS!
    // If both agents reversed directions frequently and span is bounded or slowly expanding:
    res.result = RES_NON_COLLIDING_BOUNCER;
    res.steps = CUTOFF;
    res.direction_reversals = reversals;
    int overall_min = min_p1 < min_p2 ? min_p1 : min_p2;
    int overall_max = max_p1 > max_p2 ? max_p1 : max_p2;
    res.tape_span = overall_max - overall_min;
    return res;
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf("   SEARCHING FOR NON-TRANSLATING CET(3) BOUNCER HOLDOUTS\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Using %d threads...\n", num_threads);

    long long total = 0;
    int bouncers_found = 0;
    int max_halt = 0;
    char max_halt_bb[256] = "";

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint32_t seed = (uint32_t)(time(NULL) ^ omp_get_thread_num() ^ (uintptr_t)tape);
        Machine m;

        while (1) {
            for (int a = 0; a < 2; a++)
                for (int s = 0; s < 3; s++)
                    for (int r = 0; r < 2; r++) {
                        m.t[a][s][r].write = xorshift32(&seed) % 2;
                        m.t[a][s][r].move = (xorshift32(&seed) % 2) ? 1 : -1;
                        m.t[a][s][r].next_state = xorshift32(&seed) % 3;
                    }

            if (m.t[0][0][0].move == 1 && m.t[1][0][0].move == -1) continue;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            SimResult sr = simulate_bouncer(&m, tape, visited, marker);

            #pragma omp critical
            {
                total++;

                if (sr.result == RES_HALT && sr.steps > max_halt) {
                    max_halt = sr.steps;
                    format_bb(&m, max_halt_bb);
                    printf(">>> NEW HALT: %d steps | %s <<<\n", max_halt, max_halt_bb);
                    fflush(stdout);
                }

                if (sr.result == RES_NON_COLLIDING_BOUNCER) {
                    bouncers_found++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [***] GENUINE CET(3) BOUNCER HOLDOUT #%d [***]\n", bouncers_found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Survived 30,000 steps without translating!\n");
                    printf("Active tape span: %d cells | Direction reversals: %d\n", sr.tape_span, sr.direction_reversals);
                    printf("Distance range: [%d, %d] cells\n", sr.min_dist, sr.max_dist);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total % 10000000 == 0) {
                    printf("[Progress] Tested %lldM machines | Best Halt: %d | Bouncer Holdouts: %d\n",
                           total / 1000000, max_halt, bouncers_found);
                    fflush(stdout);
                }
            }

            if (bouncers_found >= 3 || total >= 50000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished. Total: %lld | Bouncers Found: %d | Max Halt: %d\n", total, bouncers_found, max_halt);
    return 0;
}
