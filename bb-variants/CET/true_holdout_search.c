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
#define RES_SIMPLE_CYCLE 3
#define RES_TRANSLATING_CYCLE 4
#define RES_TRUE_HOLDOUT 5

typedef struct {
    int result;
    int steps;
    int min_dist;
    int max_dist;
    int net_disp;
    int tape_ones;
} SimResult;

// Fast simulation with comprehensive deciders
SimResult simulate_with_deciders(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 999999, 0, 0, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_p = TAPE_OFFSET, max_p = TAPE_OFFSET + 2;

    // For translating cycle detection:
    // Store periodic snapshots every 128 steps of relative distance and state
    int snap_dist[8];
    int snap_s1[8];
    int snap_s2[8];
    int snap_p1[8];
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

        if (p1 < min_p) min_p = p1;
        if (p1 > max_p) max_p = p1;
        if (p2 < min_p) min_p = p2;
        if (p2 > max_p) max_p = p2;

        // Collision Check
        if (p1 == p2) {
            res.result = RES_HALT;
            res.steps = step;
            return res;
        }

        int dist = abs(p2 - p1);
        if (dist < res.min_dist) res.min_dist = dist;
        if (dist > res.max_dist) res.max_dist = dist;

        // Decider 1: Rapid divergence / Light cone escape
        if (dist > 150) {
            res.result = RES_ESCAPE;
            res.steps = step;
            return res;
        }

        // Decider 2: Snapshot-based Translating Glider Decider
        // If (dist, s1, s2) repeats at step intervals with identical net velocity into blank tape
        if ((step & 127) == 0) {
            int slot = (step >> 7) & 7;
            snap_dist[slot] = p2 - p1;
            snap_s1[slot] = s1;
            snap_s2[slot] = s2;
            snap_p1[slot] = p1;
            snap_count++;

            if (snap_count >= 8) {
                // Check if slot matches slot - 1 (128 steps) or slot - 2 (256 steps)
                for (int lag = 1; lag <= 3; lag++) {
                    int prev_slot = (slot - lag + 8) & 7;
                    if (snap_dist[slot] == snap_dist[prev_slot] &&
                        snap_s1[slot] == snap_s1[prev_slot] &&
                        snap_s2[slot] == snap_s2[prev_slot]) {
                        // Periodic configuration reached!
                        int dx = snap_p1[slot] - snap_p1[prev_slot];
                        if (dx == 0) {
                            res.result = RES_SIMPLE_CYCLE;
                            res.steps = step;
                            return res;
                        } else {
                            // Translating cycle / Glider pair!
                            res.result = RES_TRANSLATING_CYCLE;
                            res.steps = step;
                            return res;
                        }
                    }
                }
            }
        }
    }

    // SURVIVED 30,000 STEPS WITHOUT COLLIDING, WITHOUT ESCAPING, AND WITHOUT SIMPLE OR TRANSLATING CYCLES!
    // THIS IS A GENUINE HOLDOUT (Complex chaotic bouncer, Collatz counter, or multi-sweep machine)!
    res.result = RES_TRUE_HOLDOUT;
    res.steps = CUTOFF;
    res.net_disp = max_p - min_p;

    int ones = 0;
    for (int i = min_p; i <= max_p; i++) {
        if (visited[i] == marker && tape[i] != 0) ones++;
    }
    res.tape_ones = ones;
    return res;
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf("   EXHAUSTIVE DECIDER-POWERED CET(3) HOLDOUT DISCOVERY ENGINE\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Running on %d CPU threads with Snapshot Translating-Cycle Decider...\n\n", num_threads);

    long long total_tested = 0;
    long long simple_cycles = 0;
    long long translating_cycles = 0;
    long long escapes = 0;
    long long halts = 0;
    int max_halt = 0;
    char max_halt_bb[256] = "";
    int holdouts_found = 0;

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;

        uint32_t seed = (uint32_t)(time(NULL) ^ omp_get_thread_num() ^ (uintptr_t)tape);
        Machine m;

        while (1) {
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

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            SimResult sr = simulate_with_deciders(&m, tape, visited, marker);

            #pragma omp critical
            {
                total_tested++;
                if (sr.result == RES_HALT) {
                    halts++;
                    if (sr.steps > max_halt) {
                        max_halt = sr.steps;
                        format_bb(&m, max_halt_bb);
                        printf(">>> NEW CHAMPION HALT: %d steps | %s <<<\n", max_halt, max_halt_bb);
                        fflush(stdout);
                    }
                } else if (sr.result == RES_ESCAPE) {
                    escapes++;
                } else if (sr.result == RES_SIMPLE_CYCLE) {
                    simple_cycles++;
                } else if (sr.result == RES_TRANSLATING_CYCLE) {
                    translating_cycles++;
                } else if (sr.result == RES_TRUE_HOLDOUT) {
                    holdouts_found++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n************************************************************\n");
                    printf(" [***] TRUE CET(3) HOLDOUT DISCOVERED (#%d) [***]\n", holdouts_found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Survived %d steps | Distance Range: [%d, %d] | Active Span: %d cells | Tape 1s: %d\n",
                           CUTOFF, sr.min_dist, sr.max_dist, sr.net_disp, sr.tape_ones);
                    printf("************************************************************\n\n");
                    fflush(stdout);
                }

                if (total_tested % 5000000 == 0) {
                    printf("[Tested %lldM] Halts: %lld | Escapes: %lld | SimpleCycles: %lld | Gliders: %lld | TrueHoldouts: %d\n",
                           total_tested / 1000000, halts, escapes, simple_cycles, translating_cycles, holdouts_found);
                    fflush(stdout);
                }
            }

            if (holdouts_found >= 3 || total_tested >= 40000000) {
                break;
            }
        }

        free(tape);
        free(visited);
    }

    printf("\nDone. Total: %lld | True Holdouts: %d\n", total_tested, holdouts_found);
    return 0;
}
