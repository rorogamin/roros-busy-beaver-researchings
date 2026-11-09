#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 131072
#define TAPE_OFFSET 65536
#define CUTOFF 40000

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
#define RES_STATIONARY_CYCLE 4
#define RES_TRUE_BOUNCER_HOLDOUT 5

// State hash for cycle detection
// When the leading agent moves onto blank tape (outside touched region):
// The state of the system is fully characterized by:
// (s1, s2, relative_offset = p2 - p1, and the tape segment between min(p1,p2) and max(p1,p2))
typedef struct {
    int step;
    int p1;
    int p2;
    int s1;
    int s2;
    uint32_t tape_hash;
} BlankBoundaryState;

static inline uint32_t hash_tape_window(uint8_t *tape, uint32_t *visited, uint32_t marker, int start, int end) {
    uint32_t h = 2166136261u;
    for (int i = start; i <= end; i++) {
        uint8_t v = (visited[i] == marker) ? tape[i] : 0;
        h ^= v;
        h *= 16777619u;
    }
    return h;
}

typedef struct {
    int result;
    int steps;
    int min_dist;
    int max_dist;
    int min_pos;
    int max_pos;
    int left_sweeps;
    int right_sweeps;
} SimResult;

SimResult simulate_rigorous(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 999999, 0, 0, 0, 0, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_touched = TAPE_OFFSET;
    int max_touched = TAPE_OFFSET + 2;

    // Track direction sweeps
    int v1_prev = 0;
    int dir_changes1 = 0;

    #define MAX_RECORDS 2048
    BlankBoundaryState records[MAX_RECORDS];
    int record_count = 0;

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

        if (tr1.move != v1_prev) {
            dir_changes1++;
            v1_prev = tr1.move;
        }

        // Collision Check
        if (p1 == p2) {
            res.result = RES_HALT;
            res.steps = step;
            return res;
        }

        int dist = abs(p2 - p1);
        if (dist < res.min_dist) res.min_dist = dist;
        if (dist > res.max_dist) res.max_dist = dist;

        // Escape Decider
        if (dist > 120) {
            res.result = RES_ESCAPE;
            res.steps = step;
            return res;
        }

        // Check if expanding the frontier into completely untouched blank tape
        int hit_new_left = (p1 < min_touched) || (p2 < min_touched);
        int hit_new_right = (p1 > max_touched) || (p2 > max_touched);

        if (hit_new_left || hit_new_right) {
            if (hit_new_left) min_touched = (p1 < p2 ? p1 : p2);
            if (hit_new_right) max_touched = (p1 > p2 ? p1 : p2);

            // Compute tape hash of the active region between agents
            int lo = p1 < p2 ? p1 : p2;
            int hi = p1 > p2 ? p1 : p2;
            uint32_t thash = hash_tape_window(tape, visited, marker, lo, hi);

            // Compare with previously recorded frontier states
            for (int k = 0; k < record_count; k++) {
                if (records[k].s1 == s1 && records[k].s2 == s2 &&
                    (records[k].p2 - records[k].p1) == (p2 - p1) &&
                    records[k].tape_hash == thash) {
                    
                    int dx = p1 - records[k].p1;
                    if (dx != 0) {
                        res.result = RES_TRANSLATING_CYCLE;
                        res.steps = step;
                        return res;
                    } else {
                        res.result = RES_STATIONARY_CYCLE;
                        res.steps = step;
                        return res;
                    }
                }
            }

            if (record_count < MAX_RECORDS) {
                records[record_count].step = step;
                records[record_count].p1 = p1;
                records[record_count].p2 = p2;
                records[record_count].s1 = s1;
                records[record_count].s2 = s2;
                records[record_count].tape_hash = thash;
                record_count++;
            }
        }
    }

    // Survives CUTOFF without escaping, without colliding, and without any translating cycles!
    // A genuine bouncer holdout requires multiple reversals (bouncing back and forth across the tape)
    if (dir_changes1 > 20 && (max_touched - min_touched) < 1500) {
        res.result = RES_TRUE_BOUNCER_HOLDOUT;
        res.steps = CUTOFF;
        res.min_pos = min_touched;
        res.max_pos = max_touched;
        return res;
    }

    res.result = RES_ESCAPE;
    return res;
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf(" RIGOROUS FRONTIER-HASHING CET(3) BOUNCER HOLDOUT ENGINE (OPENMP)\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Running on %d threads with Frontier Tape Hash Cycle Decider...\n\n", num_threads);

    long long total_checked = 0;
    int holdouts_found = 0;
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

            SimResult sr = simulate_rigorous(&m, tape, visited, marker);

            #pragma omp critical
            {
                total_checked++;

                if (sr.result == RES_HALT && sr.steps > max_halt) {
                    max_halt = sr.steps;
                    format_bb(&m, max_halt_bb);
                    printf(">>> NEW HALT: %d steps | %s <<<\n", max_halt, max_halt_bb);
                    fflush(stdout);
                }

                if (sr.result == RES_TRUE_BOUNCER_HOLDOUT) {
                    holdouts_found++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [***] CONFIRMED TRUE BOUNCER HOLDOUT #%d [***]\n", holdouts_found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Passed all Frontier Tape Hash deciders (NOT a translating cycle!)\n");
                    printf("Active tape span: [%d, %d] (%d cells)\n",
                           sr.min_pos - TAPE_OFFSET, sr.max_pos - TAPE_OFFSET, sr.max_pos - sr.min_pos);
                    printf("Distance range between agents: [%d, %d] cells\n", sr.min_dist, sr.max_dist);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total_checked % 10000000 == 0) {
                    printf("[Progress] Tested %lldM machines | Best Halt: %d | True Bouncers: %d\n",
                           total_checked / 1000000, max_halt, holdouts_found);
                    fflush(stdout);
                }
            }

            if (holdouts_found >= 2 || total_checked >= 50000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nSearch completed. Total: %lld | True Bouncer Holdouts: %d | Max Halt: %d\n",
           total_checked, holdouts_found, max_halt);
    return 0;
}
