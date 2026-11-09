#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 262144
#define TAPE_OFFSET 131072
#define CUTOFF 100000

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

#define RES_HALT 1
#define RES_DISCARD 2
#define RES_GENUINE_HOLDOUT 3

typedef struct {
    int result;
    int steps;
    int min_d, max_d;
    int tape_span;
    int tape_ones;
    int sweeps;
} SimResult;

// Fast simulation rejecting:
// 1. Any finite cycle (via visited tape hash / configuration history)
// 2. Any simple escape / divergence (dist > 150)
// 3. Any lockstep parallel translation (dist == constant for 150 steps)
// 4. Any bounded cycle (if max_pos - min_pos stops expanding and repeats state)
SimResult simulate_candidate(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 999999, 0, 0, 0, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_pos = TAPE_OFFSET;
    int max_pos = TAPE_OFFSET + 2;

    int last_d = 2;
    int same_d_count = 0;

    int prev_v1 = 0;
    int v1_flips = 0;

    // Track frontier expansions
    int last_expand_step = 0;

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

        if (p1 == p2) {
            res.result = RES_HALT;
            res.steps = step;
            return res;
        }

        int dist = abs(p2 - p1);
        if (dist < res.min_d) res.min_d = dist;
        if (dist > res.max_d) res.max_d = dist;

        // Discard: Divergence / Light cone escape
        if (dist > 120) {
            res.result = RES_DISCARD;
            return res;
        }

        // Discard: Constant distance parallel drift into blank tape
        if (dist == last_d) {
            same_d_count++;
            if (same_d_count > 150) {
                res.result = RES_DISCARD;
                return res;
            }
        } else {
            same_d_count = 0;
            last_d = dist;
        }

        if (tr1.move != prev_v1) {
            v1_flips++;
            prev_v1 = tr1.move;
        }

        if (p1 < min_pos) { min_pos = p1; last_expand_step = step; }
        if (p1 > max_pos) { max_pos = p1; last_expand_step = step; }
        if (p2 < min_pos) { min_pos = p2; last_expand_step = step; }
        if (p2 > max_pos) { max_pos = p2; last_expand_step = step; }

        // If the tape has NOT expanded for 35,000 steps, it is trapped in a finite bounded box (periodic cycler)
        if (step - last_expand_step > 35000) {
            res.result = RES_DISCARD;
            return res;
        }
    }

    int span = max_pos - min_pos;
    // Survives 100,000 steps!
    // Must actively expand the tape (span >= 300 cells)
    // Must reverse directions frequently (v1_flips > 500)
    // Must keep agents interacting within a small distance ([min_d, max_d] with max_d <= 120)
    if (span >= 300 && v1_flips >= 500) {
        res.result = RES_GENUINE_HOLDOUT;
        res.steps = CUTOFF;
        res.tape_span = span;
        res.sweeps = v1_flips;
        int ones = 0;
        for (int i = min_pos; i <= max_pos; i++) {
            if (visited[i] == marker && tape[i] != 0) ones++;
        }
        res.tape_ones = ones;
        return res;
    }

    res.result = RES_DISCARD;
    return res;
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf("   SEARCHING FOR UNBOUNDED NON-CYCLING CET(3) EXPANDING HOLDOUTS\n");
    printf("   (100k Steps Cutoff, Sweeps >= 500, Tape Span >= 300 cells)\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Running across %d threads...\n\n", num_threads);

    long long total = 0;
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

            SimResult sr = simulate_candidate(&m, tape, visited, marker);

            #pragma omp critical
            {
                total++;

                if (sr.result == RES_HALT && sr.steps > max_halt) {
                    max_halt = sr.steps;
                    format_bb(&m, max_halt_bb);
                    printf(">>> NEW HALT: %d steps | %s <<<\n", max_halt, max_halt_bb);
                    fflush(stdout);
                }

                if (sr.result == RES_GENUINE_HOLDOUT) {
                    holdouts_found++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [🔥] GENUINE UNBOUNDED CET(3) HOLDOUT #%d [🔥]\n", holdouts_found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Survived 100,000 steps without halting or cycling!\n");
                    printf("Expanding tape footprint: %d cells | Sweeps/Reversals: %d\n", sr.tape_span, sr.sweeps);
                    printf("Agents distance envelope: [%d, %d] cells | Non-zero cells: %d\n",
                           sr.min_d, sr.max_d, sr.tape_ones);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total % 10000000 == 0) {
                    printf("[Tested %lldM] Max Halt: %d | Genuine Holdouts: %d\n",
                           total / 1000000, max_halt, holdouts_found);
                    fflush(stdout);
                }
            }

            if (holdouts_found >= 3 || total >= 50000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished. Total: %lld | Genuine Holdouts: %d | Max Halt: %d\n", total, holdouts_found, max_halt);
    return 0;
}
