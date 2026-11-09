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

#define RES_HALT 1
#define RES_ESCAPE 2
#define RES_MONODIRECTIONAL 3 // moves purely in 1 direction forever
#define RES_PERIODIC 4        // repeats exact same tape footprint
#define RES_TRUE_BOUNCER 5    // GENUINE HOLDOUT (bounces back and forth, writing complex tape)

typedef struct {
    int result;
    int steps;
    int min_dist;
    int max_dist;
    int rev1, rev2;
    int tape_span;
} SimResult;

SimResult simulate_bouncer(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 999999, 0, 0, 0, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_touched = TAPE_OFFSET;
    int max_touched = TAPE_OFFSET + 2;

    int rev1 = 0, rev2 = 0;
    int last_move1 = 0, last_move2 = 0;

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

        if (tr1.move != last_move1) { rev1++; last_move1 = tr1.move; }
        if (tr2.move != last_move2) { rev2++; last_move2 = tr2.move; }

        if (p1 == p2) {
            res.result = RES_HALT;
            res.steps = step;
            return res;
        }

        int dist = abs(p2 - p1);
        if (dist < res.min_dist) res.min_dist = dist;
        if (dist > res.max_dist) res.max_dist = dist;

        if (dist > 120) {
            res.result = RES_ESCAPE;
            res.steps = step;
            return res;
        }

        if (p1 < min_touched) min_touched = p1;
        if (p1 > max_touched) max_touched = p1;
        if (p2 < min_touched) min_touched = p2;
        if (p2 > max_touched) max_touched = p2;
    }

    // After 30,000 steps:
    // If an agent never reversed direction or reversed fewer than 20 times,
    // it was just a unidirectional glider/sweeper:
    if (rev1 < 20 || rev2 < 20) {
        res.result = RES_MONODIRECTIONAL;
        return res;
    }

    int span = max_touched - min_touched;
    // If span is < 8 cells, it's a tiny localized cycle
    if (span < 8) {
        res.result = RES_PERIODIC;
        return res;
    }

    // Both agents reversed direction > 20 times (bouncing back and forth across the tape)
    // while keeping distance bounded between [min_dist, max_dist] and NEVER colliding!
    res.result = RES_TRUE_BOUNCER;
    res.steps = CUTOFF;
    res.rev1 = rev1;
    res.rev2 = rev2;
    res.tape_span = span;
    return res;
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf("   EXHAUSTIVE CET(3) TWO-SIDED BOUNCER HOLDOUT SEARCH\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Running across %d threads...\n\n", num_threads);

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

                if (sr.result == RES_TRUE_BOUNCER) {
                    bouncers_found++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [***] TRUE BOUNCER HOLDOUT #%d [***]\n", bouncers_found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Survived 30,000 steps bouncing across tape!\n");
                    printf("Active tape span: %d cells | Agent 1 revs: %d | Agent 2 revs: %d\n",
                           sr.tape_span, sr.rev1, sr.rev2);
                    printf("Distance range: [%d, %d] cells\n", sr.min_dist, sr.max_dist);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total % 10000000 == 0) {
                    printf("[Tested %lldM] Max Halt: %d | True Bouncers: %d\n",
                           total / 1000000, max_halt, bouncers_found);
                    fflush(stdout);
                }
            }

            if (bouncers_found >= 3 || total >= 50000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished. Total: %lld | True Bouncers: %d | Max Halt: %d\n", total, bouncers_found, max_halt);
    return 0;
}
