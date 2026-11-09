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
#define RES_CONFINED_BOUNCER 3 // TRUE BOUNCER HOLDOUT

typedef struct {
    int result;
    int steps;
    int min_p, max_p;
    int min_d, max_d;
} SimResult;

SimResult simulate_bounded_bouncer(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 0, 0, 999999, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_pos = TAPE_OFFSET;
    int max_pos = TAPE_OFFSET + 2;

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

        if (dist > 80) {
            res.result = RES_DISCARD;
            return res;
        }

        if (p1 < min_pos) min_pos = p1;
        if (p1 > max_pos) max_pos = p1;
        if (p2 < min_pos) min_pos = p2;
        if (p2 > max_pos) max_pos = p2;
    }

    // Must be tightly confined! Active span between 10 and 200 cells across all 30,000 steps!
    int span = max_pos - min_pos;
    if (span >= 10 && span <= 200) {
        res.result = RES_CONFINED_BOUNCER;
        res.steps = CUTOFF;
        res.min_p = min_pos - TAPE_OFFSET;
        res.max_p = max_pos - TAPE_OFFSET;
        return res;
    }

    res.result = RES_DISCARD;
    return res;
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf("   SEARCHING FOR CONFINED CET(3) BOUNCER HOLDOUTS (SPAN <= 200)\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Using %d threads...\n\n", num_threads);

    long long total = 0;
    int found = 0;
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

            SimResult sr = simulate_bounded_bouncer(&m, tape, visited, marker);

            #pragma omp critical
            {
                total++;

                if (sr.result == RES_HALT && sr.steps > max_halt) {
                    max_halt = sr.steps;
                    format_bb(&m, max_halt_bb);
                    printf(">>> NEW HALT: %d steps | %s <<<\n", max_halt, max_halt_bb);
                    fflush(stdout);
                }

                if (sr.result == RES_CONFINED_BOUNCER) {
                    found++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [***] TRUE CONFINED BOUNCER HOLDOUT #%d [***]\n", found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Tightly bounded on tape! Span: [%d, %d] (%d cells)\n",
                           sr.min_p, sr.max_p, sr.max_p - sr.min_p);
                    printf("Distance range: [%d, %d] cells\n", sr.min_d, sr.max_d);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total % 10000000 == 0) {
                    printf("[Tested %lldM] Max Halt: %d | Confined Bouncers: %d\n",
                           total / 1000000, max_halt, found);
                    fflush(stdout);
                }
            }

            if (found >= 2 || total >= 50000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished. Total: %lld | Found: %d | Best Halt: %d\n", total, found, max_halt);
    return 0;
}
