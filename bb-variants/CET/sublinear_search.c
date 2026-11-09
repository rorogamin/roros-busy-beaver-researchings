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
#define RES_CHAOTIC_BOUNCER 3

typedef struct {
    int result;
    int steps;
    int min_d, max_d;
    int min_p, max_p;
    int left_hits, right_hits;
    int tape_ones;
} SimResult;

SimResult simulate_sublinear(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 999999, 0, 0, 0, 0, 0, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_pos = TAPE_OFFSET;
    int max_pos = TAPE_OFFSET + 2;

    int left_hits = 0;
    int right_hits = 0;

    int p1_at_50k = 0;
    int p2_at_50k = 0;

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

        if (p1 < min_pos) { min_pos = p1; left_hits++; }
        if (p2 < min_pos) { min_pos = p2; left_hits++; }
        if (p1 > max_pos) { max_pos = p1; right_hits++; }
        if (p2 > max_pos) { max_pos = p2; right_hits++; }

        if (step == 50000) {
            p1_at_50k = p1;
            p2_at_50k = p2;
        }
    }

    // Survives 100,000 steps!
    // To ELIMINATE ALL CONSTANT-VELOCITY GLIDERS:
    // A glider drifts linearly: |p1(100k) - p1(50k)| ≈ 50000 * v (typically > 5000 cells)
    // A bouncer or sub-linear counter stays within a tight, slow-growing zone: |net drift| < 2000 cells!
    int drift_50k_to_100k = abs(p1 - p1_at_50k);
    int total_drift = abs(p1 - TAPE_OFFSET);

    // Filter out finite cyclers: Total tape span must be at least 40 cells!
    int span = max_pos - min_pos;

    // Check if it's NOT a constant linear glider (drift is sublinear or zero, yet active span is >= 40):
    if (drift_50k_to_100k < 2000 && span >= 40 && span <= 1500) {
        res.result = RES_CHAOTIC_BOUNCER;
        res.steps = CUTOFF;
        res.min_p = min_pos - TAPE_OFFSET;
        res.max_p = max_pos - TAPE_OFFSET;
        res.left_hits = left_hits;
        res.right_hits = right_hits;

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
    printf("   SEARCHING FOR SUBLINEAR / CHAOTIC CET(3) HOLDOUTS (SPAN 40..1500)\n");
    printf("   (Rejects all linear gliders: drift from 50k..100k must be < 2000)\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Running on %d threads...\n\n", num_threads);

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

            SimResult sr = simulate_sublinear(&m, tape, visited, marker);

            #pragma omp critical
            {
                total++;

                if (sr.result == RES_HALT && sr.steps > max_halt) {
                    max_halt = sr.steps;
                    format_bb(&m, max_halt_bb);
                    printf(">>> NEW HALT: %d steps | %s <<<\n", max_halt, max_halt_bb);
                    fflush(stdout);
                }

                if (sr.result == RES_CHAOTIC_BOUNCER) {
                    holdouts_found++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [🔥] TRUE SUBLINEAR / BOUNCER HOLDOUT #%d [🔥]\n", holdouts_found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Survived 100,000 steps without linear translation!\n");
                    printf("Active tape span: [%d, +%d] (%d cells) | Non-zero cells: %d\n",
                           sr.min_p, sr.max_p, sr.max_p - sr.min_p, sr.tape_ones);
                    printf("Distance range between agents: [%d, %d] cells\n", sr.min_d, sr.max_d);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total % 10000000 == 0) {
                    printf("[Tested %lldM] Max Halt: %d | Sublinear Holdouts: %d\n",
                           total / 1000000, max_halt, holdouts_found);
                    fflush(stdout);
                }
            }

            if (holdouts_found >= 2 || total >= 50000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished. Total: %lld | Sublinear Holdouts: %d | Max Halt: %d\n", total, holdouts_found, max_halt);
    return 0;
}
