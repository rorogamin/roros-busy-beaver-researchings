#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 524288
#define TAPE_OFFSET 262144
#define CUTOFF 150000

typedef struct {
    int8_t write;
    int8_t move;
    int8_t next_state;
} Transition;

typedef struct {
    Transition t[2][4][2];
} Machine4;

void format_bb4(const Machine4 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 4; s++) {
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
#define RES_POTENTIAL_HOLDOUT 3

typedef struct {
    int result;
    int steps;
    int min_d, max_d;
    int min_p, max_p;
    int sweeps1, sweeps2;
    int tape_ones;
    int drift_late;
} SimResult4;

SimResult4 simulate_cet4(const Machine4 *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult4 res = {0, 0, 999999, 0, 0, 0, 0, 0, 0, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_pos = TAPE_OFFSET;
    int max_pos = TAPE_OFFSET + 2;

    int last_expand_step = 0;
    int p1_at_50k = 0;

    int last_v1 = 0, last_v2 = 0;
    int sw1 = 0, sw2 = 0;

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

        // Discard if diverged
        if (dist > 120) {
            res.result = RES_DISCARD;
            return res;
        }

        if (tr1.move != last_v1) { sw1++; last_v1 = tr1.move; }
        if (tr2.move != last_v2) { sw2++; last_v2 = tr2.move; }

        int exp = 0;
        if (p1 < min_pos) { min_pos = p1; exp = 1; }
        if (p2 < min_pos) { min_pos = p2; exp = 1; }
        if (p1 > max_pos) { max_pos = p1; exp = 1; }
        if (p2 > max_pos) { max_pos = p2; exp = 1; }

        if (exp) last_expand_step = step;

        if (step == 50000) {
            p1_at_50k = p1;
        }
    }

    // Survives 150,000 steps!
    int span = max_pos - min_pos;
    int drift_50k_to_150k = abs(p1 - p1_at_50k);
    int active_recently = (CUTOFF - last_expand_step < 15000);

    // CRITERIA FOR GENUINE CET(4) HOLDOUT:
    // 1. Span is expanding (> 50 cells).
    // 2. Continues expanding recently (active_recently).
    // 3. Both agents bounce/sweep continually (sw1 >= 100, sw2 >= 100).
    // 4. Drift is NOT a trivial constant glider across blank tape (drift_50k_to_150k < 30000).
    if (span >= 50 && active_recently && sw1 >= 100 && sw2 >= 100 && drift_50k_to_150k < 30000) {
        res.result = RES_POTENTIAL_HOLDOUT;
        res.steps = CUTOFF;
        res.min_p = min_pos - TAPE_OFFSET;
        res.max_p = max_pos - TAPE_OFFSET;
        res.sweeps1 = sw1;
        res.sweeps2 = sw2;
        res.drift_late = drift_50k_to_150k;
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
    printf("   SEARCHING FOR GENUINE CET(4) HOLDOUTS (150k CUTOFF)\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Running on %d threads across CET(4) universe (16^16 = 1.84 x 10^19)...\n\n", num_threads);

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
        Machine4 m;

        while (1) {
            for (int a = 0; a < 2; a++)
                for (int s = 0; s < 4; s++)
                    for (int r = 0; r < 2; r++) {
                        m.t[a][s][r].write = xorshift32(&seed) % 2;
                        m.t[a][s][r].move = (xorshift32(&seed) % 2) ? 1 : -1;
                        m.t[a][s][r].next_state = xorshift32(&seed) % 4;
                    }

            if (m.t[0][0][0].move == 1 && m.t[1][0][0].move == -1) continue;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            SimResult4 sr = simulate_cet4(&m, tape, visited, marker);

            #pragma omp critical
            {
                total++;

                if (sr.result == RES_HALT && sr.steps > max_halt) {
                    max_halt = sr.steps;
                    format_bb4(&m, max_halt_bb);
                    printf(">>> NEW CET(4) RECORD: %d steps | %s <<<\n", max_halt, max_halt_bb);
                    fflush(stdout);
                }

                if (sr.result == RES_POTENTIAL_HOLDOUT) {
                    holdouts_found++;
                    char bb[256];
                    format_bb4(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [🌟] GENUINE CET(4) HOLDOUT CANDIDATE #%d [🌟]\n", holdouts_found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Survived 150,000 steps without halting!\n");
                    printf("Tape footprint: [%d, +%d] (%d cells) | Non-zero cells: %d\n",
                           sr.min_p, sr.max_p, sr.max_p - sr.min_p, sr.tape_ones);
                    printf("Sweeps: A1=%d, A2=%d | Distance range: [%d, %d] cells\n",
                           sr.sweeps1, sr.sweeps2, sr.min_d, sr.max_d);
                    printf("Drift (50k->150k): %d cells (NOT a full-speed glider!)\n", sr.drift_late);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total % 5000000 == 0) {
                    printf("[Tested %lldM CET(4)] Max Halt: %d | Holdouts Found: %d\n",
                           total / 1000000, max_halt, holdouts_found);
                    fflush(stdout);
                }
            }

            if (holdouts_found >= 2 || total >= 20000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished. Total: %lld | Holdouts: %d | Max Halt: %d\n", total, holdouts_found, max_halt);
    return 0;
}
