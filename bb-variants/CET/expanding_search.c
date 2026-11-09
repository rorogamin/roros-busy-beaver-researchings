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
#define RES_CYCLE 3
#define RES_EXPANDING_CHAOTIC_HOLDOUT 4

// Comprehensive decider checking:
// 1. Collision
// 2. Escape into blanks (distance > 120)
// 3. Any periodic cycle (tape between agents + agent states repeats with zero expansion or translation)
// 4. Expanding chaotic holdout: expanding tape footprint WITHOUT fixed periodicity!

typedef struct {
    int result;
    int steps;
    int min_dist;
    int max_dist;
    int tape_span;
} SimResult;

typedef struct {
    int step;
    int p1;
    int p2;
    int s1;
    int s2;
    uint32_t tape_hash;
} FrontierSnap;

static inline uint32_t hash_active_region(uint8_t *tape, uint32_t *visited, uint32_t marker, int min_p, int max_p) {
    uint32_t h = 2166136261u;
    for (int i = min_p; i <= max_p; i++) {
        uint8_t v = (visited[i] == marker) ? tape[i] : 0;
        h = (h * 16777619u) ^ v;
    }
    return h;
}

SimResult simulate_deep(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker) {
    SimResult res = {0, 0, 999999, 0, 0};
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int min_touched = TAPE_OFFSET;
    int max_touched = TAPE_OFFSET + 2;

    #define MAX_SNAPS 4096
    FrontierSnap snaps[MAX_SNAPS];
    int snap_cnt = 0;

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

        // Collision Check
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

        int hit_boundary = 0;
        if (p1 < min_touched || p2 < min_touched) {
            min_touched = p1 < p2 ? p1 : p2;
            hit_boundary = 1;
        }
        if (p1 > max_touched || p2 > max_touched) {
            max_touched = p1 > p2 ? p1 : p2;
            hit_boundary = 1;
        }

        // Whenever an agent pushes the tape boundary:
        // Hash the entire active tape from min_touched to max_touched
        if (hit_boundary) {
            uint32_t th = hash_active_region(tape, visited, marker, min_touched, max_touched);
            for (int i = 0; i < snap_cnt; i++) {
                if (snaps[i].s1 == s1 && snaps[i].s2 == s2 &&
                    (snaps[i].p2 - snaps[i].p1) == (p2 - p1) &&
                    snaps[i].tape_hash == th) {
                    res.result = RES_CYCLE;
                    res.steps = step;
                    return res;
                }
            }
            if (snap_cnt < MAX_SNAPS) {
                snaps[snap_cnt].step = step;
                snaps[snap_cnt].p1 = p1;
                snaps[snap_cnt].p2 = p2;
                snaps[snap_cnt].s1 = s1;
                snaps[snap_cnt].s2 = s2;
                snaps[snap_cnt].tape_hash = th;
                snap_cnt++;
            }
        }
    }

    // Survives CUTOFF:
    // Tape span must be growing (e.g. > 20 cells) so it's not a tiny trapped oscillator
    int span = max_touched - min_touched;
    if (span >= 20) {
        res.result = RES_EXPANDING_CHAOTIC_HOLDOUT;
        res.steps = CUTOFF;
        res.tape_span = span;
        return res;
    }

    res.result = RES_CYCLE;
    return res;
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf("   SEARCHING FOR NON-PERIODIC EXPANDING CET(3) HOLDOUTS (SPAN >= 20)\n");
    printf("====================================================================\n");

    int num_threads = omp_get_max_threads();
    printf("Using %d threads...\n", num_threads);

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

            SimResult sr = simulate_deep(&m, tape, visited, marker);

            #pragma omp critical
            {
                total++;

                if (sr.result == RES_HALT && sr.steps > max_halt) {
                    max_halt = sr.steps;
                    format_bb(&m, max_halt_bb);
                    printf(">>> NEW HALT: %d steps | %s <<<\n", max_halt, max_halt_bb);
                    fflush(stdout);
                }

                if (sr.result == RES_EXPANDING_CHAOTIC_HOLDOUT) {
                    holdouts_found++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n============================================================\n");
                    printf(" [***] NON-PERIODIC EXPANDING CET(3) HOLDOUT #%d [***]\n", holdouts_found);
                    printf("bbchallenge: %s\n", bb);
                    printf("Active tape span: %d cells | Min dist: %d | Max dist: %d\n",
                           sr.tape_span, sr.min_dist, sr.max_dist);
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total % 10000000 == 0) {
                    printf("[Progress] Tested %lldM machines | Best Halt: %d | Non-periodic Holdouts: %d\n",
                           total / 1000000, max_halt, holdouts_found);
                    fflush(stdout);
                }
            }

            if (holdouts_found >= 2 || total >= 50000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished. Total: %lld | Non-periodic Holdouts: %d | Max Halt: %d\n", total, holdouts_found, max_halt);
    return 0;
}
