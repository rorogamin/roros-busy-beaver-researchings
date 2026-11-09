#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 1048576
#define TAPE_OFFSET 524288
#define MAX_STEPS 3000000

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

int main() {
    printf("====================================================================\n");
    printf("  PARALLEL MILLION-STEP CET(3) HUNTER (16 CORES)\n");
    printf("  Searching for machines surviving > 265,383 up to 3,000,000 steps\n");
    printf("====================================================================\n\n");

    long long total = 0;
    int record = 265383;
    char record_bb[256] = "0LC1LA_0LC0LB_1RB1RC|1RC0RC_1RA1LB_0LB1RC";

    int num_threads = omp_get_max_threads();
    printf("Running on %d threads...\n", num_threads);

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint32_t seed = (uint32_t)(time(NULL) ^ omp_get_thread_num() ^ (uintptr_t)tape);

        Machine m;

        while (1) {
            // High-probability ping-pong counter structures:
            // One head biased leftwards, one head biased rightwards, with complex bouncing
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        m.t[a][s][r].write = xorshift32(&seed) % 2;
                        m.t[a][s][r].move = (xorshift32(&seed) % 2) ? 1 : -1;
                        m.t[a][s][r].next_state = xorshift32(&seed) % 3;
                    }
                }
            }

            // Quick reject 1-step collision
            if (m.t[0][0][0].move == 1 && m.t[1][0][0].move == -1) continue;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int p1 = TAPE_OFFSET;
            int p2 = TAPE_OFFSET + 2;
            int s1 = 0;
            int s2 = 0;
            int step = 1;
            int halted = 0;

            for (; step <= MAX_STEPS; step++) {
                uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
                uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

                Transition tr1 = m.t[0][s1][r1];
                Transition tr2 = m.t[1][s2][r2];

                visited[p2] = marker; tape[p2] = tr2.write;
                visited[p1] = marker; tape[p1] = tr1.write;

                p1 += tr1.move;
                p2 += tr2.move;

                s1 = tr1.next_state;
                s2 = tr2.next_state;

                if (p1 == p2) {
                    halted = 1;
                    break;
                }

                // If distance exceeds 500 cells, they have diverged
                int dist = abs(p2 - p1);
                if (dist > 500) break;

                // Tape edge check
                if (p1 <= 100 || p1 >= TAPE_SIZE - 100 || p2 <= 100 || p2 >= TAPE_SIZE - 100) break;
            }

            #pragma omp critical
            {
                total++;

                if (halted && step > record) {
                    record = step;
                    format_bb(&m, record_bb);
                    printf("\n============================================================\n");
                    printf(" [🚨] NEW CET(3) RECORD SURPASSED: %d STEPS! [🚨]\n", record);
                    printf("bbchallenge: %s\n", record_bb);
                    printf("Collision coordinate: %d\n", p1 - TAPE_OFFSET);
                    if (record >= 1000000) {
                        printf(">>> !!! OFFICIAL 1,000,000+ STEP CET(3) CHAMPION !!! <<<\n");
                    }
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (total % 5000000 == 0) {
                    printf("[Tested %lldM] Current Best: %d steps\n", total / 1000000, record);
                    fflush(stdout);
                }
            }

            if (record >= 1000000 || total >= 50000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished. Total tested: %lld | Peak record: %d\n", total, record);
    return 0;
}
