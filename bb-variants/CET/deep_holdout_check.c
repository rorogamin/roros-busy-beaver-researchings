#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

#define TAPE_SIZE 1048576
#define TAPE_OFFSET 524288

typedef struct {
    uint8_t write;
    int8_t move;
    uint8_t next_state;
} Transition;

typedef struct {
    Transition t[2][3][2];
} MachineCET3;

void format_bb(const MachineCET3 *m, char *buf) {
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

int simulate(const MachineCET3 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos, int *max_d) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;
    int max_dist = 2;

    for (int step = 1; step <= max_steps; step++) {
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
            *out_pos = p1 - TAPE_OFFSET;
            *max_d = max_dist;
            return step;
        }

        int d = (p1 > p2) ? (p1 - p2) : (p2 - p1);
        if (d > max_dist) max_dist = d;
        int rem = max_steps - step;
        if (d > 2 * rem) return -1; // escaped cone
    }
    *max_d = max_dist;
    return -2; // alive at cutoff!
}

int main() {
    printf("Sampling 50 million non-trivial start CET(3) machines...\n");
    int global_holdouts = 0;
    int global_max_halt = 0;

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 0xabcdef1234567890ULL ^ ((uint64_t)omp_get_thread_num() * 0x9e3779b97f4a7c15ULL);

        MachineCET3 m;
        int local_holdouts = 0;
        int local_max_halt = 0;

        #pragma omp for
        for (int i = 0; i < 50000000; i++) {
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        rng = (rng ^ (rng >> 30)) * 0xbf58476d1ce4e5b9ULL;
                        m.t[a][s][r].write = rng & 1;
                        m.t[a][s][r].move = ((rng >> 1) & 1) ? 1 : -1;
                        m.t[a][s][r].next_state = (rng >> 2) % 3;
                    }
                }
            }

            // Exclude trivial step-1 collision (both moving inward)
            if (m.t[0][0][0].move == 1 && m.t[1][0][0].move == -1) continue;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int out_pos = 0, max_d = 0;
            int s = simulate(&m, 10000, tape, visited, marker, &out_pos, &max_d);
            if (s == -2) {
                // Survived 10,000 steps without escaping! Run up to 200,000 steps
                marker++;
                if (marker == 0) {
                    memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                    marker = 1;
                }
                int s2 = simulate(&m, 200000, tape, visited, marker, &out_pos, &max_d);
                if (s2 == -2) {
                    local_holdouts++;
                    #pragma omp critical
                    {
                        char bb[256];
                        format_bb(&m, bb);
                        printf(">>> CONFIRMED HOLDOUT (>200,000 steps): %s (dist=%d)\n", bb, max_d);
                        fflush(stdout);
                    }
                } else if (s2 > local_max_halt) {
                    local_max_halt = s2;
                }
            } else if (s > local_max_halt) {
                local_max_halt = s;
            }
        }

        #pragma omp atomic
        global_holdouts += local_holdouts;
        #pragma omp critical
        {
            if (local_max_halt > global_max_halt) global_max_halt = local_max_halt;
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished 50M sample. Total holdouts: %d. Max halt observed: %d\n", global_holdouts, global_max_halt);
    return 0;
}
