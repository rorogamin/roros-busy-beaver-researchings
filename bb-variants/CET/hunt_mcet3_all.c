#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 1048576
#define TAPE_OFFSET 524288

typedef struct {
    uint8_t write;
    int8_t move;
    uint8_t next_state;
} Transition;

typedef struct {
    Transition t[3][3][2]; // [agent][state][read]
} Machine3;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void random_machine(Machine3 *m, uint64_t *rng) {
    for (int a = 0; a < 3; a++) {
        for (int s = 0; s < 3; s++) {
            for (int r = 0; r < 2; r++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][r].write = v & 1;
                m->t[a][s][r].move = ((v >> 1) & 1) ? 1 : -1;
                m->t[a][s][r].next_state = (v >> 2) % 3;
            }
        }
    }
}

// Check halt: ALL 3 agents at same cell: p1 == p2 && p2 == p3
int simulate_mcet3(const Machine3 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int p3 = TAPE_OFFSET + 4;
    int s1 = 0, s2 = 0, s3 = 0;

    for (int step = 1; step <= max_steps; step++) {
        // Read
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;
        uint8_t r3 = (visited[p3] == marker) ? tape[p3] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];
        Transition tr3 = m->t[2][s3][r3];

        // Write priority: Agent 1 > Agent 2 > Agent 3
        visited[p3] = marker; tape[p3] = tr3.write;
        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        // Move
        p1 += tr1.move;
        p2 += tr2.move;
        p3 += tr3.move;

        s1 = tr1.next_state;
        s2 = tr2.next_state;
        s3 = tr3.next_state;

        // Halting condition: ALL 3 agents at the exact same cell
        if (p1 == p2 && p2 == p3) {
            *out_pos = p1 - TAPE_OFFSET;
            return step;
        }

        // Catch-up pruning check
        int min_p = p1 < p2 ? (p1 < p3 ? p1 : p3) : (p2 < p3 ? p2 : p3);
        int max_p = p1 > p2 ? (p1 > p3 ? p1 : p3) : (p2 > p3 ? p2 : p3);
        int rem = max_steps - step;
        if ((max_p - min_p) > (2 * rem)) {
            return -1; // impossible to all meet
        }
    }
    return -2; // timed out
}

void format_bbchallenge(const Machine3 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 3; a++) {
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

int main(int argc, char **argv) {
    int duration = 25;
    if (argc > 1) duration = atoi(argv[1]);

    printf("Starting MCET(3) All-Agent Collision Champion Hunter for %d seconds...\n", duration);
    printf("Condition: All 3 agents must occupy the SAME cell simultaneously (p1 == p2 && p2 == p3)\n");

    int global_max_steps = 0;
    Machine3 global_best_m;
    int global_best_pos = 0;
    long long total_searched = 0;

    double start_time = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 123456789ULL ^ ((uint64_t)omp_get_thread_num() * 0x517cc1b727220a95ULL) + (uint64_t)time(NULL);

        Machine3 m;
        long long local_count = 0;

        while (omp_get_wtime() - start_time < duration) {
            random_machine(&m, &rng);
            local_count++;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int out_pos = 0;
            // Stage 1 filter: 10,000 steps
            int s = simulate_mcet3(&m, 10000, tape, visited, marker, &out_pos);
            if (s > 200 || s == -2) {
                // If it timed out at 10,000, test deeper up to 3,000,000 steps
                if (s == -2) {
                    marker++;
                    if (marker == 0) {
                        memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                        marker = 1;
                    }
                    s = simulate_mcet3(&m, 3000000, tape, visited, marker, &out_pos);
                }

                if (s > 200) {
                    #pragma omp critical
                    {
                        if (s > global_max_steps) {
                            global_max_steps = s;
                            global_best_m = m;
                            global_best_pos = out_pos;
                            char bb[256];
                            format_bbchallenge(&m, bb);
                            printf("\n>>> NEW MCET(3) ALL-AGENT RECORD: %d steps at cell %d! <<<\n", s, out_pos);
                            printf("bbchallenge: %s\n", bb);
                            fflush(stdout);
                        }
                    }
                }
            }
        }

        #pragma omp atomic
        total_searched += local_count;

        free(tape);
        free(visited);
    }

    double elapsed = omp_get_wtime() - start_time;
    printf("\nDone! Searched %lld machines in %.2f s (%.1f machines/sec)\n", total_searched, elapsed, total_searched / elapsed);
    if (global_max_steps > 0) {
        char bb[256];
        format_bbchallenge(&global_best_m, bb);
        printf("FINAL MCET(3) ALL-AGENT CHAMPION: %d steps (halt at cell %d)\n", global_max_steps, global_best_pos);
        printf("bbchallenge: %s\n", bb);
    } else {
        printf("No machine halted beyond 200 steps.\n");
    }

    return 0;
}
