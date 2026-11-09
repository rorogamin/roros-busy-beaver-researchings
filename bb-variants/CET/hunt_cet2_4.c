#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 4194304
#define TAPE_OFFSET 2097152

typedef struct {
    uint8_t write; // 0..3
    int8_t move;   // -1 or +1
    uint8_t next_state; // 0 or 1
} Transition;

typedef struct {
    Transition t[2][2][4]; // [agent][state][symbol]
} Machine2_4;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void random_machine(Machine2_4 *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
        for (int s = 0; s < 2; s++) {
            for (int sym = 0; sym < 4; sym++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][sym].write = v & 3;
                m->t[a][s][sym].move = ((v >> 2) & 1) ? 1 : -1;
                m->t[a][s][sym].next_state = (v >> 3) & 1;
            }
        }
    }
}

// Genetic mutation of a machine
void mutate_machine(Machine2_4 *dst, const Machine2_4 *src, uint64_t *rng) {
    *dst = *src;
    int a = splitmix64(rng) % 2;
    int s = splitmix64(rng) % 2;
    int sym = splitmix64(rng) % 4;
    int choice = splitmix64(rng) % 3;
    if (choice == 0) {
        dst->t[a][s][sym].write = splitmix64(rng) % 4;
    } else if (choice == 1) {
        dst->t[a][s][sym].move = (splitmix64(rng) & 1) ? 1 : -1;
    } else {
        dst->t[a][s][sym].next_state = splitmix64(rng) % 2;
    }
}

int simulate_cet2_4(const Machine2_4 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= max_steps; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];

        // Agent 1 write priority
        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        int rem = max_steps - step;
        if (dist > 2 * rem) return -1;
    }
    return -2; // timed out
}

void format_bb_4sym(const Machine2_4 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 2; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 4; sym++) {
                Transition tr = m->t[a][s][sym];
                *p++ = '0' + tr.write;
                *p++ = tr.move > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.next_state;
            }
        }
    }
    *p = '\0';
}

int main(int argc, char **argv) {
    int duration = 20;
    if (argc > 1) duration = atoi(argv[1]);

    printf("Starting CET(2,4) [2 States, 4 Symbols] Hunter for %d seconds...\n", duration);
    printf("Total search space = 2^64 = 18,446,744,073,709,551,616 machines\n");

    int global_max_steps = 0;
    Machine2_4 global_best_m;
    int global_best_pos = 0;
    long long total_searched = 0;

    double start_time = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 135792468ULL ^ ((uint64_t)omp_get_thread_num() * 0x9e3779b97f4a7c15ULL) + (uint64_t)time(NULL);

        Machine2_4 m;
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
            // Quick 5,000 filter
            int s = simulate_cet2_4(&m, 5000, tape, visited, marker, &out_pos);
            if (s > 100 || s == -2) {
                if (s == -2) {
                    marker++;
                    if (marker == 0) {
                        memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                        marker = 1;
                    }
                    // Test up to 1,000,000 steps
                    s = simulate_cet2_4(&m, 1000000, tape, visited, marker, &out_pos);
                }

                if (s > 100) {
                    #pragma omp critical
                    {
                        if (s > global_max_steps) {
                            global_max_steps = s;
                            global_best_m = m;
                            global_best_pos = out_pos;
                            char bb[256];
                            format_bb_4sym(&m, bb);
                            printf("\n>>> NEW CET(2,4) RECORD: %d steps at cell %d! <<<\n", s, out_pos);
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
        format_bb_4sym(&global_best_m, bb);
        printf("FINAL CET(2,4) RECORD: %d steps (halt at cell %d)\n", global_max_steps, global_best_pos);
        printf("bbchallenge: %s\n", bb);
    }

    return 0;
}
