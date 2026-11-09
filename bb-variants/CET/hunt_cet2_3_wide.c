#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 8388608
#define TAPE_OFFSET 4194304

typedef struct {
    uint8_t write; // 0, 1, 2
    int8_t move;   // -1 or +1
    uint8_t next_state; // 0 or 1
} Transition;

typedef struct {
    Transition t[2][2][3]; // [agent][state][symbol]
} Machine2_3;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void random_machine(Machine2_3 *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
        for (int s = 0; s < 2; s++) {
            for (int sym = 0; sym < 3; sym++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][sym].write = v % 3;
                m->t[a][s][sym].move = ((v >> 4) & 1) ? 1 : -1;
                m->t[a][s][sym].next_state = (v >> 5) % 2;
            }
        }
    }
}

// Unrestricted simulation without distance pruning
int simulate_unrestricted(const Machine2_3 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= max_steps; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) {
            return -1;
        }

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
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        int rem = max_steps - step;
        if (dist > 2 * rem) return -1;
    }
    return -2;
}

void format_bb_3sym(const Machine2_3 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 2; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 3; sym++) {
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
    int duration = 60;
    if (argc > 1) duration = atoi(argv[1]);

    printf("=== CET(2,3) Wide-Divergence Hunter (%d s) ===\n", duration);

    int global_max_steps = 8786;
    Machine2_3 global_best_m;
    int global_best_pos = 0;
    long long total_searched = 0;

    double start_time = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 123456789ULL ^ ((uint64_t)omp_get_thread_num() * 0x9e3779b97f4a7c15ULL) + (uint64_t)time(NULL);

        Machine2_3 m;
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
            // Test up to 100,000 steps with NO distance cap
            int s = simulate_unrestricted(&m, 100000, tape, visited, marker, &out_pos);
            if (s == -2) {
                // If it survives 100k steps without collision, test up to 2,000,000 steps
                marker++;
                if (marker == 0) {
                    memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                    marker = 1;
                }
                s = simulate_unrestricted(&m, 2000000, tape, visited, marker, &out_pos);
            }

            if (s > global_max_steps) {
                #pragma omp critical
                {
                    if (s > global_max_steps) {
                        global_max_steps = s;
                        global_best_m = m;
                        global_best_pos = out_pos;
                        char bb[256];
                        format_bb_3sym(&m, bb);
                        printf("\n>>> NEW CET(2,3) RECORD: %d steps at cell %d! <<<\n", s, out_pos);
                        printf("bbchallenge: %s\n", bb);
                        fflush(stdout);
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
    printf("\nFinished in %.2f s. Tested %lld machines (%.1f/sec).\n", elapsed, total_searched, total_searched / elapsed);
    if (global_max_steps > 8786) {
        char bb[256];
        format_bb_3sym(&global_best_m, bb);
        printf("FINAL CET(2,3) RECORD: %d steps at cell %d\n", global_max_steps, global_best_pos);
        printf("bbchallenge: %s\n", bb);
    } else {
        printf("Record 8,786 still stands.\n");
    }

    return 0;
}
