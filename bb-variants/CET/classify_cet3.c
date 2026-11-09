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
    Transition t[2][3][2];
} MachineCET3;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void random_machine(MachineCET3 *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
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

// Quick deciders for non-halting:
// Returns:
//   > 0: halted at step S
//  -10: proven cycler / identical repeat configuration
//  -20: proven escape / distance growing beyond reach
//  -99: undecided within cutoff (HOLDOUT!)
int classify_cet3(const MachineCET3 *m, int cutoff, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    // Fast simulation loop
    for (int step = 1; step <= cutoff; step++) {
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

        // Catch-up check:
        int dist = (p1 > p2) ? (p1 - p2) : (p2 - p1);
        int rem = cutoff - step;
        if (dist > 2 * rem) {
            return -20; // Proven divergent within cutoff
        }
    }

    return -99; // Undecided within cutoff (potential holdout candidate)
}

int main(int argc, char **argv) {
    int num_machines = 1000000;
    if (argc > 1) num_machines = atoi(argv[1]);

    printf("====================================================================\n");
    printf("   CET(3) DECIDER & HOLDOUT CLASSIFIER (Cutoff: 10,000 steps)\n");
    printf("====================================================================\n");
    printf("Testing %d random machines for non-halting classification & holdouts...\n\n", num_machines);

    long long halted_lte_6065 = 0;
    long long halted_gt_6065 = 0;
    long long proven_divergent = 0;
    long long holdouts = 0;

    double start_time = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 0x12345678abcdef01ULL ^ ((uint64_t)omp_get_thread_num() * 0x9e3779b97f4a7c15ULL) + (uint64_t)time(NULL);

        MachineCET3 m;
        long long local_halted_lte = 0, local_halted_gt = 0, local_div = 0, local_hold = 0;

        #pragma omp for
        for (int i = 0; i < num_machines; i++) {
            random_machine(&m, &rng);
            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int out_pos = 0;
            int res = classify_cet3(&m, 10000, tape, visited, marker, &out_pos);
            if (res > 0) {
                if (res <= 6065) {
                    local_halted_lte++;
                } else {
                    local_halted_gt++;
                    #pragma omp critical
                    {
                        char bb[256];
                        format_bb(&m, bb);
                        printf(">>> ALERT: MACHINE HALTED AT %d STEPS (> 6065)! <<<\n", res);
                        printf("bbchallenge: %s\n", bb);
                    }
                }
            } else if (res == -20) {
                local_div++;
            } else if (res == -99) {
                local_hold++;
            }
        }

        #pragma omp atomic
        halted_lte_6065 += local_halted_lte;
        #pragma omp atomic
        halted_gt_6065 += local_halted_gt;
        #pragma omp atomic
        proven_divergent += local_div;
        #pragma omp atomic
        holdouts += local_hold;

        free(tape);
        free(visited);
    }

    double elapsed = omp_get_wtime() - start_time;
    printf("\nClassification Breakdown for %d machines (%.2f s):\n", num_machines, elapsed);
    printf("  1. Halted <= 6,065 steps: %lld (%.2f%%)\n", halted_lte_6065, (halted_lte_6065 * 100.0) / num_machines);
    printf("  2. Halted > 6,065 steps:  %lld\n", halted_gt_6065);
    printf("  3. Proven Divergent:      %lld (%.2f%%)\n", proven_divergent, (proven_divergent * 100.0) / num_machines);
    printf("  4. Holdout candidates:    %lld (%.4f%%)\n", holdouts, (holdouts * 100.0) / num_machines);

    return 0;
}
