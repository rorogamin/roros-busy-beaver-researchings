#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 4194304
#define TAPE_OFFSET 2097152
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

// Baseline champion: 0LC1LA_0LC0LB_1RB1RC|1RC0RC_1RA1LB_0LB1RC
void init_base_champion(Machine *m) {
    // Agent 1: 0LC 1LA _ 0LC 0LB _ 1RB 1RC
    m->t[0][0][0] = (Transition){0, -1, 2};
    m->t[0][0][1] = (Transition){1, -1, 0};
    m->t[0][1][0] = (Transition){0, -1, 2};
    m->t[0][1][1] = (Transition){0, -1, 1};
    m->t[0][2][0] = (Transition){1,  1, 1};
    m->t[0][2][1] = (Transition){1,  1, 2};

    // Agent 2: 1RC 0RC _ 1RA 1LB _ 0LB 1RC
    m->t[1][0][0] = (Transition){1,  1, 2};
    m->t[1][0][1] = (Transition){0,  1, 2};
    m->t[1][1][0] = (Transition){1,  1, 0};
    m->t[1][1][1] = (Transition){1, -1, 1};
    m->t[1][2][0] = (Transition){0, -1, 1};
    m->t[1][2][1] = (Transition){1,  1, 2};
}

// Fast simulation engine
int simulate(const Machine *m, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0;
    int s2 = 0;

    int consecutive_diverge = 0;

    for (int step = 1; step <= MAX_STEPS; step++) {
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

        int dist = abs(p2 - p1);
        if (dist > 300) {
            consecutive_diverge++;
            if (consecutive_diverge > 500) return -1; // diverged
        } else {
            consecutive_diverge = 0;
        }

        // Safety bounds check against tape limits
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) {
            return -1; // Out of bounds escape
        }
    }
    return -2; // exceeded 3,000,000 steps without collision (holdout or non-halting)
}

int main() {
    printf("====================================================================\n");
    printf("   HUNTING FOR 1,000,000+ STEP CET(3) RECORD (OPENMP 16 CORES)\n");
    printf("   Base seed: Nath76 265,383 record | Cutoff: 3,000,000 steps\n");
    printf("====================================================================\n");

    Machine base;
    init_base_champion(&base);

    int num_threads = omp_get_max_threads();
    printf("Exploring genetic mutations and random space on %d threads...\n\n", num_threads);

    long long tested = 0;
    int max_record = 265383;
    char max_record_bb[256];
    format_bb(&base, max_record_bb);

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint32_t seed = (uint32_t)(time(NULL) ^ omp_get_thread_num() ^ (uintptr_t)tape);

        while (1) {
            Machine cand = base;

            // Strategy mix:
            // 70% mutate 1 to 3 transitions from the 265k champion
            // 30% random fresh machine
            uint32_t r_strat = xorshift32(&seed) % 100;
            if (r_strat < 70) {
                int num_mutations = 1 + (xorshift32(&seed) % 3);
                for (int i = 0; i < num_mutations; i++) {
                    int a = xorshift32(&seed) % 2;
                    int s = xorshift32(&seed) % 3;
                    int r = xorshift32(&seed) % 2;
                    cand.t[a][s][r].write = xorshift32(&seed) % 2;
                    cand.t[a][s][r].move = (xorshift32(&seed) % 2) ? 1 : -1;
                    cand.t[a][s][r].next_state = xorshift32(&seed) % 3;
                }
            } else {
                for (int a = 0; a < 2; a++)
                    for (int s = 0; s < 3; s++)
                        for (int r = 0; r < 2; r++) {
                            cand.t[a][s][r].write = xorshift32(&seed) % 2;
                            cand.t[a][s][r].move = (xorshift32(&seed) % 2) ? 1 : -1;
                            cand.t[a][s][r].next_state = xorshift32(&seed) % 3;
                        }
            }

            if (cand.t[0][0][0].move == 1 && cand.t[1][0][0].move == -1) continue;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int coll_pos = 0;
            int steps = simulate(&cand, tape, visited, marker, &coll_pos);

            #pragma omp critical
            {
                tested++;

                if (steps > max_record) {
                    max_record = steps;
                    format_bb(&cand, max_record_bb);
                    printf("\n============================================================\n");
                    printf(" [🚨] NEW ALL-TIME RECORD DISCOVERY: %d STEPS! [🚨]\n", max_record);
                    printf("bbchallenge: %s\n", max_record_bb);
                    printf("Collided at cell: %d\n", coll_pos);
                    if (max_record >= 1000000) {
                        printf(">>> !!! ACHIEVED 1,000,000+ STEPS IN CET(3) !!! <<<\n");
                    }
                    printf("============================================================\n\n");
                    fflush(stdout);
                }

                if (tested % 2000000 == 0) {
                    printf("[Tested %lldM] Current Best: %d steps\n", tested / 1000000, max_record);
                    fflush(stdout);
                }
            }

            if (max_record >= 1000000 || tested >= 30000000) break;
        }

        free(tape);
        free(visited);
    }

    printf("\nSearch completed. Tested: %lld | Peak: %d steps\n", tested, max_record);
    return 0;
}
