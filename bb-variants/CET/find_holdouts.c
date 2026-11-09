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

// Find holdouts:
// Machines that do NOT halt by 10,000 steps, BUT remain bounded (their agents stay close together)!
int check_holdout(const MachineCET3 *m, int cutoff, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_max_dist, int *out_min_p, int *out_max_p) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;
    int min_p = p1, max_p = p2;

    for (int step = 1; step <= cutoff; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];

        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        if (p1 < min_p) min_p = p1;
        if (p2 > max_p) max_p = p2;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        if (p1 == p2) {
            return step; // Halted!
        }

        int dist = (p1 > p2) ? (p1 - p2) : (p2 - p1);
        int rem = cutoff - step;
        if (dist > 2 * rem) {
            return -2; // Escaped cone (proven divergent)
        }
    }

    // Still in cone at cutoff!
    *out_max_dist = (p1 > p2) ? (p1 - p2) : (p2 - p1);
    *out_min_p = min_p - TAPE_OFFSET;
    *out_max_p = max_p - TAPE_OFFSET;
    return -99; // HOLDOUT CANDIDATE!
}

int main(int argc, char **argv) {
    int duration = 20;
    if (argc > 1) duration = atoi(argv[1]);

    printf("====================================================================\n");
    printf("   SEARCHING FOR CET(3) BOUNDED HOLDOUTS (Cutoff: 10,000 steps)\n");
    printf("====================================================================\n");

    int holdout_count = 0;
    long long total_searched = 0;

    double start_time = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 0xfedcba9876543210ULL ^ ((uint64_t)omp_get_thread_num() * 0x517cc1b727220a95ULL) + (uint64_t)time(NULL);

        MachineCET3 m;
        long long local_count = 0;

        while (omp_get_wtime() - start_time < duration) {
            random_machine(&m, &rng);
            local_count++;

            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int max_dist = 0, min_p = 0, max_p = 0;
            int res = check_holdout(&m, 10000, tape, visited, marker, &max_dist, &min_p, &max_p);

            if (res == -99) {
                #pragma omp critical
                {
                    holdout_count++;
                    char bb[256];
                    format_bb(&m, bb);
                    printf("\n>>> FOUND CET(3) HOLDOUT #%d! <<<\n", holdout_count);
                    printf("bbchallenge: %s\n", bb);
                    printf("At step 10,000: agent distance = %d cells, tape span = [%d, %d]\n", max_dist, min_p, max_p);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_searched += local_count;

        free(tape);
        free(visited);
    }

    double elapsed = omp_get_wtime() - start_time;
    printf("\nDone in %.2f s! Searched %lld machines. Found %d holdouts.\n", elapsed, total_searched, holdout_count);

    return 0;
}
