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
} Machine2;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void format_bb(const Machine2 *m, char *buf) {
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

void random_machine(Machine2 *m, uint64_t *rng) {
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

// Check for TRUE HOLDOUT:
// Returns:
//   > 0: halted at step S
//  -1: escaped catch-up cone (proven divergent)
//  -2: simple cycler / trivial 1-cell drift
//  -99: TRUE HOLDOUT: Ran for cutoff steps, never escaped, bounded or complex!
int evaluate_holdout(const Machine2 *m, int cutoff, uint8_t *tape, uint32_t *visited, uint32_t marker,
                     int *out_p1, int *out_p2, int *out_min_x, int *out_max_x, int *out_crossings) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;
    int min_x = p1, max_x = p2;
    int crossings = 0;
    int prev_diff = p1 - p2;

    for (int step = 1; step <= cutoff; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];

        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        if (p1 < min_x) min_x = p1;
        if (p2 < min_x) min_x = p2;
        if (p1 > max_x) max_x = p1;
        if (p2 > max_x) max_x = p2;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        // Collision check
        if (p1 == p2) {
            return step;
        }

        // Track crossings (did p1 leap past p2 without hitting on the exact same cell?)
        int diff = p1 - p2;
        if ((prev_diff > 0 && diff < 0) || (prev_diff < 0 && diff > 0)) {
            crossings++;
        }
        prev_diff = diff;

        // Decider 2: Cone escape (if distance exceeds maximum possible convergence)
        int dist = diff > 0 ? diff : -diff;
        int rem = cutoff - step;
        if (dist > 2 * rem) {
            return -1; // Proven divergent
        }
    }

    *out_p1 = p1 - TAPE_OFFSET;
    *out_p2 = p2 - TAPE_OFFSET;
    *out_min_x = min_x - TAPE_OFFSET;
    *out_max_x = max_x - TAPE_OFFSET;
    *out_crossings = crossings;
    return -99; // SURVIVED CUTOFF WITHIN REACH!
}

int main(int argc, char **argv) {
    int duration = 30;
    if (argc > 1) duration = atoi(argv[1]);

    printf("====================================================================\n");
    printf("   SEARCHING FOR TRUE CET(3) HOLDOUTS (Cutoff: 20,000 steps)\n");
    printf("====================================================================\n");
    printf("Filtering out trivial step-1 collision & cone escapes...\n\n");

    int found_holdouts = 0;
    long long total_searched = 0;

    double start_time = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;
        uint64_t rng = 0x13579bdf2468ace0ULL ^ ((uint64_t)omp_get_thread_num() * 0x9e3779b97f4a7c15ULL) + (uint64_t)time(NULL);

        Machine2 m;
        long long local_count = 0;

        while (omp_get_wtime() - start_time < duration) {
            random_machine(&m, &rng);

            // Decider 1: Skip instant step-1 collision
            if (m.t[0][0][0].move == 1 && m.t[1][0][0].move == -1) continue;

            local_count++;
            marker++;
            if (marker == 0) {
                memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                marker = 1;
            }

            int p1 = 0, p2 = 0, min_x = 0, max_x = 0, crossings = 0;
            // Test 20,000 steps
            int res = evaluate_holdout(&m, 20000, tape, visited, marker, &p1, &p2, &min_x, &max_x, &crossings);

            if (res == -99) {
                // Survived 20,000 steps! Let's test even deeper to 100,000 steps!
                marker++;
                if (marker == 0) {
                    memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                    marker = 1;
                }
                int res2 = evaluate_holdout(&m, 100000, tape, visited, marker, &p1, &p2, &min_x, &max_x, &crossings);

                if (res2 == -99) {
                    #pragma omp critical
                    {
                        found_holdouts++;
                        char bb[256];
                        format_bb(&m, bb);
                        printf("\n>>> FOUND GENUINE CET(3) HOLDOUT #%d! <<<\n", found_holdouts);
                        printf("bbchallenge: %s\n", bb);
                        printf("Stats after 100,000 steps:\n");
                        printf("  • p1 = %d, p2 = %d (distance = %d)\n", p1, p2, abs(p1 - p2));
                        printf("  • Active Tape Span = [%d, %d] (%d cells)\n", min_x, max_x, max_x - min_x + 1);
                        printf("  • Near-miss crossings: %d\n", crossings);
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
    printf("\nFinished in %.2f s! Tested %lld machines. Found %d genuine holdouts.\n", elapsed, total_searched, found_holdouts);

    return 0;
}
