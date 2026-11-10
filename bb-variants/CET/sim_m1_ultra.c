#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define TAPE_SIZE 33554432
#define TAPE_OFFSET 16777216
#define MAX_STEPS 10000000000ULL // 10 Billion steps

typedef struct {
    uint8_t w;
    int8_t m;
    uint8_t n;
} Trans;

typedef struct {
    Trans t[2][3][2];
} TM3;

static int parse_tm3(const char* spec, TM3* tm) {
    memset(tm, 0, sizeof(*tm));
    const char* p = spec;
    for (int a = 0; a < 2; a++) {
        for (int q = 0; q < 3; q++) {
            for (int s = 0; s < 2; s++) {
                while (*p == '_' || *p == '|' || *p == ' ') p++;
                if (!*p) return -1;
                tm->t[a][q][s].w = p[0] - '0';
                tm->t[a][q][s].m = (p[1] == 'R') ? 1 : -1;
                tm->t[a][q][s].n = p[2] - 'A';
                p += 3;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    const char *spec = "0LC0LC_1LB1LA_1RC0LA|1LB0RC_1RA1LB_0LB1LB";
    if (argc > 1) spec = argv[1];

    printf("=================================================================\n");
    printf("Simulating CET(3) Candidate up to 10 Billion Steps (Ultra-Speed)\n");
    printf("Spec: %s\n", spec);
    fflush(stdout);

    TM3 tm;
    if (parse_tm3(spec, &tm) < 0) {
        printf("ERROR: Parsing failed\n");
        return 1;
    }

    uint8_t *tape = (uint8_t *)calloc(TAPE_SIZE, 1);
    if (!tape) {
        printf("ERROR: Tape alloc failed\n");
        return 1;
    }

    int p0 = 0, p1 = 2;
    int q0 = 0, q1 = 0;
    int min_p = 0, max_p = 2;
    int max_dist = 2;

    clock_t start_time = clock();
    uint64_t step = 0;

    for (step = 1; step <= MAX_STEPS; step++) {
        int idx0 = p0 + TAPE_OFFSET;
        int idx1 = p1 + TAPE_OFFSET;

        uint8_t s0 = tape[idx0];
        uint8_t s1 = tape[idx1];

        Trans t0 = tm.t[0][q0][s0];
        Trans t1 = tm.t[1][q1][s1];

        tape[idx0] = t0.w;
        tape[idx1] = t1.w;

        p0 += t0.m;
        p1 += t1.m;

        q0 = t0.n;
        q1 = t1.n;

        if (p0 == p1) {
            double elapsed = (double)(clock() - start_time) / CLOCKS_PER_SEC;
            printf("\n💥💥💥 >>> NORMAL HALT! COLLISION AT STEP %llu at cell x = %d! <<< 💥💥💥\n",
                   (unsigned long long)step, p0);
            printf("  Execution Time: %.3f s (%.1f Msteps/sec)\n", elapsed, (double)step / (elapsed * 1000000.0));
            printf("  Tape Bounds: [%d, %d] (span = %d cells)\n", min_p, max_p, max_p - min_p + 1);
            printf("  Max Separation: %d cells\n", max_dist);
            fflush(stdout);
            free(tape);
            return 0;
        }

        if (p0 < min_p) min_p = p0;
        if (p1 > max_p) max_p = p1;
        int d = abs(p1 - p0);
        if (d > max_dist) max_dist = d;

        if (step % 500000000ULL == 0) {
            double elapsed = (double)(clock() - start_time) / CLOCKS_PER_SEC;
            printf("  ... reached %llu Msteps (p0=%d, p1=%d, dist=%d, time=%.1fs, speed=%.1f Msteps/s)\n",
                   (unsigned long long)(step / 1000000ULL), p0, p1, d, elapsed, (double)step / (elapsed * 1000000.0));
            fflush(stdout);
        }
    }

    double elapsed = (double)(clock() - start_time) / CLOCKS_PER_SEC;
    printf("\nReached %llu steps without collision (%.1fs, %.1f Msteps/s)\n",
           (unsigned long long)MAX_STEPS, elapsed, (double)MAX_STEPS / (elapsed * 1000000.0));
    printf("  Final p0=%d, p1=%d, dist=%d, span=%d, max_dist=%d\n",
           p0, p1, abs(p1 - p0), max_p - min_p + 1, max_dist);
    fflush(stdout);

    free(tape);
    return 0;
}
