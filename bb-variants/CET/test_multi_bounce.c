#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

typedef struct { uint8_t w; int8_t d; uint8_t ns; } Trans;
static const Trans AG1[4][2] = {
    {{1, 1, 1}, {0, 1, 1}},
    {{1,-1, 2}, {1, 1, 0}},
    {{1,-1, 3}, {0,-1, 2}},
    {{0, 1, 0}, {0,-1, 3}}
};
static const Trans AG2[4][2] = {
    {{1, 1, 2}, {0, 1, 2}},
    {{1,-1, 0}, {0, 1, 2}},
    {{1,-1, 0}, {1, 1, 3}},
    {{1,-1, 3}, {1,-1, 1}}
};

int main(void) {
    static uint8_t tape[33554432];
    int off = 10000;
    int tests[3] = {14, 42, 50};
    for (int ti = 0; ti < 3; ti++) {
        int p2_init = tests[ti];
        memset(tape, 0, sizeof(tape));
        int p1 = 0, p2 = p2_init, s1 = 0, s2 = 0, max_p1 = 0;
        int bounces = 0, last_b = -100;
        for (uint64_t t = 1; t <= 200000000ULL; t++) {
            if (off + p2 >= (int)sizeof(tape) - 10) { printf("OOB\n"); break; }
            uint8_t v1 = tape[off + p1], v2 = tape[off + p2];
            Trans tr1 = AG1[s1][v1], tr2 = AG2[s2][v2];
            tape[off + p2] = tr2.w; tape[off + p1] = tr1.w;
            p1 += tr1.d; s1 = tr1.ns; p2 += tr2.d; s2 = tr2.ns;
            if (p1 > max_p1) max_p1 = p1;
            if (p2 - p1 <= 4 && p1 != p2 && (int64_t)t - last_b > 50) {
                last_b = (int)t;
                bounces++;
                printf("  p2_init=%d bounce #%d at t=%llu (p1=%d, p2=%d)\n", p2_init, bounces, (unsigned long long)t, p1, p2);
                fflush(stdout);
            }
            if (p1 == p2) {
                printf("p2_init=%d: HALTED at t=%llu pos=%d (after %d bounces)\n", p2_init, (unsigned long long)t, p1, bounces);
                fflush(stdout);
                goto next_test;
            }
        }
        printf("p2_init=%d: SURVIVED 200M (max_p1=%d, bounces=%d)\n", p2_init, max_p1, bounces);
        fflush(stdout);
        next_test:;
    }
    return 0;
}
