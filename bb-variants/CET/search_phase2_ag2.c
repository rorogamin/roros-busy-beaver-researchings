#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { uint8_t w; int8_t d; uint8_t ns; } Trans;

static uint64_t rng_state = 0x9e3779b97f4a7c15ULL;
static inline uint64_t xorshift64(void) {
    uint64_t x = rng_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    rng_state = x;
    return x;
}

static const Trans AG1[4][2] = {
    {{1, 1, 1}, {1, -1, 2}}, /* A: 1RB 1LC */
    {{0, 1, 3}, {0, 1, 1}},  /* B: 0RD 0RB */
    {{1, -1, 0}, {0, -1, 0}},/* C: 1LA 0LA */
    {{1, -1, 3}, {0, -1, 0}} /* D: 1LD 0LA */
};

static int is_right_glider(const Trans T[4][2]) {
    uint8_t tape[512];
    memset(tape, 0, sizeof(tape));
    int p = 100, s = 0;
    int min_p = 100, max_p = 100;
    for (int t = 1; t <= 400; t++) {
        if (p < 10 || p >= 500) return 0;
        Trans tr = T[s][tape[p]];
        tape[p] = tr.w;
        p += tr.d; s = tr.ns;
        if (p < min_p) min_p = p;
        if (p > max_p) max_p = p;
    }
    return (p > 120 && max_p - min_p > 20);
}

static int sim_cet4(const Trans AG2[4][2], int max_steps, int *out_p1_max, int *out_p2) {
    static uint8_t tape[131072];
    memset(tape, 0, sizeof(tape));
    int off = 65536;
    int p1 = off, p2 = off + 2, s1 = 0, s2 = 0;
    int p1_max = off;
    for (int t = 1; t <= max_steps; t++) {
        if (p1 < 10 || p1 >= 131060 || p2 < 10 || p2 >= 131060) return -2;
        uint8_t v1 = tape[p1], v2 = tape[p2];
        Trans tr1 = AG1[s1][v1], tr2 = AG2[s2][v2];
        tape[p2] = tr2.w;
        tape[p1] = tr1.w;
        p1 += tr1.d; s1 = tr1.ns;
        p2 += tr2.d; s2 = tr2.ns;
        if (p1 == p2) return t;
        if (p1 > p1_max) p1_max = p1;
    }
    *out_p1_max = p1_max - off;
    *out_p2 = p2 - off;
    return -1;
}

int main(void) {
    Trans AG2[4][2];
    int survivors = 0;
    for (uint64_t trial = 0; trial < 20000000; trial++) {
        for (int s = 0; s < 4; s++) {
            for (int sym = 0; sym < 2; sym++) {
                uint64_t r = xorshift64();
                AG2[s][sym].w = r & 1;
                AG2[s][sym].d = ((r >> 1) & 1) ? 1 : -1;
                AG2[s][sym].ns = (r >> 2) & 3;
            }
        }
        if (!is_right_glider(AG2)) continue;
        int p1_max = 0, p2 = 0;
        int res = sim_cet4(AG2, 200000, &p1_max, &p2);
        if (res > 10000) {
            survivors++;
            printf("HALT t=%d: ", res);
            for (int s = 0; s < 4; s++) {
                if (s > 0) printf("_");
                for (int sym = 0; sym < 2; sym++)
                    printf("%d%c%c", AG2[s][sym].w, AG2[s][sym].d == 1 ? 'R' : 'L', 'A' + AG2[s][sym].ns);
            }
            printf("\n");
            fflush(stdout);
        }
    }
    printf("Done. Found %d halts > 10000.\n", survivors);
    return 0;
}
