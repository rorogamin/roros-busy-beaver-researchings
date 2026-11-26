#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { uint8_t w; int8_t d; uint8_t ns; } Trans;

static uint64_t rng_state = 0xabcdef0123456789ULL;
static inline uint64_t xorshift64(void) {
    uint64_t x = rng_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    rng_state = x;
    return x;
}

static const Trans AG2_COUNTER[4][2] = {
    {{1, 1, 1}, {1, 1, 0}},  /* A: 1RB 1RA */
    {{0, -1, 2}, {0, -1, 3}},/* B: 0LC 0LD */
    {{1, -1, 3}, {0, 1, 1}}, /* C: 1LD 0RB */
    {{0, 1, 0}, {1, -1, 2}}  /* D: 0RA 1LC */
};

static int is_left_glider(const Trans T[4][2]) {
    uint8_t tape[512];
    memset(tape, 0, sizeof(tape));
    int p = 400, s = 0;
    int hist_p[401];
    uint8_t hist_s[401];
    hist_p[0] = p; hist_s[0] = s;
    for (int t = 1; t <= 400; t++) {
        if (p < 10 || p >= 500) return 0;
        Trans tr = T[s][tape[p]];
        tape[p] = tr.w;
        p += tr.d; s = tr.ns;
        hist_p[t] = p; hist_s[t] = s;
    }
    if (p >= 400 || p < 360) return 0;
    for (int P = 16; P <= 60; P++) {
        int D = hist_p[300 - P] - hist_p[300];
        if (D <= 0) continue;
        int ok = 1;
        for (int k = 0; k < 2 * P; k++) {
            if (hist_p[300 + k - P] - hist_p[300 + k] != D || hist_s[300 + k - P] != hist_s[300 + k]) {
                ok = 0; break;
            }
        }
        if (ok) return P;
    }
    return 0;
}

static int sim_cet4(const Trans AG1[4][2], int max_steps) {
    static uint8_t tape[131072];
    memset(tape, 0, sizeof(tape));
    int off = 65536;
    int p1 = off, p2 = off + 2, s1 = 0, s2 = 0;
    for (int t = 1; t <= max_steps; t++) {
        if (p1 < 10 || p1 >= 131060 || p2 < 10 || p2 >= 131060) return -2;
        uint8_t v1 = tape[p1], v2 = tape[p2];
        Trans tr1 = AG1[s1][v1], tr2 = AG2_COUNTER[s2][v2];
        tape[p2] = tr2.w;
        tape[p1] = tr1.w;
        p1 += tr1.d; s1 = tr1.ns;
        p2 += tr2.d; s2 = tr2.ns;
        if (p1 == p2) return t;
    }
    return -1;
}

int main(void) {
    Trans AG2[4][2];
    int halts = 0;
    for (uint64_t trial = 0; trial < 200000000; trial++) {
        for (int s = 0; s < 4; s++) {
            for (int sym = 0; sym < 2; sym++) {
                uint64_t r = xorshift64();
                AG2[s][sym].w = r & 1;
                AG2[s][sym].d = ((r >> 1) & 1) ? 1 : -1;
                AG2[s][sym].ns = (r >> 2) & 3;
            }
        }
        if (!is_left_glider(AG2)) continue;
        int res = sim_cet4(AG2, 500000);
        if (res > 10000) {
            halts++;
            if (halts <= 30) {
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
    }
    printf("Done. Found %d halts > 1000.\n", halts);
    return 0;
}
