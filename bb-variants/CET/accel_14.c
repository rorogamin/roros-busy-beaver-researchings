#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

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

#define W1 20
#define L1_SIZE (1u << (W1 + 1))
typedef struct { uint64_t dt; uint32_t out_bits; uint8_t out_s; } L1Entry;
static L1Entry *l1;

static void compute_l1(uint32_t idx) {
    uint32_t bits = idx & ((1u << W1) - 1);
    int s = (idx >> W1) ? 3 : 2;
    int p = W1 - 1;
    uint64_t steps = 0;
    while (p < W1) {
        if (p < 0) exit(1);
        uint32_t v = (bits >> p) & 1u;
        Trans tr = AG1[s][v];
        if (tr.w) bits |= (1u << p); else bits &= ~(1u << p);
        p += tr.d; s = tr.ns; steps++;
    }
    l1[idx].dt = steps; l1[idx].out_bits = bits; l1[idx].out_s = (uint8_t)s;
}

int main(void) {
    l1 = (L1Entry *)calloc(L1_SIZE, sizeof(L1Entry));
    static uint8_t tape[262144];
    memset(tape, 0, sizeof(tape));
    int off = 1000;
    int p1 = 0, p2 = 14, s1 = 0, s2 = 0;
    for (uint64_t t = 1; t <= 200000; t++) {
        uint8_t v1 = tape[off + p1], v2 = tape[off + p2];
        Trans tr1 = AG1[s1][v1], tr2 = AG2[s2][v2];
        tape[off + p2] = tr2.w; tape[off + p1] = tr1.w;
        p1 += tr1.d; s1 = tr1.ns; p2 += tr2.d; s2 = tr2.ns;
    }
    int min_x = 999999;
    for (int x = 80; x <= 200; x++) if (tape[off + x] == 0 && x < min_x) min_x = x;
    printf("At t=200000 (p2_init=14): p1=%d(%c), p2=%d(%c), first 0 >=80 at x=%d\n",
           p1, 'A'+s1, p2, 'A'+s2, min_x);
    /* Print tape[75..95] */
    printf("tape[75..95]: ");
    for (int x = 75; x <= 95; x++) printf("%d", tape[off + x]);
    printf("\n");

    uint64_t lo = 0, hi = 0;
    for (int x = -2; x <= 61; x++) if (tape[off + x]) lo |= (1ULL << (x + 2));
    for (int x = 62; x <= 85; x++) if (tape[off + x]) hi |= (1ULL << (x - 62));
    uint64_t t = 200000;
    int pos = p1 + 2, s = s1;
    while (pos <= 85) { /* x <= 83 -> exits at x=84 (pos=86) */
        if (pos == W1 - 1 && s >= 2) {
            uint32_t idx = ((uint32_t)(s - 2) << W1) | (uint32_t)(lo & ((1u << W1) - 1));
            if (l1[idx].dt == 0) compute_l1(idx);
            lo = (lo & ~((1ULL << W1) - 1)) | l1[idx].out_bits; s = l1[idx].out_s; pos = W1; t += l1[idx].dt;
        } else {
            uint64_t v = (pos < 64) ? ((lo >> pos) & 1ULL) : ((hi >> (pos - 64)) & 1ULL);
            Trans tr = AG1[s][v];
            if (pos < 64) { if (tr.w) lo |= (1ULL << pos); else lo &= ~(1ULL << pos); }
            else { if (tr.w) hi |= (1ULL << (pos - 64)); else hi &= ~(1ULL << (pos - 64)); }
            pos += tr.d; s = tr.ns; t++;
        }
    }
    printf("p2_init=14 OVERFLOW #2: t=%llu (t mod 11=%llu), pos_x=%d, s=%c\n",
           (unsigned long long)t, (unsigned long long)(t % 11), pos - 2, 'A' + s);
    return 0;
}
