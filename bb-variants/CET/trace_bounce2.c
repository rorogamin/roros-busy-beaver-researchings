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

#define W1 21
#define L1_SIZE (1u << (W1 + 1))
typedef struct { uint64_t dt; uint32_t out_bits; uint8_t out_s; } L1Entry;
static L1Entry *l1;

#define W2 38
#define H2_BITS 22
#define H2_SIZE (1u << H2_BITS)
#define H2_MASK (H2_SIZE - 1)
typedef struct { uint64_t key, dt, out_bits; uint8_t out_s; } H2Entry;
static H2Entry *h2;

static inline uint64_t hash64(uint64_t x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    x ^= x >> 31; return x;
}

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

static void run_w2(uint64_t bits, int s_in, uint64_t *out_bits, int *out_s, uint64_t *out_dt) {
    uint64_t key = (1ULL << 63) | ((uint64_t)(s_in - 2) << 62) | bits;
    uint32_t h = (uint32_t)(hash64(key) & H2_MASK);
    for (int i = 0; i < 4; i++) {
        uint32_t slot = (h + i) & H2_MASK;
        if (h2[slot].key == key) {
            *out_bits = h2[slot].out_bits; *out_s = h2[slot].out_s; *out_dt = h2[slot].dt; return;
        }
        if ((h2[slot].key >> 63) == 0) break;
    }
    int p = W2 - 1, s = s_in;
    uint64_t steps = 0;
    while (p < W2) {
        if (p == W1 - 1 && s >= 2) {
            uint32_t low = (uint32_t)(bits & ((1u << W1) - 1));
            uint32_t idx = ((uint32_t)(s - 2) << W1) | low;
            if (l1[idx].dt == 0) compute_l1(idx);
            bits = (bits & ~((1ULL << W1) - 1)) | l1[idx].out_bits;
            s = l1[idx].out_s; steps += l1[idx].dt; p = W1; continue;
        }
        uint64_t v = (bits >> p) & 1ULL;
        Trans tr = AG1[s][v];
        if (tr.w) bits |= (1ULL << p); else bits &= ~(1ULL << p);
        p += tr.d; s = tr.ns; steps++;
    }
    uint32_t slot = h;
    for (int i = 0; i < 4; i++) {
        uint32_t cand = (h + i) & H2_MASK;
        if ((h2[cand].key >> 63) == 0) { slot = cand; break; }
    }
    h2[slot].key = key; h2[slot].out_bits = bits; h2[slot].out_s = (uint8_t)s; h2[slot].dt = steps;
    *out_bits = bits; *out_s = s; *out_dt = steps;
}

int main(void) {
    l1 = (L1Entry *)calloc(L1_SIZE, sizeof(L1Entry));
    h2 = (H2Entry *)calloc(H2_SIZE, sizeof(H2Entry));
    static uint8_t tape[262144];
    memset(tape, 0, sizeof(tape));
    int off = 1000;
    int p1 = 0, p2 = 2, s1 = 0, s2 = 0;
    for (uint64_t t = 1; t <= 200000; t++) {
        uint8_t v1 = tape[off + p1], v2 = tape[off + p2];
        Trans tr1 = AG1[s1][v1], tr2 = AG2[s2][v2];
        tape[off + p2] = tr2.w; tape[off + p1] = tr1.w;
        p1 += tr1.d; s1 = tr1.ns; p2 += tr2.d; s2 = tr2.ns;
    }
    uint64_t t = 200000, lo = 0, hi = 0;
    for (int x = -2; x <= 61; x++) if (tape[off + x]) lo |= (1ULL << (x + 2));
    for (int x = 62; x <= 109; x++) if (tape[off + x]) hi |= (1ULL << (x - 62));
    int pos = p1 + 2, s = s1;
    while (pos <= 109) {
        if (pos == W2 - 1 && s >= 2) {
            uint64_t ob, dt; int os;
            run_w2(lo & ((1ULL << W2) - 1), s, &ob, &os, &dt);
            lo = (lo & ~((1ULL << W2) - 1)) | ob; s = os; pos = W2; t += dt;
        } else if (pos == W1 - 1 && s >= 2) {
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
    /* Set up post-return at x=108 (pos=110), s=D (3), t=354278089790ULL */
    /* hi bits cover x=62..125 (bits 0..63). Set x=108..113 = 001000, x=114..125 = 101010101010 */
    hi &= ((1ULL << (108 - 62)) - 1); /* preserve x=62..107 */
    hi |= (1ULL << (110 - 62)); /* x=110 is 1; 108,109,111,112,113 are 0 */
    for (int x = 114; x <= 125; x++) if (x % 2 == 0) hi |= (1ULL << (x - 62));

    t = 354278089790ULL;
    pos = 110; s = 3;
    int max_x_post = 108;
    uint64_t next_rep = 360000000000ULL;
    while (pos <= 122) { /* x <= 120 */
        if (pos == W2 - 1 && s >= 2) {
            uint64_t ob, dt; int os;
            run_w2(lo & ((1ULL << W2) - 1), s, &ob, &os, &dt);
            lo = (lo & ~((1ULL << W2) - 1)) | ob; s = os; pos = W2; t += dt;
        } else if (pos == W1 - 1 && s >= 2) {
            uint32_t idx = ((uint32_t)(s - 2) << W1) | (uint32_t)(lo & ((1u << W1) - 1));
            if (l1[idx].dt == 0) compute_l1(idx);
            lo = (lo & ~((1ULL << W1) - 1)) | l1[idx].out_bits; s = l1[idx].out_s; pos = W1; t += l1[idx].dt;
        } else {
            uint64_t v = (pos < 64) ? ((lo >> pos) & 1ULL) : ((hi >> (pos - 64)) & 1ULL);
            Trans tr = AG1[s][v];
            if (pos < 64) { if (tr.w) lo |= (1ULL << pos); else lo &= ~(1ULL << pos); }
            else { if (tr.w) hi |= (1ULL << (pos - 64)); else hi &= ~(1ULL << (pos - 64)); }
            pos += tr.d; s = tr.ns; t++;
            if (pos - 2 > max_x_post) {
                max_x_post = pos - 2;
                printf("POST t=%llu: new max_x=%d s=%c\n", (unsigned long long)t, max_x_post, 'A' + s);
                fflush(stdout);
            }
        }
        if (t >= next_rep) {
            printf("[POST progress t=%llu max_x=%d pos_x=%d]\n", (unsigned long long)t, max_x_post, pos - 2);
            fflush(stdout);
            next_rep += 100000000000ULL;
        }
    }
    printf("EXITED x=120! t=%llu (t mod 11 = %llu), pos_x=%d, s=%c, tape[114..125]=",
           (unsigned long long)t, (unsigned long long)(t % 11), pos - 2, 'A' + s);
    for (int x = 114; x <= 125; x++) printf("%d", (int)((hi >> (x - 62)) & 1));
    printf("\n");
    return 0;
}
