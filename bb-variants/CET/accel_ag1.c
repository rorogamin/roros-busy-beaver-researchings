#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { uint8_t w; int8_t d; uint8_t ns; } Trans;

static const Trans AG1[4][2] = {
    {{1, 1, 1}, {0, 1, 1}},   /* A: 1RB 0RB */
    {{1,-1, 2}, {1, 1, 0}},   /* B: 1LC 1RA */
    {{1,-1, 3}, {0,-1, 2}},   /* C: 1LD 0LC */
    {{0, 1, 0}, {0,-1, 3}}    /* D: 0RA 0LD */
};

static const Trans AG2[4][2] = {
    {{1, 1, 2}, {0, 1, 2}},   /* A: 1RC 0RC */
    {{1,-1, 0}, {0, 1, 2}},   /* B: 1LA 0RC */
    {{1,-1, 0}, {1, 1, 3}},   /* C: 1LA 1RD */
    {{1,-1, 3}, {1,-1, 1}}    /* D: 1LD 1LB */
};

/* W1 = 21 bits: indices x = -2 .. 18 -> bit 0 .. 20. Exits at x = 19 (bit 21). */
#define W1 21
#define L1_SIZE (1u << (W1 + 1)) /* 2 states (C=2, D=3) * 2^21 = 4,194,304 */

typedef struct {
    uint64_t dt;     /* 0 means uncomputed */
    uint32_t out_bits;
    uint8_t out_s;
} L1Entry;

static L1Entry *l1;

/* Level 2 hash cache at W2 = 38 bits: x = -2 .. 35 -> exits at x = 36 */
#define W2 38
#define H2_BITS 22
#define H2_SIZE (1u << H2_BITS)
#define H2_MASK (H2_SIZE - 1)

typedef struct {
    uint64_t key;    /* bit 63: valid, bit 62: entry s (0=C, 1=D), bits 0..37: tape */
    uint64_t dt;
    uint64_t out_bits;
    uint8_t out_s;
} H2Entry;

static H2Entry *h2;

static inline uint64_t hash64(uint64_t x) {
    x ^= x >> 30;
    x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27;
    x *= 0x94d049bb133111ebULL;
    x ^= x >> 31;
    return x;
}

static void compute_l1(uint32_t idx) {
    uint32_t bits = idx & ((1u << W1) - 1);
    int s = (idx >> W1) ? 3 : 2; /* 2=C, 3=D */
    int p = W1 - 1; /* x = 18 */
    uint64_t steps = 0;
    while (p < W1) {
        if (p < 0) {
            fprintf(stderr, "FATAL: p < -2 in L1!\n");
            exit(1);
        }
        uint32_t v = (bits >> p) & 1u;
        Trans tr = AG1[s][v];
        if (tr.w) bits |= (1u << p); else bits &= ~(1u << p);
        p += tr.d;
        s = tr.ns;
        steps++;
    }
    l1[idx].dt = steps;
    l1[idx].out_bits = bits;
    l1[idx].out_s = (uint8_t)s;
}

static void run_w2(uint64_t bits, int s_in, uint64_t *out_bits, int *out_s, uint64_t *out_dt) {
    uint64_t key = (1ULL << 63) | ((uint64_t)(s_in - 2) << 62) | bits;
    uint32_t h = (uint32_t)(hash64(key) & H2_MASK);
    /* Direct-mapped with 4-way probe */
    for (int i = 0; i < 4; i++) {
        uint32_t slot = (h + i) & H2_MASK;
        if (h2[slot].key == key) {
            *out_bits = h2[slot].out_bits;
            *out_s = h2[slot].out_s;
            *out_dt = h2[slot].dt;
            return;
        }
        if ((h2[slot].key >> 63) == 0) break;
    }

    uint64_t orig_bits = bits;
    int p = W2 - 1; /* x = 35 */
    int s = s_in;
    uint64_t steps = 0;
    while (p < W2) {
        if (p == W1 - 1 && s >= 2) {
            uint32_t low = (uint32_t)(bits & ((1u << W1) - 1));
            uint32_t idx = ((uint32_t)(s - 2) << W1) | low;
            if (l1[idx].dt == 0) compute_l1(idx);
            bits = (bits & ~((1ULL << W1) - 1)) | l1[idx].out_bits;
            s = l1[idx].out_s;
            steps += l1[idx].dt;
            p = W1;
            continue;
        }
        uint64_t v = (bits >> p) & 1ULL;
        Trans tr = AG1[s][v];
        if (tr.w) bits |= (1ULL << p); else bits &= ~(1ULL << p);
        p += tr.d;
        s = tr.ns;
        steps++;
    }

    /* Store if space or overwrite slot h */
    uint32_t slot = h;
    for (int i = 0; i < 4; i++) {
        uint32_t cand = (h + i) & H2_MASK;
        if ((h2[cand].key >> 63) == 0) { slot = cand; break; }
    }
    h2[slot].key = key;
    h2[slot].out_bits = bits;
    h2[slot].out_s = (uint8_t)s;
    h2[slot].dt = steps;

    *out_bits = bits;
    *out_s = s;
    *out_dt = steps;
    (void)orig_bits;
}

int main(void) {
    l1 = (L1Entry *)calloc(L1_SIZE, sizeof(L1Entry));
    h2 = (H2Entry *)calloc(H2_SIZE, sizeof(H2Entry));
    if (!l1 || !h2) { fprintf(stderr, "OOM\n"); return 1; }

    /* 1. Direct simulate CET(4) up to t = 200,000 */
    static uint8_t tape[262144];
    memset(tape, 0, sizeof(tape));
    int off = 1000; /* index x -> tape[off + x] */
    int p1 = 0, p2 = 2, s1 = 0, s2 = 0;
    uint64_t t = 0;
    for (t = 1; t <= 200000; t++) {
        uint8_t v1 = tape[off + p1], v2 = tape[off + p2];
        Trans tr1 = AG1[s1][v1], tr2 = AG2[s2][v2];
        tape[off + p2] = tr2.w;
        tape[off + p1] = tr1.w;
        p1 += tr1.d; s1 = tr1.ns;
        p2 += tr2.d; s2 = tr2.ns;
    }
    t = 200000;

    /* Copy tape[-2..107] into two 64-bit words: lo = x=-2..61 (64 bits), hi = x=62..109 (48 bits) */
    uint64_t lo = 0, hi = 0;
    for (int x = -2; x <= 61; x++) {
        if (tape[off + x]) lo |= (1ULL << (x + 2));
    }
    for (int x = 62; x <= 109; x++) {
        if (tape[off + x]) hi |= (1ULL << (x - 62));
    }
    /* Note: x >= 107 are all 1s initially behind AG2 (107..111 = 11111) */

    /* 2. Verify accelerated sim matches naive sim from t=200k to t=2,000,000 */
    uint8_t tape_chk[262144];
    memcpy(tape_chk, tape, sizeof(tape_chk));
    int cp1 = p1, cs1 = s1;
    uint64_t ct = 200000;
    int pos = p1 + 2; /* shifted by +2 so x=-2 is pos=0, x=107 is pos=109, x=108 is pos=110 */
    int s = s1;

    /* Verify check from t=200k */
    int max_pos = pos;
    uint64_t next_report = 10000000ULL;
    int verified_2m = 0;

    while (pos <= 109) { /* pos=109 is x=107, pos=110 is x=108 */
        if (!verified_2m && t >= 2000000) {
            while (ct < t) {
                uint8_t v = tape_chk[off + cp1];
                Trans tr = AG1[cs1][v];
                tape_chk[off + cp1] = tr.w;
                cp1 += tr.d; cs1 = tr.ns;
                ct++;
            }
            int ok = (pos - 2 == cp1 && s == cs1);
            for (int x = -2; x <= 61 && ok; x++) {
                uint64_t b = (lo >> (x + 2)) & 1ULL;
                if (b != tape_chk[off + x]) ok = 0;
            }
            for (int x = 62; x <= 109 && ok; x++) {
                uint64_t b = (hi >> (x - 62)) & 1ULL;
                if (b != tape_chk[off + x]) ok = 0;
            }
            if (!ok) {
                fprintf(stderr, "MISMATCH at t=%llu!\n", (unsigned long long)t);
                return 1;
            }
            printf("Verified BIT-FOR-BIT exact match against naive sim at t=%llu (pos_x=%d, s=%c)!\n",
                   (unsigned long long)t, pos - 2, 'A' + s);
            fflush(stdout);
            verified_2m = 1;
        }
        if (pos == W2 - 1 && s >= 2) {
            uint64_t low38 = lo & ((1ULL << W2) - 1);
            uint64_t ob = 0, dt = 0;
            int os = 0;
            run_w2(low38, s, &ob, &os, &dt);
            lo = (lo & ~((1ULL << W2) - 1)) | ob;
            s = os;
            pos = W2;
            t += dt;
        } else if (pos == W1 - 1 && s >= 2) {
            uint32_t low21 = (uint32_t)(lo & ((1u << W1) - 1));
            uint32_t idx = ((uint32_t)(s - 2) << W1) | low21;
            if (l1[idx].dt == 0) compute_l1(idx);
            lo = (lo & ~((1ULL << W1) - 1)) | l1[idx].out_bits;
            s = l1[idx].out_s;
            pos = W1;
            t += l1[idx].dt;
        } else {
            uint64_t v = (pos < 64) ? ((lo >> pos) & 1ULL) : ((hi >> (pos - 64)) & 1ULL);
            Trans tr = AG1[s][v];
            if (pos < 64) {
                if (tr.w) lo |= (1ULL << pos); else lo &= ~(1ULL << pos);
            } else {
                if (tr.w) hi |= (1ULL << (pos - 64)); else hi &= ~(1ULL << (pos - 64));
            }
            pos += tr.d;
            s = tr.ns;
            t++;
            if (pos > max_pos) {
                max_pos = pos;
                if (max_pos >= 56) {
                    printf("t=%llu: new max_x=%d (s=%c)\n", (unsigned long long)t, max_pos - 2, 'A' + s);
                    fflush(stdout);
                }
            }
        }
        if (t >= next_report) {
            printf("[progress t=%llu, max_x=%d, pos_x=%d]\n", (unsigned long long)t, max_pos - 2, pos - 2);
            fflush(stdout);
            next_report *= 10;
        }
    }
    printf("OVERFLOWED x=107! Exact t=%llu, pos_x=%d, state=%c, t mod 11 = %llu, t mod 22 = %llu\n",
           (unsigned long long)t, pos - 2, 'A' + s, (unsigned long long)(t % 11), (unsigned long long)(t % 22));
    return 0;
}
