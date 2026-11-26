#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { uint8_t w; int8_t d; uint8_t ns; } Trans;

static uint64_t rng_state = 0x123456789abcdef0ULL;
static inline uint64_t xorshift64(void) {
    uint64_t x = rng_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    rng_state = x;
    return x;
}

typedef struct {
    const char *name;
    int dir; /* 1 = right (AG1), -1 = left (AG2), 0 = both */
    Trans T[4][2];
} Counter;

static const Counter COUNTERS[10] = {
    {"1RB0RC_0LD1RC_1LD0RB_0LA1LA",  1, {{{1,1,1},{0,1,2}},{{0,-1,3},{1,1,2}},{{1,-1,3},{0,1,1}},{{0,-1,0},{1,-1,0}}}},
    {"1RB1RA_0LC0LD_1LD0RB_0RA1LC", -1, {{{1,1,1},{1,1,0}},{{0,-1,2},{0,-1,3}},{{1,-1,3},{0,1,1}},{{0,1,0},{1,-1,2}}}},
    {"1RB0RC_1LA1RC_0LD0RB_0LA1LD",  1, {{{1,1,1},{0,1,2}},{{1,-1,0},{1,1,2}},{{0,-1,3},{0,1,1}},{{0,-1,0},{1,-1,3}}}},
    {"1RB0RB_1LC1RA_1LD0LC_0RA0LD",  1, {{{1,1,1},{0,1,1}},{{1,-1,2},{1,1,0}},{{1,-1,3},{0,-1,2}},{{0,1,0},{0,-1,3}}}},
    {"1RB1LA_0RC1RC_0LD0RB_0LA1LD", -1, {{{1,1,1},{1,-1,0}},{{0,1,2},{1,1,2}},{{0,-1,3},{0,1,1}},{{0,-1,0},{1,-1,3}}}},
    {"1RB1LC_0LC0RD_0LA1LA_0RB1RD", -1, {{{1,1,1},{1,-1,2}},{{0,-1,2},{0,1,3}},{{0,-1,0},{1,-1,0}},{{0,1,1},{1,1,3}}}},
    {"1RB0RB_0LC1RA_1LD1LC_0RA0LD",  1, {{{1,1,1},{0,1,1}},{{0,-1,2},{1,1,0}},{{1,-1,3},{1,-1,2}},{{0,1,0},{0,-1,3}}}},
    {"1RB1LC_1LD0RB_1RA0LC_0RA0LD",  0, {{{1,1,1},{1,-1,2}},{{1,-1,3},{0,1,1}},{{1,1,0},{0,-1,2}},{{0,1,0},{0,-1,3}}}},
    {"1RB1LC_0LA0RB_1RD0LC_1LA0RD",  0, {{{1,1,1},{1,-1,2}},{{0,-1,0},{0,1,1}},{{1,1,3},{0,-1,2}},{{1,-1,0},{0,1,3}}}},
    {"1RB1LC_1RD0RB_1LA0LC_0LA0RD",  0, {{{1,1,1},{1,-1,2}},{{1,1,3},{0,1,1}},{{1,-1,0},{0,-1,2}},{{0,-1,0},{0,1,3}}}}
};

/* Returns: 1 if right glider, -1 if left glider, 0 otherwise (P in 16..60) */
static int classify_glider(const Trans T[4][2]) {
    uint8_t tape[512];
    memset(tape, 0, sizeof(tape));
    int p = 256, s = 0;
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
    if (p == 256 || p < 216 || p > 296) return 0;
    int want_dir = (p > 256) ? 1 : -1;
    for (int P = 16; P <= 60; P++) {
        int D = hist_p[300] - hist_p[300 - P];
        if (want_dir == 1 && D <= 0) continue;
        if (want_dir == -1 && D >= 0) continue;
        int ok = 1;
        for (int k = 0; k < 2 * P; k++) {
            if (hist_p[300 + k] - hist_p[300 + k - P] != D || hist_s[300 + k] != hist_s[300 + k - P]) {
                ok = 0; break;
            }
        }
        if (ok) {
            int dist = (p > 256) ? (p - 256) : (256 - p);
            if (dist < 8) return 0;
            if (want_dir == 1) {
                for (int x = 258; x <= p - 4; x++) if (!tape[x]) return 0;
            } else {
                for (int x = p + 4; x <= 254; x++) if (!tape[x]) return 0;
            }
            return want_dir;
        }
    }
    return 0;
}

static int sim_cet4(const Trans AG1[4][2], const Trans AG2[4][2], int max_steps, int counter_is_ag1) {
    static uint8_t tape[131072];
    memset(tape, 0, sizeof(tape));
    int off = 65536;
    int p1 = off, p2 = off + 2, s1 = 0, s2 = 0;
    int c_p[200];
    uint8_t c_s[200];
    int tail_start = max_steps - 199;
    for (int t = 1; t <= max_steps; t++) {
        if (p1 < 10 || p1 >= 131060 || p2 < 10 || p2 >= 131060) return -2;
        uint8_t v1 = tape[p1], v2 = tape[p2];
        Trans tr1 = AG1[s1][v1], tr2 = AG2[s2][v2];
        tape[p2] = tr2.w;
        tape[p1] = tr1.w;
        p1 += tr1.d; s1 = tr1.ns;
        p2 += tr2.d; s2 = tr2.ns;
        if (p1 == p2) return t;
        if (t >= tail_start) {
            int idx = t - tail_start;
            c_p[idx] = counter_is_ag1 ? p1 : p2;
            c_s[idx] = counter_is_ag1 ? s1 : s2;
        }
    }
    for (int P = 1; P <= 60; P++) {
        int D = c_p[199] - c_p[199 - P];
        int ok = 1;
        for (int k = 0; k < 2 * P; k++) {
            int i = 199 - k;
            if (c_p[i] - c_p[i - P] != D || c_s[i] != c_s[i - P]) {
                ok = 0; break;
            }
        }
        if (ok) return -3;
    }
    return -1;
}

static void print_tm(const Trans T[4][2]) {
    for (int s = 0; s < 4; s++) {
        if (s > 0) printf("_");
        for (int sym = 0; sym < 2; sym++) {
            printf("%d%c%c", T[s][sym].w, T[s][sym].d == 1 ? 'R' : 'L', 'A' + T[s][sym].ns);
        }
    }
}

int main(void) {
    Trans G[4][2];
    int halts = 0, survs = 0;
    for (uint64_t trial = 0; trial < 200000000; trial++) {
        for (int s = 0; s < 4; s++) {
            for (int sym = 0; sym < 2; sym++) {
                uint64_t r = xorshift64();
                G[s][sym].w = r & 1;
                G[s][sym].d = ((r >> 1) & 1) ? 1 : -1;
                G[s][sym].ns = (r >> 2) & 3;
            }
        }
        int gdir = classify_glider(G);
        if (gdir == 0) continue;
        for (int c = 0; c < 10; c++) {
            if (COUNTERS[c].dir != 0 && COUNTERS[c].dir != gdir) continue;
            int res = (gdir == 1) ? sim_cet4(COUNTERS[c].T, G, 500000, 1) : sim_cet4(G, COUNTERS[c].T, 500000, 0);
            if (res > 10000) {
                halts++;
                printf("HALT t=%d (%s %s): ", res, gdir == 1 ? "AG1=counter,AG2=glider" : "AG1=glider,AG2=counter", COUNTERS[c].name);
                print_tm(G);
                printf("\n");
                fflush(stdout);
            } else if (res == -1) {
                survs++;
                if (survs <= 100) {
                    printf("SURV (%s %s): ", gdir == 1 ? "AG1=counter,AG2=glider" : "AG1=glider,AG2=counter", COUNTERS[c].name);
                    print_tm(G);
                    printf("\n");
                    fflush(stdout);
                }
            }
        }
    }
    printf("Done. Found %d halts > 10000, %d survivors > 500000.\n", halts, survs);
    return 0;
}
