#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 33554432
#define TAPE_OFFSET 16777216
#define MAX_STEPS 30000000ULL

typedef struct { int8_t w, mv, ns; } Tr;
typedef struct { Tr t[2][3][2]; } M;

static void fmt(const M *m, char *b) {
    char *p = b;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                Tr x = m->t[a][s][r];
                *p++ = '0' + x.w; *p++ = x.mv > 0 ? 'R' : 'L'; *p++ = 'A' + x.ns;
            }
        }
    }
    *p = 0;
}

static M parse(const char *s) {
    M m; const char *p = s;
    for (int a = 0; a < 2; a++) {
        for (int st = 0; st < 3; st++) {
            for (int r = 0; r < 2; r++) {
                m.t[a][st][r].w = p[0] - '0';
                m.t[a][st][r].mv = p[1] == 'R' ? 1 : -1;
                m.t[a][st][r].ns = p[2] - 'A';
                p += 3;
            }
            if (*p == '_' || *p == '|') p++;
        }
    }
    return m;
}

static inline uint32_t rnd(uint32_t *s) {
    uint32_t x = *s; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *s = x;
}

static int run_fast(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    for (uint64_t step = 1; step <= MAX_STEPS; step++) {
        if (p1 <= 500 || p1 >= TAPE_SIZE - 500 || p2 <= 500 || p2 >= TAPE_SIZE - 500) return -1;
        uint8_t r1 = vis[p1] == mk ? tape[p1] : 0;
        uint8_t r2 = vis[p2] == mk ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return (int)step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 8000) return -1;
    }
    return -2;
}
