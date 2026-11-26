/* fe0.c -- fast simulator for the fe0_5 (f_eps0 candidate) 17-state, 5-symbol
 * machine, so long runs (1e10-1e11 steps) are affordable.
 *
 * usage: fe0 [-m M] [-n N] [-cap CAP] [-blank] [-machine STR]
 *   default start: 1^m B> 2^n   (m=1, n=3)
 *   -blank: blank tape, state A (for a completed machine that boots itself)
 *   -machine STR: 17 blocks of 5 cells, '_' separated (default: the bare core,
 *                 '---' = halt)
 *
 * The 17-state table is the fe0_5 core; A0/A1/B3/B4 etc. are '---' (halt)
 * unless -machine supplies a completion.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define NS 5
#define NST 17
#define HALT -1
#define ZHALT -2 /* write, move, then halt (B0 = 1RZ) */

static const char *CORE =
    "------0RF0RD1LQ_1RZ1RB2LC------_0LI4RC2RC3RC2RC_1LE1RD2RD3RD---_3LA1LE2LE3LE---_"
    "0LG1RF2RF3RF---_0RI0LH---3RI---_2LA1LH2LH3LH---_3RN---0LA0LI---_2RO---2LJ3LJ---_"
    "2LL---2RK3RK4RK_3RO2RO2LL3LL4LL_3LL---2RM3RM4RM_4LJ1LN2LN3LN1LO_1RB4RP1RK0RM4LN_"
    "4LJ1RP2RP3RP0RP_1RB1LQ2LQ3LQ1LQ";

static int wr[NST][NS], mv[NST][NS], nx[NST][NS];

static int load(const char *s) {
    if (strlen(s) != NST * 15 + (NST - 1)) {
        fprintf(stderr, "machine string has %zu chars, want %d\n", strlen(s),
                NST * 15 + (NST - 1));
        return 0;
    }
    const char *p = s;
    for (int st = 0; st < NST; st++) {
        for (int sym = 0; sym < NS; sym++) {
            if (p[0] == '-') {
                wr[st][sym] = 0;
                mv[st][sym] = 0;
                nx[st][sym] = HALT;
            } else {
                wr[st][sym] = p[0] - '0';
                mv[st][sym] = (p[1] == 'L') ? -1 : 1;
                if (p[2] == 'Z')
                    nx[st][sym] = ZHALT;
                else if (p[2] == '-')
                    nx[st][sym] = HALT;
                else
                    nx[st][sym] = p[2] - 'A';
            }
            p += 3;
        }
        if (st + 1 < NST) {
            if (*p != '_') return 0;
            p++;
        }
    }
    return 1;
}

typedef struct {
    unsigned char *t;
    long long lo, hi, cap;
} Tape;

static inline int get(Tape *T, long long i) {
    if (i < T->lo || i > T->hi) return 0;
    return T->t[i - T->lo];
}

static inline void put(Tape *T, long long i, int v) {
    if (i < T->lo) {
        long long need = T->lo - i;
        long long ncap = T->hi - i + 1;
        T->t = realloc(T->t, (size_t)ncap * need);
        /* shift */
        memmove(T->t + need, T->t, (size_t)(T->hi - T->lo + 1));
        T->lo = i;
        T->cap = ncap;
    } else if (i > T->hi) {
        long long ncap = i - T->lo + 1;
        T->t = realloc(T->t, (size_t)ncap);
        T->hi = i;
        T->cap = ncap;
    }
    T->t[i - T->lo] = (unsigned char)v;
}

int main(int argc, char **argv) {
    long long m = 1, n = 3, cap_ = 1000000000LL;
    int blank = 0;
    const char *machine = CORE;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-m")) m = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-n")) n = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-cap")) cap_ = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-blank")) blank = 1;
        else if (!strcmp(argv[i], "-machine")) machine = argv[++i];
    }
    if (!load(machine)) return 2;

    Tape T = {0};
    T.t = malloc(1 << 20);
    T.lo = 0;
    T.hi = 0;
    T.cap = 1 << 20;
    T.t[0] = 0;

    long long pos = 0;
    int st;
    if (blank) {
        st = 0;
    } else {
        for (long long i = 0; i < m; i++) put(&T, pos - m + i, 1);
        for (long long i = 0; i < n; i++) put(&T, pos + i, 2);
        st = 1; /* B */
    }

    long long steps = 0;
    int halted = 0;
    while (steps < cap_) {
        int sym = get(&T, pos);
        int w = wr[st][sym], d = mv[st][sym], nxt = nx[st][sym];
        if (nxt == HALT) { halted = 1; break; }
        put(&T, pos, w);
        pos += d;
        if (nxt == ZHALT) { halted = 1; steps++; break; }
        st = nxt;
        steps++;
    }
    long long ones = 0, cells = 0;
    for (long long i = T.lo; i <= T.hi; i++) {
        int v = T.t[i - T.lo];
        if (v) cells++;
        if (v == 1) ones++;
    }
    printf("{\"start\":\"%s\",\"m\":%lld,\"n\":%lld,\"halted\":%s,\"steps\":%lld,"
           "\"state\":\"%c\",\"cells\":%lld,\"ones\":%lld,\"span\":[%lld,%lld]}\n",
           blank ? "blank" : "cfg", m, n, halted ? "true" : "false",
           'A' + st, cells, ones, T.lo, T.hi);
    return 0;
}
