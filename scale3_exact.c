/* scale3_exact.c -- exhaustive test of L(3m+r) - L(m) for holdout 758.
 * usage: scale3_exact N THREADS
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>
#include <string.h>

typedef unsigned long long u64;
#define CAP 2000000

static long chain_len(u64 c0) {
    u64 a = 1, c = c0;
    long n = 0;
    for (;;) {
        n++;
        if (n > CAP) return -1;
        if (a <= c) {
            if ((a & 1) == 0) {
                if ((c & 1) == 0) return n; /* halt */
                u64 na = 1, nc = a / 2 + c + 2;
                a = na; c = nc;
            } else if ((c & 1) == 0) {
                u64 na = 3 * a, nc = c - a + 4;
                a = na; c = nc;
            } else {
                u64 na = 3 * a + 2, nc = c - a + 1;
                a = na; c = nc;
            }
        } else {
            unsigned r = (unsigned)(c & 3);
            if (r == 0 || r == 2) {
                u64 na = a - c - 1, nc = 3 * (c / 2) + 2;
                a = na; c = nc;
            } else if (r == 1) {
                if (a == c + 1) return n;
                u64 na = a - c - 2, nc = 3 * (c / 2) + 5;
                a = na; c = nc;
            } else if (a == c + 1) {
                return n;
            } else if (a == c + 2) {
                u64 na = 3 * c + 8, nc = 1;
                a = na; c = nc;
            } else if (a == c + 3) {
                return n;
            } else {
                u64 na = a - c - 4, nc = 3 * (c / 2) + 8;
                a = na; c = nc;
            }
        }
        if (a == 1) return n;
    }
}

typedef struct {
    u64 lo, hi;
    long maxd[3], mind[3];
    u64 argmax[3];
    long hist[3][401]; /* diff + 200 */
    long fails;
} work;

static void *worker(void *arg) {
    work *w = (work*)arg;
    for (int r = 0; r < 3; r++) {
        w->maxd[r] = -1000000000; w->mind[r] = 1000000000;
        w->argmax[r] = 0;
        for (int i = 0; i <= 400; i++) w->hist[r][i] = 0;
    }
    w->fails = 0;
    for (u64 m = w->lo; m < w->hi; m++) {
        long lm = chain_len(m);
        if (lm < 0) { w->fails++; continue; }
        for (int r = 0; r < 3; r++) {
            long l3 = chain_len(3 * m + r);
            if (l3 < 0) { w->fails++; continue; }
            long d = l3 - lm;
            if (d > w->maxd[r]) { w->maxd[r] = d; w->argmax[r] = m; }
            if (d < w->mind[r]) w->mind[r] = d;
            long idx = d + 200;
            if (idx >= 0 && idx <= 400) w->hist[r][idx]++;
        }
    }
    return NULL;
}

int main(int argc, char **argv) {
    u64 N = 10000000ULL;
    int nt = 16;
    if (argc > 1) N = strtoull(argv[1], 0, 0);
    if (argc > 2) nt = atoi(argv[2]);
    if (nt < 1) nt = 1;
    if (nt > 64) nt = 64;
    work *ws = calloc(nt, sizeof(work));
    pthread_t *tids = calloc(nt, sizeof(pthread_t));
    u64 base = N / nt, rem = N % nt, next = 1;
    for (int i = 0; i < nt; i++) {
        u64 cnt = base + ((u64)i < rem ? 1 : 0);
        ws[i].lo = next; ws[i].hi = next + cnt;
        next += cnt;
        pthread_create(&tids[i], NULL, worker, &ws[i]);
    }
    for (int i = 0; i < nt; i++) pthread_join(tids[i], NULL);
    for (int r = 0; r < 3; r++) {
        long mx = -1000000000, mn = 1000000000;
        u64 arg = 0;
        long hist[401]; memset(hist, 0, sizeof(hist));
        long fails = 0;
        for (int i = 0; i < nt; i++) {
            if (ws[i].maxd[r] > mx) { mx = ws[i].maxd[r]; arg = ws[i].argmax[r]; }
            if (ws[i].mind[r] < mn) mn = ws[i].mind[r];
            fails += ws[i].fails;
            for (int j = 0; j <= 400; j++) hist[j] += ws[i].hist[r][j];
        }
        printf("r=%d  min=%ld  max=%ld at m=%llu  max_abs=%ld  fails=%ld\n",
               r, mn, mx, arg, labs(mx) > labs(mn) ? labs(mx) : labs(mn), fails);
        printf("  hist:");
        for (int j = 0; j <= 400; j++) {
            if (hist[j]) {
                long d = j - 200;
                if (d < -20 || d > 20) printf(" [%ld]=%ld", d, hist[j]);
            }
        }
        printf("\n");
        printf("  central:");
        for (int d = -12; d <= 12; d++) printf(" %d:%ld", d, hist[d + 200]);
        printf("\n");
    }
    return 0;
}
