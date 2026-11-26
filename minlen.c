/* minlen.c -- first c achieving each chain length for holdout 758.
 * usage: minlen N THREADS
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>
#include <string.h>

typedef unsigned long long u64;
#define MAXLEN 4096

static int chain_len(u64 c0, u64 *endc) {
    u64 a = 1, c = c0;
    int n = 0;
    for (;;) {
        n++;
        if (n >= MAXLEN) return -1;
        if (a <= c) {
            if ((a & 1) == 0) {
                if ((c & 1) == 0) return n; /* halt */
                a = 1; c = a / 2 + c + 2; /* placeholder fixed below */
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
        if (a == 1) { if (endc) *endc = c; return n; }
    }
}

typedef struct { u64 lo, hi; u64 first[MAXLEN]; int max; } work;

static void *worker(void *arg) {
    work *w = (work*)arg;
    for (int i = 0; i < MAXLEN; i++) w->first[i] = 0;
    w->max = 0;
    for (u64 c = w->lo; c < w->hi; c++) {
        int n = chain_len(c, NULL);
        if (n < 0) continue;
        if (n >= MAXLEN) continue;
        if (w->first[n] == 0) w->first[n] = c;
        if (n > w->max) w->max = n;
    }
    return NULL;
}

int main(int argc, char **argv) {
    u64 N = 100000000ULL;
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
    int max = 0;
    for (int i = 0; i < nt; i++) if (ws[i].max > max) max = ws[i].max;
    printf("N=%llu max_len=%d\n", N, max);
    for (int n = 1; n <= max; n++) {
        u64 best = 0;
        for (int i = 0; i < nt; i++)
            if (ws[i].first[n] && (!best || ws[i].first[n] < best)) best = ws[i].first[n];
        if (best) printf("%d %llu\n", n, best);
    }
    return 0;
}
