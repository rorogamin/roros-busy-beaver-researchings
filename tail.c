/* tail.c -- max chain length after the initial j-run.
 * usage: tail N [threads]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <omp.h>

typedef unsigned long long u64;

static int step(u64 *a, u64 *c, int *halt) {
    u64 A = *a, C = *c;
    *halt = 0;
    if (C + 1 <= A && (C & 1) == 0) { *a = A - C - 1; *c = 3 * (C / 2) + 2; return 'a'; }
    if (C + 2 <= A && (C & 3) == 1) { *a = A - C - 2; *c = 3 * ((C - 1) / 2) + 5; return 'b'; }
    if (C + 4 <= A && (C & 3) == 3) { *a = A - C - 4; *c = 3 * ((C - 1) / 2) + 8; return 'c'; }
    if (C + 3 == A && (C & 3) == 3) { *halt = 1; return 'd'; }
    if (C + 2 == A && (C & 3) == 3) { *a = 3 * C + 8; *c = 1; return 'e'; }
    if (C + 1 == A && (C & 1) == 1) { *halt = 1; return 'f'; }
    if (C >= A && (A & 1) == 0 && (C & 1) == 0) { *halt = 1; return 'g'; }
    if (C >= A && (A & 1) == 0 && (C & 1) == 1) { *a = 1; *c = A / 2 + C + 2; return 'h'; }
    if (C >= A && (A & 1) == 1 && (C & 1) == 0) { *a = 3 * A; *c = C - A + 4; return 'i'; }
    if (C >= A && (A & 1) == 1 && (C & 1) == 1) { *a = 3 * A + 2; *c = C - A + 1; return 'j'; }
    return 0;
}

static void chain(u64 c0, u64 *plen, u64 *pj, int *phalt) {
    u64 a = 1, c = c0, n = 0, j = 0;
    int h = 0, seen_nonj = 0;
    do {
        int r = step(&a, &c, &h);
        if (r == 0) { fprintf(stderr, "no rule at a=%llu c=%llu start=%llu\n", a, c, c0); exit(2); }
        n++;
        if (!seen_nonj) {
            if (r == 'j') j++;
            else seen_nonj = 1;
        }
        if (n > 10000000ULL) { fprintf(stderr, "guard at %llu\n", c0); exit(2); }
    } while (!h && a != 1);
    *plen = n; *pj = j; *phalt = h;
}

int main(int argc, char **argv) {
    u64 N = 10000000ULL;
    int threads = 8;
    if (argc > 1) N = strtoull(argv[1], NULL, 0);
    if (argc > 2) threads = atoi(argv[2]);
    omp_set_num_threads(threads);

    u64 gmax = 0, gmax_c = 0, gmax_len = 0, gmax_j = 0;
    u64 gmaxlen = 0, gmaxlen_c = 0, gmaxlen_j = 0;

    #pragma omp parallel
    {
        u64 lmax = 0, lmax_c = 0, lmax_len = 0, lmax_j = 0;
        u64 lmaxlen = 0, lmaxlen_c = 0, lmaxlen_j = 0;
        #pragma omp for schedule(dynamic, 10000)
        for (u64 c = 1; c <= N; c++) {
            u64 len, j; int h;
            chain(c, &len, &j, &h);
            u64 t = len - j;
            if (t > lmax) { lmax = t; lmax_c = c; lmax_len = len; lmax_j = j; }
            if (len > lmaxlen) { lmaxlen = len; lmaxlen_c = c; lmaxlen_j = j; }
        }
        #pragma omp critical
        {
            if (lmax > gmax) { gmax = lmax; gmax_c = lmax_c; gmax_len = lmax_len; gmax_j = lmax_j; }
            if (lmaxlen > gmaxlen) { gmaxlen = lmaxlen; gmaxlen_c = lmaxlen_c; gmaxlen_j = lmaxlen_j; }
        }
    }
    printf("N=%llu max_tail=%llu at c=%llu (len=%llu jrun=%llu)\n", N, gmax, gmax_c, gmax_len, gmax_j);
    printf("max_len=%llu at c=%llu (jrun=%llu tail=%llu)\n", gmaxlen, gmaxlen_c, gmaxlen_j, gmaxlen - gmaxlen_j);
    return 0;
}
