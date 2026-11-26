/* pair5_11.c -- max |F(11,c)-F(5,c)| for odd c <= N.
 * usage: pair5_11 N [threads]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <omp.h>

typedef unsigned long long u64;
typedef long long i64;

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

static u64 G(u64 a, u64 c, int *halt) {
    u64 n = 0;
    int h = 0;
    do {
        int r = step(&a, &c, &h);
        if (r == 0) { fprintf(stderr, "no rule a=%llu c=%llu\n", a, c); exit(2); }
        n++;
        if (n > 10000000ULL) { fprintf(stderr, "guard c=%llu\n", c); exit(2); }
    } while (!h && a != 1);
    *halt = h;
    return c;
}

int main(int argc, char **argv) {
    u64 N = 10000000ULL;
    int threads = 8;
    if (argc > 1) N = strtoull(argv[1], NULL, 0);
    if (argc > 2) threads = atoi(argv[2]);
    omp_set_num_threads(threads);

    u64 gmax = 0, gmax_c = 0, gmax_f5 = 0, gmax_f11 = 0;
    i64 gsigned_max = -1000000000000LL, gsigned_min = 1000000000000LL;
    u64 gsmax_c = 0, gsmin_c = 0;

    #pragma omp parallel
    {
        u64 lmax = 0, lmax_c = 0, lmax_f5 = 0, lmax_f11 = 0;
        i64 lsmax = -1000000000000LL, lsmin = 1000000000000LL;
        u64 lsmax_c = 0, lsmin_c = 0;
        #pragma omp for schedule(dynamic, 10000)
        for (u64 c = 1; c <= N; c += 2) {
            int h5, h11;
            u64 f5 = G(5, c, &h5);
            u64 f11 = G(11, c, &h11);
            if (h5 || h11) continue;
            i64 d = (i64)f11 - (i64)f5;
            u64 ad = d < 0 ? (u64)(-d) : (u64)d;
            if (ad > lmax) { lmax = ad; lmax_c = c; lmax_f5 = f5; lmax_f11 = f11; }
            if (d > lsmax) { lsmax = d; lsmax_c = c; }
            if (d < lsmin) { lsmin = d; lsmin_c = c; }
        }
        #pragma omp critical
        {
            if (lmax > gmax) { gmax = lmax; gmax_c = lmax_c; gmax_f5 = lmax_f5; gmax_f11 = lmax_f11; }
            if (lsmax > gsigned_max) { gsigned_max = lsmax; gsmax_c = lsmax_c; }
            if (lsmin < gsigned_min) { gsigned_min = lsmin; gsmin_c = lsmin_c; }
        }
    }
    printf("N=%llu max|F11-F5|=%llu at c=%llu (F5=%llu F11=%llu)\n", N, gmax, gmax_c, gmax_f5, gmax_f11);
    printf("signed max=%lld at c=%llu, min=%lld at c=%llu\n", gsigned_max, gsmax_c, gsigned_min, gsmin_c);
    return 0;
}
