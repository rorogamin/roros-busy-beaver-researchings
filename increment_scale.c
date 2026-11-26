/* increment_scale.c -- defect of D(c)=F(c)-c under c -> B*c+r.
 *
 * usage: increment_scale B N [threads]
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

static u64 chain(u64 c0, int *halt) {
    u64 a = 1, c = c0, n = 0;
    int h = 0;
    do {
        int r = step(&a, &c, &h);
        if (r == 0) { fprintf(stderr, "no rule at a=%llu c=%llu start=%llu\n", a, c, c0); exit(2); }
        n++;
        if (n > 10000000ULL) { fprintf(stderr, "guard at %llu\n", c0); exit(2); }
    } while (!h && a != 1);
    *halt = h;
    return c;
}

int main(int argc, char **argv) {
    u64 B = 3, N = 10000000ULL;
    int threads = 8;
    if (argc > 1) B = strtoull(argv[1], NULL, 0);
    if (argc > 2) N = strtoull(argv[2], NULL, 0);
    if (argc > 3) threads = atoi(argv[3]);
    if (B < 2) { fprintf(stderr, "B>=2\n"); return 2; }
    omp_set_num_threads(threads);

    i64 gmax = -1000000000000000LL, gmin = 1000000000000000LL;
    u64 gmax_m = 0, gmin_m = 0, gmax_r = 0, gmin_r = 0;
    i64 gmax_dm = 0, gmin_dm = 0, gmax_d = 0, gmin_d = 0;
    u64 skip = 0, chains = 0, maxD = 0, maxD_c = 0;

    #pragma omp parallel
    {
        i64 lmax = -1000000000000000LL, lmin = 1000000000000000LL;
        u64 lmax_m = 0, lmin_m = 0, lmax_r = 0, lmin_r = 0;
        i64 lmax_dm = 0, lmin_dm = 0, lmax_d = 0, lmin_d = 0;
        u64 lskip = 0, lchains = 0, lmaxD = 0, lmaxD_c = 0;

        #pragma omp for schedule(dynamic, 10000)
        for (u64 m = 1; m <= N; m++) {
            int hm;
            u64 fm = chain(m, &hm);
            lchains++;
            if (hm) { lskip++; continue; }
            i64 dm = (i64)(fm - m);
            if (dm > (i64)lmaxD) { lmaxD = dm; lmaxD_c = m; }
            for (u64 r = 0; r < B; r++) {
                u64 c0 = B * m + r;
                int h;
                u64 fc = chain(c0, &h);
                lchains++;
                if (h) { lskip++; continue; }
                i64 d = (i64)(fc - c0);
                i64 diff = d - dm;
                if (diff > lmax) { lmax = diff; lmax_m = m; lmax_r = r; lmax_dm = dm; lmax_d = d; }
                if (diff < lmin) { lmin = diff; lmin_m = m; lmin_r = r; lmin_dm = dm; lmin_d = d; }
            }
        }

        #pragma omp critical
        {
            if (lmax > gmax) { gmax = lmax; gmax_m = lmax_m; gmax_r = lmax_r; gmax_dm = lmax_dm; gmax_d = lmax_d; }
            if (lmin < gmin) { gmin = lmin; gmin_m = lmin_m; gmin_r = lmin_r; gmin_dm = lmin_dm; gmin_d = lmin_d; }
            if (lmaxD > maxD) { maxD = lmaxD; maxD_c = lmaxD_c; }
            skip += lskip; chains += lchains;
        }
    }

    printf("B=%llu N=%llu chains=%llu skipped=%llu maxD=%llu at %llu\n", B, N, chains, skip, maxD, maxD_c);
    printf("max diff=%lld m=%llu r=%llu D(m)=%lld D(c)=%lld\n", gmax, gmax_m, gmax_r, gmax_dm, gmax_d);
    printf("min diff=%lld m=%llu r=%llu D(m)=%lld D(c)=%lld\n", gmin, gmin_m, gmin_r, gmin_dm, gmin_d);
    return 0;
}
