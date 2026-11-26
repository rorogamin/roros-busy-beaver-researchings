/* Exhaustive sweeps of the halving run for holdout #758.
   Stop rule: halt, or a' = 1, or 2*c' <= c0.  Reports max T and max Q-growth. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#define CAP 200000
static uint64_t A0;
/* returns 0 on success, 1 if Q overflowed 64 bits */
static int step(uint64_t a, uint64_t c, uint64_t *na, uint64_t *nc, int *side) {
    if (a <= c) {
        if (a % 2 == 0) {
            if (c % 2 == 0) return 0;              /* halt (rule g) */
            *na = 1; *nc = a / 2 + c + 2; *side = 1; return 1;
        } else if (c % 2 == 0) { *na = 3*a;      *nc = c - a + 4;        *side = 0; return 1; }
        else                   { *na = 3*a + 2;  *nc = c - a + 1;        *side = 1; return 1; }
    } else {
        uint64_t m = c % 4;
        if (m == 0 || m == 2)  { *na = a - c - 1; *nc = 3*(c/2) + 2;       *side = 0; return 1; }
        if (m == 1) { if (a == c+1) return 0; *na = a - c - 2; *nc = 3*((c-1)/2) + 5; *side = 0; return 1; }
        if (a == c+1 || a == c+3) return 0;
        if (a == c+2) { *na = 3*c + 8; *nc = 1; *side = 1; return 1; }
        *na = a - c - 4; *nc = 3*((c-1)/2) + 8; *side = 0; return 1;
    }
}
int main(int argc, char **argv) {
    int k = atoi(argv[1]);
    uint64_t lim = atoi(argv[2]);
    uint64_t A = 5; for (int i = 1; i < k; i++) A = 3*A + 2;   /* 2*3^k - 1 */
    A0 = A;
    long maxT = -1, maxPh = -1; uint64_t maxDQ = 0, argT = 0, argDQ = 0;
    long over = 0;
    if (lim == 0) lim = A;
    for (uint64_t c = 1; c < lim && c < A; c++) {
        uint64_t a = A, cc = c, c0 = c; long t = 0, ph = 0; int cur = -1;
        for (;;) {
            uint64_t na, nc; int side;
            if (!step(a, cc, &na, &nc, &side)) { t++; goto done; }
            if (side != cur) { ph++; cur = side; }
            a = na; cc = nc; t++;
            if (a == 1 || (cc <= c0 / 2 && 2*cc <= c0)) goto done;
            if (t > CAP) { over++; goto done; }
        }
      done:
        { uint64_t Q0 = A + 2*c0, Qe = a + 2*cc, dq = (Qe >= Q0) ? Qe - Q0 : 0;
          if (t > maxT) { maxT = t; argT = c0; }
          if (ph > maxPh) maxPh = ph;
          if (dq > maxDQ) { maxDQ = dq; argDQ = c0; } }
    }
    printf("k=%d  c<%llu  maxT=%ld at c=%llu  maxPhases=%ld  maxDQ=%llu (%.2f) at c=%llu  overcap=%ld\n",
        k, (unsigned long long)lim, maxT, (unsigned long long)argT, maxPh,
        (unsigned long long)maxDQ, (double)maxDQ/3.0, (unsigned long long)argDQ, over);
    return 0;
}
