/* At every long cascade, print the state of the ternary counter.
 *
 * A cascade is a maximal run of leftward A-moves (gaps of at most 8 steps).  At
 * the moment a cascade starts, the head is at the right end of the used tape,
 * so the counter is settled: the cells from the frontier rightwards holding
 * `3`, `4` or `0` are exactly its digits (3=0, 4=1, 0=2, most significant digit
 * next to the frontier).  For every cascade of length >= MINLEN the program
 * prints the time, the counter length L and value v, the fraction v/3^L, the
 * number of cells between the counter and the right end of the tape, and the
 * first and last cell of the cascade measured from the frontier.
 *
 *   gcc -O2 -o cascade_counter cascade_counter.c -lm && ./cascade_counter 100000000000 10
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

static int W[2][5] = {{1, 0, 3, 2, 2}, {2, 3, 4, 4, 0}};
static int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};
static int dig[5] = {2, -1, -1, 0, 1};        /* 0->2, 3->0, 4->1 */

int main(int argc, char **argv) {
  long long LIMIT = atoll(argv[1]);
  int MINLEN = argc > 2 ? atoi(argv[2]) : 10;
  int N = 20000;
  unsigned char *tape = calloc(N, 1);
  int pos = N / 2, st = 0, lo = pos, hi = pos, m = -1;
  long long steps = 0, lastA = -100;
  int cstart = -1, cmin = 1 << 30, cl = 0, cright = 0;
  long double cv = 0, prev = -1;

  while (steps < LIMIT) {
    /* close an open cascade */
    if (cstart >= 0 && steps - lastA > 8) {
      if (cstart - cmin >= MINLEN) {
        printf("casc t=%lld L=%d v=%.0Lf frac=%.4Lf gap=%d start=%d end=%d len=%d",
               lastA, cl, cv, cv / powl(3.0L, cl), hi - cright + 1,
               cstart - m, cmin - m, cstart - cmin);
        if (prev >= 0) printf(" dv=%.0Lf ratio=%.4Lf", cv - prev, cv / prev);
        printf("\n");
        fflush(stdout);
        prev = cv;
      }
      cstart = -1;
    }
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    if (st == 0 && d == -1 && m >= 0) {
      if (cstart < 0) {
        cstart = pos; cmin = pos;
        cv = 0; cl = 0;
        int i = m + 1;
        while (i <= hi && dig[tape[i]] >= 0) { cv = cv * 3 + dig[tape[i]]; i++; cl++; }
        cright = i;
      }
      if (pos - 1 < cmin) cmin = pos - 1;
      lastA = steps;
    }
    tape[pos] = w; pos += d; st = ns; steps++;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
    if (w == 1 && (m < 0 || pos - d < m)) {
      /* the frontier moves: close any cascade still open (a long cascade that
         reaches the counter turns into a left-moving B, whose carry can push
         the frontier one cell further left, ending the epoch early) */
      if (cstart >= 0 && cstart - cmin >= MINLEN) {
        printf("casc t=%lld L=%d v=%.0Lf frac=%.4Lf gap=%d start=%d end=%d len=%d"
               " ENDS-EPOCH", lastA, cl, cv, cv / powl(3.0L, cl), hi - cright + 1,
               cstart - m, cmin - m, cstart - cmin);
        if (prev >= 0) printf(" dv=%.0Lf ratio=%.4Lf", cv - prev, cv / prev);
        printf("\n");
        fflush(stdout);
        prev = cv;
      }
      m = pos - d; cstart = -1; lastA = -100;
    }
  }
  printf("done %lld\n", LIMIT);
  return 0;
}
