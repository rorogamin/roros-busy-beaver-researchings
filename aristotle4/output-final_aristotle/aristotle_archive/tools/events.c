/* Exact value of the ternary counter at every structural event.
 *
 * Two kinds of event are recorded:
 *   grow   - the used tape is extended by one cell at the right end;
 *   casc   - a long left-moving A-cascade starts.
 * At both moments the counter is settled (the head is at the right end), so the
 * cells from the frontier rightwards holding 3, 4 or 0 are exactly its digits
 * (3=0, 4=1, 0=2, most significant digit next to the frontier).  The value is
 * printed exactly, as an unsigned 64-bit number, together with its 2-adic and
 * 3-adic valuations and the gap between the counter and the right end.
 *
 *   gcc -O2 -o events events.c && ./events 100000000000
 */
#include <stdio.h>
#include <stdlib.h>

static int W[2][5] = {{1, 0, 3, 2, 2}, {2, 3, 4, 4, 0}};
static int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};
static int dig[5] = {2, -1, -1, 0, 1};

int main(int argc, char **argv) {
  long long LIMIT = atoll(argv[1]);
  int MINLEN = argc > 2 ? atoi(argv[2]) : 10;
  int N = 20000;
  unsigned char *tape = calloc(N, 1);
  int pos = N / 2, st = 0, lo = pos, hi = pos, m = -1;
  long long steps = 0, lastA = -100;
  int cstart = -1, cmin = 1 << 30;

  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    int grow = (d == 1 && pos == hi);
    int newcasc = 0;
    if (st == 0 && d == -1 && m >= 0) {
      if (steps - lastA > 8) { cstart = pos; cmin = pos; newcasc = 1; }
      if (pos - 1 < cmin) cmin = pos - 1;
      lastA = steps;
    }
    if ((grow || newcasc) && m >= 0) {
      unsigned long long v = 0;
      int L = 0, i = m + 1, ok = 1;
      while (i <= hi && dig[tape[i]] >= 0) {
        if (L < 40) v = v * 3 + dig[tape[i]]; else ok = 0;
        i++; L++;
      }
      if (ok) {
        int v2 = 0, v3 = 0;
        unsigned long long x = v;
        while (x && x % 2 == 0) { v2++; x /= 2; }
        x = v;
        while (x && x % 3 == 0) { v3++; x /= 3; }
        printf("%s t=%lld L=%d v=%llu v2=%d v3=%d gap=%d pos=%d\n",
               grow ? "grow" : "casc", steps, L, v, v2, v3, hi - i + 1, pos - m);
        fflush(stdout);
      }
    }
    tape[pos] = w; pos += d; st = ns; steps++;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
    if (w == 1 && (m < 0 || pos - d < m)) { m = pos - d; cstart = -1; lastA = -100; }
  }
  printf("done %lld\n", LIMIT);
  (void)MINLEN; (void)cstart; (void)cmin; (void)lo;
  return 0;
}
