/* Per-epoch statistics of how far right the head goes.
 *
 * For each epoch prints: length, tape width, the maximum distance the head
 * reaches to the right of the frontier, and a histogram (by decade of the
 * distance) of the right turning points of the head.
 *
 *   gcc -O2 -o excursion excursion.c && ./excursion 3000000000
 */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  long long LIMIT = atoll(argv[1]);
  int N = 20000;
  unsigned char *tape = calloc(N, 1);
  int W[2][5] = {{1, 0, 3, 2, 2}, {2, 3, 4, 4, 0}};
  int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
  int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};
  int pos = N / 2, st = 0, lo = pos, hi = pos, m = -1;
  long long steps = 0, t0 = 0;
  int maxd = 0, lastdir = 1;
  long long hist[40];
  for (int i = 0; i < 40; i++) hist[i] = 0;
  long long epoch = 0;
  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    if (d == -1 && lastdir == 1 && m >= 0) {      /* right turning point */
      int dist = pos - m;
      if (dist > maxd) maxd = dist;
      int b = dist / 5; if (b > 39) b = 39; if (b < 0) b = 0;
      hist[b]++;
    }
    lastdir = d;
    tape[pos] = w; pos += d; st = ns; steps++;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
    if (w == 1 && (m < 0 || pos - d < m)) {
      if (m >= 0) {
        printf("epoch %lld len=%lld width=%d maxd=%d hist=", epoch, steps - t0,
               hi - lo + 1, maxd);
        for (int i = 0; i < 40; i++)
          if (hist[i]) printf("%d:%lld ", i * 5, hist[i]);
        printf("\n");
        fflush(stdout);
      }
      epoch++;
      m = pos - d; t0 = steps; maxd = 0;
      for (int i = 0; i < 40; i++) hist[i] = 0;
    }
  }
  return 0;
}
