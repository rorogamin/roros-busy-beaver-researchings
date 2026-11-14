/* Per-epoch closest approach of a left-moving A-cascade to the frontier.
 *
 * A cascade is a maximal run of leftward A-moves separated by at most 8 steps
 * (the P/Q automaton of ANALYSIS.md §4.1 takes 1 or 3 steps per cell, and a
 * bounce costs 6).  For every epoch (each move of the frontier) the program
 * prints the epoch number, its length in steps, the tape width, the distance
 * from the frontier to the leftmost cell reached by a cascade, and the length
 * of the longest cascade of that epoch.
 *
 *   gcc -O2 -o approach approach.c && ./approach 100000000000
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
  long long lastA = -100;
  int cstart = -1, cmin = 1 << 30;
  int best = 1 << 30, longest = 0;
  long long epoch = 0;
  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    if (st == 0 && d == -1) {
      if (steps - lastA > 8) {                 /* a new cascade starts here */
        if (cstart >= 0 && m >= 0) {
          if (cmin - m < best) best = cmin - m;
          if (cstart - cmin > longest) longest = cstart - cmin;
        }
        cstart = pos; cmin = pos;
      }
      if (pos - 1 < cmin) cmin = pos - 1;
      lastA = steps;
    }
    tape[pos] = w; pos += d; st = ns; steps++;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
    if (w == 1 && (m < 0 || pos - d < m)) {
      if (m >= 0) {
        if (cstart >= 0) {
          if (cmin - m < best) best = cmin - m;
          if (cstart - cmin > longest) longest = cstart - cmin;
        }
        printf("epoch %lld t0=%lld len=%lld width=%d approach=%d longest=%d\n",
               epoch, t0, steps - t0, hi - lo + 1,
               best == (1 << 30) ? -1 : best, longest);
        fflush(stdout);
      }
      epoch++;
      m = pos - d; t0 = steps; best = 1 << 30; longest = 0;
      cstart = -1; cmin = 1 << 30; lastA = -100;
    }
  }
  printf("no halt in %lld steps, width %d\n", LIMIT, hi - lo + 1);
  return 0;
}
