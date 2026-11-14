/* Snapshots at a fixed phase of the cycle: the head leaving the ternary
   counter to the right.

   Usage: ./shape2 <from-step> <count>

   We track the frontier m (position of the leftmost 1 ever written).  Each
   time the head moves right from cell m+1 we print the tape from m to the
   right end of the used region, with the state.  Unverified helper. */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  long long FROM = atoll(argv[1]);
  long long CNT = argc > 2 ? atoll(argv[2]) : 40;
  int N = 4000;
  unsigned char *tape = calloc(N, 1);
  int W[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
  int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
  int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};
  int pos = N / 2, st = 0, lo = pos, hi = pos, m = -1;
  long long steps = 0, shown = 0;
  while (shown < CNT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    int oldpos = pos;
    tape[pos] = w; pos += d; st = ns; steps++;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
    if (w == 1 && (m < 0 || oldpos < m)) m = oldpos;
    if (steps >= FROM && m >= 0 && oldpos == m + 1 && d == 1) {
      printf("t=%lld st=%c w=%d: ", steps, st == 0 ? 'A' : 'B', hi - m);
      for (int i = m; i <= hi + 1; i++) {
        if (i == pos) printf("[%d]", tape[i]); else printf("%d", tape[i]);
      }
      printf("\n");
      shown++;
    }
  }
  return 0;
}
