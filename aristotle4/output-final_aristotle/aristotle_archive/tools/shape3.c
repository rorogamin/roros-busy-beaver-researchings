/* One line per round trip: the tape at the moment the head turns around at the
   left end of the trip, printed from the frontier (leftmost 1) rightwards,
   together with the trip's leftmost and rightmost cell relative to the
   frontier.  Unverified helper.

   Usage: ./shape3 <from-step> <count> */
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
  int prevpos = pos, tripmax = pos;
  while (shown < CNT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    int oldpos = pos;
    tape[pos] = w; st = ns;
    int newpos = pos + d;
    if (newpos > pos && pos < prevpos && m >= 0) {   /* local minimum */
      if (steps >= FROM) {
        printf("t=%lld min=%d max=%d st=%c: ", steps, pos - m, tripmax - m,
               st == 0 ? 'A' : 'B');
        for (int i = m; i <= hi + 1; i++) {
          if (i == pos) printf("[%d]", tape[i]); else printf("%d", tape[i]);
        }
        printf("\n");
        shown++;
      }
      tripmax = pos;
    }
    if (newpos > tripmax) tripmax = newpos;
    if (newpos != pos) prevpos = pos;
    pos = newpos;
    steps++;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
    if (w == 1 && (m < 0 || oldpos < m)) m = oldpos;
  }
  return 0;
}
