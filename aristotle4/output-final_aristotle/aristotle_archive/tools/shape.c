/* Print the full tape at every local minimum of the head position.

   Usage: ./shape <from-step> <count>

   At each moment the head turns around at the left end of a trip (a local
   minimum of the position), print the used tape with the head marked.  This is
   the "macroscopic state" of the machine: ternary counter on the left,
   transition zone, binary region counter on the right.  Unverified helper. */
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
  int pos = N / 2, st = 0, lo = pos, hi = pos;
  long long steps = 0;
  int prevpos = pos;
  long long shown = 0;
  while (shown < CNT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    tape[pos] = w; st = ns;
    int newpos = pos + d;
    /* local minimum: we were moving left and now move right */
    if (steps >= FROM && newpos > pos && pos < prevpos) {
      printf("t=%lld pos=%d st=%c: ", steps, pos - N / 2, st == 0 ? 'A' : 'B');
      for (int i = lo - 1; i <= hi + 1; i++) {
        if (i == pos) printf("[%d]", tape[i]); else printf("%d", tape[i]);
      }
      printf("\n");
      shown++;
    }
    if (newpos != pos) prevpos = pos;
    pos = newpos;
    steps++;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
  }
  return 0;
}
