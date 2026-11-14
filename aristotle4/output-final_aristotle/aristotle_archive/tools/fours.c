/* How many cells holding `4` separate the head from the frontier?

   A `4` stops a left-moving cascade in either mode, so a single `4` strictly
   between the frontier (the leftmost `1`) and the head is enough to guarantee
   that a cascade starting at the head cannot reach the frontier.  This program
   maintains that count at every step and reports

     * its distribution at the birth of every cascade (the first step at which
       the head arrives moving left in state `A`, the head being strictly right
       of the frontier), and
     * how often it is zero while the head is in state `A` at distance at least
       two from the frontier, i.e. how often the machine is in a position where
       a cascade, if it started, would be unobstructed.

   Unverified helper.  Usage: ./fours <step-limit> */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  long long LIMIT = atoll(argv[1]);
  int N = 4000;
  unsigned char *tape = calloc(N, 1);
  int W[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
  int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
  int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};
  int pos = N / 2, st = 0, m = -1;
  long long steps = 0;
  int inCascade = 0, cnt4 = 0;
  long long births = 0, hist[8] = {0};
  int minbirth = 1 << 30;
  long long zeroA = 0, lastzero = -1;
  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    if (st == 0 && m >= 0 && pos >= m + 2 && cnt4 == 0) { zeroA++; lastzero = steps; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    if (!inCascade && ns == 0 && d == -1 && m >= 0 && pos > m) {   /* a cascade is born */
      births++;
      hist[cnt4 < 7 ? cnt4 : 7]++;
      if (cnt4 < minbirth) minbirth = cnt4;
      inCascade = 1;
    }
    if (ns == 0 && d == 1) inCascade = 0;
    int oldpos = pos;
    tape[pos] = w;
    if (d == 1) { if (w == 4) cnt4++; pos++; }
    else { pos--; if (pos >= 0 && tape[pos] == 4) cnt4--; }
    st = ns; steps++;
    if (w == 1 && (m < 0 || oldpos < m)) {      /* the frontier moves left */
      m = oldpos;
      cnt4 = 0;
      for (int i = m + 1; i < pos; i++) if (tape[i] == 4) cnt4++;
    }
  }
  printf("steps=%lld  cascade births=%lld\n", LIMIT, births);
  for (int c = 0; c < 8; c++)
    if (hist[c]) printf("  %d%s fours between frontier and head at birth: %lld\n",
                        c, c == 7 ? "+" : "", hist[c]);
  printf("minimum at a cascade birth: %d\n", minbirth);
  printf("A-steps at distance >= 2 with no four in between: %lld (last at step %lld)\n",
         zeroA, lastzero);
  return 0;
}
