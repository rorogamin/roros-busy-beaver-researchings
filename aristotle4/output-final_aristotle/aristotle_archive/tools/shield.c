/* What stops each cascade?

   A left-moving cascade is the head in state `A` arriving from the right.  It
   continues over a `3` (either mode) and over a `0` (mode `P`), and it stops on
   a `2` (mode `P`), a `0` (mode `Q`) or a `4` (either mode); on a `1` the
   machine halts.  The mode is read off the cell to the right of the head:
   `2` = mode `P`, `3` = mode `Q`.

   Only two transitions ever write a `4`: `B2 -> 4LB` (the returning sweep
   crossing a `2`) and `B3 -> 4RA` (a marker event: the marker is turned into a
   `4` and an outward pass starts).  For every cascade death this program
   records the stopping symbol, the mode, the length of the cascade in cells
   and, for a `4`, which rule wrote it.

   Unverified helper.  Usage: ./shield <step-limit> */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  long long LIMIT = atoll(argv[1]);
  int N = 4000;
  unsigned char *tape = calloc(N, 1);
  char *orig = calloc(N, 1);          /* 'b' = written by B2, 'm' = written by B3 */
  int W[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
  int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
  int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};
  int pos = N / 2, st = 0, m = -1;
  long long steps = 0;
  int arrivedLeftInA = 0;
  int cstart = -1;
  long long deaths[5][2] = {{0}};     /* [symbol][mode 0=P,1=Q] */
  long long deaths4[2] = {0, 0};      /* a 4 written by B2 / by B3 */
  long long longdeaths[5] = {0};      /* cascades of >= 5 cells */
  long long long4[2] = {0, 0};
  int closest = 1 << 30;
  char closest_by = '?';
  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    if (arrivedLeftInA) {
      int right = (pos + 1 < N) ? tape[pos + 1] : 0;
      int mode = (right == 3) ? 1 : 0;
      int stop = (s == 4) || (s == 2 && mode == 0) || (s == 0 && mode == 1);
      if (stop) {
        int len = cstart >= 0 ? cstart - pos : 0;
        deaths[s][mode]++;
        if (len >= 5) longdeaths[s]++;
        if (s == 4) {
          int i = (orig[pos] == 'b') ? 0 : 1;
          deaths4[i]++;
          if (len >= 5) long4[i]++;
        }
        if (len >= 5)
          printf("  long cascade t=%lld start=%d stop=%d sym=%d mode=%c orig=%c\n",
                 steps, cstart - m, pos - m, s, mode ? 'Q' : 'P',
                 orig[pos] ? orig[pos] : '-');
        if (m >= 0 && len >= 5 && pos - m < closest) {
          closest = pos - m;
          closest_by = (s == 4) ? orig[pos] : ('0' + s);
        }
        cstart = -1;
      }
    }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    if (cstart < 0 && ns == 0 && d == -1) cstart = pos;
    if (w == 4) orig[pos] = (st == 1 && s == 2) ? 'b' : 'm';
    else if (w != tape[pos]) orig[pos] = 0;
    int oldpos = pos;
    tape[pos] = w; pos += d; st = ns; steps++;
    arrivedLeftInA = (ns == 0 && d == -1);
    if (w == 1 && (m < 0 || oldpos < m)) m = oldpos;
  }
  printf("steps=%lld\n", LIMIT);
  for (int s = 0; s < 5; s++)
    for (int mo = 0; mo < 2; mo++)
      if (deaths[s][mo])
        printf("cascade stopped by symbol %d in mode %c: %lld (of which >=5 cells: %lld)\n",
               s, mo ? 'Q' : 'P', deaths[s][mo], longdeaths[s]);
  printf("stopping 4 written by the sweep B2: %lld (>=5 cells: %lld)\n", deaths4[0], long4[0]);
  printf("stopping 4 written by a marker event B3: %lld (>=5 cells: %lld)\n",
         deaths4[1], long4[1]);
  printf("closest stop of a cascade of >=5 cells to the frontier: %d cells, symbol/origin '%c'\n",
         closest, closest_by);
  return 0;
}
