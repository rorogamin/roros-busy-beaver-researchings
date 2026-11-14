/* Per-round-trip statistics of 1RB---3RA2LA2RB_2LB3LA4LB4RA0RA on the blank
 * tape.  A "round trip" is the stretch between two successive arrivals of the
 * head from the right, in state B, on the least significant digit of the
 * ternary counter (the same event as in region.py / tripstats.py).
 *
 * For every trip we record how far to the right of the counter the head got
 * and how many steps the trip took, and we print a histogram of the reach plus
 * every new record.
 *
 *   gcc -O2 -o tripstats tripstats.c
 *   ./tripstats <steps>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define N 4000
static unsigned char tape[N];

/* transition table: (write, move, next state), state 0 = A, 1 = B */
static const int wr[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
static const int mv[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static const int ns[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};

static int isdigit_cell(int c) { return c == 3 || c == 4 || c == 0; }

int main(int argc, char **argv) {
  long long limit = argc > 1 ? atoll(argv[1]) : 100000000LL;
  int pos = N / 2, st = 0, prev = pos, m = -1;
  long long steps = 0, t0 = 0, trips = 0;
  int base = -1, reach = 0, hi = pos;
  int recreach = 0;
  long long recsteps = 0;
  long long hist[256];
  memset(hist, 0, sizeof hist);
  memset(tape, 0, sizeof tape);

  while (steps < limit) {
    /* counter visit? */
    if (m >= 0 && st == 1 && prev == pos + 1 && pos - m <= 80) {
      int ok = 1;
      for (int i = m + 1; i <= pos; i++)
        if (!isdigit_cell(tape[i])) { ok = 0; break; }
      if (ok) {
        if (base >= 0) {
          int r = reach - base;
          long long d = steps - t0;
          trips++;
          hist[r < 255 ? r : 255]++;
          if (r > recreach) {
            recreach = r;
            printf("t=%lld trip=%lld new reach record %d (steps %lld, "
                   "right end %d cells away)\n",
                   steps, trips, r, d, hi - base);
            fflush(stdout);
          }
          if (d > recsteps) {
            recsteps = d;
            printf("t=%lld trip=%lld new length record %lld steps (reach %d)\n",
                   steps, trips, d, r);
            fflush(stdout);
          }
        }
        base = pos;
        reach = pos;
        t0 = steps;
      }
    }
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT at %lld\n", steps); return 0; }
    prev = pos;
    tape[pos] = wr[st][s];
    int nst = ns[st][s];
    pos += mv[st][s];
    st = nst;
    steps++;
    if (pos > hi) hi = pos;
    if (pos > reach) reach = pos;
    if (tape[prev] == 1 && (m < 0 || prev < m)) m = prev;
    if (pos < 2 || pos > N - 2) { printf("tape overflow\n"); return 1; }
  }
  printf("no halt in %lld steps; %lld trips; width %d\n", steps, trips,
         hi - m);
  printf("reach histogram (cells right of the counter):\n");
  for (int i = 0; i < 256; i++)
    if (hist[i]) printf("  %3d : %lld\n", i, hist[i]);
  return 0;
}
