/* Is the ternary counter Cantor-compatible at the moments a cascade is born?

   A cascade that reaches the counter crosses it, and so halts the machine,
   exactly when the counter cells it meets contain no `4` (digit 1) and no two
   consecutive `0`s (two consecutive digits 2) -- `cross_digits_iff` in
   RequestProject/Counter.lean.  The counter is incremented once per round trip,
   so it takes Cantor-compatible values infinitely often; but the condition is
   only ever *tested* at the rare moments a cascade is born.

   This program records, at every cascade birth, the counter word (the maximal
   run of digit cells 3/4/0 immediately to the right of the frontier), its
   value, whether it is Cantor-compatible, and how many digits `1` it has.

   A cascade is a maximal left-moving run of state-A steps.  Beware: while
   crossing a digit `2` in mode `Q` the machine performs `A2 -> 3RA`, a
   *right-moving* A step, so a naive "left-moving A step" flag counts one
   cascade many times.  Here the end of a cascade is detected explicitly, by
   the three ways a cascade can stop:

     - it arrives on a cell holding 4 (either mode),
     - it arrives on a cell holding 0 with a 3 to its right (mode Q),
     - it arrives on a cell holding 2 with a 2 to its right (mode P),

   and a new birth is only recorded after the previous cascade has ended.

   Unverified helper.  Usage: ./cantor <step-limit> */
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
  int inCascade = 0, arrived = 0;
  long long births = 0, cantor_ok = 0, blocked_by_four = 0, blocked_by_zeros = 0;
  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    int w = W[st][s], d = D[st][s], ns = S[st][s];
    int leftA = (ns == 0 && d == -1);
    if (inCascade && arrived) {
      /* the head has just arrived on this cell moving left: has the cascade
         come to an end here? */
      int q = tape[pos + 1];
      if (s == 4 || (s == 0 && q == 3) || (s == 2 && q == 2)) inCascade = 0;
    }
    if (!inCascade && leftA && m >= 0 && pos > m) {   /* a cascade is born */
      /* the counter word: cells m+1, m+2, ... while they are digits 3, 4, 0 */
      int end = m + 1;
      while (end < N && (tape[end] == 3 || tape[end] == 4 || tape[end] == 0)) end++;
      double val = 0.0;               /* cell m+1 is the most significant digit */
      int digits = end - (m + 1);
      int ones = 0, hasfour = 0, haszeros = 0;
      for (int i = m + 1; i < end; i++) {
        int dg = (tape[i] == 3) ? 0 : (tape[i] == 4) ? 1 : 2;
        val = val * 3 + dg;
        if (dg == 1) { ones++; hasfour = 1; }
        if (i + 1 < end && tape[i] == 0 && tape[i + 1] == 0) haszeros = 1;
      }
      births++;
      if (!hasfour && !haszeros) cantor_ok++;
      else if (hasfour) blocked_by_four++;
      else blocked_by_zeros++;
      printf("birth t=%lld dist=%d digits=%d ones=%d value=%.10g cantor=%s%s%s\n",
             steps, pos - m, digits, ones, val,
             (!hasfour && !haszeros) ? "YES" : "no",
             hasfour ? " (digit 1 present)" : "",
             (!hasfour && haszeros) ? " (two consecutive digits 2)" : "");
      inCascade = 1;
    }
    int oldpos = pos;
    arrived = (d == -1 && ns == 0);
    tape[pos] = w; pos += d; st = ns; steps++;
    if (w == 1 && (m < 0 || oldpos < m)) m = oldpos;
  }
  printf("steps=%lld  cascades=%lld\n", LIMIT, births);
  printf("  counter Cantor-compatible at birth: %lld\n", cantor_ok);
  printf("  blocked by a digit 1: %lld\n", blocked_by_four);
  printf("  blocked by two consecutive digits 2 (and no digit 1): %lld\n", blocked_by_zeros);
  return 0;
}
