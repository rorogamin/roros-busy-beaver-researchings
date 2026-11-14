/* Check the left-mover shield invariant on the target machine.
 *
 * A configuration is a "left mover" if the next transition moves left:
 *   A on 3, or B on 0/1/2.
 *
 * Shielded means: scanning left from the head, a 4 is met before any 1.
 * This is the hypothesis needed by cascade_dies_before_four and it excludes
 * the two pre-halt shapes A on 3 with a 1 immediately left and B on 1 with a 1
 * immediately left.
 *
 * Usage: ./leftshield STEPS [DUMP]
 */
#include <stdio.h>
#include <stdlib.h>

static const int W[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
static const int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static const int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};

int main(int argc, char **argv) {
  long long LIMIT = argc > 1 ? atoll(argv[1]) : 1000000000LL;
  int N = 4000;
  unsigned char *tape = calloc(N, 1);
  int pos = N / 2, st = 0;
  long long steps = 0;
  long long leftA3 = 0, leftB = 0, violA3 = 0, violB = 0;
  long long b1 = 0, b1left1 = 0, violDeep = 0;
  long long firstViol = -1, firstB1left1 = -1;
  int firstSt = -1, firstSym = -1, firstPos = 0;
  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) {
      printf("HALT %lld\n", steps);
      return 0;
    }
    int left = (st == 0 && s == 3) || (st == 1 && (s == 0 || s == 1 || s == 2));
    if (st == 0 && s == 3) {
      int seen4 = 0, bad = 0, fourPos = -1;
      for (int i = pos - 1; i >= 0; i--) {
        if (tape[i] == 1) { if (!seen4) bad = 1; break; }
        if (tape[i] == 4) { seen4 = 1; fourPos = i; break; }
      }
      if (!seen4) bad = 1;
      int deep = 0;
      for (int j = 0; j < fourPos; j++) if (tape[j]) { deep = 1; break; }
      leftA3++;
      if (bad) violA3++;
      if (!bad && !deep) violDeep++;
      if (bad && firstViol < 0) { firstViol = steps; firstSt = st; firstSym = s; firstPos = pos; }
    }
    if (st == 1 && s == 1) {
      b1++;
      if (pos > 0 && tape[pos - 1] == 1) {
        b1left1++;
        if (firstB1left1 < 0) firstB1left1 = steps;
      }
    }
    if (st == 1 && (s == 0 || s == 1 || s == 2)) leftB++;
    int ns = S[st][s];
    tape[pos] = W[st][s];
    pos += D[st][s];
    st = ns;
    steps++;
  }
  printf("steps=%lld  A3_left=%lld violA3=%lld deepViol=%lld  B_left=%lld  B1=%lld B1_left1=%lld\n",
         steps, leftA3, violA3, violDeep, leftB, b1, b1left1);
  if (firstViol >= 0)
    printf("first A3 violation at step %lld: state %c on symbol %d, pos %d\n",
           firstViol, firstSt ? 'B' : 'A', firstSym, firstPos);
  if (firstB1left1 >= 0)
    printf("first B1 with immediate left 1 at step %lld\n", firstB1left1);
  if (argc > 2) {
    FILE *f = fopen(argv[2], "w");
    for (int i = 0; i < N; i++) fputc('0' + tape[i], f);
    fputc('\n', f);
    fclose(f);
  }
  return 0;
}
