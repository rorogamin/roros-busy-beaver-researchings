/* How much of the computation is covered by the marker-increment rule
 * (`TM2x5.marker_increment`)?
 *
 * A marker event is the transition B3 -> 4RA: the head, sweeping back to the
 * left in state B, meets a cell holding 3.  The rule applies when the cells to
 * the right of the marker read
 *
 *     p0  (4 4)^k  4 2 ...
 *
 * with p0 either `4 4` or `4 2` -- i.e. when the region really is a binary
 * counter at two cells per digit (`4 2` = 0, `4 4` = 1) with a carry chain of
 * length k.  We count the events that match, the carry lengths, and the number
 * of machine steps the rule accounts for (4k + 13 per matching event).
 *
 *   gcc -O2 -o markerstats markerstats.c
 *   ./markerstats <steps>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define N 4000
static unsigned char tape[N];

static const int wr[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
static const int mv[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static const int ns[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};

int main(int argc, char **argv) {
  long long limit = argc > 1 ? atoll(argv[1]) : 100000000LL;
  int pos = N / 2, st = 0, hi = pos;
  long long steps = 0;
  long long events = 0, matched = 0, covered = 0;
  long long carry[64];
  long long shape[25][5];
  memset(carry, 0, sizeof carry);
  memset(shape, 0, sizeof shape);
  memset(tape, 0, sizeof tape);

  while (steps < limit) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT at %lld\n", steps); return 0; }
    if (st == 1 && s == 3) {           /* a marker event */
      events++;
      int i = pos + 1, ok = 1;
      /* the lowest digit */
      if (i + 1 > hi || tape[i] != 4 || (tape[i + 1] != 2 && tape[i + 1] != 4))
        ok = 0;
      i += 2;
      int k = 0;
      while (ok && i + 1 <= hi && tape[i] == 4 && tape[i + 1] == 4) { k++; i += 2; }
      if (ok && (i + 1 > hi || tape[i] != 4 || tape[i + 1] != 2)) ok = 0;
      if (!ok) {
        int a = pos + 1 <= hi ? tape[pos + 1] : 0;
        int b = pos + 2 <= hi ? tape[pos + 2] : 0;
        shape[a * 5 + b >= 25 ? 24 : a][b]++;
      }
      if (ok) {
        matched++;
        covered += 4LL * k + 13;
        carry[k < 63 ? k : 63]++;
      }
    }
    tape[pos] = wr[st][s];
    int nst = ns[st][s];
    pos += mv[st][s];
    st = nst;
    steps++;
    if (pos > hi) hi = pos;
    if (pos < 2 || pos > N - 2) { printf("tape overflow\n"); return 1; }
  }
  printf("steps %lld\n", steps);
  printf("marker events %lld, of which the rule applies to %lld (%.4f)\n", events,
         matched, events ? (double)matched / events : 0.0);
  printf("steps covered by the rule: %lld (%.4f of all steps)\n", covered,
         (double)covered / steps);
  printf("first two cells right of a non-matching marker:\n");
  for (int a = 0; a < 5; a++)
    for (int b = 0; b < 5; b++)
      if (shape[a][b]) printf("  %d %d : %lld\n", a, b, shape[a][b]);
  printf("carry length histogram:\n");
  for (int i = 0; i < 64; i++)
    if (carry[i]) printf("  %2d : %lld\n", i, carry[i]);
  return 0;
}
