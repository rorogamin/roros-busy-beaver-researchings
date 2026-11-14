/* Dump the left context at every A3 birth (and every B1 visit) of
 * 1RB---3RA2LA2RB_2LB3LA4LB4RA0RA.
 *
 * Usage: ./a3context STEPS [OUTFILE]
 *
 * For A3 the output line is:
 *   A3 <step> <pos> <d4> <d1> <left-prefix>
 * where d4/d1 are distances from the head to the nearest 4/1 scanning left,
 * and the prefix is nearest-first, up to 80 cells.  For B1:
 *   B1 <step> <pos> <left-prefix>
 */
#include <stdio.h>
#include <stdlib.h>

static const int W[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
static const int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static const int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};

static int make_prefix(const unsigned char *tape, int pos, char *buf, int cap) {
  int k = 0;
  for (int i = pos - 1; i >= 0 && k < cap - 1; i--) buf[k++] = (char)('0' + tape[i]);
  buf[k] = 0;
  return k;
}

int main(int argc, char **argv) {
  long long LIMIT = argc > 1 ? atoll(argv[1]) : 10000000000LL;
  int N = 20000;
  unsigned char *tape = calloc((size_t)N, 1);
  int pos = N / 2, st = 0;
  long long steps = 0, a3 = 0, b1 = 0, no4 = 0, no1 = 0, maxd4 = 0;
  long long hist[201] = {0};
  FILE *out = NULL;
  if (argc > 2) {
    out = fopen(argv[2], "w");
    if (!out) { perror("fopen"); return 1; }
  }
  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) {
      printf("HALT %lld\n", steps);
      if (out) fclose(out);
      return 0;
    }
    if (st == 0 && s == 3) {
      int d4 = -1, d1 = -1;
      for (int i = pos - 1; i >= 0; i--) {
        if (d4 < 0 && tape[i] == 4) d4 = pos - i;
        if (d1 < 0 && tape[i] == 1) d1 = pos - i;
        if (d4 >= 0 && d1 >= 0) break;
      }
      char pre[81];
      make_prefix(tape, pos, pre, (int)sizeof(pre));
      if (d4 < 0) no4++;
      if (d1 < 0) no1++;
      if (d4 > maxd4) maxd4 = d4;
      if (d4 >= 0 && d4 <= 200) hist[d4]++;
      if (out) fprintf(out, "A3 %lld %d %d %d %s\n", steps, pos, d4, d1, pre);
      a3++;
    }
    if (st == 1 && s == 1) {
      char pre[81];
      make_prefix(tape, pos, pre, (int)sizeof(pre));
      if (out) fprintf(out, "B1 %lld %d %s\n", steps, pos, pre);
      b1++;
    }
    int ns = S[st][s];
    tape[pos] = (unsigned char)W[st][s];
    pos += D[st][s];
    st = ns;
    steps++;
  }
  printf("steps=%lld A3=%lld no4=%lld no1=%lld maxd4=%lld B1=%lld\n",
         steps, a3, no4, no1, maxd4, b1);
  printf("d4 histogram (1..20):");
  for (int i = 1; i <= 20; i++) printf(" %lld", hist[i]);
  printf("\n");
  if (out) fclose(out);
  return 0;
}
