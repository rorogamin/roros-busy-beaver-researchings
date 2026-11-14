/* Track the next A3 after every margin-1 (4 1 boundary) A3 birth.
 * Usage: ./a3margin STEPS
 */
#include <stdio.h>
#include <stdlib.h>

static const int W[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
static const int D[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static const int S[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};

static void prefix(const unsigned char *tape, int pos, char *buf, int cap) {
  int k = 0;
  for (int i = pos - 1; i >= 0 && k < cap - 1; i--) buf[k++] = (char)('0' + tape[i]);
  buf[k] = 0;
}

int main(int argc, char **argv) {
  long long LIMIT = argc > 1 ? atoll(argv[1]) : 10000000000LL;
  int N = 20000;
  unsigned char *tape = calloc((size_t)N, 1);
  int pos = N / 2, st = 0;
  long long steps = 0, margin1 = 0, next = 0, next_deep = 0, next_margin1 = 0;
  long long pend_step = -1;
  char pend_pre[81] = {0};
  while (steps < LIMIT) {
    int s = tape[pos];
    if (st == 0 && s == 1) { printf("HALT %lld\n", steps); return 0; }
    if (st == 0 && s == 3) {
      int d4 = -1, d1 = -1;
      for (int i = pos - 1; i >= 0; i--) {
        if (d4 < 0 && tape[i] == 4) d4 = pos - i;
        if (d1 < 0 && tape[i] == 1) d1 = pos - i;
        if (d4 >= 0 && d1 >= 0) break;
      }
      char pre[81]; prefix(tape, pos, pre, (int)sizeof(pre));
      if (pend_step >= 0) {
        next++;
        int deep = (d4 >= 1 && d4 < 80 && d1 > d4);
        if (deep) next_deep++;
        if (d1 - d4 == 1) next_margin1++;
        printf("NEXT from=%lld to=%lld delta=%lld d4=%d d1=%d deep=%d pre=%s frompre=%s\n",
               pend_step, steps, steps - pend_step, d4, d1, deep, pre, pend_pre);
        pend_step = -1;
      }
      if (d4 > 0 && d1 - d4 == 1 && d4 < 80 && pre[d4 - 1] == '4' && pre[d4] == '1') {
        margin1++;
        pend_step = steps;
        snprintf(pend_pre, sizeof(pend_pre), "%s", pre);
      }
    }
    int ns = S[st][s];
    tape[pos] = (unsigned char)W[st][s];
    pos += D[st][s];
    st = ns;
    steps++;
  }
  printf("steps=%lld margin1=%lld next=%lld next_deep=%lld next_margin1=%lld pending=%lld\n",
         steps, margin1, next, next_deep, next_margin1, pend_step);
  return 0;
}
