/*
 * fastsim.c -- fast exact simulator for the TM 1RB---3RA2LA2RB_2LB3LA4LB4RA0RA
 * started on the blank tape.
 *
 * Unverified helper (not a Lean proof).  It uses exactly one macro rule, the
 * "drain" (base-3 counter + token-word exhaustion), whose correctness is proved
 * in Lean (Accel/Exhaust.lean, Accel/Drain.lean); every other transition is
 * executed literally.  All step counts are exact (GMP integers).
 *
 * GMP headers are not installed here, so the few needed prototypes are declared
 * by hand.  Build:  gcc -O2 -o fastsim fastsim.c -l:libgmp.so.10
 *
 * Usage: ./fastsim MAXDIGITS [SECONDS] [DUMPFILE]
 *   runs until the step count has more than MAXDIGITS decimal digits (or the
 *   time limit), printing one line per new decimal digit of the step count.
 *   DUMPFILE, if given, receives the final tape.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef struct { int alloc; int size; unsigned long *d; } mpz_s;
typedef mpz_s mpz_t[1];
void __gmpz_init(mpz_t);
void __gmpz_set_ui(mpz_t, unsigned long);
void __gmpz_set(mpz_t, const mpz_t);
void __gmpz_add(mpz_t, const mpz_t, const mpz_t);
void __gmpz_add_ui(mpz_t, const mpz_t, unsigned long);
void __gmpz_sub_ui(mpz_t, const mpz_t, unsigned long);
void __gmpz_mul_ui(mpz_t, const mpz_t, unsigned long);
void __gmpz_mul_2exp(mpz_t, const mpz_t, unsigned long);
unsigned long __gmpz_fdiv_q_ui(mpz_t, const mpz_t, unsigned long);
int __gmpz_set_str(mpz_t, const char *, int);
char *__gmpz_get_str(char *, int, const mpz_t);
size_t __gmpz_sizeinbase(const mpz_t, int);
int __gmpz_cmp_ui(const mpz_t, unsigned long);
int __gmpz_cmp(const mpz_t, const mpz_t);
void __gmpz_sub(mpz_t, const mpz_t, const mpz_t);
unsigned long __gmpz_get_ui(const mpz_t);
void __gmpz_addmul_ui(mpz_t, const mpz_t, unsigned long);
void __gmpz_ui_pow_ui(mpz_t, unsigned long, unsigned long);
static mpz_t T;             /* total steps */
static int exact = 0; static mpz_t TARGET;
static uint64_t budget = UINT64_MAX;  /* literal steps allowed before hitting TARGET */
static void set_budget(void) {
  if (!exact) return;
  static mpz_t d; static int i = 0; if (!i) { __gmpz_init(d); i = 1; }
  __gmpz_sub(d, TARGET, T);
  if (__gmpz_sizeinbase(d, 2) < 62) budget = __gmpz_get_ui(d); else budget = UINT64_MAX;
}

/* transition table: write, move, next state.  A = 0, B = 1. */
static const int TW[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
static const int TM[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static const int TQ[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};

static unsigned char *a;
static long CELLS;
static long p, lo, hi;
static int q;
static uint64_t litpend;    /* literal steps not yet added to T */

static inline int isdig(int s) { return s == 3 || s == 4 || s == 0; }
static inline int dval(int s) { return s == 3 ? 0 : (s == 4 ? 1 : 2); }
static const unsigned char DSYM[3] = {3, 4, 0};

static long *tokpos; static unsigned char *toktype; /* 0 = two, else 10 + second symbol */
static unsigned char *ed1, *ed2;                    /* pending new symbols per token */
static char *sbuf, *sbuf2;

static uint64_t ndrain, nlit, nnogrow, nA3inside;
static long cb = 0;            /* right end of the main counter (first token cell at the last main drain) */
static long minCb = 1L << 60;  /* min over A-reading-3 of (p - cb), current decade */
static long minCball = 1L << 60;
static long minA3d = 1L << 60;      /* min over A-reading-3 of (p - lo), current decade */
static long minA3dall = 1L << 60;

static void add_i128(mpz_t z, __int128 v) {
  static mpz_t w; static int i = 0; if (!i) { __gmpz_init(w); i = 1; }
  int neg = v < 0; unsigned __int128 u = neg ? (unsigned __int128)(-v) : (unsigned __int128)v;
  __gmpz_set_ui(w, (unsigned long)(u >> 64)); __gmpz_mul_2exp(w, w, 64);
  __gmpz_add_ui(w, w, (unsigned long)(u & 0xFFFFFFFFFFFFFFFFULL));
  if (neg) __gmpz_sub(z, z, w); else __gmpz_add(z, z, w);
}

/* try a drain at the current configuration (state A).  Returns 1 if applied. */
static int try_drain(void) {
  long i = p - 1;
  while (i > lo && isdig(a[i])) i--;
  if (i == p - 1 || a[i] != 1) return 0;
  long m = p - 1 - i;
  long j = p, nt = 0;
  for (;;) {
    if (j + 2 >= CELLS) { fprintf(stderr, "tape overflow right\n"); exit(2); }
    if (a[j] == 2) { tokpos[nt] = j; toktype[nt] = 0; nt++; j++; }
    else if (a[j] == 4 && (a[j+1] == 0 || a[j+1] == 2 || a[j+1] == 3 || a[j+1] == 4)) {
      tokpos[nt] = j; toktype[nt] = 10 + a[j+1]; nt++; j += 2;
    } else break;
  }
  if (nt == 0) return 0;
  static mpz_t c, tt, tmp, N; static int init = 0;
  if (!init) { __gmpz_init(c); __gmpz_init(tt); __gmpz_init(tmp); __gmpz_init(N); init = 1; }
  uint64_t cs = 0, ts = 0; int big = 0;
  for (long k = nt - 1; k >= 0; k--) {
    int ty = toktype[k];
    if (!big && (cs > (1ULL << 58) || ts > (1ULL << 60))) {
      big = 1; __gmpz_set_ui(c, cs); __gmpz_set_ui(tt, ts);
    }
    if (!big) {
      if (ty == 0) { uint64_t qq = cs / 3, r = cs % 3; ed1[k] = DSYM[r]; ts += 4 * qq + 1 + r; cs = qq; }
      else {
        int s = ty - 10; uint64_t cap;
        if (s == 0) cap = 2 * cs + 2; else if (s == 2) cap = 2 * cs + 1;
        else if (s == 4) cap = 2 * cs; else cap = cs >= 1 ? 2 * cs - 2 : 0;
        ed1[k] = 2; ed2[k] = (s == 3 && cs == 0) ? 4 : 0;
        ts += 3 * cap + cs + 2; cs = cap;
      }
    } else if (ty != 0) {
      /* a run of pair tokens, processed in chunks of up to 56 with one big-number update */
      long j0 = k; int jn = 0; __int128 A = 0, D = 0;
      while (k >= 0 && toktype[k] != 0 && jn < 56) {
        int s = toktype[k] - 10;
        long dl = s == 0 ? 2 : (s == 2 ? 1 : (s == 3 ? -2 : 0));
        __int128 An = 2 * A + dl;
        D += A + 3 * An + 2;
        A = An; ed1[k] = 2; ed2[k] = 0; jn++; k--;
      }
      k++;  /* the for-loop decrements again */
      (void)j0;
      /* tt += c * 7 (2^jn - 1) + D ;  c = c 2^jn + A */
      __gmpz_addmul_ui(tt, c, 7UL * ((1UL << jn) - 1));
      add_i128(tt, D);
      __gmpz_mul_2exp(c, c, jn);
      add_i128(c, A);
    } else {
      if (ty == 0) {
        unsigned long r = __gmpz_fdiv_q_ui(tmp, c, 3);
        ed1[k] = DSYM[r];
        __gmpz_add_ui(tt, tt, 1 + r);
        __gmpz_set(c, tmp);
        __gmpz_mul_2exp(tmp, tmp, 2);
        __gmpz_add(tt, tt, tmp);
      } else {
        int s = ty - 10;               /* c > 2^58 here: no small special cases */
        __gmpz_add(tt, tt, c); __gmpz_add_ui(tt, tt, 2);
        __gmpz_mul_2exp(c, c, 1);
        if (s == 0) __gmpz_add_ui(c, c, 2); else if (s == 2) __gmpz_add_ui(c, c, 1);
        else if (s == 3) __gmpz_sub_ui(c, c, 2);
        ed1[k] = 2; ed2[k] = 0;
        __gmpz_mul_ui(tmp, c, 3); __gmpz_add(tt, tt, tmp);
      }
    }
  }
  if (!big) { __gmpz_set_ui(c, cs); __gmpz_set_ui(tt, ts); }
  long s0 = 0;
  for (long x = 0; x < m; x++) { int d = dval(a[i + 1 + x]); sbuf[x] = '0' + d; s0 += d; }
  sbuf[m] = 0;
  __gmpz_set_str(N, sbuf, 3);
  __gmpz_add(N, N, c);
  long m2;
  if (__gmpz_cmp_ui(N, 0) == 0) { m2 = 0; sbuf2[0] = 0; }
  else { __gmpz_get_str(sbuf2, 3, N); m2 = (long)strlen(sbuf2); }
  long mn = m2 > m ? m2 : m;
  if (mn > m) {
    for (long x = p - mn - 1; x <= i - 1; x++)
      if (x < 1 || a[x] != 0) { nnogrow++; return 0; }
  }
  if (exact) {
    static mpz_t chk; static int ci = 0; if (!ci) { __gmpz_init(chk); ci = 1; }
    __gmpz_add(chk, T, tt); __gmpz_add(chk, chk, c); __gmpz_add(chk, chk, c);
    long dl = s0 + 2 * (mn - m);  /* upper bound on the extra term */
    __gmpz_add_ui(chk, chk, (unsigned long)dl);
    if (__gmpz_cmp(chk, TARGET) > 0) return 0;   /* conservative: might overshoot */
  }
  if (i == lo) cb = p;
  /* commit */
  for (long k = 0; k < nt; k++) {
    a[tokpos[k]] = ed1[k];
    if (toktype[k]) a[tokpos[k] + 1] = ed2[k];
  }
  long s1 = 0, pad = mn - m2;
  for (long x = 0; x < mn; x++) {
    int d = x < pad ? 0 : sbuf2[x - pad] - '0';
    s1 += d;
    a[p - mn + x] = DSYM[d];
  }
  a[p - mn - 1] = 1;
  if (p - mn - 1 < lo) lo = p - mn - 1;
  __gmpz_add(tt, tt, c); __gmpz_add(tt, tt, c);
  long delta = s0 - s1 + 2 * (mn - m);
  if (delta >= 0) __gmpz_add_ui(tt, tt, (unsigned long)delta);
  else __gmpz_sub_ui(tt, tt, (unsigned long)(-delta));
  __gmpz_add(T, T, tt);
  p = j; q = 0;
  if (p > hi) hi = p;
  ndrain++;
  return 1;
}

int main(int argc, char **argv) {
  long maxdig = argc > 1 ? atol(argv[1]) : 100;
  double maxsec = argc > 2 ? atof(argv[2]) : 1e18;
  const char *dump = argc > 3 ? argv[3] : NULL;
  if (argc > 4) { exact = 1; __gmpz_init(TARGET); __gmpz_ui_pow_ui(TARGET, 10, atol(argv[4])); }
  CELLS = 200000000L;
  a = calloc(CELLS, 1);
  tokpos = malloc(sizeof(long) * (CELLS / 2));
  toktype = malloc(CELLS / 2); ed1 = malloc(CELLS / 2); ed2 = malloc(CELLS / 2);
  sbuf = malloc(CELLS / 2); sbuf2 = malloc(CELLS / 2);
  if (!a || !tokpos || !toktype || !ed1 || !ed2 || !sbuf || !sbuf2) { fprintf(stderr, "alloc\n"); return 1; }
  p = lo = hi = CELLS / 2; q = 0;
  long origin = p;
  __gmpz_init(T);
  set_budget();
  time_t start = time(NULL);
  long lastdig = 0;
  int halted = 0;
  for (;;) {
    if (q == 0 && isdig(a[p - 1]) && (a[p] == 2 || a[p] == 4)) {
      if (litpend) { __gmpz_add_ui(T, T, litpend); litpend = 0; }
      if (try_drain()) {
        set_budget();
        long dig = (long)__gmpz_sizeinbase(T, 10);
        if (dig > lastdig) {
          lastdig = dig;
          printf("digits~%ld drains=%llu lit=%llu nogrow=%llu lo=%ld hi=%ld width=%ld p=%ld minA3(decade)=%ld minA3(all)=%ld A3-cb(decade)=%ld A3-cb(all,after 1000 drains)=%ld A3inside=%llu sec=%ld\n",
                 dig, (unsigned long long)ndrain, (unsigned long long)nlit,
                 (unsigned long long)nnogrow, lo - origin, hi - origin,
                 hi - lo, p - origin, minA3d, minA3dall, minCb, minCball, (unsigned long long)nA3inside, (long)(time(NULL) - start));
          fflush(stdout);
          minA3d = 1L << 60; minCb = 1L << 60;
          if (dig > maxdig) break;
        }
        if ((ndrain & 15) == 0 && difftime(time(NULL), start) > maxsec) break;
        continue;
      }
    }
    if (exact && budget == 0) break;
    for (;;) {
      if (budget == 0) break;
      int s = a[p];
      if (q == 0) {
        if (s == 1) { halted = 1; break; }
        if (s == 3) { long d = p - lo; if (d < minA3d) minA3d = d; if (d < minA3dall) minA3dall = d;
          long e = p - cb; if (e < minCb) minCb = e; if (ndrain > 1000 && e < minCball) minCball = e; if (e < 0) { nA3inside++; if (getenv("LOGIN")) { fprintf(stderr, "INSIDE drains=%llu depth=%ld lo-dist=%ld low:", (unsigned long long)ndrain, -e, p - lo); for (long z = cb - 1; z >= cb - 16; z--) fputc(48 + a[z], stderr); fputc(10, stderr);} } }
      }
      a[p] = TW[q][s]; p += TM[q][s]; q = TQ[q][s];
      litpend++; nlit++; if (budget != UINT64_MAX) budget--;
      if (p < lo) lo = p;
      if (p > hi) hi = p;
      if (q == 0 && isdig(a[p - 1]) && (a[p] == 2 || a[p] == 4)) break;
    }
    if (halted) break;
    if (p < 2 || p > CELLS - 4) { fprintf(stderr, "tape bound\n"); return 2; }
  }
  if (litpend) { __gmpz_add_ui(T, T, litpend); litpend = 0; }
  char *ts = __gmpz_get_str(NULL, 10, T);
  long tl = (long)strlen(ts);
  if (halted) printf("HALT: state A reads 1 after %s steps\n", ts);
  printf("final: steps has %ld digits, leading %.30s, drains=%llu lit=%llu width=%ld state=%c head=%ld\n",
         tl, ts, (unsigned long long)ndrain, (unsigned long long)nlit, hi - lo, q ? 'B' : 'A', p - origin);
  if (dump) {
    FILE *f = fopen(dump, "w");
    fprintf(f, "{\"t\":\"%s\",\"q\":%d,\"p\":%ld,\"lo\":%ld,\"hi\":%ld,\"tape\":\"", ts, q, p - origin, lo - origin, hi - origin);
    for (long x = lo; x <= hi; x++) fputc('0' + a[x], f);
    fprintf(f, "\"}\n");
    fclose(f);
  }
  return 0;
}
