/*
 * fastsim2.c -- faster exact simulator for 1RB---3RA2LA2RB_2LB3LA4LB4RA0RA
 * (blank tape).  Unverified helper, not a Lean proof.
 *
 * Same macro rule as fastsim.c (the drain, proved in Accel/Drain.lean); the
 * difference is purely in data representation: the main base-3 counter (the one
 * whose frontier 1 is the leftmost visited cell) is kept as a binary big number
 * N_hi between drains, and its low digits are written to the tape only when the
 * head actually walks into them ("materialization", 40 digits at a time).  This
 * removes the base-3 <-> binary conversions that dominated fastsim.c.
 *
 * Exact step count bookkeeping: the true step count is  Tacc - s3(N_hi)  where
 * s3 is the base-3 digit sum (see the comments at the update sites).
 *
 * Build:  gcc -O2 -o fastsim2 fastsim2.c -l:libgmp.so.10
 * Usage:  ./fastsim2 MAXDIGITS [SECONDS] [DUMPFILE]
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
void __gmpz_sub(mpz_t, const mpz_t, const mpz_t);
void __gmpz_add_ui(mpz_t, const mpz_t, unsigned long);
void __gmpz_sub_ui(mpz_t, const mpz_t, unsigned long);
void __gmpz_mul_ui(mpz_t, const mpz_t, unsigned long);
void __gmpz_mul(mpz_t, const mpz_t, const mpz_t);
void __gmpz_mul_2exp(mpz_t, const mpz_t, unsigned long);
void __gmpz_addmul_ui(mpz_t, const mpz_t, unsigned long);
unsigned long __gmpz_fdiv_q_ui(mpz_t, const mpz_t, unsigned long);
int __gmpz_set_str(mpz_t, const char *, int);
char *__gmpz_get_str(char *, int, const mpz_t);
size_t __gmpz_sizeinbase(const mpz_t, int);
int __gmpz_cmp(const mpz_t, const mpz_t);
int __gmpz_cmp_ui(const mpz_t, unsigned long);
void __gmpz_ui_pow_ui(mpz_t, unsigned long, unsigned long);

static const int TW[2][5] = {{1, -1, 3, 2, 2}, {2, 3, 4, 4, 0}};
static const int TM[2][5] = {{1, 0, 1, -1, 1}, {-1, -1, -1, 1, 1}};
static const int TQ[2][5] = {{1, 0, 0, 0, 1}, {1, 0, 1, 0, 0}};

static unsigned char *a;
static long CELLS, p, lo, hi;
static int q;
static mpz_t Tacc;
static uint64_t litpend;

static inline int isdig(int s) { return s == 3 || s == 4 || s == 0; }
static inline int dval(int s) { return s == 3 ? 0 : (s == 4 ? 1 : 2); }
static const unsigned char DSYM[3] = {3, 4, 0};

static long *tokpos; static unsigned char *toktype, *ed1, *ed2;
static char *sbuf, *sbuf2;
static uint64_t ndrain, nlazy, nlit, nnogrow, nmat, nfullmat, nA3inside;
static long minA3d = 1L << 60, minCb = 1L << 60, minCball = 1L << 60;

/* lazy main counter: cells F+1 .. matlo-1 hold the base-3 digits of Nhi (MSD at
   F+1); cells matlo .. are real.  F holds the frontier 1 (when lazy is valid). */
static int lazy = 0;
static long F = 0, matlo = 0, cb = 0;
static mpz_t Nhi;
#define LAZY_MIN 300

static inline int stale(long x) { return lazy && x > F && x < matlo; }
static inline int drain_point(void) {
  if (q != 0 || !(a[p] == 2 || a[p] == 4)) return 0;
  if (lazy && p == matlo) return 1;
  return !stale(p - 1) && isdig(a[p - 1]);
}

static void add_i128(mpz_t z, __int128 v) {
  static mpz_t w; static int i = 0; if (!i) { __gmpz_init(w); i = 1; }
  int neg = v < 0; unsigned __int128 u = neg ? (unsigned __int128)(-v) : (unsigned __int128)v;
  __gmpz_set_ui(w, (unsigned long)(u >> 64)); __gmpz_mul_2exp(w, w, 64);
  __gmpz_add_ui(w, w, (unsigned long)(u & 0xFFFFFFFFFFFFFFFFULL));
  if (neg) __gmpz_sub(z, z, w); else __gmpz_add(z, z, w);
}

/* write all remaining lazy digits to the tape */
static void materialize_full(void) {
  if (!lazy) return;
  long ms = matlo - F - 1;
  long s = 0;
  if (ms > 0) {
    long len = 0;
    if (__gmpz_cmp_ui(Nhi, 0) != 0) { __gmpz_get_str(sbuf2, 3, Nhi); len = (long)strlen(sbuf2); }
    if (len > ms) { fprintf(stderr, "lazy invariant broken\n"); exit(5); }
    for (long x = 0; x < ms; x++) {
      int d = x < ms - len ? 0 : sbuf2[x - (ms - len)] - '0';
      s += d; a[F + 1 + x] = DSYM[d];
    }
  }
  __gmpz_sub_ui(Tacc, Tacc, (unsigned long)s);   /* T = Tacc - s3(Nhi) stays invariant */
  __gmpz_set_ui(Nhi, 0);
  matlo = F + 1;
  lazy = 0;
  nfullmat++;
}

/* make the cells down to position target real */
static void materialize_until(long target) {
  while (lazy && matlo > target) {
    long ms = matlo - F - 1;
    if (ms <= 40 || matlo - target > 400) { materialize_full(); return; }
    unsigned long r = __gmpz_fdiv_q_ui(Nhi, Nhi, 12157665459056928801UL); /* 3^40 */
    long s = 0;
    for (int x = 0; x < 40; x++) { int d = r % 3; r /= 3; s += d; a[matlo - 1 - x] = DSYM[d]; }
    __gmpz_sub_ui(Tacc, Tacc, (unsigned long)s);
    matlo -= 40;
    nmat++;
  }
}

/* exhaustion recursion over the parsed tokens; leaves C in c and the time in tt */
static mpz_t c, tt, tmp, N, P3;
static void exhaust(long nt) {
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
      int jn = 0; __int128 A = 0, D = 0;
      while (k >= 0 && toktype[k] != 0 && jn < 56) {
        int s = toktype[k] - 10;
        long dl = s == 0 ? 2 : (s == 2 ? 1 : (s == 3 ? -2 : 0));
        __int128 An = 2 * A + dl;
        D += A + 3 * An + 2;
        A = An; ed1[k] = 2; ed2[k] = 0; jn++; k--;
      }
      k++;
      __gmpz_addmul_ui(tt, c, 7UL * ((1UL << jn) - 1));
      add_i128(tt, D);
      __gmpz_mul_2exp(c, c, jn);
      add_i128(c, A);
    } else {
      unsigned long r = __gmpz_fdiv_q_ui(tmp, c, 3);
      ed1[k] = DSYM[r];
      __gmpz_add_ui(tt, tt, 1 + r);
      __gmpz_set(c, tmp);
      __gmpz_mul_2exp(tmp, tmp, 2);
      __gmpz_add(tt, tt, tmp);
    }
  }
  if (!big) { __gmpz_set_ui(c, cs); __gmpz_set_ui(tt, ts); }
}

static long parse_tokens(long *jend) {
  long j = p, nt = 0;
  for (;;) {
    if (j + 2 >= CELLS) { fprintf(stderr, "tape overflow right\n"); exit(2); }
    if (a[j] == 2) { tokpos[nt] = j; toktype[nt] = 0; nt++; j++; }
    else if (a[j] == 4 && (a[j+1] == 0 || a[j+1] == 2 || a[j+1] == 3 || a[j+1] == 4)) {
      tokpos[nt] = j; toktype[nt] = 10 + a[j+1]; nt++; j += 2;
    } else break;
  }
  *jend = j;
  return nt;
}

static void commit_tokens(long nt) {
  for (long k = 0; k < nt; k++) {
    a[tokpos[k]] = ed1[k];
    if (toktype[k]) a[tokpos[k] + 1] = ed2[k];
  }
}

/* number of base-3 digits of N (N > 0) */
static long digits3(const mpz_t x) {
  if (__gmpz_cmp_ui(x, 0) == 0) return 0;
  long s = (long)__gmpz_sizeinbase(x, 3);
  __gmpz_ui_pow_ui(P3, 3, (unsigned long)(s - 1));
  if (__gmpz_cmp(x, P3) < 0) s--;
  return s;
}

static int try_drain(void) {
  long i = p - 1;
  long stop = lazy ? matlo : lo;   /* do not scan into stale cells */
  while (i >= stop && i > lo && isdig(a[i])) i--;
  int lazypath = 0;
  if (lazy && i < matlo) {
    if (a[F] != 1) { materialize_full(); return 0; }
    lazypath = 1;
  } else {
    if (i == p - 1 || a[i] != 1) return 0;
  }
  long jend; long nt = parse_tokens(&jend);
  if (nt == 0) return 0;
  exhaust(nt);
  if (lazypath) {
    /* N = Nhi * 3^(p - matlo) + value(cells matlo .. p-1) */
    long jlow = p - matlo; long slow = 0;
    __gmpz_set(N, Nhi);
    for (long x = matlo; x < p; x++) {
      int d = dval(a[x]); slow += d;
      __gmpz_mul_ui(N, N, 3); __gmpz_add_ui(N, N, (unsigned long)d);
    }
    (void)jlow;
    long m = p - 1 - F;
    __gmpz_add(N, N, c);
    long d3 = digits3(N);
    long mn = d3 > m ? d3 : m;
    if (mn > m) {
      for (long x = p - mn - 1; x <= F - 1; x++)
        if (x < 1 || a[x] != 0) { nnogrow++; return 0; }
    }
    commit_tokens(nt);
    /* true T += tt + 2C + 2(mn-m) + s(N) - s(N');  s(N) = s(Nhi) + slow; new Nhi = N'.
       With T = Tacc - s(Nhi):  Tacc += tt + 2C + 2(mn-m) + slow. */
    __gmpz_add(Tacc, Tacc, tt); __gmpz_add(Tacc, Tacc, c); __gmpz_add(Tacc, Tacc, c);
    __gmpz_add_ui(Tacc, Tacc, (unsigned long)(2 * (mn - m) + slow));
    F = p - mn - 1; a[F] = 1; if (F < lo) lo = F;
    matlo = p; cb = p;
    __gmpz_set(Nhi, N);
    p = jend; q = 0; if (p > hi) hi = p;
    ndrain++; nlazy++;
    return 1;
  }
  /* ordinary path: counter fully on the tape, frontier at i */
  long m = p - 1 - i;
  long s0 = 0;
  for (long x = 0; x < m; x++) { int d = dval(a[i + 1 + x]); sbuf[x] = '0' + d; s0 += d; }
  sbuf[m] = 0;
  __gmpz_set_str(N, sbuf, 3);
  __gmpz_add(N, N, c);
  long m2 = 0;
  if (__gmpz_cmp_ui(N, 0) != 0) m2 = digits3(N);
  long mn = m2 > m ? m2 : m;
  if (mn > m) {
    for (long x = p - mn - 1; x <= i - 1; x++)
      if (x < 1 || a[x] != 0) { nnogrow++; return 0; }
  }
  commit_tokens(nt);
  int golazy = (i == lo) && mn >= LAZY_MIN && !lazy;
  __gmpz_add(Tacc, Tacc, tt); __gmpz_add(Tacc, Tacc, c); __gmpz_add(Tacc, Tacc, c);
  __gmpz_add_ui(Tacc, Tacc, (unsigned long)(2 * (mn - m) + s0));
  if (golazy) {
    /* T_true += ... + s0 - s(N');  new Nhi = N' and T = Tacc - s(Nhi): Tacc += ... + s0 */
    F = p - mn - 1; a[F] = 1; if (F < lo) lo = F;
    matlo = p; cb = p; lazy = 1;
    __gmpz_set(Nhi, N);
  } else {
    long s1 = 0;
    long len = (__gmpz_cmp_ui(N, 0) == 0) ? 0 : (__gmpz_get_str(sbuf2, 3, N), (long)strlen(sbuf2));
    long pad = mn - len;
    for (long x = 0; x < mn; x++) {
      int d = x < pad ? 0 : sbuf2[x - pad] - '0';
      s1 += d; a[p - mn + x] = DSYM[d];
    }
    a[p - mn - 1] = 1;
    if (p - mn - 1 < lo) lo = p - mn - 1;
    if (i == lo || p - mn - 1 == lo) cb = p;
    __gmpz_sub_ui(Tacc, Tacc, (unsigned long)s1);
  }
  p = jend; q = 0; if (p > hi) hi = p;
  ndrain++;
  return 1;
}

int main(int argc, char **argv) {
  long maxdig = argc > 1 ? atol(argv[1]) : 100;
  double maxsec = argc > 2 ? atof(argv[2]) : 1e18;
  const char *dump = argc > 3 ? argv[3] : NULL;
  CELLS = 400000000L;
  a = calloc(CELLS, 1);
  tokpos = malloc(sizeof(long) * (CELLS / 2));
  toktype = malloc(CELLS / 2); ed1 = malloc(CELLS / 2); ed2 = malloc(CELLS / 2);
  sbuf = malloc(CELLS / 2); sbuf2 = malloc(CELLS / 2);
  if (!a || !tokpos || !toktype || !ed1 || !ed2 || !sbuf || !sbuf2) { fprintf(stderr, "alloc\n"); return 1; }
  __gmpz_init(Tacc); __gmpz_init(Nhi); __gmpz_init(c); __gmpz_init(tt); __gmpz_init(tmp);
  __gmpz_init(N); __gmpz_init(P3);
  p = lo = hi = CELLS / 2; q = 0;
  long origin = p;
  time_t start = time(NULL);
  long lastdig = 0; int halted = 0;
  for (;;) {
    if (drain_point()) {
      if (litpend) { __gmpz_add_ui(Tacc, Tacc, litpend); litpend = 0; }
      if (try_drain()) {
        long dig = (long)__gmpz_sizeinbase(Tacc, 10);
        if (dig > lastdig) {
          lastdig = dig;
          printf("digits~%ld drains=%llu lazy=%llu lit=%llu mat=%llu fullmat=%llu nogrow=%llu lo=%ld hi=%ld width=%ld minA3(decade)=%ld A3-cb(decade)=%ld A3-cb(all)=%ld A3inside=%llu sec=%ld\n",
                 dig, (unsigned long long)ndrain, (unsigned long long)nlazy, (unsigned long long)nlit,
                 (unsigned long long)nmat, (unsigned long long)nfullmat, (unsigned long long)nnogrow,
                 lo - origin, hi - origin, hi - lo, minA3d, minCb, minCball,
                 (unsigned long long)nA3inside, (long)(time(NULL) - start));
          fflush(stdout);
          minA3d = 1L << 60; minCb = 1L << 60;
          if (dig > maxdig) break;
        }
        if ((ndrain & 15) == 0 && difftime(time(NULL), start) > maxsec) break;
        continue;
      }
    }
    for (;;) {
      if (lazy && p < matlo && p > F) materialize_until(p);
      int s = a[p];
      if (q == 0) {
        if (s == 1) { halted = 1; break; }
        if (s == 3) {
          long d = p - lo; if (d < minA3d) minA3d = d;
          long e = p - cb; if (e < minCb) minCb = e;
          if (ndrain > 1000 && e < minCball) minCball = e;
          if (e < 0) nA3inside++;
        }
      }
      a[p] = TW[q][s]; p += TM[q][s]; q = TQ[q][s];
      litpend++; nlit++;
      if (p < lo) lo = p;
      if (p > hi) hi = p;
      if (drain_point()) break;
    }
    if (halted) break;
    if (p < 2 || p > CELLS - 4) { fprintf(stderr, "tape bound\n"); return 2; }
  }
  if (litpend) { __gmpz_add_ui(Tacc, Tacc, litpend); litpend = 0; }
  materialize_full();
  char *ts = __gmpz_get_str(NULL, 10, Tacc);
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
