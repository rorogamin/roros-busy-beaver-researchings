/* halving_scan.c -- exact 512-bit halving-time scans for BB(3,3) #758.
 *
 * usage:
 *   halving_scan state A_DEC C_LO C_HI
 *       fixed a, sweep c in [C_LO,C_HI], max halving time.
 *   halving_scan jend K C_LO C_HI
 *       a = 2*3^K - 1, sweep c in [C_LO,C_HI].
 *   halving_scan boundary K R_LO R_HI
 *       c0 = 3^K - 2K + r, r in [R_LO,R_HI], scan every state of the chain.
 *   halving_scan chain C0_DEC
 *       scan every state of the chain from A(1,c0).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef unsigned long long u64;
#define NL 8

typedef struct { u64 x[NL]; } big;

static void bzero(big *a) { memset(a->x, 0, sizeof(a->x)); }
static void bset(big *a, u64 v) { bzero(a); a->x[0] = v; }
static void bcopy(big *d, const big *s) { memcpy(d->x, s->x, sizeof(d->x)); }
static int bcmp(const big *a, const big *b) {
    for (int i = NL - 1; i >= 0; i--) {
        if (a->x[i] < b->x[i]) return -1;
        if (a->x[i] > b->x[i]) return 1;
    }
    return 0;
}
static int is_zero(const big *a) {
    for (int i = 0; i < NL; i++) if (a->x[i]) return 0;
    return 1;
}
static int is_one(const big *a) {
    if (a->x[0] != 1) return 0;
    for (int i = 1; i < NL; i++) if (a->x[i]) return 0;
    return 1;
}
static int is_even(const big *a) { return (a->x[0] & 1) == 0; }
static unsigned mod4(const big *a) { return (unsigned)(a->x[0] & 3); }
static void badd(big *a, u64 v) {
    u64 carry = v;
    for (int i = 0; i < NL && carry; i++) {
        u64 old = a->x[i];
        a->x[i] = old + carry;
        carry = a->x[i] < old;
    }
}
static void bsub(big *a, const big *b) { /* a >= b */
    u64 borrow = 0;
    for (int i = 0; i < NL; i++) {
        u64 bi = b->x[i];
        u64 ai = a->x[i];
        u64 t = ai - bi - borrow;
        borrow = (ai < bi) || (ai - bi < borrow);
        a->x[i] = t;
    }
}
static void baddbig(big *a, const big *b) {
    u64 carry = 0;
    for (int i = 0; i < NL; i++) {
        u64 s = a->x[i] + b->x[i];
        u64 c1 = s < a->x[i];
        u64 s2 = s + carry;
        u64 c2 = s2 < s;
        a->x[i] = s2;
        carry = c1 | c2;
    }
}
static void bmul_small(big *a, u64 m) {
    u64 carry = 0;
    for (int i = 0; i < NL; i++) {
        u64 lo = a->x[i] * m;
        u64 hi = (u64)(((unsigned __int128)a->x[i] * m) >> 64);
        u64 t = lo + carry;
        if (t < lo) hi++;
        a->x[i] = t;
        carry = hi;
    }
    if (carry) { fprintf(stderr, "overflow in bmul_small\n"); exit(3); }
}
static void bdiv2(big *a) {
    for (int i = 0; i < NL - 1; i++)
        a->x[i] = (a->x[i] >> 1) | (a->x[i + 1] << 63);
    a->x[NL - 1] >>= 1;
}
static int ble_add(const big *a, u64 d, const big *b) {
    big t; bcopy(&t, a); badd(&t, d); return bcmp(&t, b) <= 0;
}
static int beq_add(const big *a, u64 d, const big *b) {
    big t; bcopy(&t, a); badd(&t, d); return bcmp(&t, b) == 0;
}
static int bhalve_le(const big *c2, const big *c0) {
    big t; bcopy(&t, c2); bmul_small(&t, 2); return bcmp(&t, c0) <= 0;
}
static void bprint(const big *a) {
    /* decimal via repeated division by 10^19 */
    big t; bcopy(&t, a);
    if (is_zero(&t)) { putchar('0'); return; }
    u64 chunks[128]; int n = 0;
    while (!is_zero(&t)) {
        unsigned __int128 rem = 0;
        for (int i = NL - 1; i >= 0; i--) {
            unsigned __int128 cur = (rem << 64) | t.x[i];
            t.x[i] = (u64)(cur / 10000000000000000000ULL);
            rem = cur % 10000000000000000000ULL;
        }
        chunks[n++] = (u64)rem;
    }
    printf("%llu", chunks[n - 1]);
    for (int i = n - 2; i >= 0; i--) printf("%019llu", chunks[i]);
}
static void bparse(big *a, const char *s) {
    bzero(a);
    for (; *s; s++) {
        if (*s < '0' || *s > '9') { fprintf(stderr, "bad decimal\n"); exit(3); }
        bmul_small(a, 10);
        badd(a, (u64)(*s - '0'));
    }
}
static void bpow3(big *a, int k) {
    bset(a, 1);
    for (int i = 0; i < k; i++) bmul_small(a, 3);
}

/* returns rule char; halt=1 if terminal; a2,c2 outputs. */
static char step(const big *a, const big *c, big *a2, big *c2, int *halt) {
    big one, two, four;
    bset(&one, 1); bset(&two, 2); bset(&four, 4);
    *halt = 0;
    if (ble_add(c, 1, a) && is_even(c)) {                 /* (a) */
        bcopy(a2, a); bsub(a2, c); bsub(a2, &one);
        bcopy(c2, c); bdiv2(c2); bmul_small(c2, 3); badd(c2, 2);
        return 'a';
    }
    if (ble_add(c, 2, a) && mod4(c) == 1) {               /* (b) */
        bcopy(a2, a); bsub(a2, c); bsub(a2, &two);
        bcopy(c2, c); bdiv2(c2); bmul_small(c2, 3); badd(c2, 5);
        return 'b';
    }
    if (ble_add(c, 4, a) && mod4(c) == 3) {               /* (c) */
        bcopy(a2, a); bsub(a2, c); bsub(a2, &four);
        bcopy(c2, c); bdiv2(c2); bmul_small(c2, 3); badd(c2, 8);
        return 'c';
    }
    if (beq_add(c, 3, a) && mod4(c) == 3) { *halt = 1; return 'd'; }
    if (beq_add(c, 2, a) && mod4(c) == 3) {               /* (e) */
        bcopy(a2, c); bmul_small(a2, 3); badd(a2, 8);
        bset(c2, 1); return 'e';
    }
    if (beq_add(c, 1, a) && !is_even(c)) { *halt = 1; return 'f'; }
    if (bcmp(c, a) >= 0 && is_even(a) && is_even(c)) { *halt = 1; return 'g'; }
    if (bcmp(c, a) >= 0 && is_even(a) && !is_even(c)) {   /* (h) */
        bset(a2, 1);
        bcopy(c2, a); bdiv2(c2); baddbig(c2, c); badd(c2, 2);
        return 'h';
    }
    if (bcmp(c, a) >= 0 && !is_even(a) && is_even(c)) {   /* (i) */
        bcopy(a2, a); bmul_small(a2, 3);
        bcopy(c2, c); bsub(c2, a); badd(c2, 4);
        return 'i';
    }
    if (bcmp(c, a) >= 0 && !is_even(a) && !is_even(c)) {  /* (j) */
        bcopy(a2, a); bmul_small(a2, 3); badd(a2, 2);
        bcopy(c2, c); bsub(c2, a); badd(c2, 1);
        return 'j';
    }
    return 0;
}

static unsigned long long halve_time(big a, big c, unsigned long long cap) {
    big c0 = c, a2, c2;
    for (unsigned long long n = 1; n <= cap; n++) {
        int h = 0;
        char r = step(&a, &c, &a2, &c2, &h);
        if (!r) { fprintf(stderr, "no rule\n"); exit(4); }
        if (h || is_one(&a2) || bhalve_le(&c2, &c0)) return n;
        a = a2; c = c2;
    }
    return cap;
}

static void scan_chain(const big *c0, unsigned long long cap) {
    big a, c, a2, c2;
    bset(&a, 1); bcopy(&c, c0);
    unsigned long long best = 0, besti = 0;
    big ba, bc;
    for (unsigned long long i = 0; i < cap; i++) {
        unsigned long long t = halve_time(a, c, cap);
        if (t > best) { best = t; besti = i; ba = a; bc = c; }
        int h = 0;
        char r = step(&a, &c, &a2, &c2, &h);
        if (!r) { fprintf(stderr, "no rule in chain\n"); exit(4); }
        if (h || is_one(&a2)) break;
        a = a2; c = c2;
    }
    printf("chain c0="); bprint(c0);
    printf(" best=%llu at index=%llu a=", best, besti); bprint(&ba);
    printf(" c="); bprint(&bc); printf("\n");
}

static void scan_interval_jend(int K, u64 lo, u64 hi) {
    big a, p; bpow3(&p, K); bcopy(&a, &p); bmul_small(&a, 2); { big one; bset(&one,1); bsub(&a,&one); }
    unsigned long long best = 0, bestc = 0;
    for (u64 c = lo; c <= hi; c++) {
        big bc; bset(&bc, c);
        unsigned long long t = halve_time(a, bc, 20000);
        if (t > best) { best = t; bestc = c; }
    }
    printf("jend K=%d a=", K); bprint(&a);
    printf(" c in [%llu,%llu] best=%llu at c=%llu\n", lo, hi, best, bestc);
}

static void scan_interval_boundary(int K, long long rlo, long long rhi) {
    big p, c0; bpow3(&p, K);
    long long base_off = 2LL * K;
    unsigned long long best = 0; long long bestr = 0; unsigned long long besti = 0;
    big ba, bc;
    for (long long r = rlo; r <= rhi; r++) {
        long long v = (long long)0; /* 3^K is huge: construct by subtraction/addition */
        bcopy(&c0, &p);
        if (base_off >= 0) { big off; bset(&off, (u64)base_off); bsub(&c0, &off); }
        if (r >= 0) badd(&c0, (u64)r); else { big off; bset(&off, (u64)(-r)); bsub(&c0, &off); }
        if (is_zero(&c0)) continue;
        big a, c, a2, c2; bset(&a, 1); bcopy(&c, &c0);
        for (unsigned long long i = 0; i < 5000; i++) {
            unsigned long long t = halve_time(a, c, 20000);
            if (t > best) { best = t; bestr = r; besti = i; ba = a; bc = c; }
            int h = 0; char rr = step(&a, &c, &a2, &c2, &h);
            if (!rr) { fprintf(stderr, "no rule boundary\n"); exit(4); }
            if (h || is_one(&a2)) break;
            a = a2; c = c2;
        }
        (void)v;
    }
    printf("boundary K=%d r in [%lld,%lld] best=%llu at r=%lld index=%llu a=", K, rlo, rhi, best, bestr, besti);
    bprint(&ba); printf(" c="); bprint(&bc); printf("\n");
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "mode?\n"); return 2; }
    if (!strcmp(argv[1], "jend") && argc == 5) {
        scan_interval_jend(atoi(argv[2]), strtoull(argv[3],0,0), strtoull(argv[4],0,0));
    } else if (!strcmp(argv[1], "boundary") && argc == 5) {
        scan_interval_boundary(atoi(argv[2]), atoll(argv[3]), atoll(argv[4]));
    } else if (!strcmp(argv[1], "chain") && argc == 3) {
        big c0; bparse(&c0, argv[2]); scan_chain(&c0, 20000);
    } else if (!strcmp(argv[1], "state") && argc == 5) {
        big a,c; bparse(&a, argv[2]); bset(&c, strtoull(argv[3],0,0));
        u64 lo = strtoull(argv[3],0,0), hi = strtoull(argv[4],0,0);
        unsigned long long best=0,bestc=0;
        for (u64 cc=lo; cc<=hi; cc++) { bset(&c,cc); unsigned long long t=halve_time(a,c,20000); if(t>best){best=t;bestc=cc;} }
        printf("state a="); bprint(&a); printf(" c in [%llu,%llu] best=%llu at c=%llu\n",lo,hi,best,bestc);
    } else { fprintf(stderr, "bad args\n"); return 2; }
    return 0;
}
