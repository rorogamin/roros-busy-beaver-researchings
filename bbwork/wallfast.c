/* wallfast.c -- fast exact scan of the documented A(a,c) chain map of 758.
 *
 * A(a,c) = 0^inf 1 2^a <C (20)^c 0^inf
 * The wiki rules (a)-(j) are implemented in order, exactly as in wall.py.
 * Integers are fixed 768-bit unsigned values (24 x 32-bit limbs); H is only
 * 463 bits, leaving ample headroom for intermediate 3*a and 3*c values.
 *
 * usage: wallfast START_K COUNT [THREADS] [-v]
 *   START_K = 1 tests H-8,000,001; COUNT consecutive values downward.
 *   -v prints each successful k and its chain count.
 *
 * Exit status 0 iff every tested value reaches H; otherwise the printed
 * FAIL line gives the first k (smallest across chunks) and the reason.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

#define NL 24 /* 768 bits */
typedef struct { uint32_t w[NL]; } big;

/* H = (3^307 - 8282708212) / 13959275, 463 bits. */
static const char *H_HEX =
    "7342f276da762ac02e45c096113c9451e2d8710ea1dfff3d687e7de1b85d2583"
    "4658497d3c2ec24ab6f7c8135c295fbff68c14b286f301b2b8f5";

static void big_zero(big *x) {
    for (int i = 0; i < NL; i++) x->w[i] = 0;
}

static void big_set_ui(big *x, uint64_t v) {
    big_zero(x);
    x->w[0] = (uint32_t)v;
    x->w[1] = (uint32_t)(v >> 32);
}

static void big_copy(big *d, const big *s) {
    for (int i = 0; i < NL; i++) d->w[i] = s->w[i];
}

static int big_cmp(const big *a, const big *b) {
    for (int i = NL - 1; i >= 0; i--) {
        if (a->w[i] != b->w[i]) return a->w[i] < b->w[i] ? -1 : 1;
    }
    return 0;
}

static int big_add_ui(big *x, uint32_t v);

/* Compare a with c+k.  Materialize c+k so the comparison is high-to-low;
 * a low-limb-first early return is wrong when the addition carries. */
static int big_cmp_add_ui(const big *a, const big *c, uint32_t k) {
    big t;
    big_copy(&t, c);
    if (big_add_ui(&t, k)) return -1;
    return big_cmp(a, &t);
}

static int big_add_ui(big *x, uint32_t v) {
    uint64_t carry = v;
    for (int i = 0; i < NL; i++) {
        uint64_t s = (uint64_t)x->w[i] + carry;
        x->w[i] = (uint32_t)s;
        carry = s >> 32;
        if (!carry) return 0;
    }
    return -1;
}

static int big_add(big *r, const big *a, const big *b) {
    uint64_t carry = 0;
    for (int i = 0; i < NL; i++) {
        uint64_t s = (uint64_t)a->w[i] + b->w[i] + carry;
        r->w[i] = (uint32_t)s;
        carry = s >> 32;
    }
    return carry ? -1 : 0;
}

static int big_sub(big *r, const big *a, const big *b) {
    uint64_t borrow = 0;
    for (int i = 0; i < NL; i++) {
        uint64_t av = a->w[i];
        uint64_t bv = (uint64_t)b->w[i] + borrow;
        if (av < bv) {
            r->w[i] = (uint32_t)(av + ((uint64_t)1 << 32) - bv);
            borrow = 1;
        } else {
            r->w[i] = (uint32_t)(av - bv);
            borrow = 0;
        }
    }
    return borrow ? -1 : 0;
}

static int big_sub_ui(big *x, uint32_t v) {
    uint64_t borrow = v;
    for (int i = 0; i < NL; i++) {
        uint64_t av = x->w[i];
        if (av < borrow) {
            x->w[i] = (uint32_t)(av + ((uint64_t)1 << 32) - borrow);
            borrow = 1;
        } else {
            x->w[i] = (uint32_t)(av - borrow);
            return 0;
        }
    }
    return -1;
}

static int big_mul_small(big *x, uint32_t m) {
    uint64_t carry = 0;
    for (int i = 0; i < NL; i++) {
        uint64_t p = (uint64_t)x->w[i] * m + carry;
        x->w[i] = (uint32_t)p;
        carry = p >> 32;
    }
    return carry ? -1 : 0;
}

static void big_div2(big *x) {
    uint32_t carry = 0;
    for (int i = NL - 1; i >= 0; i--) {
        uint32_t cur = x->w[i];
        x->w[i] = (cur >> 1) | (carry << 31);
        carry = cur & 1;
    }
}

static int big_is_one(const big *x) {
    if (x->w[0] != 1) return 0;
    for (int i = 1; i < NL; i++) if (x->w[i]) return 0;
    return 1;
}

static int big_is_ui(const big *x, uint32_t v) {
    if (x->w[0] != v) return 0;
    for (int i = 1; i < NL; i++) if (x->w[i]) return 0;
    return 1;
}

static int big_from_hex(big *x, const char *s) {
    big_zero(x);
    for (; *s; s++) {
        int d;
        if (*s >= '0' && *s <= '9') d = *s - '0';
        else if (*s >= 'a' && *s <= 'f') d = *s - 'a' + 10;
        else if (*s >= 'A' && *s <= 'F') d = *s - 'A' + 10;
        else return -1;
        if (big_mul_small(x, 16)) return -1;
        if (big_add_ui(x, (uint32_t)d)) return -1;
    }
    return 0;
}

/* One wiki rule.  Returns the rule letter, or 0 if no rule applies.
 * Sets *halt when the rule is a halting rule. */
static int step(big *a, big *c, int *halt) {
    const uint32_t c0 = c->w[0];
    big t;

    *halt = 0;

    if ((c0 & 1u) == 0 && big_cmp_add_ui(a, c, 1) >= 0) { /* (a) */
        big_copy(&t, a);
        big_sub(&t, &t, c);
        big_sub_ui(&t, 1);
        big_copy(a, &t);
        big_div2(c);
        big_mul_small(c, 3);
        big_add_ui(c, 2);
        return 'a';
    }
    if ((c0 & 3u) == 1 && big_cmp_add_ui(a, c, 2) >= 0) { /* (b) */
        big_copy(&t, a);
        big_sub(&t, &t, c);
        big_sub_ui(&t, 2);
        big_copy(a, &t);
        big_div2(c);
        big_mul_small(c, 3);
        big_add_ui(c, 5);
        return 'b';
    }
    if ((c0 & 3u) == 3 && big_cmp_add_ui(a, c, 4) >= 0) { /* (c) */
        big_copy(&t, a);
        big_sub(&t, &t, c);
        big_sub_ui(&t, 4);
        big_copy(a, &t);
        big_div2(c);
        big_mul_small(c, 3);
        big_add_ui(c, 8);
        return 'c';
    }
    if ((c0 & 3u) == 3 && big_cmp_add_ui(a, c, 3) == 0) { /* (d) */
        *halt = 1;
        return 'd';
    }
    if ((c0 & 3u) == 3 && big_cmp_add_ui(a, c, 2) == 0) { /* (e) */
        big_copy(&t, c);
        big_mul_small(&t, 3);
        big_add_ui(&t, 8);
        big_set_ui(c, 1);
        big_copy(a, &t);
        return 'e';
    }
    if ((c0 & 1u) == 1 && big_cmp_add_ui(a, c, 1) == 0) { /* (f) */
        *halt = 1;
        return 'f';
    }
    if (big_cmp(c, a) >= 0) {
        const int aodd = (int)(a->w[0] & 1u);
        if (!aodd && !(c0 & 1u)) { /* (g) */
            *halt = 1;
            return 'g';
        }
        if (!aodd && (c0 & 1u)) { /* (h) */
            big_copy(&t, a);
            big_div2(&t);
            big_add(&t, &t, c);
            big_add_ui(&t, 2);
            big_copy(c, &t);
            big_set_ui(a, 1);
            return 'h';
        }
        if (aodd && !(c0 & 1u)) { /* (i) */
            big_copy(&t, c);
            big_sub(&t, &t, a);
            big_add_ui(&t, 4);
            big_copy(c, &t);
            big_mul_small(a, 3);
            return 'i';
        }
        if (aodd && (c0 & 1u)) { /* (j) */
            big_copy(&t, c);
            big_sub(&t, &t, a);
            big_add_ui(&t, 1);
            big_copy(c, &t);
            big_mul_small(a, 3);
            big_add_ui(a, 2);
            return 'j';
        }
    }
    return 0;
}

/* Apply rules from A(1,c) until it ends at a=1 or halts.
 * Returns 1 halt, 0 end, -1 no rule, -2 rule guard. */
static int run_chain(big *a, big *c, unsigned long long *rules) {
    big_set_ui(a, 1);
    *rules = 0;
    for (;;) {
        int halt = 0;
        int r = step(a, c, &halt);
        if (!r) return -1;
        (*rules)++;
        if (halt) return 1;
        if (big_is_one(a)) return 0;
        if (*rules > 10000000ULL) return -2;
    }
}

/* Iterate chains from start until c=H, overshoot, halt, or a guard.
 * Returns 0 success (chains_out set), 2 halt, 3 over, 4 chain guard,
 * -1/-2 propagated from run_chain. */
static int scan_one(const big *H, const big *start,
                    unsigned long long *chains_out) {
    big a, c;
    unsigned long long chains = 0;

    big_copy(&c, start);
    for (;;) {
        unsigned long long rules = 0;
        int r = run_chain(&a, &c, &rules);
        if (r < 0) return r;
        if (r == 1) return 2;
        chains++;
        int cmp = big_cmp(&c, H);
        if (cmp == 0) { *chains_out = chains; return 0; }
        if (cmp > 0) return 3;
        if (chains > 1000000ULL) return 4;
    }
}

static int selftest(const big *H) {
    big a, c;
    unsigned long long rules = 0;

    big_set_ui(&c, 12);
    if (run_chain(&a, &c, &rules) != 1) {
        printf("selftest FAIL c=12\n");
        return 1;
    }
    big_set_ui(&c, 14);
    if (run_chain(&a, &c, &rules) != 1) {
        printf("selftest FAIL c=14\n");
        return 1;
    }
    big_set_ui(&c, 3);
    if (run_chain(&a, &c, &rules) != 0 || !big_is_ui(&c, 23)) {
        printf("selftest FAIL c=3\n");
        return 1;
    }

    big t;
    unsigned long long chains = 0;
    big_copy(&t, H);
    big_sub_ui(&t, 8000001);
    if (scan_one(H, &t, &chains) != 0 || chains != 7391) {
        printf("selftest FAIL H-8000001 (chains=%llu)\n", chains);
        return 1;
    }
    printf("selftest ok (H-8000001 reaches H in %llu chains)\n", chains);
    return 0;
}

typedef struct {
    const big *H;
    unsigned long long k0;
    unsigned long long count;
    int tid;
    int verbose;
    unsigned long long done;
    unsigned long long fail_k;
    int fail_kind;
    unsigned long long fail_chains;
} work;

static void *worker(void *arg) {
    work *w = (work *)arg;
    big c;
    big_copy(&c, w->H);
    big_sub_ui(&c, (uint32_t)(8000000ULL + w->k0));

    for (unsigned long long i = 0; i < w->count; i++) {
        unsigned long long chains = 0;
        int r = scan_one(w->H, &c, &chains);
        if (r != 0) {
            w->fail_k = w->k0 + i;
            w->fail_kind = r;
            w->fail_chains = chains;
            return NULL;
        }
        w->done++;
        if (w->verbose) {
            printf("OK k=%llu chains=%llu\n", w->k0 + i, chains);
            fflush(stdout);
        } else if (w->done % 100000ULL == 0) {
            fprintf(stderr, "thread %d: %llu/%llu done\n",
                    w->tid, w->done, w->count);
            fflush(stderr);
        }
        if (i + 1 < w->count) big_sub_ui(&c, 1);
    }
    return NULL;
}

int main(int argc, char **argv) {
    big H;
    if (big_from_hex(&H, H_HEX) != 0) {
        printf("bad H constant\n");
        return 1;
    }
    if (selftest(&H) != 0) return 1;

    unsigned long long start = 1, count = 1000;
    int threads = 16, verbose = 0;
    if (argc > 1) start = strtoull(argv[1], NULL, 0);
    if (argc > 2) count = strtoull(argv[2], NULL, 0);
    if (argc > 3) threads = atoi(argv[3]);
    if (argc > 4 && strcmp(argv[4], "-v") == 0) verbose = 1;
    if (threads < 1) threads = 1;
    if (threads > 64) threads = 64;
    if (count == 0) {
        printf("nothing to do\n");
        return 0;
    }

    int nt = (count < (unsigned long long)threads) ? (int)count : threads;
    work *ws = (work *)calloc((size_t)nt, sizeof(work));
    pthread_t *tids = (pthread_t *)calloc((size_t)nt, sizeof(pthread_t));
    if (!ws || !tids) {
        printf("out of memory\n");
        return 1;
    }

    unsigned long long base = count / (unsigned long long)nt;
    unsigned long long rem = count % (unsigned long long)nt;
    unsigned long long next = start;
    for (int i = 0; i < nt; i++) {
        unsigned long long cnt = base + ((unsigned long long)i < rem ? 1 : 0);
        ws[i].H = &H;
        ws[i].k0 = next;
        ws[i].count = cnt;
        ws[i].tid = i;
        ws[i].verbose = verbose;
        next += cnt;
    }

    time_t t0 = time(NULL);
    for (int i = 0; i < nt; i++) {
        if (pthread_create(&tids[i], NULL, worker, &ws[i]) != 0) {
            printf("pthread_create failed at %d\n", i);
            return 1;
        }
    }
    for (int i = 0; i < nt; i++) pthread_join(tids[i], NULL);
    long elapsed = (long)(time(NULL) - t0);

    unsigned long long fail_k = 0;
    int fail_kind = 0;
    unsigned long long fail_chains = 0;
    for (int i = 0; i < nt; i++) {
        if (ws[i].fail_kind &&
            (fail_kind == 0 || ws[i].fail_k < fail_k)) {
            fail_k = ws[i].fail_k;
            fail_kind = ws[i].fail_kind;
            fail_chains = ws[i].fail_chains;
        }
    }
    if (fail_kind) {
        printf("FAIL k=%llu kind=%d chains=%llu (start=%llu count=%llu)\n",
               fail_k, fail_kind, fail_chains, start, count);
        return 1;
    }
    printf("OK start=%llu end=%llu count=%llu threads=%d elapsed=%lds\n",
           start, start + count - 1, count, nt, elapsed);
    return 0;
}
