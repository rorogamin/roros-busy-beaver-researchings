/* wallmemo.c -- merge-aware exact scan of the 758 A(a,c) wall.
 *
 * The naive scan re-runs ~7,391 chains for every start c=H-8,000,000-k.
 * Consecutive starts merge quickly.  For each start we follow chains until
 * we reach H or a value already known to reach H; then every value on the
 * new path is known too.  Values near H are represented by d = H-c, a
 * 64-bit offset, so the "known-good" set is a hash set of exact uint64s.
 *
 * Each thread owns a contiguous chunk and its own set, so the verification
 * is independent per value and needs no cross-thread agreement.
 *
 * usage: wallmemo START_K COUNT [THREADS] [-v]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

#define NL 24 /* 768 bits */
#define MAX_PATH_LEN 100000
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

static int big_add_ui(big *x, uint32_t v);
static int big_cmp_add_ui(const big *a, const big *c, uint32_t k) {
    big t;
    big_copy(&t, c);
    if (big_add_ui(&t, k)) return -1;
    return big_cmp(a, &t);
}

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

/* Return 0 if c <= H and d=H-c fits in 64 bits; 1 if c>H; -1 if too far. */
static int dist_to_H(const big *H, const big *c, uint64_t *d) {
    int cmp = big_cmp(c, H);
    if (cmp > 0) return 1;
    if (cmp == 0) { *d = 0; return 0; }
    big t;
    big_sub(&t, H, c);
    for (int i = 2; i < NL; i++) if (t.w[i]) return -1;
    *d = (uint64_t)t.w[0] | ((uint64_t)t.w[1] << 32);
    return 0;
}

typedef struct {
    uint64_t *keys;
    size_t cap;
    size_t size;
} hset;

static uint64_t mix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static int hs_init(hset *h, size_t cap) {
    h->keys = (uint64_t *)calloc(cap, sizeof(uint64_t));
    if (!h->keys) return -1;
    h->cap = cap;
    h->size = 0;
    return 0;
}

static size_t hs_find(const hset *h, uint64_t d) {
    size_t mask = h->cap - 1;
    size_t i = (size_t)mix64(d) & mask;
    while (h->keys[i] && h->keys[i] != d) i = (i + 1) & mask;
    return i;
}

static int hs_contains(const hset *h, uint64_t d) {
    size_t i = hs_find(h, d);
    return h->keys[i] == d;
}

static int hs_grow(hset *h) {
    size_t ncap = h->cap ? h->cap * 2 : (1u << 16);
    uint64_t *nk = (uint64_t *)calloc(ncap, sizeof(uint64_t));
    if (!nk) return -1;
    for (size_t j = 0; j < h->cap; j++) {
        uint64_t d = h->keys[j];
        if (!d) continue;
        size_t mask = ncap - 1;
        size_t i = (size_t)mix64(d) & mask;
        while (nk[i]) i = (i + 1) & mask;
        nk[i] = d;
    }
    free(h->keys);
    h->keys = nk;
    h->cap = ncap;
    return 0;
}

static int hs_insert(hset *h, uint64_t d) {
    if (!h->cap) {
        if (hs_init(h, 1u << 16)) return -1;
    }
    if ((h->size + 1) * 10 > h->cap * 7) {
        if (hs_grow(h)) return -1;
    }
    size_t i = hs_find(h, d);
    if (!h->keys[i]) {
        h->keys[i] = d;
        h->size++;
    }
    return 0;
}

/* Verify one start c=H-start_d.  On success insert every new path value.
 * Codes: 0 ok, 2 halt, 3 over, 4 chain guard, 5 far, 6 cycle, 7 path guard,
 * -1 no rule, -2 rule guard. */
static int memo_start(const big *H, uint32_t start_d, hset *seen,
                      uint64_t *path, int path_cap, int *path_len,
                      unsigned long long *chains_out) {
    big a, c;
    int plen = 0;
    unsigned long long chains = 0;

    big_copy(&c, H);
    big_sub_ui(&c, start_d);

    for (;;) {
        uint64_t d;
        int dr = dist_to_H(H, &c, &d);
        if (dr == 1) return 3;
        if (dr < 0) return 5;
        if (d == 0) break;
        if (hs_contains(seen, d)) break;
        for (int j = 0; j < plen; j++) {
            if (path[j] == d) return 6;
        }
        if (plen >= path_cap) return 7;
        path[plen++] = d;

        unsigned long long rules = 0;
        int r = run_chain(&a, &c, &rules);
        if (r < 0) return r;
        if (r == 1) return 2;
        chains++;
        if (chains > 1000000ULL) return 4;
    }

    *path_len = plen;
    *chains_out = chains;
    for (int j = 0; j < plen; j++) {
        if (hs_insert(seen, path[j])) return 8;
    }
    return 0;
}

static int selftest(const big *H) {
    big a, c;
    unsigned long long rules = 0;

    big_set_ui(&c, 12);
    if (run_chain(&a, &c, &rules) != 1) return printf("selftest FAIL c=12\n"), 1;
    big_set_ui(&c, 14);
    if (run_chain(&a, &c, &rules) != 1) return printf("selftest FAIL c=14\n"), 1;
    big_set_ui(&c, 3);
    if (run_chain(&a, &c, &rules) != 0 || !big_is_ui(&c, 23))
        return printf("selftest FAIL c=3\n"), 1;

    hset seen;
    if (hs_init(&seen, 1u << 16)) return printf("selftest OOM\n"), 1;
    uint64_t *path = (uint64_t *)malloc(sizeof(uint64_t) * MAX_PATH_LEN);
    if (!path) return printf("selftest OOM\n"), 1;

    int plen = 0;
    unsigned long long chains = 0;
    int r = memo_start(H, 8000001u, &seen, path, MAX_PATH_LEN, &plen, &chains);
    if (r != 0 || chains != 7391 || plen != 7391) {
        printf("selftest FAIL H-8000001 r=%d chains=%llu path=%d\n",
               r, chains, plen);
        return 1;
    }
    int plen2 = 0;
    unsigned long long chains2 = 0;
    r = memo_start(H, 8000002u, &seen, path, MAX_PATH_LEN, &plen2, &chains2);
    if (r != 0) {
        printf("selftest FAIL H-8000002 r=%d\n", r);
        return 1;
    }
    printf("selftest ok (k=1: %llu chains; k=2 merges after %llu chains, "
           "path %d, seen %zu)\n",
           chains, chains2, plen2, seen.size);
    free(path);
    free(seen.keys);
    return 0;
}

typedef struct {
    const big *H;
    unsigned long long k0;
    unsigned long long count;
    int tid;
    int verbose;
    unsigned long long done;
    unsigned long long total_chains;
    unsigned long long fail_k;
    unsigned long long fail_chains;
    int fail_kind;
    int fail_path;
} work;

static void *worker(void *arg) {
    work *w = (work *)arg;
    hset seen;
    if (hs_init(&seen, 1u << 16)) {
        w->fail_kind = 8;
        w->fail_k = w->k0;
        return NULL;
    }
    uint64_t *path = (uint64_t *)malloc(sizeof(uint64_t) * MAX_PATH_LEN);
    if (!path) {
        w->fail_kind = 8;
        w->fail_k = w->k0;
        free(seen.keys);
        return NULL;
    }

    for (unsigned long long i = 0; i < w->count; i++) {
        unsigned long long k = w->k0 + i;
        unsigned long long d64 = 8000000ULL + k;
        if (d64 > 0xffffffffULL) {
            w->fail_k = k;
            w->fail_kind = 5;
            break;
        }
        int plen = 0;
        unsigned long long chains = 0;
        int r = memo_start(w->H, (uint32_t)d64, &seen, path, MAX_PATH_LEN,
                           &plen, &chains);
        if (r != 0) {
            w->fail_k = k;
            w->fail_kind = r;
            w->fail_chains = chains;
            w->fail_path = plen;
            break;
        }
        w->done++;
        w->total_chains += chains;
        if (w->verbose) {
            printf("OK k=%llu chains=%llu path=%d seen=%zu\n",
                   k, chains, plen, seen.size);
            fflush(stdout);
        } else if (w->done % 100000ULL == 0) {
            fprintf(stderr, "thread %d: %llu/%llu done, chains=%llu, seen=%zu\n",
                    w->tid, w->done, w->count, w->total_chains, seen.size);
            fflush(stderr);
        }
    }
    free(path);
    free(seen.keys);
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

    unsigned long long fail_k = 0, fail_chains = 0;
    int fail_kind = 0, fail_path = 0;
    unsigned long long total_chains = 0;
    for (int i = 0; i < nt; i++) {
        total_chains += ws[i].total_chains;
        if (ws[i].fail_kind &&
            (fail_kind == 0 || ws[i].fail_k < fail_k)) {
            fail_k = ws[i].fail_k;
            fail_kind = ws[i].fail_kind;
            fail_chains = ws[i].fail_chains;
            fail_path = ws[i].fail_path;
        }
    }
    if (fail_kind) {
        printf("FAIL k=%llu kind=%d chains=%llu path=%d "
               "(start=%llu count=%llu)\n",
               fail_k, fail_kind, fail_chains, fail_path, start, count);
        return 1;
    }
    printf("OK start=%llu end=%llu count=%llu threads=%d total_chains=%llu "
           "elapsed=%lds\n",
           start, start + count - 1, count, nt, total_chains, elapsed);
    return 0;
}
