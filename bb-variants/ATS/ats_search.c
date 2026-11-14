/*
 * Exhaustive ATS champion search.
 *
 * Token encoding:
 *   primitive: is_fn = 0, off = 0/1, len = 1
 *   function:  is_fn = 1, off = offset into arena, len = alpha length
 *
 * Alpha bytes are 0/1.  Offsets are stable across arena reallocations.
 *
 * Build:
 *   gcc -O3 -std=c11 -o ats_search.exe ats_search.c
 *
 * Examples:
 *   ./ats_search.exe --n 6 --max-steps 10000000 --max-tokens 1000000
 *   ./ats_search.exe --n 7 --max-steps 10000000 --max-tokens 1000000
 *   ./ats_search.exe --n 8 --max-steps 1000000 --max-tokens 1000000
 */

#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAX_TOKENS 1000000u
#define MAX_ARENA (256u * 1024u * 1024u)

static FILE *g_dump;
static uint64_t g_dump_mod = 1;

typedef struct {
    uint32_t off;
    uint32_t len;
    uint8_t is_fn;
} Token;

typedef struct {
    Token *v;
    uint32_t n;
    uint32_t cap;
    uint32_t zeros;
    uint32_t prims;
    uint32_t head;   /* physical index of logical token 0 */
} Tape;

typedef struct {
    unsigned char *p;
    size_t n;
    size_t cap;
} Arena;

typedef enum {
    R_HALT = 0,
    R_ZERO_FREE,
    R_CYCLE,
    R_LIMIT,
    R_TAPE_LIMIT,
    R_ARENA_LIMIT
} Reason;

static const char *reason_name(Reason r) {
    switch (r) {
        case R_HALT: return "halt";
        case R_ZERO_FREE: return "zero-free";
        case R_CYCLE: return "cycle";
        case R_LIMIT: return "step-limit";
        case R_TAPE_LIMIT: return "tape-limit";
        case R_ARENA_LIMIT: return "arena-limit";
    }
    return "?";
}

static void die(const char *msg) {
    fprintf(stderr, "fatal: %s\n", msg);
    exit(1);
}

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) die("out of memory");
    return p;
}

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n ? n : 1);
    if (!q) die("out of memory");
    return q;
}

static void arena_init(Arena *a, size_t cap) {
    a->p = xmalloc(cap);
    a->n = 0;
    a->cap = cap;
}

static void arena_destroy(Arena *a) {
    free(a->p);
    a->p = NULL;
    a->n = a->cap = 0;
}

static int arena_reserve(Arena *a, size_t add) {
    if (add > MAX_ARENA || a->n > MAX_ARENA - add) return 0;
    size_t need = a->n + add;
    if (need > a->cap) {
        size_t cap = a->cap ? a->cap : 4096;
        while (cap < need) {
            if (cap > MAX_ARENA / 2) { cap = MAX_ARENA; break; }
            cap *= 2;
        }
        if (cap < need) return 0;
        a->p = xrealloc(a->p, cap);
        a->cap = cap;
    }
    return 1;
}

static int arena_put(Arena *a, const unsigned char *s, size_t len, uint32_t *off) {
    if (!arena_reserve(a, len)) return 0;
    *off = (uint32_t)a->n;
    if (len) memcpy(a->p + a->n, s, len);
    a->n += len;
    return 1;
}

/* Prepend one bit d to the alpha at (off,len). */
static int arena_prepend(Arena *a, unsigned char d, uint32_t off, uint32_t len,
                         uint32_t *new_off) {
    if (!arena_reserve(a, (size_t)len + 1)) return 0;
    *new_off = (uint32_t)a->n;
    a->p[a->n] = d;
    if (len) memmove(a->p + a->n + 1, a->p + off, len);
    a->n += (size_t)len + 1;
    return 1;
}

static uint32_t token_zeros(const Arena *a, Token t) {
    if (!t.is_fn) return t.off == 0 ? 1u : 0u;
    uint32_t z = 0;
    const unsigned char *s = a->p + t.off;
    for (uint32_t i = 0; i < t.len; i++) z += (s[i] == 0);
    return z;
}

static uint32_t token_length(Token t) {
    return t.is_fn ? t.len : 1u;
}

static void tape_init(Tape *t, uint32_t cap) {
    t->v = xmalloc((size_t)cap * sizeof(Token));
    t->n = 0;
    t->cap = cap;
    t->zeros = 0;
    t->prims = 0;
    t->head = 0;
}

static void tape_destroy(Tape *t) {
    free(t->v);
    t->v = NULL;
    t->n = t->cap = t->zeros = t->prims = t->head = 0;
}

static int tape_ensure(Tape *t, uint32_t need) {
    if (t->head + need <= t->cap) return 1;
    if (need > MAX_TOKENS) return 0;
    /* Compact when the dead prefix is large enough to be worth it. */
    if (t->head && need <= t->cap) {
        if (t->n) memmove(t->v, t->v + t->head,
                          (size_t)t->n * sizeof(Token));
        t->head = 0;
        return 1;
    }
    uint32_t cap = t->cap ? t->cap : 32;
    while (cap < t->head + need) {
        if (cap > MAX_TOKENS / 2) { cap = MAX_TOKENS; break; }
        cap *= 2;
    }
    if (cap < t->head + need) return 0;
    t->v = xrealloc(t->v, (size_t)cap * sizeof(Token));
    t->cap = cap;
    return 1;
}

static int tape_append(Tape *t, const Arena *a, Token x) {
    if (t->n >= MAX_TOKENS) return 0;
    if (!tape_ensure(t, t->n + 1)) return 0;
    t->v[t->head + t->n++] = x;
    t->zeros += token_zeros(a, x);
    if (!x.is_fn) t->prims++;
    return 1;
}

static Token tape_pop_head(Tape *t) {
    Token h = t->v[t->head++];
    t->n--;
    if (!h.is_fn) t->prims--;
    if (t->n == 0) t->head = 0;
    return h;
}

static void tape_pop_tail(Tape *t, const Arena *a) {
    if (!t->n) return;
    Token x = t->v[t->head + --t->n];
    t->zeros -= token_zeros(a, x);
    if (!x.is_fn) t->prims--;
    if (t->n == 0) t->head = 0;
}

static int append_lookahead(Tape *t, const Arena *a) {
    Token tmp[2];
    uint32_t m = t->n < 2 ? t->n : 2;
    for (uint32_t i = 0; i < m; i++) tmp[i] = t->v[t->head + i];
    for (uint32_t i = 0; i < m; i++) {
        if (!tape_append(t, a, tmp[i])) return 0;
    }
    return 1;
}

static int absorption_phase(Tape *t, Arena *a) {
    if (t->prims == 0) return 1;
    uint32_t j = 1;
    while (j + 1 < t->n) { /* j < n-1 */
        if (t->v[t->head + j].is_fn && !t->v[t->head + j + 1].is_fn) {
            Token *f = &t->v[t->head + j];
            unsigned char d = (unsigned char)t->v[t->head + j + 1].off;
            uint32_t new_off;
            if (!arena_prepend(a, d, f->off, f->len, &new_off)) return 0;
            f->off = new_off;
            f->len++;
            t->prims--;
            /* delete token j+1 */
            memmove(&t->v[t->head + j + 1], &t->v[t->head + j + 2],
                    (size_t)(t->n - (j + 2)) * sizeof(Token));
            t->n--;
            continue;
        }
        j++;
    }
    return 1;
}

static int one_rule(Tape *t, Arena *a, Token h) {
    const unsigned char *alpha = a->p + h.off;
    uint32_t len = h.len;
    int32_t first_one = -1;
    for (uint32_t i = 0; i < len; i++) {
        if (alpha[i] == 1) { first_one = (int32_t)i; break; }
    }
    if (first_one < 0) return 0; /* composite should contain a 1 */

    uint32_t drop = (len > 3) ? (uint32_t)first_one : 0u;
    uint32_t rest_len = len - 1;
    uint32_t rest_off = 0;

    if (rest_len) {
        if (!arena_reserve(a, rest_len)) return 0;
        rest_off = (uint32_t)a->n;
        const unsigned char *src = a->p + h.off; /* re-resolve after reserve */
        unsigned char *dst = a->p + rest_off;
        uint32_t p = 0;
        for (uint32_t i = 0; i < len; i++) {
            if (i != drop) dst[p++] = src[i];
        }
        a->n += rest_len;
    }

    unsigned char one = 1;
    uint32_t one_off;
    if (!arena_put(a, &one, 1, &one_off)) return 0;
    Token f1 = {one_off, 1, 1};
    if (!tape_append(t, a, f1)) return 0;

    if (rest_len) {
        Token fr = {rest_off, rest_len, 1};
        if (!tape_append(t, a, fr)) return 0;
    }
    return 1;
}

static int zero_rule(Tape *t, const Arena *a) {
    tape_pop_tail(t, a);
    return 1;
}

static int execution_phase(Tape *t, Arena *a) {
    Token h = tape_pop_head(t);
    t->zeros -= token_zeros(a, h);

    if (!h.is_fn) {
        if (h.off == 0) return 1;      /* lone 0 */
        return append_lookahead(t, a); /* primitive 1 */
    }

    const unsigned char *alpha = a->p + h.off;
    uint32_t c0 = 0, c1 = 0;
    for (uint32_t i = 0; i < h.len; i++) {
        if (alpha[i] == 0) c0++;
        else c1++;
    }

    if (c1 == 0) return 1; /* pure zeros: lone 0 */

    if (h.len == 1 && alpha[0] == 1) {
        return append_lookahead(t, a); /* fn(1) */
    }

    int one_first;
    if (c0 == 0) {
        one_first = 1;
    } else if (c1 > c0) {
        one_first = 1;
    } else if (c0 > c1) {
        one_first = 0;
    } else {
        one_first = (alpha[0] == 1);
    }

    if (one_first) {
        if (!one_rule(t, a, h)) return 0;
        if (c0 > 0) return zero_rule(t, a);
        return 1;
    } else {
        if (!zero_rule(t, a)) return 0;
        return one_rule(t, a, h);
    }
}

/* A small exact-ish cycle detector for search classification. */
#define CYCLE_BITS 21
#define CYCLE_SIZE (1u << CYCLE_BITS)
#define CYCLE_MASK (CYCLE_SIZE - 1u)

typedef struct {
    uint64_t h1, h2;
    uint32_t gen;
} CycleSlot;

static uint64_t state_hash(const Tape *t, const Arena *a, uint64_t seed) {
    uint64_t h = seed;
    for (uint32_t i = 0; i < t->n; i++) {
        Token x = t->v[t->head + i];
        h ^= (uint64_t)x.is_fn + 0x9e3779b97f4a7c15ull;
        h *= 1099511628211ull;
        h ^= (uint64_t)x.len + 0x9e3779b97f4a7c15ull;
        h *= 1099511628211ull;
        if (x.is_fn) {
            const unsigned char *s = a->p + x.off;
            for (uint32_t j = 0; j < x.len; j++) {
                h ^= (uint64_t)s[j] + 0x9e3779b97f4a7c15ull;
                h *= 1099511628211ull;
            }
        } else {
            h ^= (uint64_t)x.off + 0x9e3779b97f4a7c15ull;
            h *= 1099511628211ull;
        }
    }
    return h;
}

static int state_seen(CycleSlot *tab, uint32_t gen, const Tape *t,
                      const Arena *a) {
    if (t->n > 100000) return 0; /* avoid hashing very large tapes */
    uint64_t h1 = state_hash(t, a, 1469598103934665603ull);
    uint64_t h2 = state_hash(t, a, 1099511628211ull + 0x9e3779b97f4a7c15ull);
    uint32_t idx = (uint32_t)(h1 ^ (h1 >> 32)) & CYCLE_MASK;
    for (uint32_t probes = 0; probes < CYCLE_SIZE; probes++) {
        CycleSlot *s = &tab[idx];
        if (s->gen != gen) {
            s->gen = gen;
            s->h1 = h1;
            s->h2 = h2;
            return 0;
        }
        if (s->h1 == h1 && s->h2 == h2) return 1;
        idx = (idx + 1) & CYCLE_MASK;
    }
    return 0;
}

static Reason simulate(Tape *t, Arena *a, uint64_t max_steps,
                       uint32_t max_tokens, CycleSlot *cycle, uint32_t cycle_gen,
                       uint64_t *out_steps) {
    for (uint64_t steps = 0;; steps++) {
        if (t->n == 0) {
            *out_steps = steps;
            return R_HALT;
        }
        if (t->n > max_tokens) {
            *out_steps = steps;
            return R_TAPE_LIMIT;
        }
        if (t->zeros == 0 && t->n >= 2) {
            *out_steps = steps;
            return R_ZERO_FREE;
        }
        if (steps >= 64 && (steps & 15) == 0 && t->n <= 5000 &&
            cycle && state_seen(cycle, cycle_gen, t, a)) {
            *out_steps = steps;
            return R_CYCLE;
        }
        if (steps >= max_steps) {
            *out_steps = steps;
            return R_LIMIT;
        }
        if (!absorption_phase(t, a)) {
            *out_steps = steps;
            return R_ARENA_LIMIT;
        }
        if (!execution_phase(t, a)) {
            *out_steps = steps + 1;
            return R_ARENA_LIMIT;
        }
        if (t->n == 0) {
            *out_steps = steps + 1;
            return R_HALT;
        }
    }
}

static void format_tape(const Token *v, uint32_t n, const Arena *a,
                        char *buf, size_t cap) {
    size_t p = 0;
    if (cap < 3) { if (cap) buf[0] = 0; return; }
    buf[p++] = '[';
    for (uint32_t i = 0; i < n; i++) {
        if (i && p + 2 < cap) { buf[p++] = ','; buf[p++] = ' '; }
        if (v[i].is_fn) {
            const char *pre = "fn(";
            for (const char *q = pre; *q && p + 1 < cap; q++) buf[p++] = *q;
            const unsigned char *s = a->p + v[i].off;
            for (uint32_t j = 0; j < v[i].len && p + 1 < cap; j++)
                buf[p++] = s[j] ? '1' : '0';
            if (p + 1 < cap) buf[p++] = ')';
        } else {
            if (p + 1 < cap) buf[p++] = v[i].off ? '1' : '0';
        }
    }
    if (p + 1 < cap) buf[p++] = ']';
    buf[p < cap ? p : cap - 1] = 0;
}

typedef struct {
    int n;
    uint64_t max_steps;
    uint32_t max_tokens;
    uint64_t best_steps;
    char best_tape[8192];
    uint64_t candidates;
    uint64_t halted;
    uint64_t zero_free;
    uint64_t cycles;
    uint64_t limited;
    uint64_t tape_limited;
    uint64_t arena_limited;
    uint64_t candidate_index;
    uint32_t shard;
    uint32_t shards;
    FILE *dump;
    uint64_t dump_mod;
    Tape base;
    Tape run;
    Arena arena;
    CycleSlot *cycle;
    uint32_t cycle_gen;
    int failed;
} SearchCtx;

static void evaluate(SearchCtx *c) {
    uint64_t index = c->candidate_index++;
    if (c->shards > 1 && (index % c->shards) != c->shard) return;
    size_t base_end = c->arena.n;
    c->run.n = c->base.n;
    c->run.head = 0;
    c->run.zeros = c->base.zeros;
    c->run.prims = c->base.prims;
    if (c->run.cap < c->run.n) die("run tape capacity");
    if (c->run.n)
        memcpy(c->run.v, c->base.v + c->base.head,
               (size_t)c->run.n * sizeof(Token));

    if (++c->cycle_gen == 0) {
        memset(c->cycle, 0, (size_t)CYCLE_SIZE * sizeof(CycleSlot));
        c->cycle_gen = 1;
    }
    uint64_t steps = 0;
    Reason r = simulate(&c->run, &c->arena, c->max_steps,
                        c->max_tokens, c->cycle, c->cycle_gen, &steps);
    c->candidates++;
    if (r == R_LIMIT && c->dump && c->dump_mod &&
        (c->candidates % c->dump_mod) == 0) {
        format_tape(c->base.v + c->base.head, c->base.n, &c->arena,
                    c->best_tape, sizeof(c->best_tape));
        fprintf(c->dump, "LIMIT %" PRIu64 " %" PRIu64 " %s\n",
                c->candidates, steps, c->best_tape);
    }
    switch (r) {
        case R_HALT:
            c->halted++;
            if (steps > c->best_steps) {
                c->best_steps = steps;
                format_tape(c->base.v + c->base.head, c->base.n, &c->arena,
                            c->best_tape, sizeof(c->best_tape));
                printf("new best n=%d: %" PRIu64 " steps  %s\n",
                       c->n, steps, c->best_tape);
                fflush(stdout);
            }
            break;
        case R_ZERO_FREE: c->zero_free++; break;
        case R_CYCLE: c->cycles++; break;
        case R_LIMIT: c->limited++; break;
        case R_TAPE_LIMIT: c->tape_limited++; break;
        case R_ARENA_LIMIT: c->arena_limited++; break;
    }
    c->arena.n = base_end;
}

static void base_append(SearchCtx *c, Token x) {
    if (!tape_append(&c->base, &c->arena, x)) c->failed = 1;
}

static void base_pop(SearchCtx *c) {
    tape_pop_tail(&c->base, &c->arena);
}

static void generate(SearchCtx *c, int rem) {
    if (c->failed) return;
    if (rem == 0) {
        evaluate(c);
        return;
    }

    for (int k = 1; k <= rem && !c->failed; k++) {
        size_t mark = c->arena.n;

        if (k == 1) {
            /* Four length-one tokens: 0, 1, fn(0), fn(1). */
            for (int opt = 0; opt < 4 && !c->failed; opt++) {
                size_t tok_mark = c->arena.n;
                Token x;
                if (opt < 2) {
                    x.off = (uint32_t)opt;
                    x.len = 1;
                    x.is_fn = 0;
                } else {
                    unsigned char bit = (unsigned char)(opt - 2);
                    uint32_t off;
                    if (!arena_put(&c->arena, &bit, 1, &off)) {
                        c->failed = 1;
                        break;
                    }
                    x.off = off;
                    x.len = 1;
                    x.is_fn = 1;
                }
                base_append(c, x);
                generate(c, rem - 1);
                base_pop(c);
                c->arena.n = tok_mark;
            }
        } else {
            uint32_t count = 1u << k;
            for (uint32_t bits = 0; bits < count && !c->failed; bits++) {
                unsigned char alpha[32];
                for (int i = 0; i < k; i++)
                    alpha[i] = (unsigned char)((bits >> (k - 1 - i)) & 1u);
                uint32_t off;
                if (!arena_put(&c->arena, alpha, (size_t)k, &off)) {
                    c->failed = 1;
                    break;
                }
                Token x = {off, (uint32_t)k, 1};
                base_append(c, x);
                generate(c, rem - k);
                base_pop(c);
                c->arena.n = mark;
            }
        }
        c->arena.n = mark;
    }
}

static void search_n(int n, uint64_t max_steps, uint32_t max_tokens,
                     uint32_t shard, uint32_t shards) {
    SearchCtx c;
    memset(&c, 0, sizeof(c));
    c.n = n;
    c.max_steps = max_steps;
    c.max_tokens = max_tokens;
    c.shard = shard;
    c.shards = shards;
    c.dump = g_dump;
    c.dump_mod = g_dump_mod;
    c.best_steps = 0;
    c.best_tape[0] = 0;

    tape_init(&c.base, 16);
    tape_init(&c.run, 1024);
    arena_init(&c.arena, 4096);
    c.cycle = xmalloc((size_t)CYCLE_SIZE * sizeof(CycleSlot));
    memset(c.cycle, 0, (size_t)CYCLE_SIZE * sizeof(CycleSlot));

    clock_t start = clock();
    generate(&c, n);

    if (c.failed) {
        fprintf(stderr, "search aborted: arena/tape limit or allocation failure\n");
    }

    double secs = (double)(clock() - start) / CLOCKS_PER_SEC;
    printf("\nn=%d\n", n);
    printf("candidates: %" PRIu64 "\n", c.candidates);
    printf("halted:     %" PRIu64 "\n", c.halted);
    printf("zero-free:  %" PRIu64 "\n", c.zero_free);
    printf("cycle:      %" PRIu64 "\n", c.cycles);
    printf("step-limit: %" PRIu64 "\n", c.limited);
    printf("tape-limit: %" PRIu64 "\n", c.tape_limited);
    printf("arena-limit:%" PRIu64 "\n", c.arena_limited);
    printf("best:       %" PRIu64 " steps\n", c.best_steps);
    printf("tape:       %s\n", c.best_tape);
    printf("time:       %.2f s\n", secs);

    tape_destroy(&c.base);
    tape_destroy(&c.run);
    arena_destroy(&c.arena);
    free(c.cycle);
}

int main(int argc, char **argv) {
    int n = 6;
    uint64_t max_steps = 10000000ull;
    uint32_t max_tokens = 1000000u;
    uint32_t shard = 0, shards = 1;
    const char *dump_path = NULL;

    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--n") && i + 1 < argc) {
            n = atoi(argv[++i]);
        } else if (!strcmp(argv[i], "--max-steps") && i + 1 < argc) {
            max_steps = strtoull(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--max-tokens") && i + 1 < argc) {
            max_tokens = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--shard") && i + 1 < argc) {
            shard = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--shards") && i + 1 < argc) {
            shards = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--dump-limit") && i + 1 < argc) {
            dump_path = argv[++i];
        } else if (!strcmp(argv[i], "--dump-mod") && i + 1 < argc) {
            g_dump_mod = strtoull(argv[++i], NULL, 10);
        } else {
            fprintf(stderr, "unknown argument: %s\n", argv[i]);
            return 2;
        }
    }
    if (n < 1 || n > 10) die("n must be in 1..10");
    if (!shards || shard >= shards) die("require 0 <= shard < shards");
    if (dump_path) {
        g_dump = fopen(dump_path, "w");
        if (!g_dump) die("cannot open dump file");
    }
    search_n(n, max_steps, max_tokens, shard, shards);
    if (g_dump) fclose(g_dump);
    return 0;
}
