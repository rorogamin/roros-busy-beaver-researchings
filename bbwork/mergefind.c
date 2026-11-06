/* mergefind.c -- find a configuration merge between two TMs.
 *
 * Runs machine A for up to CAP steps, recording a 64-bit hash of each
 * translation-normalized configuration (state, head offset, tape from the
 * leftmost to the rightmost non-zero cell).  Then runs machine B and looks
 * each configuration up.  A hit means the two runs reach the same
 * configuration (up to translation) at the reported steps; the caller should
 * re-verify exactly with a language-level check.
 *
 * usage: mergefind A_SPEC B_SPEC [-c CAP] [-v]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 8
#define MAXM 8

typedef struct {
    int n, m;
    int8_t w[MAXN][MAXM];
    int8_t d[MAXN][MAXM];
    int8_t nx[MAXN][MAXM];
} TM;

static int parse_tm(const char *line, TM *tm) {
    int len = (int)strlen(line);
    int n = 0;
    for (int i = 0; i < len; i++) if (line[i] == '_') n++;
    n++;
    if (n < 1 || n > MAXN) return -1;
    int blen = 0;
    for (int i = 0; i < len && line[i] != '_'; i++) blen++;
    if (blen % 3 || blen == 0) return -1;
    int m = blen / 3;
    if (m < 1 || m > MAXM) return -1;
    if (len != n * blen + (n - 1)) return -1;
    tm->n = n; tm->m = m;
    const char *p = line;
    for (int s = 0; s < n; s++) {
        for (int sym = 0; sym < m; sym++) {
            const char *tok = p + 3 * sym;
            if (tok[0] == '-' && tok[1] == '-' && tok[2] == '-') {
                tm->w[s][sym] = -1; tm->d[s][sym] = 0; tm->nx[s][sym] = -1;
            } else {
                int w = tok[0] - '0';
                int d = (tok[1] == 'R') ? 1 : (tok[1] == 'L' ? -1 : 0);
                char c = tok[2];
                int nx = (c == 'Z' || c == 'H') ? -1 : (c - 'A');
                if (nx < 0) { tm->w[s][sym] = -1; tm->d[s][sym] = 0; tm->nx[s][sym] = -1; continue; }
                if (w < 0 || w >= m || d == 0) return -1;
                tm->w[s][sym] = (int8_t)w; tm->d[s][sym] = (int8_t)d; tm->nx[s][sym] = (int8_t)nx;
            }
        }
        p += blen + 1;
    }
    return 0;
}

typedef struct { int8_t *tape; size_t cap; long long head; long long lo, hi; int any; } Tape;

static void tinit(Tape *t) {
    t->cap = 1u << 18;
    t->tape = (int8_t *)calloc(t->cap, 1);
    if (!t->tape) { perror("calloc"); exit(2); }
    t->head = (long long)(t->cap / 2);
    t->lo = t->hi = t->head;
    t->any = 0;
}

static void tfree(Tape *t) { free(t->tape); t->tape = NULL; }

static void tgrow(Tape *t) {
    size_t ncap = t->cap * 2;
    int8_t *nt = (int8_t *)calloc(ncap, 1);
    if (!nt) { perror("calloc"); exit(2); }
    size_t shift = (ncap - t->cap) / 2;
    memcpy(nt + shift, t->tape, t->cap);
    free(t->tape);
    t->tape = nt; t->cap = ncap;
    t->head += (long long)shift;
    t->lo += (long long)shift; t->hi += (long long)shift;
}

/* FNV-1a over the normalized configuration */
static uint64_t conf_hash(const Tape *t, int state, int m) {
    (void)m;
    uint64_t h = 1469598103934665603ULL;
    long long len = t->any ? (t->hi - t->lo + 1) : 0;
    long long hoff = t->head - (t->any ? t->lo : t->head);
    unsigned char buf[16];
    memcpy(buf, &state, 4);
    memcpy(buf + 4, &hoff, 8);
    for (int i = 0; i < 12; i++) { h ^= buf[i]; h *= 1099511628211ULL; }
    memcpy(buf, &len, 8);
    for (int i = 0; i < 8; i++) { h ^= buf[i]; h *= 1099511628211ULL; }
    for (long long i = 0; i < len; i++) { h ^= (unsigned char)t->tape[t->lo + i]; h *= 1099511628211ULL; }
    return h;
}

#define TBITS 23
#define TSLOTS (1u << TBITS)
typedef struct { uint64_t hash; long long step; } Slot;
static Slot *table;

static int table_put(uint64_t h, long long step) {
    size_t i = (size_t)(h >> (64 - TBITS));
    for (;;) {
        if (table[i].step == 0) { table[i].hash = h; table[i].step = step + 1; return 0; }
        if (table[i].hash == h) return 1;
        i = (i + 1) & (TSLOTS - 1);
    }
}
static long long table_get(uint64_t h) {
    size_t i = (size_t)(h >> (64 - TBITS));
    for (;;) {
        if (table[i].step == 0) return -1;
        if (table[i].hash == h) return table[i].step - 1;
        i = (i + 1) & (TSLOTS - 1);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s A B [-c CAP]\n", argv[0]); return 2; }
    long long cap = 5000000;
    long long skip = 0;
    for (int i = 3; i + 1 < argc; i++) {
        if (!strcmp(argv[i], "-c")) cap = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-s")) skip = atoll(argv[++i]);
    }
    TM A, B;
    if (parse_tm(argv[1], &A) || parse_tm(argv[2], &B)) { fprintf(stderr, "parse error\n"); return 2; }
    if (A.n != B.n || A.m != B.m) { fprintf(stderr, "incompatible machines\n"); return 2; }

    table = (Slot *)calloc(TSLOTS, sizeof(Slot));
    if (!table) { perror("calloc"); return 2; }

    Tape t; tinit(&t);
    int st = 0;
    for (long long s = 0; s < cap; s++) {
        int v = t.tape[t.head];
        int w = A.w[st][v];
        if (w < 0) break;
        t.tape[t.head] = (int8_t)w;
        if (w) { if (!t.any) { t.lo = t.hi = t.head; t.any = 1; } else { if (t.head < t.lo) t.lo = t.head; if (t.head > t.hi) t.hi = t.head; } }
        else if (t.any) {
            if (t.head == t.lo) { while (t.lo <= t.hi && t.tape[t.lo] == 0) t.lo++; if (t.lo > t.hi) t.any = 0; }
            else if (t.head == t.hi) { while (t.hi >= t.lo && t.tape[t.hi] == 0) t.hi--; if (t.hi < t.lo) t.any = 0; }
        }
        t.head += A.d[st][v];
        st = A.nx[st][v];
        if (t.head < 0 || (size_t)t.head >= t.cap) tgrow(&t);
        if (s + 1 >= skip) table_put(conf_hash(&t, st, A.m), s + 1);
    }
    long long asize = 0;
    for (size_t i = 0; i < TSLOTS; i++) if (table[i].step) asize++;
    fprintf(stderr, "A recorded %lld configs\n", asize);
    tfree(&t);

    /* run B */
    tinit(&t); st = 0;
    for (long long s = 0; s < cap; s++) {
        int v = t.tape[t.head];
        int w = B.w[st][v];
        if (w < 0) { fprintf(stderr, "B halted at %lld\n", s); break; }
        t.tape[t.head] = (int8_t)w;
        if (w) { if (!t.any) { t.lo = t.hi = t.head; t.any = 1; } else { if (t.head < t.lo) t.lo = t.head; if (t.head > t.hi) t.hi = t.head; } }
        else if (t.any) {
            if (t.head == t.lo) { while (t.lo <= t.hi && t.tape[t.lo] == 0) t.lo++; if (t.lo > t.hi) t.any = 0; }
            else if (t.head == t.hi) { while (t.hi >= t.lo && t.tape[t.hi] == 0) t.hi--; if (t.hi < t.lo) t.any = 0; }
        }
        t.head += B.d[st][v];
        st = B.nx[st][v];
        if (t.head < 0 || (size_t)t.head >= t.cap) tgrow(&t);
        if (s + 1 >= skip) {
            long long hit = table_get(conf_hash(&t, st, B.m));
            if (hit >= 0) {
                printf("MERGE A_step=%lld B_step=%lld\n", hit, s + 1);
                return 0;
            }
        }
    }
    printf("NO_MERGE within %lld\n", cap);
    return 0;
}
