/* sim.c -- fast simulator for bbchallenge standard-format TMs.
 *
 * usage: sim -c CAP -f MACHINES [options]
 *   -c CAP     step cap per machine
 *   -f FILE    one machine per line ('#' comments, blank lines ignored)
 *   -R         also print the final tape as an RLE string
 *   -r N       RLE window radius around the head (default 80)
 *   -s N       skip first N machines
 *   -l N       at most N machines
 *
 * CSV output, one line per machine:
 *   idx,steps,halted,score,head_min,head_max
 * followed by ",RLE" when -R is given.
 *
 * Tape symbols are int8 cells in a calloc'd buffer that doubles when the head
 * runs off an edge; head indices are shifted on growth.  Score counts
 * non-zero cells incrementally.
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
    int n = 0, block = 0;
    /* count blocks */
    for (int i = 0; i < len; i++) if (line[i] == '_') n++;
    n++;
    if (n < 1 || n > MAXN) return -1;
    /* block length in chars (excluding '_') */
    int blen = 0;
    for (int i = 0; i < len && line[i] != '_'; i++) blen++;
    if (blen % 3 != 0) return -1;
    int m = blen / 3;
    if (m < 1 || m > MAXM) return -1;
    if (len != n * blen + (n - 1)) return -1;
    tm->n = n; tm->m = m;
    block = 0;
    for (int i = 0; i < len; i++) {
        if (line[i] == '_') { block++; continue; }
        int pos = i - block - block * blen; /* char offset inside block */
        (void)pos;
    }
    /* simpler: walk blocks explicitly */
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
                if (nx < 0) { /* explicit halt token, like 1RZ */
                    tm->w[s][sym] = -1; tm->d[s][sym] = 0; tm->nx[s][sym] = -1;
                    continue;
                }
                if (w < 0 || w >= m || d == 0) return -1;
                tm->w[s][sym] = (int8_t)w;
                tm->d[s][sym] = (int8_t)d;
                tm->nx[s][sym] = (int8_t)nx;
            }
        }
        p += blen + 1; /* skip block and '_' */
    }
    return 0;
}

static int8_t *tape;
static size_t tcap;
static long long head;
static long long head_min, head_max;
static long long score;

static void tape_init(void) {
    tcap = 1u << 20;
    tape = (int8_t *)calloc(tcap, 1);
    if (!tape) { perror("calloc"); exit(2); }
    head = (long long)(tcap / 2);
    head_min = head_max = head;
    score = 0;
}

static void tape_free(void) { free(tape); tape = NULL; }

static void tape_grow(void) {
    size_t ncap = tcap * 2;
    int8_t *nt = (int8_t *)calloc(ncap, 1);
    if (!nt) { perror("calloc"); exit(2); }
    size_t shift = (ncap - tcap) / 2;
    memcpy(nt + shift, tape, tcap);
    free(tape);
    tape = nt;
    tcap = ncap;
    head += (long long)shift;
    head_min += (long long)shift;
    head_max += (long long)shift;
}

static void rle_print(long long rad) {
    /* locate nonzero extent */
    long long lo = 0, hi = 0;
    int any = 0;
    for (size_t i = 0; i < tcap; i++) {
        if (tape[i]) {
            if (!any) { lo = hi = (long long)i; any = 1; }
            else { if ((long long)i < lo) lo = i; if ((long long)i > hi) hi = i; }
        }
    }
    if (!any) { printf("blank"); return; }
    if (head - rad > lo) lo = head - rad;
    if (head + rad < hi) hi = head + rad;
    int v = tape[lo];
    long long run = 1;
    if (lo == head) printf("<%d>", v);
    for (long long i = lo + 1; i <= hi; i++) {
        int nv = tape[i];
        if (i == head) {
            if (run) printf("%dx%lld ", v, run);
            printf("<%d>", nv);
            v = nv; run = 0;
            continue;
        }
        if (nv == v) run++;
        else { if (run) printf("%dx%lld ", v, run); v = nv; run = 1; }
    }
    if (run) printf("%dx%lld", v, run);
    if (lo == head && run == 0) { /* head printed at lo only */ }
}

int main(int argc, char **argv) {
    long long cap = 1000000;
    const char *path = NULL;
    int want_rle = 0;
    long long rad = 80;
    long long skip = 0, limit = -1;

    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-c") && i + 1 < argc) cap = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-f") && i + 1 < argc) path = argv[++i];
        else if (!strcmp(argv[i], "-R")) want_rle = 1;
        else if (!strcmp(argv[i], "-r") && i + 1 < argc) rad = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-s") && i + 1 < argc) skip = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-l") && i + 1 < argc) limit = atoll(argv[++i]);
        else { fprintf(stderr, "bad arg %s\n", argv[i]); return 2; }
    }
    if (!path) { fprintf(stderr, "need -f FILE\n"); return 2; }
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); return 2; }

    static char line[4096];
    long long idx = 0, used = 0;
    while (fgets(line, sizeof line, f)) {
        char *h = strchr(line, '#');
        if (h) *h = 0;
        int L = (int)strlen(line);
        while (L > 0 && (line[L-1] == '\n' || line[L-1] == '\r' || line[L-1] == ' ')) line[--L] = 0;
        if (!L) continue;
        if (idx++ < skip) continue;
        if (limit >= 0 && used >= limit) break;
        used++;
        TM tm;
        if (parse_tm(line, &tm)) { fprintf(stderr, "parse error: %s\n", line); continue; }
        tape_init();
        int state = 0, halted = 0;
        long long steps = 0;
        for (long long s = 0; s < cap; s++) {
            int v = tape[head];
            int tr = state * tm.m + v;
            int w = tm.w[state][v];
            if (w < 0) { halted = 1; steps = s; break; }
            if (w != v) {
                if (v == 0 && w != 0) score++;
                else if (v != 0 && w == 0) score--;
            }
            tape[head] = (int8_t)w;
            head += tm.d[state][v];
            state = tm.nx[state][v];
            if (head < head_min) head_min = head;
            if (head > head_max) head_max = head;
            if (head < 0 || (size_t)head >= tcap) tape_grow();
            steps = s + 1;
        }
        printf("%lld,%lld,%d,%lld,%lld,%lld", idx - 1, steps, halted, score, head_min, head_max);
        if (want_rle) { printf(","); rle_print(rad); }
        printf("\n");
        fflush(stdout);
        tape_free();
    }
    fclose(f);
    return 0;
}
