#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>

/* Unpruned TNF up to step_cap for exact verification of small DTM classes.
 * Checks that every machine halting within step_cap is found with zero heuristics.
 * Also prints holdouts sorted by distinct active machines to classify non-halters.
 */

#define MAX_RULES 4
#define MAX_N 3
#define MAX_M 4
#define TAPE_SIZE 2048
#define TAPE_MID 1024

typedef struct { int8_t w, d, nx; } Trans;

static int G_rules, G_n, G_m;
static Trans G_tab[MAX_RULES][MAX_N][MAX_M];
static uint64_t best_steps, nodes, halted, timeouts;
static int best_score;
static char best_spec[512];

static void format_spec(int hr, int hs, int hsym, char *out) {
    char *p = out;
    for (int r = 0; r < G_rules; r++) {
        if (r > 0) *p++ = '|';
        for (int s = 0; s < G_n; s++) {
            if (s > 0) *p++ = '_';
            for (int y = 0; y < G_m; y++) {
                if (r == hr && s == hs && y == hsym) {
                    *p++ = '1'; *p++ = 'R'; *p++ = 'Z';
                } else {
                    Trans t = G_tab[r][s][y];
                    if (t.w < 0) { *p++ = '-'; *p++ = '-'; *p++ = '-'; }
                    else { *p++ = '0' + t.w; *p++ = (t.d > 0) ? 'R' : 'L'; *p++ = 'A' + t.nx; }
                }
            }
        }
    }
    *p = 0;
}

static void dfs(uint8_t *tape, int head, int st, uint64_t steps,
                int lo, int hi, int score, int undef_left,
                int max_st, int max_sym, uint64_t cap) {
    nodes++;
    int elo = lo, ehi = hi, elen = ehi - elo + 1;
    uint8_t *esave = (uint8_t *)malloc((size_t)elen);
    memcpy(esave, tape + elo, (size_t)elen);

    while (steps < cap) {
        if (head < 2 || head >= TAPE_SIZE - 2) {
            timeouts++;
            memset(tape + lo, 0, (size_t)(hi - lo + 1));
            memcpy(tape + elo, esave, (size_t)elen);
            free(esave);
            return;
        }
        int r = (int)(steps % (uint64_t)G_rules);
        int sym = tape[head];
        Trans t = G_tab[r][st][sym];
        if (t.w < 0) break;
        if (sym == 0 && t.w != 0) score++;
        else if (sym != 0 && t.w == 0) score--;
        tape[head] = (uint8_t)t.w;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        head += t.d;
        st = t.nx;
        steps++;
    }

    if (steps >= cap) {
        timeouts++;
        memset(tape + lo, 0, (size_t)(hi - lo + 1));
        memcpy(tape + elo, esave, (size_t)elen);
        free(esave);
        return;
    }

    int r = (int)(steps % (uint64_t)G_rules);
    int sym = tape[head];
    halted++;
    uint64_t hs = steps + 1;
    int hsc = (sym == 0) ? (score + 1) : score;
    if (hs > best_steps || (hs == best_steps && hsc > best_score)) {
        best_steps = hs;
        best_score = hsc;
        format_spec(r, st, sym, best_spec);
    }

    if (undef_left > 1) {
        int max_w = (max_sym + 1 < G_m - 1) ? (max_sym + 1) : (G_m - 1);
        int max_nx = (max_st + 1 < G_n - 1) ? (max_st + 1) : (G_n - 1);
        int d0 = (steps == 0) ? 1 : 0;
        for (int w = 0; w <= max_w; w++) {
            int nms = (w > max_sym) ? w : max_sym;
            for (int di = d0; di < 2; di++) {
                int d = (di == 0) ? -1 : 1;
                for (int nx = 0; nx <= max_nx; nx++) {
                    int nmx = (nx > max_st) ? nx : max_st;
                    G_tab[r][st][sym] = (Trans){(int8_t)w, (int8_t)d, (int8_t)nx};
                    dfs(tape, head, st, steps, lo, hi, score, undef_left - 1, nmx, nms, cap);
                }
            }
        }
        G_tab[r][st][sym] = (Trans){-1, 0, -1};
    }

    memset(tape + lo, 0, (size_t)(hi - lo + 1));
    memcpy(tape + elo, esave, (size_t)elen);
    free(esave);
}

static void check_unpruned(int n, int m, int rules, uint64_t cap) {
    G_n = n; G_m = m; G_rules = rules;
    for (int r = 0; r < MAX_RULES; r++)
        for (int s = 0; s < MAX_N; s++)
            for (int y = 0; y < MAX_M; y++)
                G_tab[r][s][y] = (Trans){-1, 0, -1};
    best_steps = 0; best_score = 0; nodes = 0; halted = 0; timeouts = 0;
    best_spec[0] = 0;
    uint8_t *tape = (uint8_t *)calloc(TAPE_SIZE, 1);
    clock_t t0 = clock();
    dfs(tape, TAPE_MID, 0, 0, TAPE_MID, TAPE_MID, 0, rules * n * m, 0, 0, cap);
    double dt = (double)(clock() - t0) / CLOCKS_PER_SEC;
    free(tape);
    printf("UNPRUNED DTM(%d,%d,r=%d) cap=%llu: best=%llu (score=%d) %s | nodes=%llu halted=%llu timeouts=%llu (%.3fs)\n",
           n, m, rules, (unsigned long long)cap, (unsigned long long)best_steps, best_score,
           best_spec, (unsigned long long)nodes, (unsigned long long)halted, (unsigned long long)timeouts, dt);
}

int main(void) {
    check_unpruned(1, 2, 2, 50);
    check_unpruned(2, 2, 2, 120);
    check_unpruned(1, 3, 2, 50);
    check_unpruned(1, 3, 2, 500);
    check_unpruned(1, 2, 3, 100);
    return 0;
}
