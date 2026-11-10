#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include <omp.h>

/* 16-thread TNF Filtered Champion Hunter for DTM(n, m, rules).
 * Catches:
 *   1) Exact Cyclers (Brent power-of-2)
 *   2) Translated Cyclers (left & right record snapshot depth check)
 *   3) Quadratic Bouncers (period 1, 2, 3 arithmetic progression of expansion intervals
 *      + identical (rule, state, 12-cell tape edge) on BOTH left and right expansions)
 * Promotes remaining anomalies through tight zero-overhead Stage 3 loop up to G_tier3!
 */

#define MAX_RULES 4
#define MAX_N 4
#define MAX_M 4
#define MAX_DEPTH 18
#define FAST_TAPE 4096
#define FAST_MID  2048
#define ULTRA_TAPE 524288
#define ULTRA_MID  262144
#define TC_HIST 32
#define TC_WIN  24
#define BNC_HIST 16

typedef struct { int8_t w, d, nx; } Trans;
typedef struct { uint64_t step; int pos; int st; uint8_t ctx[TC_WIN]; } Snap;
typedef struct { uint64_t step; int r; int st; uint8_t edge[12]; } BncSnap;

typedef struct {
    Trans tab[MAX_RULES][MAX_N][MAX_M];
    int undef_left, max_st, max_sym, head, st, lo, hi, score, tape_len;
    uint64_t steps;
    uint8_t tape[FAST_TAPE];
} WorkItem;

typedef struct {
    Trans tab[MAX_RULES][MAX_N][MAX_M];
    uint8_t tapes[MAX_DEPTH][FAST_TAPE];
    uint8_t u_tape[ULTRA_TAPE];
    uint8_t u_tt[ULTRA_TAPE];
    Snap rsnaps[TC_HIST], lsnaps[TC_HIST];
    int min_sr[TC_HIST], max_sl[TC_HIST];
    uint64_t nodes, halted, cyclers, bouncers, holdouts, best_steps;
    int best_score;
    char best_spec[256];
    char *holdout_specs[512];
    int n_hold;
} ThreadCtx;

static int G_rules = 2, G_n = 3, G_m = 2;
static uint64_t G_tier1 = 400;
static uint64_t G_tier2 = 6000;
static uint64_t G_tier3 = 50000;
static int G_split_depth = 4;

static WorkItem *G_items = NULL;
static int G_n_items = 0, G_cap_items = 0;

static uint64_t G_pre_nodes = 0, G_pre_halted = 0, G_pre_cyclers = 0, G_pre_bouncers = 0, G_pre_holdouts = 0;
static uint64_t G_pre_best_steps = 0;
static int G_pre_best_score = 0;
static char G_pre_best_spec[256] = "";

static void format_spec_tab(const Trans tab[MAX_RULES][MAX_N][MAX_M],
                            int hr, int hs, int hsym, char *out) {
    char *p = out;
    for (int r = 0; r < G_rules; r++) {
        if (r > 0) *p++ = '|';
        for (int s = 0; s < G_n; s++) {
            if (s > 0) *p++ = '_';
            for (int y = 0; y < G_m; y++) {
                if (r == hr && s == hs && y == hsym) {
                    *p++ = '1'; *p++ = 'R'; *p++ = 'Z';
                } else {
                    Trans t = tab[r][s][y];
                    if (t.w < 0) { *p++ = '-'; *p++ = '-'; *p++ = '-'; }
                    else { *p++ = '0' + t.w; *p++ = (t.d > 0) ? 'R' : 'L'; *p++ = 'A' + t.nx; }
                }
            }
        }
    }
    *p = 0;
}

static bool is_periodic_bouncer(const BncSnap *hist, int cnt) {
    /* Need sufficient history after initial transient: check periods p = 1, 2, 3 */
    for (int p = 1; p <= 3; p++) {
        int need = 1 + 4 * p; /* >= 4 full period-p transitions */
        if (cnt < need) continue;
        int base = cnt - 1;
        /* Check dt[k] - dt[k-p] is constant >= 0 across 3 consecutive intervals and matches edge+state */
        uint64_t dt0 = hist[base].step - hist[base - p].step;
        uint64_t dt1 = hist[base - p].step - hist[base - 2 * p].step;
        int64_t ddt = (int64_t)dt0 - (int64_t)dt1;
        if (ddt < 0 || dt0 < 4) continue;
        bool ok = true;
        for (int g = 0; g < 3 * p; g++) {
            int idx = base - g;
            if (hist[idx].r != hist[idx - p].r || hist[idx].st != hist[idx - p].st ||
                memcmp(hist[idx].edge, hist[idx - p].edge, 12) != 0) {
                ok = false; break;
            }
            if (g < 2 * p) {
                uint64_t d_a = hist[idx].step - hist[idx - p].step;
                uint64_t d_b = hist[idx - p].step - hist[idx - 2 * p].step;
                if ((int64_t)d_a - (int64_t)d_b != ddt) { ok = false; break; }
            }
        }
        if (ok) return true;
    }
    return false;
}

static int64_t eval_leaf(ThreadCtx *ctx, int *out_hr, int *out_hs, int *out_hy, int *out_score, int *out_span) {
    uint8_t *tape = ctx->u_tape, *tt = ctx->u_tt;
    const Trans (*tab)[MAX_N][MAX_M] = ctx->tab;
    int rules = G_rules;

    int head = ULTRA_MID, st = 0, lo = ULTRA_MID, hi = ULTRA_MID, score = 0;
    int ht = ULTRA_MID, st_t = 0, lot = ULTRA_MID, hit = ULTRA_MID;
    uint64_t step_t = 0, power = 1, lam = 1, steps = 0;

    int n_r = 0, n_l = 0, rh = 0, lh = 0;
    int max_hi = ULTRA_MID - 1, min_lo = ULTRA_MID + 1;

    BncSnap rbnc[BNC_HIST], lbnc[BNC_HIST];
    int rb_cnt = 0, lb_cnt = 0;

    int64_t ret = -1;

    while (steps < G_tier2) {
        if (head < TC_WIN + 4 || head >= ULTRA_TAPE - TC_WIN - 4) { ret = -1; goto cleanup; }
        int r = (int)(steps % (uint64_t)rules);
        uint8_t sym = tape[head];
        Trans tr = tab[r][st][sym];
        if (tr.w < 0) {
            *out_hr = r; *out_hs = st; *out_hy = sym;
            *out_score = (sym == 0) ? (score + 1) : score;
            *out_span = hi - lo + 1;
            ret = (int64_t)steps;
            goto cleanup;
        }
        if (steps > 0 && st == st_t && (steps % (uint64_t)rules) == (step_t % (uint64_t)rules) && head == ht) {
            int lmin = (lo < lot) ? lo : lot, rmax = (hi > hit) ? hi : hit;
            if (memcmp(tape + lmin, tt + lmin, (size_t)(rmax - lmin + 1)) == 0) { ret = -2; goto cleanup; }
        }
        if (lam == power) {
            memset(tt + lot, 0, (size_t)(hit - lot + 1));
            memcpy(tt + lo, tape + lo, (size_t)(hi - lo + 1));
            ht = head; st_t = st; step_t = steps; lot = lo; hit = hi;
            power *= 2; lam = 0;
        }
        if (head > max_hi) {
            max_hi = head;
            for (int c = 0; c < n_r; c++) {
                int i = (rh - 1 - c + TC_HIST) % TC_HIST;
                int depth = ctx->rsnaps[i].pos - ctx->min_sr[i];
                if (depth >= 0 && depth < TC_WIN - 1 && r == (int)(ctx->rsnaps[i].step % (uint64_t)rules) && st == ctx->rsnaps[i].st) {
                    bool ok = true;
                    for (int off = 0; off <= depth; off++) if (tape[head - off] != ctx->rsnaps[i].ctx[off]) { ok = false; break; }
                    if (ok) { ret = -2; goto cleanup; }
                }
            }
            ctx->rsnaps[rh].step = steps; ctx->rsnaps[rh].pos = head; ctx->rsnaps[rh].st = st;
            for (int off = 0; off < TC_WIN; off++) ctx->rsnaps[rh].ctx[off] = tape[head - off];
            ctx->min_sr[rh] = head; rh = (rh + 1) % TC_HIST; if (n_r < TC_HIST) n_r++;

            if (steps > 400) {
                BncSnap *bs = &rbnc[rb_cnt < BNC_HIST ? rb_cnt : (BNC_HIST - 1)];
                if (rb_cnt >= BNC_HIST) { memmove(rbnc, rbnc + 1, (BNC_HIST - 1) * sizeof(BncSnap)); }
                else rb_cnt++;
                bs->step = steps; bs->r = r; bs->st = st;
                for (int off = 0; off < 12; off++) bs->edge[off] = tape[head - off];
                if (is_periodic_bouncer(rbnc, rb_cnt)) { ret = -3; goto cleanup; }
            }
        }
        if (head < min_lo) {
            min_lo = head;
            for (int c = 0; c < n_l; c++) {
                int i = (lh - 1 - c + TC_HIST) % TC_HIST;
                int depth = ctx->max_sl[i] - ctx->lsnaps[i].pos;
                if (depth >= 0 && depth < TC_WIN - 1 && r == (int)(ctx->lsnaps[i].step % (uint64_t)rules) && st == ctx->lsnaps[i].st) {
                    bool ok = true;
                    for (int off = 0; off <= depth; off++) if (tape[head + off] != ctx->lsnaps[i].ctx[off]) { ok = false; break; }
                    if (ok) { ret = -2; goto cleanup; }
                }
            }
            ctx->lsnaps[lh].step = steps; ctx->lsnaps[lh].pos = head; ctx->lsnaps[lh].st = st;
            for (int off = 0; off < TC_WIN; off++) ctx->lsnaps[lh].ctx[off] = tape[head + off];
            ctx->max_sl[lh] = head; lh = (lh + 1) % TC_HIST; if (n_l < TC_HIST) n_l++;

            if (steps > 400) {
                BncSnap *bs = &lbnc[lb_cnt < BNC_HIST ? lb_cnt : (BNC_HIST - 1)];
                if (lb_cnt >= BNC_HIST) { memmove(lbnc, lbnc + 1, (BNC_HIST - 1) * sizeof(BncSnap)); }
                else lb_cnt++;
                bs->step = steps; bs->r = r; bs->st = st;
                for (int off = 0; off < 12; off++) bs->edge[off] = tape[head + off];
                if (is_periodic_bouncer(lbnc, lb_cnt)) { ret = -3; goto cleanup; }
            }
        }
        for (int c = 0; c < n_r; c++) { int i = (rh - 1 - c + TC_HIST) % TC_HIST; if (ctx->min_sr[i] <= head) break; ctx->min_sr[i] = head; }
        for (int c = 0; c < n_l; c++) { int i = (lh - 1 - c + TC_HIST) % TC_HIST; if (ctx->max_sl[i] >= head) break; ctx->max_sl[i] = head; }

        if (sym == 0 && tr.w != 0) score++;
        else if (sym != 0 && tr.w == 0) score--;
        tape[head] = (uint8_t)tr.w;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        head += tr.d; st = tr.nx; steps++; lam++;
    }

    memset(tt + lot, 0, (size_t)(hit - lot + 1));
    lot = hit = ULTRA_MID;
    while (steps < G_tier3) {
        if (head < 4 || head >= ULTRA_TAPE - 4) break;
        int r = (int)(steps % (uint64_t)rules);
        uint8_t sym = tape[head];
        Trans tr = tab[r][st][sym];
        if (tr.w < 0) {
            *out_hr = r; *out_hs = st; *out_hy = sym;
            *out_score = (sym == 0) ? (score + 1) : score;
            *out_span = hi - lo + 1;
            ret = (int64_t)steps;
            goto cleanup;
        }
        if (sym == 0 && tr.w != 0) score++;
        else if (sym != 0 && tr.w == 0) score--;
        tape[head] = (uint8_t)tr.w;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        head += tr.d; st = tr.nx; steps++;
    }
    *out_span = hi - lo + 1;
    ret = -1;

cleanup:
    memset(tape + lo, 0, (size_t)(hi - lo + 1));
    memset(tt + lot, 0, (size_t)(hit - lot + 1));
    return ret;
}

static void worker_dfs(ThreadCtx *ctx, int depth, int head, int st, uint64_t steps,
                       int lo, int hi, int score, int undef_left, int max_st, int max_sym) {
    ctx->nodes++;
    uint8_t *tape = ctx->tapes[depth];

    while (steps < G_tier1) {
        if (head < 2 || head >= FAST_TAPE - 2) break;
        int r = (int)(steps % (uint64_t)G_rules);
        int sym = tape[head];
        Trans t = ctx->tab[r][st][sym];
        if (t.w < 0) {
            ctx->halted++;
            uint64_t hs = steps + 1;
            int hsc = (sym == 0) ? (score + 1) : score;
            if (hs > ctx->best_steps || (hs == ctx->best_steps && hsc > ctx->best_score)) {
                ctx->best_steps = hs; ctx->best_score = hsc;
                format_spec_tab(ctx->tab, r, st, sym, ctx->best_spec);
            }
            if (undef_left <= 1 || depth + 1 >= MAX_DEPTH) {
                memset(tape + lo, 0, (size_t)(hi - lo + 1));
                return;
            }
            int max_w = (max_sym + 1 < G_m - 1) ? (max_sym + 1) : (G_m - 1);
            int max_nx = (max_st + 1 < G_n - 1) ? (max_st + 1) : (G_n - 1);
            int d0 = (steps == 0) ? 1 : 0;
            int clen = hi - lo + 1;
            uint8_t *child_tape = ctx->tapes[depth + 1];

            for (int w = 0; w <= max_w; w++) {
                int nms = (w > max_sym) ? w : max_sym;
                for (int di = d0; di < 2; di++) {
                    int d = (di == 0) ? -1 : 1;
                    for (int nx = 0; nx <= max_nx; nx++) {
                        int nmx = (nx > max_st) ? nx : max_st;
                        ctx->tab[r][st][sym] = (Trans){(int8_t)w, (int8_t)d, (int8_t)nx};
                        memcpy(child_tape + lo, tape + lo, (size_t)clen);
                        worker_dfs(ctx, depth + 1, head, st, steps, lo, hi, score, undef_left - 1, nmx, nms);
                    }
                }
            }
            ctx->tab[r][st][sym] = (Trans){-1, 0, -1};
            memset(tape + lo, 0, (size_t)clen);
            return;
        }
        if (sym == 0 && t.w != 0) score++;
        else if (sym != 0 && t.w == 0) score--;
        tape[head] = (uint8_t)t.w;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        head += t.d; st = t.nx; steps++;
    }

    memset(tape + lo, 0, (size_t)(hi - lo + 1));
    int hr, hs, hy, hsc, span = 0;
    int64_t er = eval_leaf(ctx, &hr, &hs, &hy, &hsc, &span);
    if (er == -2) ctx->cyclers++;
    else if (er == -3) ctx->bouncers++;
    else if (er == -1) {
        ctx->holdouts++;
        if (span <= 80 && ctx->n_hold < 512) {
            char buf[256]; format_spec_tab(ctx->tab, -1, -1, -1, buf);
            ctx->holdout_specs[ctx->n_hold++] = strdup(buf);
        }
    } else {
        ctx->halted++;
        uint64_t hsteps = (uint64_t)er + 1;
        if (hsteps > ctx->best_steps || (hsteps == ctx->best_steps && hsc > ctx->best_score)) {
            ctx->best_steps = hsteps; ctx->best_score = hsc;
            format_spec_tab(ctx->tab, hr, hs, hy, ctx->best_spec);
        }
    }
}

static ThreadCtx *P_ctx = NULL;

static void gen_prefixes(int depth, int head, int st, uint64_t steps,
                         int lo, int hi, int score, int undef_left, int max_st, int max_sym) {
    if (depth >= G_split_depth) {
        if (G_n_items >= G_cap_items) {
            G_cap_items = (G_cap_items == 0) ? 65536 : (G_cap_items * 2);
            G_items = (WorkItem *)realloc(G_items, (size_t)G_cap_items * sizeof(WorkItem));
        }
        WorkItem *it = &G_items[G_n_items++];
        memcpy(it->tab, P_ctx->tab, sizeof(it->tab));
        it->undef_left = undef_left; it->max_st = max_st; it->max_sym = max_sym;
        it->head = head; it->st = st; it->steps = steps;
        it->lo = lo; it->hi = hi; it->score = score; it->tape_len = hi - lo + 1;
        memcpy(it->tape + lo, P_ctx->tapes[depth] + lo, (size_t)it->tape_len);
        memset(P_ctx->tapes[depth] + lo, 0, (size_t)it->tape_len);
        return;
    }

    G_pre_nodes++;
    uint8_t *tape = P_ctx->tapes[depth];

    while (steps < G_tier1) {
        if (head < 2 || head >= FAST_TAPE - 2) break;
        int r = (int)(steps % (uint64_t)G_rules);
        int sym = tape[head];
        Trans t = P_ctx->tab[r][st][sym];
        if (t.w < 0) {
            G_pre_halted++;
            uint64_t hs = steps + 1;
            int hsc = (sym == 0) ? (score + 1) : score;
            if (hs > G_pre_best_steps || (hs == G_pre_best_steps && hsc > G_pre_best_score)) {
                G_pre_best_steps = hs; G_pre_best_score = hsc;
                format_spec_tab(P_ctx->tab, r, st, sym, G_pre_best_spec);
            }
            if (undef_left <= 1) { memset(tape + lo, 0, (size_t)(hi - lo + 1)); return; }
            int max_w = (max_sym + 1 < G_m - 1) ? (max_sym + 1) : (G_m - 1);
            int max_nx = (max_st + 1 < G_n - 1) ? (max_st + 1) : (G_n - 1);
            int d0 = (steps == 0) ? 1 : 0;
            int clen = hi - lo + 1;
            uint8_t *child_tape = P_ctx->tapes[depth + 1];

            for (int w = 0; w <= max_w; w++) {
                int nms = (w > max_sym) ? w : max_sym;
                for (int di = d0; di < 2; di++) {
                    int d = (di == 0) ? -1 : 1;
                    for (int nx = 0; nx <= max_nx; nx++) {
                        int nmx = (nx > max_st) ? nx : max_st;
                        P_ctx->tab[r][st][sym] = (Trans){(int8_t)w, (int8_t)d, (int8_t)nx};
                        memcpy(child_tape + lo, tape + lo, (size_t)clen);
                        gen_prefixes(depth + 1, head, st, steps, lo, hi, score, undef_left - 1, nmx, nms);
                    }
                }
            }
            P_ctx->tab[r][st][sym] = (Trans){-1, 0, -1};
            memset(tape + lo, 0, (size_t)clen);
            return;
        }
        if (sym == 0 && t.w != 0) score++;
        else if (sym != 0 && t.w == 0) score--;
        tape[head] = (uint8_t)t.w;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        head += t.d; st = t.nx; steps++;
    }
    memset(tape + lo, 0, (size_t)(hi - lo + 1));
    int hr, hs, hy, hsc, span = 0;
    int64_t er = eval_leaf(P_ctx, &hr, &hs, &hy, &hsc, &span);
    if (er == -2) G_pre_cyclers++;
    else if (er == -3) G_pre_bouncers++;
    else if (er == -1) G_pre_holdouts++;
    else {
        G_pre_halted++;
        uint64_t hsteps = (uint64_t)er + 1;
        if (hsteps > G_pre_best_steps) {
            G_pre_best_steps = hsteps; G_pre_best_score = hsc;
            format_spec_tab(P_ctx->tab, hr, hs, hy, G_pre_best_spec);
        }
    }
}

int main(int argc, char **argv) {
    int threads = 16, stride = 1;
    const char *holdout_out = NULL;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--n") && i + 1 < argc) G_n = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--m") && i + 1 < argc) G_m = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--rules") && i + 1 < argc) G_rules = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--tier1") && i + 1 < argc) G_tier1 = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--tier2") && i + 1 < argc) G_tier2 = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--tier3") && i + 1 < argc) G_tier3 = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--split") && i + 1 < argc) G_split_depth = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--threads") && i + 1 < argc) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--stride") && i + 1 < argc) stride = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--compact") && i + 1 < argc) holdout_out = argv[++i];
    }

    P_ctx = (ThreadCtx *)calloc(1, sizeof(ThreadCtx));
    for (int r = 0; r < MAX_RULES; r++)
        for (int s = 0; s < MAX_N; s++)
            for (int y = 0; y < MAX_M; y++)
                P_ctx->tab[r][s][y] = (Trans){-1, 0, -1};

    double t0 = omp_get_wtime();
    gen_prefixes(0, FAST_MID, 0, 0, FAST_MID, FAST_MID, 0, G_rules * G_n * G_m, 0, 0);
    double t1 = omp_get_wtime();

    int selected = 0;
    for (int i = 0; i < G_n_items; i += stride) {
        if (i != selected) G_items[selected] = G_items[i];
        selected++;
    }

    printf("BOUNCER-TNF DTM(%d,%d,r=%d) split=%d -> %d items, running %d (stride=%d), t1=%llu t2=%llu t3=%llu\n",
           G_n, G_m, G_rules, G_split_depth, G_n_items, selected, stride,
           (unsigned long long)G_tier1, (unsigned long long)G_tier2, (unsigned long long)G_tier3);
    fflush(stdout);

    omp_set_num_threads(threads);
    ThreadCtx *ctxs = (ThreadCtx *)calloc((size_t)threads, sizeof(ThreadCtx));
    for (int t = 0; t < threads; t++) {
        ctxs[t].best_steps = G_pre_best_steps; ctxs[t].best_score = G_pre_best_score;
        strcpy(ctxs[t].best_spec, G_pre_best_spec);
    }

    int done_items = 0;
    double last_rep = t1;

    #pragma omp parallel for schedule(dynamic, 1)
    for (int idx = 0; idx < selected; idx++) {
        int tid = omp_get_thread_num();
        ThreadCtx *c = &ctxs[tid];
        const WorkItem *it = &G_items[idx];
        memcpy(c->tab, it->tab, sizeof(c->tab));
        memcpy(c->tapes[0] + it->lo, it->tape + it->lo, (size_t)it->tape_len);
        worker_dfs(c, 0, it->head, it->st, it->steps, it->lo, it->hi, it->score,
                   it->undef_left, it->max_st, it->max_sym);

        int cur;
        #pragma omp atomic capture
        cur = ++done_items;
        if ((cur & 3) == 0 || cur == selected) {
            #pragma omp critical
            {
                double now = omp_get_wtime();
                if (now - last_rep >= 2.0 || cur == selected) {
                    last_rep = now;
                    uint64_t tn = G_pre_nodes, th = G_pre_halted, tc = G_pre_cyclers, tbnc = G_pre_bouncers, tho = G_pre_holdouts, tb = G_pre_best_steps;
                    char bs[256]; strcpy(bs, G_pre_best_spec);
                    for (int k = 0; k < threads; k++) {
                        tn += ctxs[k].nodes; th += ctxs[k].halted; tc += ctxs[k].cyclers; tbnc += ctxs[k].bouncers; tho += ctxs[k].holdouts;
                        if (ctxs[k].best_steps > tb) { tb = ctxs[k].best_steps; strcpy(bs, ctxs[k].best_spec); }
                    }
                    printf("  [%d/%d %.1f%%] %.1fs | nodes=%llu (%.2fM/s) halted=%llu cyc=%llu bnc=%llu hold=%llu | best=%llu %s\n",
                           cur, selected, 100.0 * cur / (selected ? selected : 1), now - t1,
                           (unsigned long long)tn, (double)tn / 1e6 / (now - t1 + 1e-6),
                           (unsigned long long)th, (unsigned long long)tc, (unsigned long long)tbnc, (unsigned long long)tho,
                           (unsigned long long)tb, bs);
                    fflush(stdout);
                }
            }
        }
    }

    uint64_t tn = G_pre_nodes, th = G_pre_halted, tc = G_pre_cyclers, tbnc = G_pre_bouncers, tho = G_pre_holdouts, tb = G_pre_best_steps;
    int tsc = G_pre_best_score; char bs[256]; strcpy(bs, G_pre_best_spec);
    for (int k = 0; k < threads; k++) {
        tn += ctxs[k].nodes; th += ctxs[k].halted; tc += ctxs[k].cyclers; tbnc += ctxs[k].bouncers; tho += ctxs[k].holdouts;
        if (ctxs[k].best_steps > tb || (ctxs[k].best_steps == tb && ctxs[k].best_score > tsc)) {
            tb = ctxs[k].best_steps; tsc = ctxs[k].best_score; strcpy(bs, ctxs[k].best_spec);
        }
    }
    printf("DONE in %.2fs: best_steps=%llu score=%d spec=%s\n",
           omp_get_wtime() - t0, (unsigned long long)tb, tsc, bs);
    printf("  nodes=%llu halted=%llu cyclers=%llu bouncers=%llu holdouts=%llu\n",
           (unsigned long long)tn, (unsigned long long)th, (unsigned long long)tc,
           (unsigned long long)tbnc, (unsigned long long)tho);

    if (holdout_out) {
        FILE *cf = fopen(holdout_out, "w");
        if (cf) {
            for (int k = 0; k < threads; k++)
                for (int j = 0; j < ctxs[k].n_hold; j++) {
                    fprintf(cf, "%s\n", ctxs[k].holdout_specs[j]);
                    free(ctxs[k].holdout_specs[j]);
                }
            fclose(cf);
        }
    }
    free(ctxs); free(P_ctx); free(G_items);
    return 0;
}
