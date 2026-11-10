#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <omp.h>

/* Deep evaluator + 1- & 2-mutant holdout breaker with TC & Bouncer pruning for DTM. */

#define MAX_RULES 4
#define MAX_N 4
#define MAX_M 4
#define TAPE_SZ 1048576
#define TAPE_MID 524288
#define TC_HIST 32
#define TC_WIN  24
#define BNC_HIST 16
#define FILTER_STEPS 8000

typedef struct { int8_t w, d, nx; } Trans;
typedef struct { Trans tab[MAX_RULES][MAX_N][MAX_M]; } Mach;
typedef struct { uint64_t step; int pos; int st; uint8_t ctx[TC_WIN]; } Snap;
typedef struct { uint64_t step; int r; int st; uint8_t edge[12]; } BncSnap;

typedef struct {
    uint8_t tape[TAPE_SZ];
    uint8_t tt[TAPE_SZ];
    Snap rsnaps[TC_HIST], lsnaps[TC_HIST];
    int min_sr[TC_HIST], max_sl[TC_HIST];
    BncSnap rbnc[BNC_HIST], lbnc[BNC_HIST];
} EvalBuf;

static int G_rules = 2, G_n = 3, G_m = 2;

static bool parse_mach(const char *spec, Mach *m) {
    for (int r = 0; r < MAX_RULES; r++)
        for (int s = 0; s < MAX_N; s++)
            for (int y = 0; y < MAX_M; y++)
                m->tab[r][s][y] = (Trans){-1, 0, -1};
    const char *p = spec;
    for (int r = 0; r < G_rules; r++) {
        if (r > 0) { if (*p != '|') return false; p++; }
        for (int s = 0; s < G_n; s++) {
            if (s > 0) { if (*p != '_') return false; p++; }
            for (int y = 0; y < G_m; y++) {
                if (p[0] == '-' && p[1] == '-' && p[2] == '-') {
                    m->tab[r][s][y] = (Trans){-1, 0, -1};
                } else {
                    int w = p[0] - '0';
                    int d = (p[1] == 'R') ? 1 : -1;
                    int nx = (p[2] == 'Z' || p[2] == 'H') ? -1 : (p[2] - 'A');
                    m->tab[r][s][y] = (Trans){(int8_t)w, (int8_t)d, (int8_t)nx};
                }
                p += 3;
            }
        }
    }
    return true;
}

static void format_mach(const Mach *m, char *out) {
    char *p = out;
    for (int r = 0; r < G_rules; r++) {
        if (r > 0) *p++ = '|';
        for (int s = 0; s < G_n; s++) {
            if (s > 0) *p++ = '_';
            for (int y = 0; y < G_m; y++) {
                Trans t = m->tab[r][s][y];
                if (t.w < 0) { *p++ = '-'; *p++ = '-'; *p++ = '-'; }
                else if (t.nx < 0) { *p++ = '0' + t.w; *p++ = (t.d > 0 ? 'R' : 'L'); *p++ = 'Z'; }
                else { *p++ = '0' + t.w; *p++ = (t.d > 0 ? 'R' : 'L'); *p++ = 'A' + t.nx; }
            }
        }
    }
    *p = 0;
}

static bool is_periodic_bouncer(const BncSnap *hist, int cnt) {
    for (int p = 1; p <= 3; p++) {
        int need = 1 + 4 * p;
        if (cnt < need) continue;
        int base = cnt - 1;
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

static int64_t eval_fast(const Mach *m, EvalBuf *buf, uint64_t cap, int *out_score, int *out_span) {
    uint8_t *tape = buf->tape, *tt = buf->tt;
    int head = TAPE_MID, st = 0, lo = TAPE_MID, hi = TAPE_MID, score = 0;
    int ht = TAPE_MID, st_t = 0, lot = TAPE_MID, hit = TAPE_MID;
    uint64_t step_t = 0, power = 1, lam = 1, steps = 0;
    int rules = G_rules;
    int n_r = 0, n_l = 0, rh = 0, lh = 0;
    int max_hi = TAPE_MID - 1, min_lo = TAPE_MID + 1;
    int rb_cnt = 0, lb_cnt = 0;
    int64_t ret = -1;

    uint64_t phase1 = (cap < FILTER_STEPS) ? cap : FILTER_STEPS;
    while (steps < phase1) {
        if (head < TC_WIN + 4 || head >= TAPE_SZ - TC_WIN - 4) goto clean;
        int r = (int)(steps % (uint64_t)rules);
        uint8_t sym = tape[head];
        Trans tr = m->tab[r][st][sym];
        if (tr.w < 0 || tr.nx < 0) {
            if (tr.w > 0 && sym == 0) score++;
            else if (tr.w == 0 && sym != 0) score--;
            *out_score = score; *out_span = hi - lo + 1;
            ret = (int64_t)(steps + 1); goto clean;
        }
        if (steps > 0 && st == st_t && (steps % (uint64_t)rules) == (step_t % (uint64_t)rules) && head == ht) {
            int lmin = (lo < lot) ? lo : lot, rmax = (hi > hit) ? hi : hit;
            if (memcmp(tape + lmin, tt + lmin, (size_t)(rmax - lmin + 1)) == 0) { ret = -2; goto clean; }
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
                int depth = buf->rsnaps[i].pos - buf->min_sr[i];
                if (depth >= 0 && depth < TC_WIN - 1 && r == (int)(buf->rsnaps[i].step % (uint64_t)rules) && st == buf->rsnaps[i].st) {
                    bool ok = true;
                    for (int off = 0; off <= depth; off++) if (tape[head - off] != buf->rsnaps[i].ctx[off]) { ok = false; break; }
                    if (ok) { ret = -2; goto clean; }
                }
            }
            buf->rsnaps[rh].step = steps; buf->rsnaps[rh].pos = head; buf->rsnaps[rh].st = st;
            for (int off = 0; off < TC_WIN; off++) buf->rsnaps[rh].ctx[off] = tape[head - off];
            buf->min_sr[rh] = head; rh = (rh + 1) % TC_HIST; if (n_r < TC_HIST) n_r++;
            if (steps > 400) {
                BncSnap *bs = &buf->rbnc[rb_cnt < BNC_HIST ? rb_cnt : (BNC_HIST - 1)];
                if (rb_cnt >= BNC_HIST) memmove(buf->rbnc, buf->rbnc + 1, (BNC_HIST - 1) * sizeof(BncSnap));
                else rb_cnt++;
                bs->step = steps; bs->r = r; bs->st = st;
                for (int off = 0; off < 12; off++) bs->edge[off] = tape[head - off];
                if (is_periodic_bouncer(buf->rbnc, rb_cnt)) { ret = -3; goto clean; }
            }
        }
        if (head < min_lo) {
            min_lo = head;
            for (int c = 0; c < n_l; c++) {
                int i = (lh - 1 - c + TC_HIST) % TC_HIST;
                int depth = buf->max_sl[i] - buf->lsnaps[i].pos;
                if (depth >= 0 && depth < TC_WIN - 1 && r == (int)(buf->lsnaps[i].step % (uint64_t)rules) && st == buf->lsnaps[i].st) {
                    bool ok = true;
                    for (int off = 0; off <= depth; off++) if (tape[head + off] != buf->lsnaps[i].ctx[off]) { ok = false; break; }
                    if (ok) { ret = -2; goto clean; }
                }
            }
            buf->lsnaps[lh].step = steps; buf->lsnaps[lh].pos = head; buf->lsnaps[lh].st = st;
            for (int off = 0; off < TC_WIN; off++) buf->lsnaps[lh].ctx[off] = tape[head + off];
            buf->max_sl[lh] = head; lh = (lh + 1) % TC_HIST; if (n_l < TC_HIST) n_l++;
            if (steps > 400) {
                BncSnap *bs = &buf->lbnc[lb_cnt < BNC_HIST ? lb_cnt : (BNC_HIST - 1)];
                if (lb_cnt >= BNC_HIST) memmove(buf->lbnc, buf->lbnc + 1, (BNC_HIST - 1) * sizeof(BncSnap));
                else lb_cnt++;
                bs->step = steps; bs->r = r; bs->st = st;
                for (int off = 0; off < 12; off++) bs->edge[off] = tape[head + off];
                if (is_periodic_bouncer(buf->lbnc, lb_cnt)) { ret = -3; goto clean; }
            }
        }
        for (int c = 0; c < n_r; c++) { int i = (rh - 1 - c + TC_HIST) % TC_HIST; if (buf->min_sr[i] <= head) break; buf->min_sr[i] = head; }
        for (int c = 0; c < n_l; c++) { int i = (lh - 1 - c + TC_HIST) % TC_HIST; if (buf->max_sl[i] >= head) break; buf->max_sl[i] = head; }

        if (sym == 0 && tr.w != 0) score++;
        else if (sym != 0 && tr.w == 0) score--;
        tape[head] = (uint8_t)tr.w;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        head += tr.d; st = tr.nx; steps++; lam++;
    }

    while (steps < cap) {
        if (head < 4 || head >= TAPE_SZ - 4) break;
        int r = (int)(steps % (uint64_t)rules);
        uint8_t sym = tape[head];
        Trans tr = m->tab[r][st][sym];
        if (tr.w < 0 || tr.nx < 0) {
            if (tr.w > 0 && sym == 0) score++;
            else if (tr.w == 0 && sym != 0) score--;
            *out_score = score; *out_span = hi - lo + 1;
            ret = (int64_t)(steps + 1); goto clean;
        }
        if (steps > 0 && st == st_t && (steps % (uint64_t)rules) == (step_t % (uint64_t)rules) && head == ht) {
            int lmin = (lo < lot) ? lo : lot, rmax = (hi > hit) ? hi : hit;
            if (memcmp(tape + lmin, tt + lmin, (size_t)(rmax - lmin + 1)) == 0) { ret = -2; goto clean; }
        }
        if (lam == power) {
            memset(tt + lot, 0, (size_t)(hit - lot + 1));
            memcpy(tt + lo, tape + lo, (size_t)(hi - lo + 1));
            ht = head; st_t = st; step_t = steps; lot = lo; hit = hi;
            power *= 2; lam = 0;
        }
        if (sym == 0 && tr.w != 0) score++;
        else if (sym != 0 && tr.w == 0) score--;
        tape[head] = (uint8_t)tr.w;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        head += tr.d; st = tr.nx; steps++; lam++;
    }
    *out_score = score; *out_span = hi - lo + 1;
clean:
    memset(tape + lo, 0, (size_t)(hi - lo + 1));
    memset(tt + lot, 0, (size_t)(hit - lot + 1));
    return ret;
}

int main(int argc, char **argv) {
    const char *path = NULL;
    uint64_t cap = 2000000;
    uint64_t mut_cap = 200000;
    int max_mut_seeds = 4096;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--n") && i + 1 < argc) G_n = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--m") && i + 1 < argc) G_m = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--rules") && i + 1 < argc) G_rules = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--file") && i + 1 < argc) path = argv[++i];
        else if (!strcmp(argv[i], "--cap") && i + 1 < argc) cap = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--mut-cap") && i + 1 < argc) mut_cap = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--mut-seeds") && i + 1 < argc) max_mut_seeds = atoi(argv[++i]);
    }
    if (!path) return 1;

    FILE *f = fopen(path, "r");
    if (!f) return 2;
    char **specs = NULL; int n_specs = 0, cap_sp = 0;
    char line[512];
    while (fgets(line, sizeof(line), f)) {
        size_t l = strlen(line);
        while (l > 0 && (line[l - 1] == '\n' || line[l - 1] == '\r')) line[--l] = 0;
        if (!l) continue;
        if (n_specs >= cap_sp) { cap_sp = cap_sp ? cap_sp * 2 : 1024; specs = realloc(specs, (size_t)cap_sp * sizeof(char *)); }
        specs[n_specs++] = strdup(line);
    }
    fclose(f);

    uint64_t best_s = 0; int best_sc = 0; char best_sp[256] = "";
    int halted_raw = 0, halted_mut = 0, skipped_seeds = 0;

    omp_set_num_threads(16);
    #pragma omp parallel reduction(+:halted_raw,halted_mut,skipped_seeds)
    {
        EvalBuf *buf = (EvalBuf *)calloc(1, sizeof(EvalBuf));
        #pragma omp for schedule(dynamic, 4)
        for (int idx = 0; idx < n_specs; idx++) {
            Mach m; if (!parse_mach(specs[idx], &m)) continue;
            int sc = 0, sp = 0;
            int64_t res = eval_fast(&m, buf, cap, &sc, &sp);
            if (res > 0) {
                halted_raw++;
                if ((uint64_t)res > best_s) {
                    #pragma omp critical
                    if ((uint64_t)res > best_s) {
                        best_s = (uint64_t)res; best_sc = sc; format_mach(&m, best_sp);
                        printf("[RAW HALT] steps=%llu score=%d span=%d %s\n", (unsigned long long)best_s, sc, sp, best_sp);
                        fflush(stdout);
                    }
                }
            } else if (res == -1 && sp <= 80 && mut_cap > 0) {
                if (idx >= max_mut_seeds) { skipped_seeds++; continue; }
                for (int r = 0; r < G_rules; r++)
                    for (int s = 0; s < G_n; s++)
                        for (int y = 0; y < G_m; y++) {
                            if (r == 0 && s == 0 && y == 0) continue;
                            Trans orig = m.tab[r][s][y];
                            Mach mu = m;
                            for (int mode = 0; mode < 1 + 2 * G_m * G_n; mode++) {
                                if (mode == 0) {
                                    mu.tab[r][s][y] = (Trans){1, 1, -1};
                                } else {
                                    int k = mode - 1;
                                    int nx = k % G_n; k /= G_n;
                                    int d = (k % 2) ? 1 : -1; k /= 2;
                                    int w = k;
                                    if (w == orig.w && d == orig.d && nx == orig.nx) continue;
                                    mu.tab[r][s][y] = (Trans){(int8_t)w, (int8_t)d, (int8_t)nx};
                                }
                                int msc = 0, msp = 0;
                                int64_t mres = eval_fast(&mu, buf, mut_cap, &msc, &msp);
                                if (mres > 0) {
                                    halted_mut++;
                                    if ((uint64_t)mres > best_s) {
                                        #pragma omp critical
                                        if ((uint64_t)mres > best_s) {
                                            best_s = (uint64_t)mres; best_sc = msc; format_mach(&mu, best_sp);
                                            printf("[MUT HALT] steps=%llu score=%d span=%d %s\n",
                                                   (unsigned long long)best_s, msc, msp, best_sp);
                                            fflush(stdout);
                                        }
                                    }
                                }
                            }
                        }
            }
        }
        free(buf);
    }

    printf("Checked %d holdouts (mut_skipped=%d) -> raw_halted=%d, mut_halted=%d, best=%llu (score=%d, %s)\n",
           n_specs, skipped_seeds, halted_raw, halted_mut, (unsigned long long)best_s, best_sc, best_sp);
    for (int i = 0; i < n_specs; i++) free(specs[i]);
    free(specs);
    return 0;
}
