#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>

/* Fast native simulator & random/mutation searcher for Double Turing Machines:
 *   - DTM(n, m)       : 2 rules, each n states x m symbols
 *   - DTM(n, m, a)    : a rules, each n states x m symbols (active = step % a)
 *   - DTM(n, m, a, b) : 2 rules with independent (n,m) and (a,b) dimensions
 *
 * Usage:
 *   dtm_fast --sim "<spec>" [--cap 10000000] [--slice-rad 40]
 *   dtm_fast --search --n 3 --m 2 --rules 2 [--a 0 --b 0] --budget-ms 1500 --cap 200000 [--seed 42]
 *   dtm_fast --mutate "<spec>" --budget-ms 1500 --cap 500000 [--seed 42]
 */

#define MAX_RULES 16
#define MAX_SCHED 64
#define MAX_N 10
#define MAX_M 10
#define INIT_TAPE 65536
#define MAX_TAPE  (1u << 24)

typedef struct {
    int8_t w;   /* -1 = undef/halt */
    int8_t d;   /* -1 or +1 */
    int8_t nx;  /* -1 = HALT (explicit), >=0 next state */
} Trans;

typedef struct {
    int states;
    int symbols;
    Trans tab[MAX_N][MAX_M];
} Rule;

typedef struct {
    int num_rules;
    Rule rules[MAX_RULES];
    int sched_len;
    int sched[MAX_SCHED];
    char order_str[128];
} DTM;

static int parse_rule(const char *s, int len, Rule *r) {
    /* count '_' */
    int blocks = 1;
    for (int i = 0; i < len; i++) if (s[i] == '_') blocks++;
    if (blocks < 1 || blocks > MAX_N) return -1;
    int blen = 0;
    while (blen < len && s[blen] != '_') blen++;
    if (blen == 0 || blen % 3 != 0) return -1;
    int syms = blen / 3;
    if (syms < 1 || syms > MAX_M) return -1;
    if (len != blocks * blen + (blocks - 1)) return -1;

    r->states = blocks;
    r->symbols = syms;
    const char *p = s;
    for (int st = 0; st < blocks; st++) {
        for (int sym = 0; sym < syms; sym++) {
            const char *tok = p + 3 * sym;
            if (tok[0] == '-' && tok[1] == '-' && tok[2] == '-') {
                r->tab[st][sym] = (Trans){-1, 0, -1};
            } else {
                if (tok[0] < '0' || tok[0] > '9') return -1;
                int w = tok[0] - '0';
                int d = (tok[1] == 'R') ? 1 : (tok[1] == 'L' ? -1 : 0);
                if (d == 0) return -1;
                char c = tok[2];
                int nx = (c == 'Z' || c == 'H') ? -1 : (c - 'A');
                if (nx < -1 || nx >= MAX_N) return -1;
                r->tab[st][sym] = (Trans){(int8_t)w, (int8_t)d, (int8_t)nx};
            }
        }
        p += blen + 1;
    }
    return 0;
}

static int parse_order_str(const char *s, int *sched, int *out_len, int *out_max_r, char *norm_out, size_t norm_cap) {
    int len = 0, max_r = 0;
    const char *p = s;
    if (*p == '{') p++;
    size_t npos = 0;
    while (*p && *p != '}') {
        if (*p == 'r' || *p == 'R') {
            p++;
            if (*p < '1' || *p > '9') return -1;
            int val = 0;
            while (*p >= '0' && *p <= '9') { val = val * 10 + (*p - '0'); p++; }
            if (val < 1 || val > MAX_RULES || len >= MAX_SCHED) return -1;
            sched[len++] = val - 1;
            if (val > max_r) max_r = val;
            if (npos + 4 < norm_cap) {
                npos += (size_t)snprintf(norm_out + npos, norm_cap - npos, "r%d", val);
            }
        } else if (*p == ',' || *p == ' ' || *p == '-') {
            p++;
        } else {
            return -1;
        }
    }
    if (len <= 0) return -1;
    norm_out[npos] = '\0';
    *out_len = len;
    *out_max_r = max_r;
    return 0;
}

static bool is_identity_sched(const int *sched, int len, int num_rules) {
    if (len != num_rules) return false;
    for (int i = 0; i < len; i++) if (sched[i] != i) return false;
    return true;
}

static int parse_dtm(const char *spec, DTM *m) {
    m->num_rules = 0;
    m->sched_len = 0;
    m->order_str[0] = '\0';

    char buf[1024];
    size_t slen = strlen(spec);
    if (slen >= sizeof(buf)) return -1;
    memcpy(buf, spec, slen + 1);

    while (slen > 0 && (buf[slen - 1] == ' ' || buf[slen - 1] == '\t' || buf[slen - 1] == '\n' || buf[slen - 1] == '\r'))
        buf[--slen] = '\0';

    bool has_order = false;
    int max_r_ord = 0;
    if (slen > 0 && buf[slen - 1] == '}') {
        char *open = strrchr(buf, '{');
        if (!open) return -1;
        if (parse_order_str(open, m->sched, &m->sched_len, &max_r_ord, m->order_str, sizeof(m->order_str)) != 0)
            return -1;
        has_order = true;
        if (open > buf && *(open - 1) == '@') open--;
        *open = '\0';
    }

    const char *p = buf;
    while (*p) {
        while (*p == ' ' || *p == '\t' || *p == '|') p++;
        if (!*p) break;
        const char *q = p;
        while (*q && *q != '|') q++;
        int len = (int)(q - p);
        while (len > 0 && (p[len - 1] == ' ' || p[len - 1] == '\t')) len--;
        if (m->num_rules >= MAX_RULES) return -1;
        if (parse_rule(p, len, &m->rules[m->num_rules]) != 0) return -1;
        m->num_rules++;
        p = q;
    }
    if (m->num_rules <= 0) return -1;
    if (has_order) {
        if (max_r_ord > m->num_rules) return -1;
        if (is_identity_sched(m->sched, m->sched_len, m->num_rules)) {
            m->order_str[0] = '\0';
        }
    } else {
        m->sched_len = m->num_rules;
        for (int i = 0; i < m->num_rules; i++) m->sched[i] = i;
    }
    return 0;
}

static void format_dtm(const DTM *m, char *out) {
    char *p = out;
    for (int r = 0; r < m->num_rules; r++) {
        if (r > 0) *p++ = '|';
        const Rule *rl = &m->rules[r];
        for (int s = 0; s < rl->states; s++) {
            if (s > 0) *p++ = '_';
            for (int y = 0; y < rl->symbols; y++) {
                Trans t = rl->tab[s][y];
                if (t.w < 0) {
                    *p++ = '-'; *p++ = '-'; *p++ = '-';
                } else {
                    *p++ = (char)('0' + t.w);
                    *p++ = (t.d > 0) ? 'R' : 'L';
                    *p++ = (t.nx < 0) ? 'Z' : (char)('A' + t.nx);
                }
            }
        }
    }
    if (m->order_str[0] && !is_identity_sched(m->sched, m->sched_len, m->num_rules)) {
        p += sprintf(p, "{%s}", m->order_str);
    }
    *p = '\0';
}

typedef struct {
    uint64_t steps;
    int halted;        /* 1 = halted, 0 = cap/cycler */
    int cycle_type;    /* 0 = none, 1 = cycler, 2 = translated_cycler */
    int64_t score;     /* non-zero count */
    int64_t ones;      /* symbol==1 count */
    int64_t head;      /* relative to start 0 */
    int state;
    int rule_idx;
    int64_t min_pos;
    int64_t max_pos;
    char halt_reason[128];
} SimOutcome;

static void simulate_dtm(const DTM *m, uint64_t cap, uint8_t **out_tape, size_t *out_cap,
                         int64_t *out_origin, SimOutcome *out, bool want_cycle_det) {
    size_t tcap = INIT_TAPE;
    uint8_t *tape = (uint8_t *)calloc(tcap, 1);
    int64_t origin = (int64_t)(tcap / 2);
    int64_t head = origin;
    int64_t lo_w = origin, hi_w = origin;
    int64_t min_rel = 0, max_rel = 0;
    int st = 0;
    int64_t score = 0, ones = 0;
    uint64_t steps = 0;
    int slen = (m->sched_len > 0) ? m->sched_len : m->num_rules;

    /* Brent exact cycler detection on small tapes */
    size_t bcap = 0;
    uint8_t *tt = NULL;
    int64_t ht = origin, lor_t = origin, hir_t = origin, t_orig = origin;
    int st_t = 0;
    uint64_t step_t = 0, power = 1, lam = 1;
    if (want_cycle_det) {
        bcap = INIT_TAPE;
        tt = (uint8_t *)calloc(bcap, 1);
        t_orig = (int64_t)(bcap / 2);
        ht = t_orig; lor_t = t_orig; hir_t = t_orig;
    }

    /* Translated cycler snapshot tracking */
    #define FAST_TC_HIST 128
    #define FAST_TC_WIN  96
    typedef struct { uint64_t step; int64_t pos; int st; uint8_t ctx[FAST_TC_WIN]; } FSnap;
    FSnap *rsnaps = want_cycle_det ? (FSnap *)malloc(FAST_TC_HIST * sizeof(FSnap)) : NULL;
    FSnap *lsnaps = want_cycle_det ? (FSnap *)malloc(FAST_TC_HIST * sizeof(FSnap)) : NULL;
    int min_sr[FAST_TC_HIST], max_sl[FAST_TC_HIST];
    int n_r = 0, n_l = 0, r_head = 0, l_head = 0;
    int64_t max_hi_seen = 0, min_lo_seen = 0;

    memset(out, 0, sizeof(*out));
    strcpy(out->halt_reason, "Step limit reached");

    while (steps < cap) {
        if (head < 128 || head >= (int64_t)tcap - 128) {
            if (tcap >= MAX_TAPE) {
                strcpy(out->halt_reason, "Tape memory cap reached");
                break;
            }
            size_t ncap = tcap * 2;
            uint8_t *nt = (uint8_t *)calloc(ncap, 1);
            size_t shift = (ncap - tcap) / 2;
            memcpy(nt + shift, tape, tcap);
            free(tape);
            tape = nt;
            tcap = ncap;
            origin += (int64_t)shift;
            head += (int64_t)shift;
            lo_w += (int64_t)shift;
            hi_w += (int64_t)shift;
        }

        int phase = (int)(steps % (uint64_t)slen);
        int r = (m->sched_len > 0) ? m->sched[phase] : phase;
        const Rule *rl = &m->rules[r];
        uint8_t sym = tape[head];

        if (st >= rl->states || sym >= rl->symbols) {
            steps++;
            out->halted = 1;
            snprintf(out->halt_reason, sizeof(out->halt_reason),
                     (st >= rl->states) ? "State %c out of range for Rule %d"
                                        : "Symbol %u out of range for Rule %d",
                     (st >= rl->states) ? ('A' + st) : (unsigned)sym, r + 1);
            st = -1;
            break;
        }

        Trans tr = rl->tab[st][sym];
        if (tr.w < 0) {
            steps++;
            out->halted = 1;
            snprintf(out->halt_reason, sizeof(out->halt_reason),
                     "Undefined --- in Rule %d (%c%u)", r + 1, 'A' + st, (unsigned)sym);
            st = -1;
            break;
        }

        if (want_cycle_det && steps > 0 && st == st_t &&
            phase == (int)(step_t % (uint64_t)slen) &&
            (head - origin) == (ht - t_orig)) {
            int64_t lrel = (lo_w - origin < lor_t - t_orig) ? (lo_w - origin) : (lor_t - t_orig);
            int64_t rrel = (hi_w - origin > hir_t - t_orig) ? (hi_w - origin) : (hir_t - t_orig);
            if (t_orig + lrel >= 0 && t_orig + rrel < (int64_t)bcap &&
                memcmp(tape + origin + lrel, tt + t_orig + lrel, (size_t)(rrel - lrel + 1)) == 0) {
                out->cycle_type = 1;
                snprintf(out->halt_reason, sizeof(out->halt_reason),
                         "Exact Cycler (period %llu)", (unsigned long long)(steps - step_t));
                break;
            }
        }
        if (want_cycle_det && lam == power) {
            int64_t lrel = lo_w - origin, rrel = hi_w - origin;
            size_t need = (size_t)(rrel - lrel + 256);
            if (need < bcap / 2) {
                memset(tt + t_orig + (lor_t - t_orig), 0, (size_t)(hir_t - lor_t + 1));
                memcpy(tt + t_orig + lrel, tape + origin + lrel, (size_t)(rrel - lrel + 1));
                ht = t_orig + (head - origin);
                lor_t = t_orig + lrel;
                hir_t = t_orig + rrel;
                st_t = st; step_t = steps;
                power *= 2;
                lam = 0;
            }
        }

        int64_t hrel = head - origin;
        if (want_cycle_det && hrel > max_hi_seen) {
            max_hi_seen = hrel;
            for (int c = 0; c < n_r; c++) {
                int i = (r_head - 1 - c + FAST_TC_HIST) % FAST_TC_HIST;
                int depth = (int)(rsnaps[i].pos - min_sr[i]);
                if (depth >= 0 && depth < FAST_TC_WIN - 1 &&
                    phase == (int)(rsnaps[i].step % (uint64_t)slen) && st == rsnaps[i].st) {
                    bool ok = true;
                    for (int off = 0; off <= depth; off++) {
                        if (tape[head - off] != rsnaps[i].ctx[off]) { ok = false; break; }
                    }
                    if (ok) {
                        out->cycle_type = 2;
                        snprintf(out->halt_reason, sizeof(out->halt_reason),
                                 "Rightward Translated Cycler (period %llu, shift +%lld)",
                                 (unsigned long long)(steps - rsnaps[i].step),
                                 (long long)(hrel - rsnaps[i].pos));
                        goto done_loop;
                    }
                }
            }
            rsnaps[r_head].step = steps;
            rsnaps[r_head].pos = hrel;
            rsnaps[r_head].st = st;
            for (int off = 0; off < FAST_TC_WIN; off++) rsnaps[r_head].ctx[off] = tape[head - off];
            min_sr[r_head] = (int)hrel;
            r_head = (r_head + 1) % FAST_TC_HIST;
            if (n_r < FAST_TC_HIST) n_r++;
        }
        if (want_cycle_det && hrel < min_lo_seen) {
            min_lo_seen = hrel;
            for (int c = 0; c < n_l; c++) {
                int i = (l_head - 1 - c + FAST_TC_HIST) % FAST_TC_HIST;
                int depth = (int)(max_sl[i] - lsnaps[i].pos);
                if (depth >= 0 && depth < FAST_TC_WIN - 1 &&
                    phase == (int)(lsnaps[i].step % (uint64_t)slen) && st == lsnaps[i].st) {
                    bool ok = true;
                    for (int off = 0; off <= depth; off++) {
                        if (tape[head + off] != lsnaps[i].ctx[off]) { ok = false; break; }
                    }
                    if (ok) {
                        out->cycle_type = 2;
                        snprintf(out->halt_reason, sizeof(out->halt_reason),
                                 "Leftward Translated Cycler (period %llu, shift %lld)",
                                 (unsigned long long)(steps - lsnaps[i].step),
                                 (long long)(hrel - lsnaps[i].pos));
                        goto done_loop;
                    }
                }
            }
            lsnaps[l_head].step = steps;
            lsnaps[l_head].pos = hrel;
            lsnaps[l_head].st = st;
            for (int off = 0; off < FAST_TC_WIN; off++) lsnaps[l_head].ctx[off] = tape[head + off];
            max_sl[l_head] = (int)hrel;
            l_head = (l_head + 1) % FAST_TC_HIST;
            if (n_l < FAST_TC_HIST) n_l++;
        }
        if (want_cycle_det) {
            for (int c = 0; c < n_r; c++) {
                int i = (r_head - 1 - c + FAST_TC_HIST) % FAST_TC_HIST;
                if (min_sr[i] <= (int)hrel) break;
                min_sr[i] = (int)hrel;
            }
            for (int c = 0; c < n_l; c++) {
                int i = (l_head - 1 - c + FAST_TC_HIST) % FAST_TC_HIST;
                if (max_sl[i] >= (int)hrel) break;
                max_sl[i] = (int)hrel;
            }
        }

        if (sym == 0 && tr.w != 0) score++;
        else if (sym != 0 && tr.w == 0) score--;
        if (sym != 1 && tr.w == 1) ones++;
        else if (sym == 1 && tr.w != 1) ones--;

        tape[head] = (uint8_t)tr.w;
        if (head < lo_w) lo_w = head;
        if (head > hi_w) hi_w = head;
        head += tr.d;
        hrel = head - origin;
        if (hrel < min_rel) min_rel = hrel;
        if (hrel > max_rel) max_rel = hrel;
        steps++;
        lam++;

        if (tr.nx < 0) {
            out->halted = 1;
            snprintf(out->halt_reason, sizeof(out->halt_reason),
                     "Halted cleanly via %d%cZ (Rule %d, %c%u)",
                     tr.w, (tr.d > 0) ? 'R' : 'L', r + 1, 'A' + st, (unsigned)sym);
            st = -1;
            break;
        }
        st = tr.nx;
    }

done_loop:
    out->steps = steps;
    out->score = score;
    out->ones = ones;
    out->head = head - origin;
    out->state = st;
    int end_phase = (int)(steps % (uint64_t)slen);
    out->rule_idx = (m->sched_len > 0) ? m->sched[end_phase] : end_phase;
    out->min_pos = min_rel;
    out->max_pos = max_rel;

    free(tt);
    free(rsnaps);
    free(lsnaps);

    if (out_tape) { *out_tape = tape; *out_cap = tcap; *out_origin = origin; }
    else free(tape);
}

static uint64_t xorshift64(uint64_t *s) {
    uint64_t x = *s;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *s = x;
    return x;
}

static void random_dtm(DTM *m, int n, int sym, int rules, int a, int b,
                       const int *sched, int slen, const char *ord_str, uint64_t *rng) {
    m->num_rules = rules;
    if (sched && slen > 0) {
        m->sched_len = slen;
        for (int i = 0; i < slen; i++) m->sched[i] = sched[i];
        snprintf(m->order_str, sizeof(m->order_str), "%s", ord_str ? ord_str : "");
        if (is_identity_sched(m->sched, m->sched_len, m->num_rules)) m->order_str[0] = '\0';
    } else {
        m->sched_len = rules;
        for (int i = 0; i < rules; i++) m->sched[i] = i;
        m->order_str[0] = '\0';
    }
    for (int r = 0; r < rules; r++) {
        int rs = (r == 1 && a > 0) ? a : n;
        int rm = (r == 1 && b > 0) ? b : sym;
        m->rules[r].states = rs;
        m->rules[r].symbols = rm;
        for (int s = 0; s < rs; s++) {
            for (int y = 0; y < rm; y++) {
                int w = (int)(xorshift64(rng) % (uint64_t)rm);
                int d = (xorshift64(rng) & 1) ? 1 : -1;
                int nx = (int)(xorshift64(rng) % (uint64_t)rs);
                m->rules[r].tab[s][y] = (Trans){(int8_t)w, (int8_t)d, (int8_t)nx};
            }
        }
    }
    /* Inject 1 random halt transition */
    int hr = (int)(xorshift64(rng) % (uint64_t)rules);
    int hs = (int)(xorshift64(rng) % (uint64_t)m->rules[hr].states);
    int hy = (int)(xorshift64(rng) % (uint64_t)m->rules[hr].symbols);
    m->rules[hr].tab[hs][hy].nx = -1;
    m->rules[hr].tab[hs][hy].w = 1;
    m->rules[hr].tab[hs][hy].d = 1;
    /* Canonical first step direction R */
    int first_r = (m->sched_len > 0 && m->sched[0] < rules) ? m->sched[0] : 0;
    m->rules[first_r].tab[0][0].d = 1;
}

int main(int argc, char **argv) {
    const char *sim_spec = NULL;
    const char *mutate_spec = NULL;
    const char *order_arg = NULL;
    bool do_search = false;
    int n = 3, m_sym = 2, rules = 2, a_st = 0, b_sym = 0;
    uint64_t cap = 1000000;
    int slice_rad = 48;
    int budget_ms = 1200;
    uint64_t seed = (uint64_t)time(NULL) ^ 0x9e3779b97f4a7c15ULL;

    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--sim") && i + 1 < argc) sim_spec = argv[++i];
        else if (!strcmp(argv[i], "--mutate") && i + 1 < argc) mutate_spec = argv[++i];
        else if (!strcmp(argv[i], "--order") && i + 1 < argc) order_arg = argv[++i];
        else if (!strcmp(argv[i], "--search")) do_search = true;
        else if (!strcmp(argv[i], "--n") && i + 1 < argc) n = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--m") && i + 1 < argc) m_sym = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--rules") && i + 1 < argc) rules = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--a") && i + 1 < argc) a_st = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--b") && i + 1 < argc) b_sym = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--cap") && i + 1 < argc) cap = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--slice-rad") && i + 1 < argc) slice_rad = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--budget-ms") && i + 1 < argc) budget_ms = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--seed") && i + 1 < argc) seed = strtoull(argv[++i], NULL, 10);
    }

    if (sim_spec) {
        DTM dtm;
        if (parse_dtm(sim_spec, &dtm) != 0) {
            printf("{\"error\":\"Invalid DTM spec\"}\n");
            return 1;
        }
        uint8_t *tape = NULL;
        size_t tcap = 0;
        int64_t origin = 0;
        SimOutcome out;
        clock_t t0 = clock();
        simulate_dtm(&dtm, cap, &tape, &tcap, &origin, &out, true);
        double ms = 1000.0 * (double)(clock() - t0) / CLOCKS_PER_SEC;

        char norm_spec[1024];
        format_dtm(&dtm, norm_spec);
        int64_t hpos = origin + out.head;
        int64_t slo = hpos - slice_rad, shi = hpos + slice_rad;
        if (slo < 0) slo = 0;
        if (shi >= (int64_t)tcap) shi = (int64_t)tcap - 1;

        printf("{\"spec\":\"%s\",\"steps\":%llu,\"halted\":%s,\"cycle_type\":%d,"
               "\"halt_reason\":\"%s\",\"score\":%lld,\"ones\":%lld,"
               "\"head\":%lld,\"state\":%d,\"rule_idx\":%d,"
               "\"min_pos\":%lld,\"max_pos\":%lld,\"elapsed_ms\":%.2f,"
               "\"slice_start\":%lld,\"slice\":[",
               norm_spec, (unsigned long long)out.steps,
               out.halted ? "true" : "false", out.cycle_type,
               out.halt_reason, (long long)out.score, (long long)out.ones,
               (long long)out.head, out.state, out.rule_idx,
               (long long)out.min_pos, (long long)out.max_pos, ms,
               (long long)(slo - origin));
        for (int64_t p = slo; p <= shi; p++) {
            printf("%s%u", (p > slo) ? "," : "", (unsigned)tape[p]);
        }
        printf("]}\n");
        free(tape);
        return 0;
    }

    if (do_search || mutate_spec) {
        int sched[MAX_SCHED];
        int slen = 0, max_r_ord = 0;
        char ord_norm[128] = "";
        if (order_arg && order_arg[0]) {
            if (parse_order_str(order_arg, sched, &slen, &max_r_ord, ord_norm, sizeof(ord_norm)) != 0) {
                printf("{\"error\":\"Invalid --order string\"}\n");
                return 1;
            }
            if (max_r_ord > rules) rules = max_r_ord;
        }

        DTM base;
        bool has_base = false;
        if (mutate_spec && parse_dtm(mutate_spec, &base) == 0) has_base = true;

        clock_t t0 = clock();
        uint64_t tested = 0, halted = 0, holdouts = 0;
        uint64_t best_steps = 0;
        int64_t best_score = 0;
        char best_spec[1024] = "";
        uint64_t hold_best_steps = 0;
        char hold_spec[1024] = "";

        if (has_base) {
            SimOutcome out;
            simulate_dtm(&base, cap, NULL, NULL, NULL, &out, true);
            tested++;
            if (out.halted) {
                halted++;
                best_steps = out.steps; best_score = out.score;
                format_dtm(&base, best_spec);
            }
        }

        while (1) {
            clock_t now = clock();
            if (1000.0 * (double)(now - t0) / CLOCKS_PER_SEC >= (double)budget_ms && tested > 0) break;

            for (int batch = 0; batch < 256; batch++) {
                DTM cand;
                if (has_base && (xorshift64(&seed) % 10) < 8) {
                    cand = base;
                    int muts = 1 + (int)(xorshift64(&seed) % 2);
                    for (int mu = 0; mu < muts; mu++) {
                        int r = (int)(xorshift64(&seed) % (uint64_t)cand.num_rules);
                        int s = (int)(xorshift64(&seed) % (uint64_t)cand.rules[r].states);
                        int y = (int)(xorshift64(&seed) % (uint64_t)cand.rules[r].symbols);
                        if ((xorshift64(&seed) % 16) == 0) {
                            cand.rules[r].tab[s][y].nx = -1;
                        } else {
                            cand.rules[r].tab[s][y].w = (int8_t)(xorshift64(&seed) % (uint64_t)cand.rules[r].symbols);
                            cand.rules[r].tab[s][y].d = (xorshift64(&seed) & 1) ? 1 : -1;
                            cand.rules[r].tab[s][y].nx = (int8_t)(xorshift64(&seed) % (uint64_t)cand.rules[r].states);
                        }
                    }
                } else {
                    random_dtm(&cand, n, m_sym, rules, a_st, b_sym, slen > 0 ? sched : NULL, slen, ord_norm, &seed);
                }
                SimOutcome out;
                simulate_dtm(&cand, cap, NULL, NULL, NULL, &out, true);
                tested++;
                if (out.halted) {
                    halted++;
                    if (out.steps > best_steps || (out.steps == best_steps && out.score > best_score)) {
                        best_steps = out.steps;
                        best_score = out.score;
                        format_dtm(&cand, best_spec);
                        if (has_base && best_steps > 20) base = cand;
                    }
                } else if (out.cycle_type == 0) {
                    holdouts++;
                    if (out.steps > hold_best_steps) {
                        hold_best_steps = out.steps;
                        format_dtm(&cand, hold_spec);
                    }
                }
            }
        }
        double ms = 1000.0 * (double)(clock() - t0) / CLOCKS_PER_SEC;
        printf("{\"tested\":%llu,\"halted\":%llu,\"holdouts\":%llu,\"elapsed_ms\":%.2f,"
               "\"best_steps\":%llu,\"best_score\":%lld,\"best_spec\":\"%s\",\"holdout_spec\":\"%s\"}\n",
               (unsigned long long)tested, (unsigned long long)halted,
               (unsigned long long)holdouts, ms,
               (unsigned long long)best_steps, (long long)best_score, best_spec, hold_spec);
        return 0;
    }

    printf("{\"error\":\"Specify --sim, --search, or --mutate\"}\n");
    return 1;
}
