#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns; } Tr;

static int parse_ag(const char *s, Tr *T, int *NS, int *NSYM) {
    int states = 1, len = (int)strlen(s);
    for (int i = 0; i < len; i++) if (s[i] == '_') states++;
    *NS = states;
    const char *us = strchr(s, '_');
    int per = us ? (int)(us - s) : len;
    *NSYM = per / 3;
    const char *p = s;
    for (int q = 0; q < *NS; q++) {
        for (int b = 0; b < *NSYM; b++) {
            if (p[0] == '-') T[q * (*NSYM) + b] = (Tr){0, 1, 0};
            else T[q * (*NSYM) + b] = (Tr){p[0]-'0', p[1]=='R'?1:-1, p[2]-'A'};
            p += 3;
        }
        if (*p == '_') p++;
    }
    return 1;
}

static int detect_glider_full(const Tr *T2, int NSYM, const uint8_t *orig_tape, int orig_sz,
                              int p2_cur, int s2_cur, int tsym,
                              int *out_P, int *out_D, int *out_gl_s, uint8_t *out_pat, int *out_pat_off, int *out_span_l) {
    uint8_t tp[1024];
    int base = p2_cur - 64;
    if (base < 0 || p2_cur >= orig_sz) return 0;
    int avail = orig_sz - base;
    if (avail > 1024) avail = 1024;
    memset(tp, 0, 1024);
    memcpy(tp, orig_tape + base, avail);

    int p = p2_cur - base, s = s2_cur;
    int ph[300], ps[300];
    for (int t = 0; t < 300; t++) {
        ph[t] = p; ps[t] = s;
        if (p < 12 || p >= 1012) return 0;
        Tr x = T2[s * NSYM + tp[p]];
        tp[p] = x.w; p += x.d; s = x.ns;
    }
    for (int P = 3; P <= 80; P++) {
        int D = ph[299] - ph[299 - P];
        if (D <= 0 || D >= P) continue;
        int ok = 1;
        for (int t = 300 - 2 * P; t < 300; t++) {
            if (ph[t] - ph[t - P] != D || ps[t] != ps[t - P]) { ok = 0; break; }
        }
        if (!ok) continue;
        int min_h = ph[299];
        for (int t = 300 - P; t < 300; t++) if (ph[t] < min_h) min_h = ph[t];
        int trail_ok = 1;
        for (int z = min_h - 10; z < min_h; z++) {
            if (z < 0 || tp[z] != tsym) { trail_ok = 0; break; }
        }
        if (!trail_ok) continue;
        memset(tp, 0, 1024);
        memcpy(tp, orig_tape + base, avail);
        p = p2_cur - base; s = s2_cur;
        for (int t = 0; t < 299; t++) {
            Tr x = T2[s * NSYM + tp[p]];
            tp[p] = x.w; p += x.d; s = x.ns;
        }
        *out_P = P; *out_D = D; *out_gl_s = s;
        int span_l = p - min_h;
        if (span_l < 0 || span_l > 70) return 0;
        int start = min_h - 8;
        if (start < 0 || start + 96 > 1024) return 0;
        memcpy(out_pat, tp + start, 96);
        *out_pat_off = span_l + 8;
        *out_span_l = span_l;
        for (int i = 0; i < 8; i++) if (out_pat[i] != tsym) return 0;
        return 1;
    }
    return 0;
}

typedef struct { char spec[64]; int tsym, sr, ex; } EM;

typedef struct {
    char raw[32768];
    char pair[140], e_spec[64];
    long long tc;
    int mg, M;
    int tsym, sr, ex;
    int is_bounce;
} Item;

static int resolve_one_item(const Item *it, char *out_buf) {
    char ce[64], cg[64];
    const char *bar = strchr(it->pair, '|');
    if (!bar) return 0;
    int elen = (int)(bar - it->pair);
    memcpy(ce, it->pair, elen); ce[elen] = 0;
    strcpy(cg, bar + 1);
    Tr T1[12], T2[12]; int NS = 0, NSYM = 0;
    parse_ag(ce, T1, &NS, &NSYM);
    parse_ag(cg, T2, &NS, &NSYM);

    const int TSZ = 16000000;
    const int OFF = 500000;
    uint8_t *tape = calloc(TSZ, 1);
    if (!tape) return 0;

    /* First get Ag2 glider pattern at t=5000 */
    int p1 = OFF, p2 = OFF + 2, s1 = 0, s2 = 0;
    int act_P = 0, act_D = 0, gl_s = 0, pat_off = 0, span_l = 0;
    uint8_t pat[96];
    for (int t = 1; t <= 5000; t++) {
        Tr x = T1[s1 * NSYM + tape[p1]], y = T2[s2 * NSYM + tape[p2]];
        tape[p2] = y.w; tape[p1] = x.w;
        p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
        if (p1 == p2) { free(tape); sprintf(out_buf, "HALT_EARLY:%d", t); return 1; }
    }
    if (!detect_glider_full(T2, NSYM, tape, TSZ, p2, s2, it->tsym, &act_P, &act_D, &gl_s, pat, &pat_off, &span_l)) {
        free(tape); sprintf(out_buf, "NOGLIDER5K"); return 1;
    }
    int M = act_P - act_D;
    int mg = span_l + 4; if (mg < 8) mg = 8;

    /* Reset tape and run up to tc + 2000 looking for COL1 starting from t >= max(500, tc - 200) */
    memset(tape, 0, TSZ);
    p1 = OFF; p2 = OFF + 2; s1 = 0; s2 = 0;
    long long start_chk = it->tc - 200;
    if (start_chk < 500) start_chk = 500;
    long long lim = it->tc + 20000;
    long long col1_t = 0;
    int col1_gap = -1, x_bounce = 0, min1_r1 = OFF;
    for (long long t = 1; t <= lim; t++) {
        if (p1 < 100 || p1 >= TSZ - 200 || p2 < 100 || p2 >= TSZ - 200) { free(tape); sprintf(out_buf, "OOB:%lld", t); return 1; }
        Tr x = T1[s1 * NSYM + tape[p1]], y = T2[s2 * NSYM + tape[p2]];
        tape[p2] = y.w; tape[p1] = x.w;
        p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
        if (p1 == p2) { col1_t = -t; break; }
        if (t <= it->tc + 200 && p1 < min1_r1) min1_r1 = p1;
        if (t >= start_chk && col1_t == 0 && s1 == it->ex && s2 == gl_s &&
            p2 - p1 >= mg && p2 - p1 < mg + M) {
            int st = p2 - pat_off, m = 1;
            if (st >= 0 && st + 20 < TSZ) {
                for (int k = 0; k < 20; k++) if (tape[st + k] != pat[k]) { m = 0; break; }
            } else m = 0;
            if (m) { col1_t = t; col1_gap = p2 - p1; x_bounce = p1; break; }
        }
    }
    if (col1_t < 0) { free(tape); sprintf(out_buf, "HALT1:%lld", -col1_t); return 1; }
    if (col1_t == 0) {
        /* Try fallback from t=5000 in case tc was slightly off! */
        memset(tape, 0, TSZ);
        p1 = OFF; p2 = OFF + 2; s1 = 0; s2 = 0;
        int min1_early = OFF, max1_early = OFF;
        for (long long t = 1; t <= lim; t++) {
            Tr x = T1[s1 * NSYM + tape[p1]], y = T2[s2 * NSYM + tape[p2]];
            tape[p2] = y.w; tape[p1] = x.w;
            p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
            if (p1 == p2) { col1_t = -t; break; }
            if (t <= 5000) { if (p1 < min1_early) min1_early = p1; if (p1 > max1_early) max1_early = p1; }
            if (p1 > max1_early + 50 && s1 == it->ex && s2 == gl_s &&
                p2 - p1 >= mg && p2 - p1 < mg + M) {
                int st = p2 - pat_off, m = 1;
                if (st >= 0 && st + 20 < TSZ) {
                    for (int k = 0; k < 20; k++) if (tape[st + k] != pat[k]) { m = 0; break; }
                } else m = 0;
                if (m) { col1_t = t; col1_gap = p2 - p1; x_bounce = p1; break; }
            }
        }
        if (col1_t <= 0) { free(tape); sprintf(out_buf, "NOCOL1_AT_%lld", it->tc); return 1; }
    }

    /* Follow bounce until left-wipe finishes! */
    int r2_min1 = x_bounce, r2_hit_left = 0;
    for (int k = 1; k <= 1500000; k++) {
        if (p1 < 100 || p1 >= TSZ - 200 || p2 < 100 || p2 >= TSZ - 200) break;
        Tr x = T1[s1 * NSYM + tape[p1]], y = T2[s2 * NSYM + tape[p2]];
        tape[p2] = y.w; tape[p1] = x.w;
        p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
        if (p1 == p2) { col1_t = -(col1_t + k); break; }
        if (p1 < r2_min1) r2_min1 = p1;
        if (p1 < min1_r1 + 5 && k > 500) r2_hit_left = 1;
        if (r2_hit_left && k > 15000 && p1 > min1_r1 + 40) break;
    }
    if (col1_t < 0) { free(tape); sprintf(out_buf, "HALT2:%lld", -col1_t); return 1; }
    int cz = 1;
    for (int z = r2_min1 - 6; z < r2_min1; z++) if (tape[z] != 0) cz = 0;
    char lw[16];
    for (int z = 0; z < 10; z++) lw[z] = '0' + tape[r2_min1 - 2 + z];
    lw[10] = 0;
    sprintf(out_buf, "R1=COL1:t=%lld:gap=%d:x1=%d:r2min=%d:cz=%d:lw=%s",
            col1_t, col1_gap, x_bounce - OFF, r2_min1 - OFF, cz, lw);
    free(tape);
    return 1;
}

static void process(const char *eng_path, const char *r1_path, const char *out_path) {
    EM *ems = malloc(sizeof(EM) * 2000); int n_em = 0;
    FILE *fe = fopen(eng_path, "r");
    char *line = malloc(65536);
    while (fgets(line, 65536, fe)) {
        char sp[64], sr_c, ex_c; int ts;
        if (sscanf(line, "%63s tsym=%d sr=%c exit=%c", sp, &ts, &sr_c, &ex_c) == 4) {
            strcpy(ems[n_em].spec, sp); ems[n_em].tsym = ts; ems[n_em].sr = sr_c - 'A'; ems[n_em].ex = ex_c - 'A'; n_em++;
        }
    }
    fclose(fe);

    Item *its = malloc(sizeof(Item) * 1000); int n_it = 0;
    FILE *fr = fopen(r1_path, "r");
    while (fgets(line, 65536, fr) && n_it < 1000) {
        if (strncmp(line, "BOUNCE_R1", 9) != 0) continue;
        Item *it = &its[n_it];
        memset(it, 0, sizeof(Item));
        int L = (int)strlen(line);
        while (L > 0 && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        strcpy(it->raw, line);
        char *sep = strstr(line, "\t||");
        if (!sep) continue;
        /* Parse t=... and pair and mech */
        char *p_t = strstr(line, "\tt=");
        if (p_t) it->tc = atoll(p_t + 3);
        char *mech_str = strchr(sep + 3, '\t');
        if (!mech_str) continue;
        mech_str++;
        sscanf(mech_str, "%139[^\t]\t%63[^\t]", it->pair, it->e_spec);
        for (int i = 0; i < n_em; i++) {
            if (strcmp(ems[i].spec, it->e_spec) == 0) {
                it->tsym = ems[i].tsym; it->sr = ems[i].sr; it->ex = ems[i].ex; break;
            }
        }
        it->is_bounce = 1;
        n_it++;
    }
    fclose(fr); free(line); free(ems);

    char (*outs)[256] = calloc(n_it ? n_it : 1, 256);
    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < n_it; i++) {
        resolve_one_item(&its[i], outs[i]);
    }

    FILE *fo = fopen(out_path, "w");
    for (int i = 0; i < n_it; i++) {
        /* Replace R1=... in its[i].raw with resolved outs[i] if resolved cleanly! */
        fprintf(fo, "%s\t||%s\n", outs[i], its[i].raw);
    }
    fclose(fo);
    printf("Resolved %s: %d BOUNCE_R1 items -> %s\n", r1_path, n_it, out_path);
    free(outs); free(its);
}

int main(void) {
    process("bbwork/bb-variants/CET/engines_3x2_t1.txt", "bbwork/bb-variants/CET/r1_exact_cet3.txt", "bbwork/bb-variants/CET/pinned_cet3.txt");
    process("bbwork/bb-variants/CET/engines_2x3_t1.txt", "bbwork/bb-variants/CET/r1_exact_cet23_t1.txt", "bbwork/bb-variants/CET/pinned_cet23_t1.txt");
    process("bbwork/bb-variants/CET/engines_2x3_t2.txt", "bbwork/bb-variants/CET/r1_exact_cet23_t2.txt", "bbwork/bb-variants/CET/pinned_cet23_t2.txt");
    return 0;
}
