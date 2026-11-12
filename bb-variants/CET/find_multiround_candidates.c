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

typedef struct {
    char c_pair[140], e_spec[64];
    int tsym, sr, ex, NS, NSYM;
    Tr T1[12], T2[12];
    int P, D, M, exit_t;
} Cand;

/* Measure bounce+count for gap G using clean-region splice (L_mid = 6..11 + uw=4 vs uw=7).
   Returns 1=HALT (steps=hstp), 2=CLEAN_BOUNCE_AND_CYCLE, 0=FAIL. */
static int probe_bounce_splice(const Tr *T1, const Tr *T2, int NS, int NSYM, int tsym, int ex,
                               int gap, const uint8_t *pat, int pat_off, int gl_s, int P, int D,
                               int *out_halt_stp, int *out_tsep, int *out_lp1_rel,
                               int *out_uw, int *out_w3, int *out_L0, long long *out_Ts,
                               int *out_ex_rel, int *out_gdx, int *out_gstp, int *out_btype, int *out_min_anchor_shift) {
    uint8_t tp[2048];
    int OFF = 1000;
    for (int i = 0; i < OFF + gap; i++) tp[i] = tsym;
    for (int i = OFF + gap; i < 2048; i++) tp[i] = 0;
    for (int i = 0; i < 96; i++) {
        int dst = OFF + gap - pat_off + i;
        if (dst >= 0 && dst < 2048) tp[dst] = pat[i];
    }
    int lp1 = OFF, ls1 = ex, lp2 = OFF + gap, ls2 = gl_s;
    int max_p1 = OFF, t_sep = 0, synced = 0, gdx = 0, gstp = 0;
    int nP = 0, nD = 0, ngs = 0, noff = 0, nsl = 0; uint8_t npat[96];

    for (int t = 1; t <= 450; t++) {
        Tr x = T1[ls1 * NSYM + tp[lp1]], y = T2[ls2 * NSYM + tp[lp2]];
        tp[lp2] = y.w; tp[lp1] = x.w;
        lp1 += x.d; ls1 = x.ns; lp2 += y.d; ls2 = y.ns;
        if (lp1 > max_p1) max_p1 = lp1;
        if (lp1 == lp2) { *out_halt_stp = t; return 1; }
        if (lp1 < 50 || lp1 >= 1950 || lp2 < 50 || lp2 >= 1950) return 0;
        if (lp1 < OFF - 20 && lp2 > OFF + gap && lp2 - lp1 > 24) {
            if (!detect_glider_full(T2, NSYM, tp, 2048, lp2, ls2, tsym, &nP, &nD, &ngs, npat, &noff, &nsl)) return 0;
            if (nP != P || nD != D) return 0;
            uint8_t sync_tp[2048]; memcpy(sync_tp, tp, 2048);
            int sp2 = lp2, ss2 = ls2;
            for (int k = 0; k < 299; k++) {
                Tr sy = T2[ss2 * NSYM + sync_tp[sp2]];
                sync_tp[sp2] = sy.w; sp2 += sy.d; ss2 = sy.ns;
            }
            for (int extra = 0; extra < P; extra++) {
                if (ss2 == gl_s) {
                    int st = sp2 - pat_off, match = 1;
                    if (st >= 0 && st + 64 <= 2048) {
                        for (int i = 0; i < 64; i++) if (sync_tp[st + i] != pat[i]) { match = 0; break; }
                        if (match) { gdx = sp2 - (OFF + gap); gstp = t + 299 + extra; synced = 1; break; }
                    }
                }
                Tr sy = T2[ss2 * NSYM + sync_tp[sp2]];
                sync_tp[sp2] = sy.w; sp2 += sy.d; ss2 = sy.ns;
            }
            if (!synced) return 0;
            t_sep = t;
            break;
        }
    }
    if (!t_sep) return 0;

    uint8_t clean_sym = tp[lp1 + 1];
    int clean_end = lp1 + 1;
    while (clean_end < max_p1 + 5 && tp[clean_end] == clean_sym) clean_end++;
    if (clean_end - (lp1 + 1) < 6) return 0; /* not wiping uniformly leftward */

    /* Check if Ag1 actually returns to anchor & rebounds cleanly on SMALL test first?
       Use L_mid = 3..8 and uw = 2 (vs uw = 5) so L_eff stays ~10..15 (<500k even for base 3!). */
    for (int i = lp2 - nsl - 2; i < 2048; i++) if (i > max_p1) tp[i] = tsym;

    long long Ts[6] = {0}; /* L_mid = 3..8 at uw = 2 */
    long long Tuw5 = 0;    /* L_mid = 3 at uw = 5 (same L_eff as L_mid = 6 at uw = 2) */
    int ex_pos[6] = {0}, anchor_shifts[6] = {0}, L_effs[6] = {0};

    for (int li = 0; li < 7; li++) {
        int L_mid = (li < 6) ? (3 + li) : 3;
        int uw = (li < 6) ? 2 : 5;
        uint8_t sp[2048];
        int tail_len = 400;
        int new_lp1 = 500;
        int anchor_start = new_lp1 - uw + 1;
        int c_start = new_lp1 + 1;
        int suf_start = c_start + L_mid;
        if (clean_end + tail_len >= 2048 || suf_start + tail_len >= 2048) return 0;

        memset(sp, 0, sizeof(sp));
        for (int z = anchor_start; z <= new_lp1; z++) sp[z] = tsym;
        for (int z = c_start; z < suf_start; z++) sp[z] = clean_sym;
        memcpy(sp + suf_start, tp + clean_end, tail_len);

        int shift = suf_start - clean_end;
        int ap = new_lp1, as = ls1, mn_ap = anchor_start;
        int thresh = max_p1 + shift;
        long long max_stp = (li == 0) ? 300000 : ((li == 1) ? 900000 : ((li <= 3) ? 3000000 : 12000000));
        if (li >= 2 && Ts[0] < 10000) max_stp = 600000; /* pow2 doesn't need 12M! */
        long long stp = 0;
        int ok = 0;
        for (stp = 1; stp <= max_stp; stp++) {
            Tr xx = T1[as * NSYM + sp[ap]];
            sp[ap] = xx.w; ap += xx.d; as = xx.ns;
            if (ap < mn_ap) mn_ap = ap;
            if (ap < 20 || ap >= 2020) break;
            if (ap > thresh + 4 && as == ex) {
                int ok_t = 1;
                for (int z = 0; z < 8; z++) if (sp[ap + z] != tsym) { ok_t = 0; break; }
                if (ok_t) {
                    int exit_rel_OFF = (ap - shift) - OFF;
                    int L_eff = ap - anchor_start;
                    if (li < 6) {
                        Ts[li] = stp; ex_pos[li] = exit_rel_OFF;
                        L_effs[li] = L_eff;
                        anchor_shifts[li] = mn_ap - anchor_start;
                    } else {
                        Tuw5 = stp;
                    }
                    ok = 1; break;
                }
            }
        }
        if (!ok) return 0;
    }

    for (int i = 1; i < 6; i++) {
        if (ex_pos[i] != ex_pos[0]) return 0;
        if (anchor_shifts[i] != anchor_shifts[0]) return 0;
        if (L_effs[i] != L_effs[0] + i) return 0;
    }

    int w3 = (int)(Tuw5 - Ts[3]);
    if (w3 <= 0) return 0;

    /* Classify counter type:
       1 = pow2 exact: Ts[i+1] - 2*Ts[i] linear (diff2 constant)
       2 = pow2 pair (2^k period 2): Ts[i+2] - 4*Ts[i] linear (even/odd separated)
       3 = pow3 exact: Ts[i+1] - 3*Ts[i] linear
       4 = pow3 pair (9^k period 2): Ts[i+2] - 9*Ts[i] linear */
    long long d2[5], d3[5];
    for (int i = 0; i < 5; i++) { d2[i] = Ts[i+1] - 2*Ts[i]; d3[i] = Ts[i+1] - 3*Ts[i]; }
    int is_p2 = (d2[4] - d2[3] == d2[3] - d2[2]) && (d2[3] - d2[2] == d2[2] - d2[1]) && (d2[2] - d2[1] == d2[1] - d2[0]);
    int is_p3 = (d3[4] - d3[3] == d3[3] - d3[2]) && (d3[3] - d3[2] == d3[2] - d3[1]) && (d3[2] - d3[1] == d3[1] - d3[0]);

    long long p4[4], p9[4];
    for (int i = 0; i < 4; i++) { p4[i] = Ts[i+2] - 4*Ts[i]; p9[i] = Ts[i+2] - 9*Ts[i]; }
    int is_pp2 = (p4[2] - p4[0] == p4[3] - p4[1]) && (Ts[3] > 2*Ts[1]); /* linear over +2 */
    int is_pp3 = (p9[2] - p9[0] == p9[3] - p9[1]) && (Ts[3] > 5*Ts[1]);

    int btype = 0;
    if (is_p2 && Ts[2] > Ts[1]) btype = 1;
    else if (is_p3 && Ts[2] > Ts[1]) btype = 3;
    else if (is_pp2) btype = 2;
    else if (is_pp3) btype = 4;
    if (!btype) return 0; /* require exact algebraic counter formula for Rocq! */

    *out_tsep = t_sep;
    *out_lp1_rel = lp1 - OFF;
    *out_uw = 2;
    *out_w3 = w3;
    *out_L0 = L_effs[0];
    memcpy(out_Ts, Ts, sizeof(long long) * 6);
    *out_ex_rel = ex_pos[0];
    *out_gdx = gdx;
    *out_gstp = gstp;
    *out_btype = btype;
    *out_min_anchor_shift = anchor_shifts[0];
    return 2;
}

static void run_analysis(const char *uniq_path, const char *eng_path, const char *out_path, const char *label) {
    typedef struct { char spec[64]; int tsym, sr, ex; } EM;
    EM *ems = malloc(sizeof(EM) * 2000); int n_em = 0;
    FILE *fe = fopen(eng_path, "r");
    char line[1024];
    while (fgets(line, sizeof(line), fe)) {
        char sp[64], sr_c, ex_c; int ts;
        if (sscanf(line, "%63s tsym=%d sr=%c exit=%c", sp, &ts, &sr_c, &ex_c) == 4) {
            strcpy(ems[n_em].spec, sp); ems[n_em].tsym = ts; ems[n_em].sr = sr_c - 'A'; ems[n_em].ex = ex_c - 'A'; n_em++;
        }
    }
    fclose(fe);

    Cand *cands = malloc(sizeof(Cand) * 20000); int n_c = 0;
    FILE *fu = fopen(uniq_path, "r");
    while (fgets(line, sizeof(line), fu) && n_c < 20000) {
        Cand c; memset(&c, 0, sizeof(c));
        char *p1 = strtok(line, "\t"); char *p2 = strtok(NULL, "\t");
        if (!p1 || !p2) continue;
        strcpy(c.c_pair, p1); strcpy(c.e_spec, p2);
        char *bar = strchr(p1, '|'); if (!bar) continue;
        char ce[64], cg[64];
        int elen = (int)(bar - p1);
        memcpy(ce, p1, elen); ce[elen] = 0;
        strcpy(cg, bar + 1);
        parse_ag(ce, c.T1, &c.NS, &c.NSYM);
        parse_ag(cg, c.T2, &c.NS, &c.NSYM);
        int ok = 0;
        for (int i = 0; i < n_em; i++) {
            if (strcmp(ems[i].spec, c.e_spec) == 0) {
                c.tsym = ems[i].tsym; c.sr = ems[i].sr; c.ex = ems[i].ex; ok = 1; break;
            }
        }
        if (!ok) continue;
        char *rest;
        while ((rest = strtok(NULL, "\t\n\r"))) {
            if (strncmp(rest, "P=", 2) == 0) c.P = atoi(rest + 2);
            else if (strncmp(rest, "D=", 2) == 0) c.D = atoi(rest + 2);
            else if (strncmp(rest, "M=", 2) == 0) c.M = atoi(rest + 2);
            else if (strncmp(rest, "exit_t=", 7) == 0) c.exit_t = atoi(rest + 7);
        }
        if (c.M >= 2) cands[n_c++] = c;
    }
    fclose(fu); free(ems);

    FILE *fout = fopen(out_path, "w");
    int clean_cnt = 0;

    #pragma omp parallel for schedule(dynamic, 16)
    for (int ci = 0; ci < n_c; ci++) {
        const Cand *c = &cands[ci];
        uint8_t *tape = calloc(131072, 1);
        const int OFF = 10000;
        int p1 = OFF, p2 = OFF + 2, s1 = 0, s2 = 0, bad5k = 0;
        for (int t = 1; t <= 5000; t++) {
            if (p1 < 500 || p1 >= 130000 || p2 < 500 || p2 >= 130000) { bad5k = 1; break; }
            Tr x = c->T1[s1 * c->NSYM + tape[p1]];
            Tr y = c->T2[s2 * c->NSYM + tape[p2]];
            tape[p2] = y.w; tape[p1] = x.w;
            p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
        }
        int act_P, act_D, gl_s, pat_off, span_l;
        uint8_t pat[96];
        if (bad5k || !detect_glider_full(c->T2, c->NSYM, tape, 131072, p2, s2, c->tsym,
                                         &act_P, &act_D, &gl_s, pat, &pat_off, &span_l)) {
            free(tape); continue;
        }
        int M = act_P - act_D;
        int min_gap = span_l + 4; if (min_gap < 8) min_gap = 8;

        char *buf = malloc(32768); int blen = 0;
        int nH = 0, nB = 0, btype_ref = 0;
        for (int r = 0; r < M && r < 60; r++) {
            int gap = min_gap + r;
            int hstp = 0, tsep = 0, lp1r = 0, uw = 0, w3 = 0, L0 = 0, xr = 0, gdx = 0, gstp = 0, bt = 0, mna = 0;
            long long Ts[6];
            int res = probe_bounce_splice(c->T1, c->T2, c->NS, c->NSYM, c->tsym, c->ex,
                                          gap, pat, pat_off, gl_s, act_P, act_D,
                                          &hstp, &tsep, &lp1r, &uw, &w3, &L0, Ts, &xr, &gdx, &gstp, &bt, &mna);
            if (res == 1) {
                nH++;
                blen += sprintf(buf + blen, "|H:%d:%d", gap, hstp);
            } else if (res == 2) {
                nB++;
                if (!btype_ref) btype_ref = bt;
                blen += sprintf(buf + blen, "|B:%d:bt=%d:ts=%d:lp=%d:w3=%d:L0=%d:xr=%d:gdx=%d:gs=%d:mna=%d:T=%lld,%lld,%lld,%lld,%lld,%lld",
                                gap, bt, tsep, lp1r, w3, L0, xr, gdx, gstp, mna, Ts[0], Ts[1], Ts[2], Ts[3], Ts[4], Ts[5]);
            }
        }
        if (nH >= 1 && nB >= 2) {
            /* Concretely simulate Round 1 up to Collision #1 + left wall check if exit_t > 0 */
            char r1_info[256] = "R1=BIG";
            if (c->exit_t > 0 && c->exit_t < 200000) {
                memset(tape, 0, 131072);
                int q1 = OFF, q2 = OFF + 2, qs1 = 0, qs2 = 0;
                int min1_r1 = OFF, max1_r1 = OFF, col1_t = 0;
                int x_bounce = 0, col1_gap = -1;
                for (int t = 1; t <= 1200000; t++) {
                    Tr x = c->T1[qs1 * c->NSYM + tape[q1]];
                    Tr y = c->T2[qs2 * c->NSYM + tape[q2]];
                    tape[q2] = y.w; tape[q1] = x.w;
                    q1 += x.d; qs1 = x.ns; q2 += y.d; qs2 = y.ns;
                    if (t <= 5000) { if (q1 < min1_r1) min1_r1 = q1; if (q1 > max1_r1) max1_r1 = q1; }
                    if (q1 == q2) { col1_t = -t; break; }
                    if (q1 < 50 || q1 >= 130000 || q2 < 50 || q2 >= 130000) break;
                    if (q1 > max1_r1 + 50 && col1_t == 0 && qs1 == c->ex && qs2 == gl_s && q2 - q1 >= min_gap && q2 - q1 < min_gap + M) {
                        int st = q2 - pat_off, m = 1;
                        if (st >= 0 && st + 20 < 131072) {
                            for (int k = 0; k < 20; k++) if (tape[st + k] != pat[k]) { m = 0; break; }
                        } else m = 0;
                        if (m) {
                            col1_t = t; col1_gap = q2 - q1; x_bounce = q1; break;
                        }
                    }
                }
                if (col1_t < 0) sprintf(r1_info, "R1=HALT1:%d", -col1_t);
                else if (col1_t > 0) {
                    /* Run up to 350k more steps to find where left wipe stops! */
                    int r2_min1 = x_bounce, r2_hit_left = 0;
                    for (int k = 1; k <= 350000; k++) {
                        Tr x = c->T1[qs1 * c->NSYM + tape[q1]];
                        Tr y = c->T2[qs2 * c->NSYM + tape[q2]];
                        tape[q2] = y.w; tape[q1] = x.w;
                        q1 += x.d; qs1 = x.ns; q2 += y.d; qs2 = y.ns;
                        if (q1 == q2) { col1_t = -(col1_t + k); break; }
                        if (q1 < 50 || q1 >= 130000 || q2 < 50 || q2 >= 130000) break;
                        if (q1 < r2_min1) r2_min1 = q1;
                        if (q1 < min1_r1 + 5 && k > 500) r2_hit_left = 1;
                        if (r2_hit_left && k > 15000 && q1 > min1_r1 + 40) break;
                    }
                    if (col1_t < 0) sprintf(r1_info, "R1=HALT2:%d", -col1_t);
                    else {
                        int cz = 1; for (int z = r2_min1 - 6; z < r2_min1; z++) if (tape[z] != 0) cz = 0;
                        /* Also record tape[r2_min1-2 .. r2_min1+7] */
                        char lw[16]; for (int z = 0; z < 10; z++) lw[z] = '0' + tape[r2_min1 - 2 + z]; lw[10] = 0;
                        sprintf(r1_info, "R1=COL1:t=%d:gap=%d:x1=%d:r2min=%d:cz=%d:lw=%s",
                                col1_t, col1_gap, x_bounce - OFF, r2_min1 - OFF, cz, lw);
                    }
                } else sprintf(r1_info, "R1=NOCOL1");
            }
            #pragma omp critical
            {
                clean_cnt++;
                fprintf(fout, "%s\t%s\tP=%d\tD=%d\tM=%d\tmg=%d\tbt=%d\tnH=%d\tnB=%d\t%s\t%s\n",
                        c->c_pair, c->e_spec, act_P, act_D, M, min_gap, btype_ref, nH, nB, r1_info, buf);
            }
        }
        free(buf);
        free(tape);
    }

    fclose(fout);
    free(cands);
    printf("[%s] analyzed=%d -> clean exact exponential bounce mechanisms=%d\n", label, n_c, clean_cnt);
    fflush(stdout);
}

int main(void) {
    run_analysis("bbwork/bb-variants/CET/uniq_cet3.txt", "bbwork/bb-variants/CET/engines_3x2_t1.txt",
                 "bbwork/bb-variants/CET/mechs_cet3.txt", "CET(3)");
    run_analysis("bbwork/bb-variants/CET/uniq_cet23_t1.txt", "bbwork/bb-variants/CET/engines_2x3_t1.txt",
                 "bbwork/bb-variants/CET/mechs_cet23_t1.txt", "CET(2,3) t1");
    run_analysis("bbwork/bb-variants/CET/uniq_cet23_t2.txt", "bbwork/bb-variants/CET/engines_2x3_t2.txt",
                 "bbwork/bb-variants/CET/mechs_cet23_t2.txt", "CET(2,3) t2");
    return 0;
}
