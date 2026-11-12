/* Exhaustive (3,2) Multi-Round Shift-Overflow Pair Hunter (both tsym=0 and tsym=1, any Pc/Dc) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns; } Tr;

typedef struct {
    char spec[32];
    Tr T[6];
    int tsym, sr, ex, Pc, Dc;
} Eng3;

typedef struct {
    char spec[32];
    Tr T[6];
    int tsym, P, D, M, mg, gl_s, pat_off, span_l;
    uint8_t pat[96];
} Gli3;

static void parse_tbl3(const char *s, Tr T[6]) {
    const char *p = s;
    for (int q = 0; q < 3; q++) {
        for (int b = 0; b < 2; b++) {
            T[q * 2 + b] = (Tr){p[0] - '0', p[1] == 'R' ? 1 : -1, p[2] - 'A'};
            p += 3;
        }
        if (*p == '_') p++;
    }
}

static int detect_glider_3(const Tr *T2, const uint8_t *orig_tape, int orig_sz,
                           int p2_cur, int s2_cur, int tsym,
                           int *out_P, int *out_D, int *out_gl_s, uint8_t *out_pat, int *out_pat_off, int *out_span_l) {
    uint8_t tp[1024];
    int base = p2_cur - 64;
    if (base < 0 || p2_cur >= orig_sz) return 0;
    int avail = orig_sz - base; if (avail > 1024) avail = 1024;
    memset(tp, 0, 1024); memcpy(tp, orig_tape + base, avail);
    int p = p2_cur - base, s = s2_cur;
    int ph[300], ps[300];
    for (int t = 0; t < 300; t++) {
        ph[t] = p; ps[t] = s;
        if (p < 12 || p >= 1012) return 0;
        Tr x = T2[s * 2 + tp[p]];
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
        for (int z = min_h - 10; z < min_h; z++) if (z < 0 || tp[z] != tsym) { trail_ok = 0; break; }
        if (!trail_ok) continue;
        memset(tp, 0, 1024); memcpy(tp, orig_tape + base, avail);
        p = p2_cur - base; s = s2_cur;
        for (int t = 0; t < 299; t++) {
            Tr x = T2[s * 2 + tp[p]];
            tp[p] = x.w; p += x.d; s = x.ns;
        }
        *out_P = P; *out_D = D; *out_gl_s = s;
        int span_l = p - min_h; if (span_l < 0 || span_l > 70) return 0;
        int start = min_h - 8; if (start < 0 || start + 96 > 1024) return 0;
        memcpy(out_pat, tp + start, 96);
        *out_pat_off = span_l + 8; *out_span_l = span_l;
        for (int i = 0; i < 8; i++) if (out_pat[i] != tsym) return 0;
        return 1;
    }
    return 0;
}

static int probe_bounce_3x2(const Tr *T1, const Tr *T2, int tsym, int ex,
                            int gap, const uint8_t *pat, int pat_off, int gl_s, int P, int D,
                            int *out_hstp, int *out_tsep, int *out_lp1_rel,
                            int *out_w3, int *out_L0, long long *out_Ts,
                            int *out_ex_rel, int *out_gdx, int *out_gstp, int *out_btype, int *out_mna) {
    uint8_t tp[2048];
    const int OFF = 1000;
    const int clean_sym_exp = 1 - tsym;
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
        Tr x = T1[ls1 * 2 + tp[lp1]], y = T2[ls2 * 2 + tp[lp2]];
        tp[lp2] = y.w; tp[lp1] = x.w;
        lp1 += x.d; ls1 = x.ns; lp2 += y.d; ls2 = y.ns;
        if (lp1 > max_p1) max_p1 = lp1;
        if (lp1 == lp2) { *out_hstp = t; return 1; }
        if (lp1 < 50 || lp1 >= 1950 || lp2 < 50 || lp2 >= 1950) return 0;
        if (lp1 < OFF - 20 && lp2 > OFF + gap && lp2 - lp1 > 24) {
            if (!detect_glider_3(T2, tp, 2048, lp2, ls2, tsym, &nP, &nD, &ngs, npat, &noff, &nsl)) return 0;
            if (nP != P || nD != D) return 0;
            uint8_t sync_tp[2048]; memcpy(sync_tp, tp, 2048);
            int sp2 = lp2, ss2 = ls2;
            for (int k = 0; k < 299; k++) {
                Tr sy = T2[ss2 * 2 + sync_tp[sp2]];
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
                Tr sy = T2[ss2 * 2 + sync_tp[sp2]];
                sync_tp[sp2] = sy.w; sp2 += sy.d; ss2 = sy.ns;
            }
            if (!synced) return 0;
            t_sep = t; break;
        }
    }
    if (!t_sep) return 0;

    uint8_t clean_sym = tp[lp1 + 1];
    if (clean_sym != clean_sym_exp) return 0;
    int clean_end = lp1 + 1;
    while (clean_end < max_p1 + 5 && tp[clean_end] == clean_sym) clean_end++;
    if (clean_end - (lp1 + 1) < 6) return 0;

    for (int i = lp2 - nsl - 2; i < 2048; i++) if (i > max_p1) tp[i] = tsym;

    long long Ts[6] = {0}, Tuw5 = 0;
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
        long long max_stp = (li <= 1) ? 900000 : 2500000;
        long long stp = 0;
        int ok = 0;
        for (stp = 1; stp <= max_stp; stp++) {
            Tr xx = T1[as * 2 + sp[ap]];
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
        if (ex_pos[i] != ex_pos[0] || anchor_shifts[i] != anchor_shifts[0] || L_effs[i] != L_effs[0] + i) return 0;
    }

    int w3 = (int)(Tuw5 - Ts[3]);
    if (w3 <= 0) return 0;

    long long d2[5], d3[5];
    for (int i = 0; i < 5; i++) { d2[i] = Ts[i+1] - 2*Ts[i]; d3[i] = Ts[i+1] - 3*Ts[i]; }
    int is_p2 = (d2[4] - d2[3] == d2[3] - d2[2]) && (d2[3] - d2[2] == d2[2] - d2[1]) && (d2[2] - d2[1] == d2[1] - d2[0]);
    int is_p3 = (d3[4] - d3[3] == d3[3] - d3[2]) && (d3[3] - d3[2] == d3[2] - d3[1]) && (d3[2] - d3[1] == d3[1] - d3[0]);

    long long p4[4], p9[4];
    for (int i = 0; i < 4; i++) { p4[i] = Ts[i+2] - 4*Ts[i]; p9[i] = Ts[i+2] - 9*Ts[i]; }
    int is_pp2 = (p4[2] - p4[0] == p4[3] - p4[1]) && (Ts[3] > 2*Ts[1]);
    int is_pp3 = (p9[2] - p9[0] == p9[3] - p9[1]) && (Ts[3] > 5*Ts[1]);

    int btype = 0;
    if (is_p2 && Ts[2] > Ts[1]) btype = 1;
    else if (is_p3 && Ts[2] > Ts[1]) btype = 3;
    else if (is_pp2) btype = 2;
    else if (is_pp3) btype = 4;
    if (!btype) return 0;

    *out_tsep = t_sep; *out_lp1_rel = lp1 - OFF; *out_w3 = w3;
    *out_L0 = L_effs[0]; memcpy(out_Ts, Ts, sizeof(long long) * 6);
    *out_ex_rel = ex_pos[0]; *out_gdx = gdx; *out_gstp = gstp;
    *out_btype = btype; *out_mna = anchor_shifts[0];
    return 2;
}

static Eng3 engs[4000];
static int n_eng = 0;
static Gli3 gls[80000];
static int n_gli = 0;

int main(int argc, char **argv) {
    int min_M = argc >= 2 ? atoi(argv[1]) : 4;

    FILE *fe = fopen("bbwork/bb-variants/CET/engines_3x2_all.txt", "r");
    char line[256];
    while (fgets(line, sizeof(line), fe)) {
        char sp[32], sr_c, ex_c; int ts, Pc, Dc;
        if (sscanf(line, "%31s\ttsym=%d\tsr=%c\texit=%c\tPc=%d\tDc=%d", sp, &ts, &sr_c, &ex_c, &Pc, &Dc) == 6) {
            Eng3 e; memset(&e, 0, sizeof(e));
            strcpy(e.spec, sp); parse_tbl3(sp, e.T);
            e.tsym = ts; e.sr = sr_c - 'A'; e.ex = ex_c - 'A'; e.Pc = Pc; e.Dc = Dc;
            engs[n_eng++] = e;
        }
    }
    fclose(fe);

    FILE *fg = fopen("bbwork/bb-variants/CET/gliders_3x2_all.txt", "r");
    while (fgets(line, sizeof(line), fg)) {
        char sp[32]; int P, D, M, ts, sl;
        if (sscanf(line, "%31s\tP=%d\tD=%d\tM=%d\ttsym=%d\tsl=%d", sp, &P, &D, &M, &ts, &sl) == 6) {
            if (M < min_M) continue;
            Gli3 g; memset(&g, 0, sizeof(g));
            strcpy(g.spec, sp); parse_tbl3(sp, g.T);
            uint8_t tp[2048]; memset(tp, 0, sizeof(tp));
            int p = 512, s = 0, ok = 1;
            for (int t = 1; t <= 1200; t++) {
                Tr x = g.T[s * 2 + tp[p]];
                tp[p] = x.w; p += x.d; s = x.ns;
                if (p < 20 || p >= 1980) { ok = 0; break; }
            }
            if (!ok) continue;
            int dP = 0, dD = 0;
            if (!detect_glider_3(g.T, tp, 2048, p, s, ts, &dP, &dD, &g.gl_s, g.pat, &g.pat_off, &g.span_l)) continue;
            if (dP != P || dD != D) continue;
            g.tsym = ts; g.P = dP; g.D = dD; g.M = dP - dD;
            g.mg = g.span_l + 4; if (g.mg < 8) g.mg = 8;
            gls[n_gli++] = g;
        }
    }
    fclose(fg);
    printf("Exhaustive CET(3): engines=%d gliders(M>=%d)=%d\n", n_eng, min_M, n_gli); fflush(stdout);

    FILE *fout = fopen("bbwork/bb-variants/CET/mechs_cet3_exh.txt", "w");
    long long pairs = 0, mechs = 0;

    #pragma omp parallel for schedule(dynamic, 16) reduction(+:pairs,mechs)
    for (int gi = 0; gi < n_gli; gi++) {
        const Gli3 *g = &gls[gi];
        uint8_t tape[16384];
        for (int ei = 0; ei < n_eng; ei++) {
            const Eng3 *e = &engs[ei];
            if (e->tsym != g->tsym) continue;
            if (e->Dc * g->P <= g->D * e->Pc) continue;
            pairs++;

            /* R1 survival check to t=3000 (just prevent early <300 halt or left runaway & ensure active glider survives!) */
            const int OFF = 2048;
            memset(tape, 0, sizeof(tape));
            int p1 = OFF, p2 = OFF + 2, s1 = 0, s2 = 0, ok = 1;
            for (int t = 1; t <= 3000; t++) {
                Tr x = e->T[s1 * 2 + tape[p1]], y = g->T[s2 * 2 + tape[p2]];
                tape[p2] = y.w; tape[p1] = x.w;
                p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
                if (p1 == p2) { ok = 0; break; }
                if (p1 < 200 || p1 >= 15000 || p2 < 200 || p2 >= 15000) { ok = 0; break; }
            }
            if (!ok) continue;

            int nP = 0, nD = 0, gl_s = 0, pat_off = 0, span_l = 0; uint8_t pat[96];
            if (!detect_glider_3(g->T, tape, 16384, p2, s2, g->tsym, &nP, &nD, &gl_s, pat, &pat_off, &span_l)) continue;
            if (nP != g->P || nD != g->D) continue;

            int M = nP - nD, mg = span_l + 4; if (mg < 8) mg = 8;
            char buf[32768]; int blen = 0;
            int nH = 0, nB = 0, btype_ref = 0;
            for (int gap = mg; gap < mg + M; gap++) {
                int hstp = 0, tsep = 0, lp1r = 0, w3 = 0, L0 = 0, xr = 0, gdx = 0, gstp = 0, bt = 0, mna = 0;
                long long Ts[6];
                int res = probe_bounce_3x2(e->T, g->T, g->tsym, e->ex, gap, pat, pat_off, gl_s, nP, nD,
                                           &hstp, &tsep, &lp1r, &w3, &L0, Ts, &xr, &gdx, &gstp, &bt, &mna);
                if (res == 1) { nH++; blen += sprintf(buf + blen, "|H:%d:%d", gap, hstp); }
                else if (res == 2) {
                    if (btype_ref == 0) btype_ref = bt;
                    if (bt == btype_ref) {
                        nB++;
                        blen += sprintf(buf + blen, "|B:%d:bt=%d:ts=%d:lp=%d:w3=%d:L0=%d:xr=%d:gdx=%d:gs=%d:mna=%d:T=%lld,%lld,%lld,%lld,%lld,%lld",
                                        gap, bt, tsep, lp1r, w3, L0, xr, gdx, gstp, mna, Ts[0], Ts[1], Ts[2], Ts[3], Ts[4], Ts[5]);
                    }
                }
                if (blen > 30000) break;
            }
            if (nH >= 1 && nB >= 2) {
                mechs++;
                #pragma omp critical
                fprintf(fout, "%s|%s\t%s\tP=%d\tD=%d\tM=%d\tmg=%d\tbt=%d\tnH=%d\tnB=%d\tR1=BIG:tsym=%d\t%s\n",
                        e->spec, g->spec, e->spec, nP, nD, M, mg, btype_ref, nH, nB, g->tsym, buf);
            }
        }
    }
    fclose(fout);
    printf("Exhaustive CET(3) DONE: matched_vel=%lld mechs=%lld -> mechs_cet3_exh.txt\n", pairs, mechs);
    return 0;
}
