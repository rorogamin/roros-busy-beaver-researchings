#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

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
            T[q * (*NSYM) + b] = (Tr){p[0]-'0', p[1]=='R'?1:-1, p[2]-'A'};
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
        for (int t = 300 - 2 * P; t < 300; t++) if (ph[t] - ph[t - P] != D || ps[t] != ps[t - P]) { ok = 0; break; }
        if (!ok) continue;
        int min_h = ph[299]; for (int t = 300 - P; t < 300; t++) if (ph[t] < min_h) min_h = ph[t];
        int trail_ok = 1; for (int z = min_h - 10; z < min_h; z++) if (z < 0 || tp[z] != tsym) { trail_ok = 0; break; }
        if (!trail_ok) continue;
        memset(tp, 0, 1024); memcpy(tp, orig_tape + base, avail);
        p = p2_cur - base; s = s2_cur;
        for (int t = 0; t < 299; t++) { Tr x = T2[s * NSYM + tp[p]]; tp[p] = x.w; p += x.d; s = x.ns; }
        *out_P = P; *out_D = D; *out_gl_s = s;
        int span_l = p - min_h;
        if (span_l < 0 || span_l > 70) return 0;
        int start = min_h - 8;
        if (start < 0 || start + 96 > 1024) return 0;
        memcpy(out_pat, tp + start, 96);
        *out_pat_off = span_l + 8; *out_span_l = span_l;
        for (int i = 0; i < 8; i++) if (out_pat[i] != tsym) return 0;
        return 1;
    }
    return 0;
}

int main(void) {
    Tr T1[12], T2[12]; int NS, NSYM;
    parse_ag("1LB0RA_1LC1RB_0RB0LC", T1, &NS, &NSYM);
    parse_ag("1RB0LB_0RC0LA_1LB1RC", T2, &NS, &NSYM);
    int tsym = 1, ex = 1;

    uint8_t *t0 = calloc(131072, 1);
    int p1=2000, p2=2002, s1=0, s2=0;
    for (int t=1;t<=5000;t++){ Tr x=T1[s1*2+t0[p1]], y=T2[s2*2+t0[p2]]; t0[p2]=y.w; t0[p1]=x.w; p1+=x.d; s1=x.ns; p2+=y.d; s2=y.ns; }
    int act_P, act_D, gl_s, pat_off, span_l; uint8_t pat[96];
    detect_glider_full(T2, NSYM, t0, 131072, p2, s2, tsym, &act_P, &act_D, &gl_s, pat, &pat_off, &span_l);
    int M = act_P - act_D, min_gap = span_l + 4; if (min_gap < 8) min_gap = 8;

    for (int r = 0; r < M; r++) {
        int gap = min_gap + r;
        uint8_t tp[2048]; int OFF = 1000;
        for (int i = 0; i < OFF + gap; i++) tp[i] = tsym;
        for (int i = OFF + gap; i < 2048; i++) tp[i] = 0;
        for (int i = 0; i < 96; i++) { int dst = OFF + gap - pat_off + i; if (dst>=0&&dst<2048) tp[dst] = pat[i]; }
        int lp1 = OFF, ls1 = ex, lp2 = OFF + gap, ls2 = gl_s;
        int max_p1 = OFF, t_sep = 0, synced = 0, gdx = 0, gstp = 0;
        for (int t = 1; t <= 450; t++) {
            Tr x = T1[ls1*NSYM+tp[lp1]], y = T2[ls2*NSYM+tp[lp2]];
            tp[lp2] = y.w; tp[lp1] = x.w; lp1 += x.d; ls1 = x.ns; lp2 += y.d; ls2 = y.ns;
            if (lp1 > max_p1) max_p1 = lp1;
            if (lp1 == lp2) { printf("gap=%2d HALT t=%d\n", gap, t); t_sep = -1; break; }
            if (lp1 < OFF - 20 && lp2 > OFF + gap && lp2 - lp1 > 24) {
                int nP, nD, ngs, noff, nsl; uint8_t npat[96];
                if (!detect_glider_full(T2, NSYM, tp, 2048, lp2, ls2, tsym, &nP, &nD, &ngs, npat, &noff, &nsl)) break;
                if (nP != act_P || nD != act_D) break;
                uint8_t sync_tp[2048]; memcpy(sync_tp, tp, 2048);
                int sp2 = lp2, ss2 = ls2;
                for (int k = 0; k < 299; k++) { Tr sy=T2[ss2*NSYM+sync_tp[sp2]]; sync_tp[sp2]=sy.w; sp2+=sy.d; ss2=sy.ns; }
                for (int extra = 0; extra < act_P; extra++) {
                    if (ss2 == gl_s) {
                        int st = sp2 - pat_off, match = 1;
                        for (int i=0;i<64;i++) if (sync_tp[st+i]!=pat[i]) { match=0; break; }
                        if (match) { gdx = sp2 - (OFF+gap); gstp = t + 299 + extra; synced = 1; break; }
                    }
                    Tr sy = T2[ss2*NSYM+sync_tp[sp2]]; sync_tp[sp2]=sy.w; sp2+=sy.d; ss2=sy.ns;
                }
                if (synced) t_sep = t;
                break;
            }
        }
        if (t_sep <= 0) continue;

        /* Find rightmost cell x_wall strictly right of max_p1? Actually first check clean_sym behind lp1! */
        uint8_t clean_sym = tp[lp1 + 1];
        int clean_end = lp1 + 1;
        while (clean_end < max_p1 + 5 && tp[clean_end] == clean_sym) clean_end++;
        /* Make >= lp2 - span_l uniform tsym so Ag1 chases freely past right wall */
        for (int i = lp2 - span_l; i < 2048; i++) if (i > max_p1) tp[i] = tsym;
        /* Keep suffix [clean_end .. 1500] and splice L_test clean_syms BEFORE clean_end, preceded by uw=4 tsyms and anchor 0s! */
        /* Note: total cells from anchor (inclusive first tsym) to clean_end + suffix! Let's run L_mid = 6, 7, 8, 9 (and uw=7 vs uw=4) */
        /* Check w_cost using uw=4 vs uw=7 at same L_eff */
        long long Ts[4], Tuw7 = 0; int ex_pos[4];
        for (int li = 0; li < 5; li++) {
            int L_mid = (li < 4) ? (6 + li) : 6; /* li=4: uw=7, L_mid=6 => L_eff = 7+6+suf = same as li=3 (uw=4, L_mid=9) */
            int uw = (li < 4) ? 4 : 7;
            uint8_t sp[2048];
            int tail_len = 300;
            int new_lp1 = 500;
            int c_start = new_lp1 + 1;
            int suf_start = c_start + L_mid;
            memset(sp, 0, sizeof(sp));
            for (int z = new_lp1 - uw + 1; z <= new_lp1; z++) sp[z] = tsym;
            for (int z = c_start; z < suf_start; z++) sp[z] = clean_sym;
            memcpy(sp + suf_start, tp + clean_end, tail_len);
            int shift = suf_start - clean_end;
            int ap = new_lp1, as = ls1;
            int thresh = max_p1 + shift;
            long long stp;
            for (stp = 1; stp <= 1000000; stp++) {
                Tr xx = T1[as*NSYM+sp[ap]]; sp[ap]=xx.w; ap+=xx.d; as=xx.ns;
                if (ap > thresh + 4 && as == ex) {
                    int exit_rel_OFF = (ap - shift) - OFF;
                    int L_eff = ap - (new_lp1 - uw + 1);
                    if (li < 4) { Ts[li] = stp; ex_pos[li] = exit_rel_OFF; }
                    else Tuw7 = stp;
                    if (li == 0) printf("gap=%2d BOUNCE t=%d lp1=%+d gdx=%+d gstp=%d ex_rel=%+d L0=%d T=%lld",
                                        gap, t_sep, lp1-OFF, gdx, gstp, exit_rel_OFF, L_eff, stp);
                    else if (li < 4) printf(",%lld", stp);
                    else printf(" | w3=%lld", Tuw7 - Ts[3]);
                    break;
                }
            }
        }
        printf("\n");
    }
    return 0;
}
