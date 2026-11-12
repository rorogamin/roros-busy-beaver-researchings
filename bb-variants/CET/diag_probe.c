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
    int tsym = 1, ex = 1; /* B */
    uint8_t *tape = calloc(131072, 1);
    const int OFF0 = 2000;
    int p1 = OFF0, p2 = OFF0 + 2, s1 = 0, s2 = 0;
    for (int t = 1; t <= 5000; t++) {
        Tr x = T1[s1*NSYM+tape[p1]], y = T2[s2*NSYM+tape[p2]];
        tape[p2]=y.w; tape[p1]=x.w; p1+=x.d; s1=x.ns; p2+=y.d; s2=y.ns;
    }
    int act_P, act_D, gl_s, pat_off, span_l; uint8_t pat[96];
    int det = detect_glider_full(T2, NSYM, tape, 131072, p2, s2, tsym, &act_P, &act_D, &gl_s, pat, &pat_off, &span_l);
    printf("det=%d P=%d D=%d gl_s=%c pat_off=%d span_l=%d\n", det, act_P, act_D, 'A'+gl_s, pat_off, span_l);
    int M = act_P - act_D, min_gap = span_l + 4; if (min_gap < 8) min_gap = 8;
    for (int r = 0; r < M; r++) {
        int gap = min_gap + r;
        int L = 9;
        uint8_t tp[2048]; int OFF = 1000;
        for (int i=0;i<OFF-L;i++) tp[i]=0;
        for (int i=OFF-L;i<OFF+gap;i++) tp[i]=tsym;
        for (int i=OFF+gap;i<2048;i++) tp[i]=0;
        for (int i=0;i<96;i++){ int dst=OFF+gap-pat_off+i; if(dst>=0&&dst<2048) tp[dst]=pat[i]; }
        int lp1=OFF, ls1=ex, lp2=OFF+gap, ls2=gl_s;
        int reason=0, synced=0, exit_x=0; long long exit_t=0;
        for (long long t=1; t<=450; t++) {
            Tr x=T1[ls1*NSYM+tp[lp1]], y=T2[ls2*NSYM+tp[lp2]];
            tp[lp2]=y.w; tp[lp1]=x.w; lp1+=x.d; ls1=x.ns; lp2+=y.d; ls2=y.ns;
            if (lp1==lp2) { reason=1; printf("gap=%d -> HALT step %lld\n", gap, t); break; }
            if (lp1<OFF-8 && lp2>OFF+gap && lp2-lp1>16) {
                int nP, nD, ngs, noff, nsl; uint8_t npat[96];
                if (!detect_glider_full(T2, NSYM, tp, 2048, lp2, ls2, tsym, &nP, &nD, &ngs, npat, &noff, &nsl)) { reason=2; break; }
                uint8_t sync_tp[2048]; memcpy(sync_tp, tp, 2048);
                int sp2=lp2, ss2=ls2;
                for (int k=0;k<299;k++){ Tr sy=T2[ss2*NSYM+sync_tp[sp2]]; sync_tp[sp2]=sy.w; sp2+=sy.d; ss2=sy.ns; }
                for (int extra=0; extra<act_P; extra++) {
                    if (ss2==gl_s) {
                        int st=sp2-pat_off, match=1;
                        for (int i=0;i<64;i++) if (sync_tp[st+i]!=pat[i]) { match=0; break; }
                        if (match) { synced=1; break; }
                    }
                    Tr sy=T2[ss2*NSYM+sync_tp[sp2]]; sync_tp[sp2]=sy.w; sp2+=sy.d; ss2=sy.ns;
                }
                if (!synced) { reason=3; printf("gap=%d -> det_gl ok P=%d D=%d gs=%c but NOT synced!\n", gap, nP, nD, 'A'+ngs); break; }
                for (int i=lp2-nsl-2;i<2048;i++) if (i>=OFF+gap) tp[i]=tsym;
                /* wait: run standalone! */
                int hit_left=0;
                for (long long step=t+1; step<=1000000; step++) {
                    Tr xx=T1[ls1*NSYM+tp[lp1]]; tp[lp1]=xx.w; lp1+=xx.d; ls1=xx.ns;
                    if (lp1 <= OFF-L+1) hit_left=1;
                    if (lp1<20||lp1>=2000) { reason=4; break; }
                    if (hit_left && ls1==ex && lp1>=OFF-4) {
                        int ok=1; for (int z=0;z<8;z++) if (tp[lp1+z]!=tsym) ok=0;
                        if (ok) { reason=5; exit_x=lp1-OFF; exit_t=step; break; }
                    }
                }
                printf("gap=%d -> BOUNCE t=%lld sync=%d reason=%d exit_x=%d exit_t=%lld\n", gap, t, synced, reason, exit_x, exit_t);
                break;
            }
        }
        if (reason == 0 || reason == 2) printf("gap=%d -> FAIL reason=%d\n", gap, reason);
    }
    return 0;
}
