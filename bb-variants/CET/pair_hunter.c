#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns; } Tr;
typedef struct {
    Tr T[12];
    int NS, NSYM;
    int sr, exit_s, tsym;
    char spec[64];
} Engine;

typedef struct {
    Tr T[12];
    int P, D, tsym;
    char spec[64];
} Glider;

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

/* Measure active glider at (p2_cur, s2_cur) on orig_tape[0..orig_sz-1] */
static int detect_active_glider(const Tr *T2, int NS2, int NSYM, const uint8_t *orig_tape, int orig_sz,
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
        /* Verify behind head is tsym */
        int min_h = ph[299];
        for (int t = 300 - P; t < 300; t++) if (ph[t] < min_h) min_h = ph[t];
        int trail_ok = 1;
        for (int z = min_h - 10; z < min_h; z++) {
            if (z < 0 || tp[z] != tsym) { trail_ok = 0; break; }
        }
        if (!trail_ok) continue;
        /* Snapshot tape at t=299 */
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
        *out_pat_off = span_l + 8; /* pat[*out_pat_off] is head p */
        *out_span_l = span_l;
        for (int i = 0; i < 8; i++) if (out_pat[i] != tsym) return 0;
        return 1;
    }
    return 0;
}

/* Check local collision at gap G (p1=0 in exit_s, p2=G in gl_s)
   Returns: 1=HALT, 2=CLEAN_BOUNCE, 0=OTHER/BREAK */
static int check_local_gap(const Engine *E, const Glider *Ggl, int gap,
                           const uint8_t *pat, int pat_off, int gl_s, int P, int D, int *out_step) {
    uint8_t tp[1024];
    int OFF = 300;
    for (int i = 0; i < OFF + gap; i++) tp[i] = E->tsym;
    for (int i = OFF + gap; i < 1024; i++) tp[i] = 0;
    /* Place glider pattern relative to OFF + gap */
    for (int i = 0; i < 96; i++) {
        int dst = OFF + gap - pat_off + i;
        if (dst >= 0 && dst < 1024) tp[dst] = pat[i];
    }
    int p1 = OFF, s1 = E->exit_s;
    int p2 = OFF + gap, s2 = gl_s;
    int left_reflected = 0;
    for (int step = 1; step <= 450; step++) {
        Tr x = E->T[s1 * E->NSYM + tp[p1]];
        Tr y = Ggl->T[s2 * E->NSYM + tp[p2]];
        tp[p2] = y.w; tp[p1] = x.w;
        p1 += x.d; s1 = x.ns;
        p2 += y.d; s2 = y.ns;
        if (p1 == p2) { *out_step = step; return 1; }
        if (p1 < 20 || p1 >= 1000 || p2 < 20 || p2 >= 1000) return 0;
        if (p1 < OFF - 15) {
            /* Agent 1 is sweeping left! Check if it has separated from Agent 2 and is in wipe/reset */
            if (!left_reflected && p2 > OFF + gap && p2 - p1 > 20) {
                left_reflected = step;
                /* Test if Ag2 re-enters clean glider P, D (or any slow glider) while Ag1 is sweeping left! */
                int tmp_P, tmp_D, tmp_gs, tmp_off, tmp_spanl;
                uint8_t tmp_pat[96];
                if (detect_active_glider(Ggl->T, E->NS, E->NSYM, tp, 1024, p2, s2, E->tsym,
                                         &tmp_P, &tmp_D, &tmp_gs, tmp_pat, &tmp_off, &tmp_spanl)) {
                    /* Also check Ag1 is wiping leftward (not looping or flying away right) */
                    uint8_t tp1_chk[128];
                    memcpy(tp1_chk, tp + p1 - 64, 128);
                    int ap = 64, as = s1, min_ap = 64;
                    for (int k = 0; k < 60; k++) {
                        Tr tx = E->T[as * E->NSYM + tp1_chk[ap]];
                        tp1_chk[ap] = tx.w; ap += tx.d; as = tx.ns;
                        if (ap < min_ap) min_ap = ap;
                    }
                    if (ap <= 64 - 4) { /* actively wiping leftward! */
                        *out_step = step;
                        return 2;
                    }
                }
                return 0;
            }
        }
    }
    return 0;
}

static void run_search(const char *eng_path, const char *gl_path, const char *out_path,
                       int min_P, int target_tsym, int max_eng, const char *label) {
    Engine *engs = malloc(sizeof(Engine) * 4000);
    int n_eng = 0;
    FILE *fe = fopen(eng_path, "r");
    char line[256];
    while (fgets(line, sizeof(line), fe) && n_eng < max_eng) {
        Engine e; memset(&e, 0, sizeof(e));
        char sr_c = 'A', ex_c = 'B';
        int am = 0; long long l8 = 0, l11 = 0; double rat = 0;
        if (sscanf(line, "%63s tsym=%d sr=%c exit=%c anchor=%d L8=%lld L11=%lld ratio=%lf",
                   e.spec, &e.tsym, &sr_c, &ex_c, &am, &l8, &l11, &rat) >= 4) {
            if (e.tsym != target_tsym) continue;
            parse_ag(e.spec, e.T, &e.NS, &e.NSYM);
            e.sr = sr_c - 'A'; e.exit_s = ex_c - 'A';
            engs[n_eng++] = e;
        }
    }
    fclose(fe);

    Glider *gls = malloc(sizeof(Glider) * 500000);
    int n_gl = 0;
    FILE *fg = fopen(gl_path, "r");
    while (fgets(line, sizeof(line), fg) && n_gl < 500000) {
        Glider g; memset(&g, 0, sizeof(g));
        int unif = 0;
        if (sscanf(line, "%63s P=%d D=%d unif=%d tsym=%d", g.spec, &g.P, &g.D, &unif, &g.tsym) == 5) {
            if (!unif || g.tsym != target_tsym || g.P < min_P) continue;
            int ns, nsym;
            parse_ag(g.spec, g.T, &ns, &nsym);
            gls[n_gl++] = g;
        }
    }
    fclose(fg);

    printf("=== %s: engines=%d gliders(P>=%d,tsym=%d)=%d (total=%lld pairs) ===\n",
           label, n_eng, min_P, target_tsym, n_gl, (long long)n_eng * n_gl);
    fflush(stdout);

    FILE *fout = fopen(out_path, "w");
    long long hits = 0;

    #pragma omp parallel
    {
        uint8_t *tape = malloc(16384);
        const int OFF = 6000;
        #pragma omp for schedule(dynamic, 1)
        for (int ei = 0; ei < n_eng; ei++) {
            const Engine *E = &engs[ei];
            for (int gi = 0; gi < n_gl; gi++) {
                const Glider *G = &gls[gi];
                memset(tape + OFF - 500, 0, 6000);
                int p1 = OFF, p2 = OFF + 2, s1 = 0, s2 = 0;
                int min1_4k = 999999, max1_4k = -999999;
                int p2_4k = 0, min2_4k = 999999;
                int bad = 0;
                for (int t = 1; t <= 5000; t++) {
                    Tr x = E->T[s1 * E->NSYM + tape[p1]];
                    Tr y = G->T[s2 * E->NSYM + tape[p2]];
                    tape[p2] = y.w; tape[p1] = x.w;
                    p1 += x.d; s1 = x.ns;
                    p2 += y.d; s2 = y.ns;
                    if (p1 == p2) { bad = 1; break; }
                    if (p1 < 500 || p1 >= 15800 || p2 < 500 || p2 >= 15800) { bad = 1; break; }
                    if (t == 4000) { p2_4k = p2; }
                    if (t >= 4000) {
                        if (p1 < min1_4k) min1_4k = p1;
                        if (p1 > max1_4k) max1_4k = p1;
                        if (p2 < min2_4k) min2_4k = p2;
                    }
                }
                if (bad) continue;
                if (min2_4k <= max1_4k + 6) continue;
                if (max1_4k - min1_4k > 120) continue;
                if (p2 <= p2_4k || p2 - p2_4k >= 950) continue;

                /* Detect active glider at t=5000 */
                int act_P, act_D, gl_s, pat_off, span_l;
                uint8_t pat[96];
                if (!detect_active_glider(G->T, E->NS, E->NSYM, tape, 16384, p2, s2, E->tsym,
                                          &act_P, &act_D, &gl_s, pat, &pat_off, &span_l)) continue;
                int M = act_P - act_D;
                if (M < 2) continue;

                int n_halt = 0, n_bounce = 0;
                char summary[512]; int slen = 0;
                int min_gap = span_l + 4;
                if (min_gap < 8) min_gap = 8;
                for (int r = 0; r < M && r < 60; r++) {
                    int gap = min_gap + r;
                    int stp = 0;
                    int res = check_local_gap(E, G, gap, pat, pat_off, gl_s, act_P, act_D, &stp);
                    if (res == 1) { n_halt++; if (slen < 480) slen += sprintf(summary + slen, " H(%d:%d)", gap, stp); }
                    else if (res == 2) { n_bounce++; if (slen < 480) slen += sprintf(summary + slen, " B(%d:%d)", gap, stp); }
                }
                if (n_halt >= 1 && n_bounce >= 1) {
                    #pragma omp critical
                    {
                        hits++;
                        if (fout) fprintf(fout, "%s|%s\tP=%d D=%d M=%d nH=%d nB=%d p1=[%d,%d] p2=%d spanL=%d%s\n",
                                          E->spec, G->spec, act_P, act_D, M, n_halt, n_bounce,
                                          min1_4k - OFF, max1_4k - OFF, p2 - OFF, span_l, summary);
                        if (hits <= 20) {
                            printf("  HIT #%lld: %s|%s (P=%d D=%d M=%d) nH=%d nB=%d%s\n",
                                   hits, E->spec, G->spec, act_P, act_D, M, n_halt, n_bounce, summary);
                            fflush(stdout);
                        }
                    }
                }
            }
        }
        free(tape);
    }
    if (fout) fclose(fout);
    free(engs); free(gls);
    printf("Finished %s: total hits=%lld\n\n", label, hits);
    fflush(stdout);
}

static void self_test_pair(const char *e_spec, int exit_ch, int tsym, const char *g_spec, const char *label) {
    Engine E; memset(&E, 0, sizeof(E));
    parse_ag(e_spec, E.T, &E.NS, &E.NSYM);
    E.tsym = tsym; E.exit_s = exit_ch - 'A'; strcpy(E.spec, e_spec);
    Glider G; memset(&G, 0, sizeof(G));
    parse_ag(g_spec, G.T, &E.NS, &E.NSYM);
    strcpy(G.spec, g_spec);

    uint8_t *tape = calloc(16384, 1);
    const int OFF = 6000;
    int p1 = OFF, p2 = OFF + 2, s1 = 0, s2 = 0;
    int min1_4k = 999999, max1_4k = -999999, p2_4k = 0, min2_4k = 999999, bad = 0;
    for (int t = 1; t <= 5000; t++) {
        Tr x = E.T[s1 * E.NSYM + tape[p1]];
        Tr y = G.T[s2 * E.NSYM + tape[p2]];
        tape[p2] = y.w; tape[p1] = x.w;
        p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
        if (p1 == p2) { bad = 1; break; }
        if (t == 4000) p2_4k = p2;
        if (t >= 4000) {
            if (p1 < min1_4k) min1_4k = p1;
            if (p1 > max1_4k) max1_4k = p1;
            if (p2 < min2_4k) min2_4k = p2;
        }
    }
    int act_P = 0, act_D = 0, gl_s = 0, pat_off = 0, span_l = 0;
    uint8_t pat[96];
    int det = (!bad) && detect_active_glider(G.T, E.NS, E.NSYM, tape, 16384, p2, s2, E.tsym,
                                             &act_P, &act_D, &gl_s, pat, &pat_off, &span_l);
    printf("[SELF-TEST %s] bad=%d p1=[%d,%d] p2_4k=%d min2_4k=%d p2=%d det=%d (P=%d D=%d spanL=%d)\n",
           label, bad, min1_4k - OFF, max1_4k - OFF, p2_4k - OFF, min2_4k - OFF, p2 - OFF, det, act_P, act_D, span_l);
    if (det) {
        int M = act_P - act_D, nH = 0, nB = 0;
        int min_gap = span_l + 4; if (min_gap < 8) min_gap = 8;
        printf("  classes (mod %d):", M);
        for (int r = 0; r < M; r++) {
            int stp = 0, gap = min_gap + r;
            int res = check_local_gap(&E, &G, gap, pat, pat_off, gl_s, act_P, act_D, &stp);
            if (res == 1) { nH++; printf(" H(%d:%d)", gap, stp); }
            else if (res == 2) { nB++; printf(" B(%d:%d)", gap, stp); }
            else printf(" .(%d)", gap);
        }
        printf(" => nH=%d nB=%d\n", nH, nB);
    }
    free(tape);
    fflush(stdout);
}

int main(int argc, char **argv) {
    self_test_pair("1LB0RA_1LC1RB_0RB0LC", 'B', 1, "1RB0LB_0RC0LA_1LB1RC", "CET3_3round");
    self_test_pair("1LB1RA_0RB1LC_1RA0LB", 'B', 1, "1RB0RC_1LB1LC_1RA0RB", "CET3_5e47");
    run_search("bbwork/bb-variants/CET/engines_3x2_t1.txt", "bbwork/bb-variants/CET/gliders_3x2.txt",
               "bbwork/bb-variants/CET/hits_cet3_P4.txt", 4, 1, 600, "CET(3) P>=4 tsym=1");
    run_search("bbwork/bb-variants/CET/engines_2x3_t1.txt", "bbwork/bb-variants/CET/gliders_2x3.txt",
               "bbwork/bb-variants/CET/hits_cet23_t1_P4.txt", 4, 1, 600, "CET(2,3) P>=4 tsym=1");
    run_search("bbwork/bb-variants/CET/engines_2x3_t2.txt", "bbwork/bb-variants/CET/gliders_2x3.txt",
               "bbwork/bb-variants/CET/hits_cet23_t2_P4.txt", 4, 2, 600, "CET(2,3) P>=4 tsym=2");
    return 0;
}
