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
    char e_spec[64], g_spec[64];
    int n_ent;
    Tr T1[12], T2[12];
    int NS, NSYM, tsym, sr, ex;
    int P, D, M, nH, nB;
} PairItem;

static void analyze_dataset(const char *hits_path, const char *eng_path, const char *out_path, const char *label) {
    /* Load engine exit_s/tsym lookup */
    typedef struct { char spec[64]; int tsym, sr, ex, am; } EngMeta;
    EngMeta *em = malloc(sizeof(EngMeta) * 2000);
    int n_em = 0;
    FILE *fe = fopen(eng_path, "r");
    char line[1024];
    while (fgets(line, sizeof(line), fe)) {
        char sp[64], sr_c, ex_c; int ts, am; long long l8, l11;
        if (sscanf(line, "%63s tsym=%d sr=%c exit=%c anchor=%d L8=%lld L11=%lld",
                   sp, &ts, &sr_c, &ex_c, &am, &l8, &l11) >= 6) {
            strcpy(em[n_em].spec, sp);
            em[n_em].tsym = ts; em[n_em].sr = sr_c - 'A'; em[n_em].ex = ex_c - 'A'; em[n_em].am = am;
            n_em++;
        }
    }
    fclose(fe);

    FILE *fh = fopen(hits_path, "r");
    PairItem *items = malloc(sizeof(PairItem) * 90000);
    int n_items = 0;
    while (fgets(line, sizeof(line), fh) && n_items < 90000) {
        char *tab = strchr(line, '\t');
        if (!tab) continue;
        *tab = 0;
        char *bar = strchr(line, '|');
        if (!bar) continue;
        *bar = 0;
        PairItem it; memset(&it, 0, sizeof(it));
        strcpy(it.e_spec, line);
        strcpy(it.g_spec, bar + 1);
        parse_ag(it.e_spec, it.T1, &it.NS, &it.NSYM);
        parse_ag(it.g_spec, it.T2, &it.NS, &it.NSYM);
        it.n_ent = it.NS * it.NSYM;
        int matched = 0;
        for (int i = 0; i < n_em; i++) {
            if (strcmp(em[i].spec, it.e_spec) == 0) {
                it.tsym = em[i].tsym; it.sr = em[i].sr; it.ex = em[i].ex; matched = 1; break;
            }
        }
        if (!matched) continue;
        if (sscanf(tab + 1, "P=%d D=%d M=%d nH=%d nB=%d", &it.P, &it.D, &it.M, &it.nH, &it.nB) != 5) continue;
        items[n_items++] = it;
    }
    fclose(fh);
    free(em);

    /* Phase 1: Parallel simulation up to t=20000 to mask visited transitions & check bounded Ag1 */
    char (*canon_keys)[140] = calloc(n_items, 140);
    int *valid_flag = calloc(n_items, sizeof(int));

    #pragma omp parallel
    {
        uint8_t *tape = malloc(32768);
        const int OFF = 10000;
        #pragma omp for schedule(dynamic, 64)
        for (int idx = 0; idx < n_items; idx++) {
            const PairItem *it = &items[idx];
            /* Quick verify speed-1 chase on exit_s */
            Tr ch = it->T1[it->ex * it->NSYM + it->tsym];
            if (!(ch.w == it->tsym && ch.d == 1 && ch.ns == it->ex)) continue;

            uint16_t m1 = 0, m2 = 0;
            memset(tape + OFF - 2000, 0, 24000);
            int p1 = OFF, p2 = OFF + 2, s1 = 0, s2 = 0;
            int min1_2k = 999999, min1_20k = 999999, max1_20k = -999999;
            int p1_5k = 0, p2_5k = 0, s1_5k = 0, s2_5k = 0, min1_5k = 999999, max1_5k = -999999;
            int min2_after = 999999;
            int bad = 0;
            int early_exit = 0;
            for (int t = 1; t <= 20000; t++) {
                int r1 = tape[p1], r2 = tape[p2];
                m1 |= (1 << (s1 * it->NSYM + r1));
                m2 |= (1 << (s2 * it->NSYM + r2));
                Tr x = it->T1[s1 * it->NSYM + r1];
                Tr y = it->T2[s2 * it->NSYM + r2];
                tape[p2] = y.w; tape[p1] = x.w;
                p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
                if (p1 == p2) { bad = 1; break; }
                if (p1 < 500 || p1 >= 32000 || p2 < 500 || p2 >= 32000) { bad = 1; break; }
                if (t == 5000) { p1_5k = p1; p2_5k = p2; s1_5k = s1; s2_5k = s2; }
                if (t <= 5000) {
                    if (p1 < min1_5k) min1_5k = p1;
                    if (p1 > max1_5k) max1_5k = p1;
                }
                if (t >= 2000 && t <= 5000 && p1 < min1_2k) min1_2k = p1;
                if (t > 5000) {
                    if (p1 < min1_20k) min1_20k = p1;
                    if (p1 > max1_20k) max1_20k = p1;
                    if (p2 < min2_after) min2_after = p2;
                    if (p1 > max1_5k + 5 && !early_exit) early_exit = t;
                }
            }
            if (bad) continue;
            /* Reject left-drifting Ag1: if not early_exiting right, min1 should not expand significantly left */
            if (!early_exit && min1_20k < min1_5k - 2) continue;

            /* Construct canonical masked spec string using masks from 0..20000 + check_local */
            /* Re-run 5000 steps to get tape for detect_glider_full */
            memset(tape + OFF - 500, 0, 7000);
            p1 = OFF; p2 = OFF + 2; s1 = 0; s2 = 0;
            for (int t = 1; t <= 5000; t++) {
                Tr x = it->T1[s1 * it->NSYM + tape[p1]];
                Tr y = it->T2[s2 * it->NSYM + tape[p2]];
                tape[p2] = y.w; tape[p1] = x.w;
                p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
            }
            int act_P, act_D, gl_s, pat_off, span_l;
            uint8_t pat[96];
            if (!detect_glider_full(it->T2, it->NSYM, tape, 32768, p2, s2, it->tsym,
                                    &act_P, &act_D, &gl_s, pat, &pat_off, &span_l)) continue;
            int min_gap = span_l + 4; if (min_gap < 8) min_gap = 8;
            int M = act_P - act_D;
            for (int r = 0; r < M && r < 60; r++) {
                int gap = min_gap + r;
                uint8_t tp[1024]; int LOFF = 300;
                for (int i = 0; i < LOFF + gap; i++) tp[i] = it->tsym;
                for (int i = LOFF + gap; i < 1024; i++) tp[i] = 0;
                for (int i = 0; i < 96; i++) {
                    int dst = LOFF + gap - pat_off + i;
                    if (dst >= 0 && dst < 1024) tp[dst] = pat[i];
                }
                int lp1 = LOFF, ls1 = it->ex, lp2 = LOFF + gap, ls2 = gl_s;
                for (int step = 1; step <= 450; step++) {
                    int r1 = tp[lp1], r2 = tp[lp2];
                    m1 |= (1 << (ls1 * it->NSYM + r1));
                    m2 |= (1 << (ls2 * it->NSYM + r2));
                    Tr x = it->T1[ls1 * it->NSYM + r1];
                    Tr y = it->T2[ls2 * it->NSYM + r2];
                    tp[lp2] = y.w; tp[lp1] = x.w;
                    lp1 += x.d; ls1 = x.ns; lp2 += y.d; ls2 = y.ns;
                    if (lp1 == lp2 || lp1 < 20 || lp1 >= 1000 || lp2 < 20 || lp2 >= 1000) break;
                    if (lp1 < LOFF - 15 && lp2 > LOFF + gap && lp2 - lp1 > 20) break;
                }
            }
            /* Also mask counter transitions on L=9 */
            {
                uint8_t ctp[512]; int COFF = 256;
                memset(ctp, 0, sizeof(ctp));
                for (int z = 0; z < 100; z++) ctp[COFF + z] = it->tsym;
                int cp = COFF + 8, cs = it->sr;
                for (int stp = 1; stp <= 200000; stp++) {
                    int r1 = ctp[cp];
                    m1 |= (1 << (cs * it->NSYM + r1));
                    Tr x = it->T1[cs * it->NSYM + r1];
                    ctp[cp] = x.w; cp += x.d; cs = x.ns;
                    if (cp < 10 || cp >= COFF + 9) break;
                }
            }
            /* Build canonical key replacing unmasked entries with --- */
            char ke[64], kg[64];
            for (int q = 0; q < it->NS; q++) {
                int p_off = q * (it->NSYM * 3 + 1);
                if (q) { ke[p_off - 1] = '_'; kg[p_off - 1] = '_'; }
                for (int b = 0; b < it->NSYM; b++) {
                    int ei = q * it->NSYM + b;
                    if (m1 & (1 << ei)) memcpy(ke + p_off + b*3, it->e_spec + p_off + b*3, 3);
                    else memcpy(ke + p_off + b*3, "---", 3);
                    if (m2 & (1 << ei)) memcpy(kg + p_off + b*3, it->g_spec + p_off + b*3, 3);
                    else memcpy(kg + p_off + b*3, "---", 3);
                }
            }
            int slen = it->NS * it->NSYM * 3 + it->NS - 1;
            ke[slen] = 0; kg[slen] = 0;
            sprintf(canon_keys[idx], "%s|%s", ke, kg);
            valid_flag[idx] = 1;
        }
        free(tape);
    }

    /* Deduplicate by canon_keys, write unique mechanisms with concrete Round1 check up to 1M steps */
    FILE *fout = fopen(out_path, "w");
    int n_uniq = 0, n_r1_fast = 0;
    /* Simple hash table */
    int hsz = 262144;
    int *ht = malloc(sizeof(int) * hsz);
    memset(ht, -1, sizeof(int) * hsz);

    for (int i = 0; i < n_items; i++) {
        if (!valid_flag[i]) continue;
        unsigned long h = 5381;
        for (const char *p = canon_keys[i]; *p; p++) h = ((h << 5) + h) + (unsigned char)(*p);
        unsigned int slot = h & (hsz - 1);
        int dup = 0;
        while (ht[slot] != -1) {
            if (strcmp(canon_keys[ht[slot]], canon_keys[i]) == 0) { dup = 1; break; }
            slot = (slot + 1) & (hsz - 1);
        }
        if (dup) continue;
        ht[slot] = i;
        n_uniq++;

        /* Test Round 1 overflow concretely up to 600,000 steps (just Ag1 once past t=5000 + chase!) */
        const PairItem *it = &items[i];
        static uint8_t tape[200000];
        const int OFF = 2000;
        memset(tape, 0, 8000);
        int p1 = OFF, p2 = OFF + 2, s1 = 0, s2 = 0;
        int min1 = OFF, max1 = OFF;
        int exit_t = 0, exit_p1 = 0;
        for (int t = 1; t <= 5000; t++) {
            Tr x = it->T1[s1 * it->NSYM + tape[p1]];
            Tr y = it->T2[s2 * it->NSYM + tape[p2]];
            tape[p2] = y.w; tape[p1] = x.w;
            p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
            if (p1 < min1) min1 = p1;
            if (p1 > max1) max1 = p1;
        }
        int wall_x = max1;
        /* Count how far tsym wall extends from max1..p2 */
        int p1_r1_exit = 0, t_r1_exit = 0;
        /* Actually find first time p1 exceeds max1 and reaches p1 > max1 + 2 in state ex (while remaining < p2) */
        for (int t = 5001; t <= 600000; t++) {
            Tr x = it->T1[s1 * it->NSYM + tape[p1]];
            Tr y = it->T2[s2 * it->NSYM + tape[p2]];
            tape[p2] = y.w; tape[p1] = x.w;
            p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
            if (p1 == p2) { t_r1_exit = -t; break; }
            if (p1 >= sizeof(tape) - 200 || p2 >= sizeof(tape) - 200 || p1 < 50) break;
            if (s1 == it->ex && p1 > wall_x + 4 && p1 < p2 - 10) {
                t_r1_exit = t; p1_r1_exit = p1; break;
            }
        }
        if (t_r1_exit > 0) n_r1_fast++;
        fprintf(fout, "%s\t%s\tP=%d\tD=%d\tM=%d\tnH=%d\tnB=%d\texit_t=%d\tmin1=%d\twall=%d\n",
                canon_keys[i], it->e_spec, it->P, it->D, it->M, it->nH, it->nB, t_r1_exit, min1 - OFF, wall_x - OFF);
    }
    fclose(fout);
    free(ht); free(canon_keys); free(valid_flag); free(items);
    printf("[%s] input=%d -> unique canonical=%d (fast R1 exit <=600k: %d)\n", label, n_items, n_uniq, n_r1_fast);
}

int main(void) {
    analyze_dataset("bbwork/bb-variants/CET/hits_cet3_P4.txt", "bbwork/bb-variants/CET/engines_3x2_t1.txt",
                    "bbwork/bb-variants/CET/uniq_cet3.txt", "CET(3)");
    analyze_dataset("bbwork/bb-variants/CET/hits_cet23_t1_P4.txt", "bbwork/bb-variants/CET/engines_2x3_t1.txt",
                    "bbwork/bb-variants/CET/uniq_cet23_t1.txt", "CET(2,3) t1");
    analyze_dataset("bbwork/bb-variants/CET/hits_cet23_t2_P4.txt", "bbwork/bb-variants/CET/engines_2x3_t2.txt",
                    "bbwork/bb-variants/CET/uniq_cet23_t2.txt", "CET(2,3) t2");
    return 0;
}
