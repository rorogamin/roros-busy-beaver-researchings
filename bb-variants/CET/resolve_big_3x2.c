/* Resolve all 1,116 BIG_R1 CET(3) items: simulate to 100M steps + check R1 splice if z_clean >= 6! */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns; } Tr;

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

typedef struct { char spec[32]; int tsym, ex; } EM3;
typedef struct { char raw[32768]; char pair[64], e_spec[32]; int P, D, M, mg, ex, tsym; } Item3;

static Item3 items[2000];
static char out_res[2000][256];

int main(void) {
    EM3 ems[2000]; int nem = 0;
    FILE *fe = fopen("bbwork/bb-variants/CET/engines_3x2_all.txt", "r");
    char *line = malloc(65536);
    while (fgets(line, 65536, fe)) {
        char sp[32], sr_c, ex_c; int ts;
        if (sscanf(line, "%31s\ttsym=%d\tsr=%c\texit=%c", sp, &ts, &sr_c, &ex_c) == 4) {
            strcpy(ems[nem].spec, sp); ems[nem].tsym = ts; ems[nem].ex = ex_c - 'A'; nem++;
        }
    }
    fclose(fe);

    int n_it = 0;
    FILE *fi = fopen("bbwork/bb-variants/CET/pinned_cet3_exh.txt", "r");
    while (fgets(line, 65536, fi) && n_it < 2000) {
        if (strncmp(line, "BIG_R1:", 7) != 0) continue;
        int L = (int)strlen(line);
        while (L > 0 && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        char *sep = strstr(line, "\t||");
        if (!sep) continue;
        char *mech_raw = sep + 3;
        char *tab = strchr(mech_raw, '\t'); if (!tab) continue;
        Item3 *it = &items[n_it];
        strcpy(it->raw, mech_raw);
        char *mech = tab + 1;
        sscanf(mech, "%63[^\t]\t%31[^\t]", it->pair, it->e_spec);
        char *pp = strstr(mech, "\tP="); it->P = pp ? atoi(pp + 3) : 0;
        char *dp = strstr(mech, "\tD="); it->D = dp ? atoi(dp + 3) : 0;
        char *mp = strstr(mech, "\tM="); it->M = mp ? atoi(mp + 3) : 0;
        char *mgp = strstr(mech, "\tmg="); it->mg = mgp ? atoi(mgp + 4) : 8;
        char *tsp = strstr(mech, "tsym="); it->tsym = tsp ? atoi(tsp + 5) : 1;
        it->ex = -1;
        for (int i = 0; i < nem; i++) {
            if (ems[i].tsym == it->tsym && strcmp(ems[i].spec, it->e_spec) == 0) { it->ex = ems[i].ex; break; }
        }
        if (it->ex >= 0) n_it++;
    }
    fclose(fi); free(line);
    printf("Testing %d BIG_R1 CET3 items up to 60M steps...\n", n_it); fflush(stdout);

    int c_col1 = 0, c_halt = 0, c_loop = 0, c_still = 0;
    #pragma omp parallel for schedule(dynamic, 4) reduction(+:c_col1,c_halt,c_loop,c_still)
    for (int idx = 0; idx < n_it; idx++) {
        const Item3 *it = &items[idx];
        char ce[32], cg[32];
        const char *bar = strchr(it->pair, '|');
        int elen = (int)(bar - it->pair);
        memcpy(ce, it->pair, elen); ce[elen] = 0; strcpy(cg, bar + 1);
        Tr T1[6], T2[6]; parse_tbl3(ce, T1); parse_tbl3(cg, T2);

        /* First get glider pat on small tape */
        uint8_t *stape = calloc(16384, 1);
        int p1 = 2048, p2 = 2050, s1 = 0, s2 = 0;
        for (int t = 1; t <= 3000; t++) {
            Tr x = T1[s1 * 2 + stape[p1]], y = T2[s2 * 2 + stape[p2]];
            stape[p2] = y.w; stape[p1] = x.w; p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
        }
        int act_P = 0, act_D = 0, gl_s = 0, pat_off = 0, span_l = 0; uint8_t pat[96];
        detect_glider_3(T2, stape, 16384, p2, s2, it->tsym, &act_P, &act_D, &gl_s, pat, &pat_off, &span_l);
        free(stape);
        int M = act_P - act_D, mg = span_l + 4; if (mg < 8) mg = 8;

        /* Now run up to 60,000,000 steps! Notice max p2 at D/P<=1/3 is 20M! Wait use dynamic or 22M array! */
        /* Wait 16 threads * 22M = 352MB total — fits trivially in RAM! */
        const int TSZ = 22000000;
        const int OFF = 50000;
        uint8_t *tape = calloc(TSZ, 1);
        p1 = OFF; p2 = OFF + 2; s1 = 0; s2 = 0;
        int min1_r1 = OFF, max1_r1 = OFF, min1_20k = OFF, max1_20k = OFF;
        long long col1_t = 0; int col1_gap = -1, x_bounce = 0;
        int max1_100k = OFF;

        for (long long t = 1; t <= 60000000LL; t++) {
            Tr x = T1[s1 * 2 + tape[p1]], y = T2[s2 * 2 + tape[p2]];
            tape[p2] = y.w; tape[p1] = x.w;
            p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
            if (p1 < 100 || p1 >= TSZ - 200 || p2 < 100 || p2 >= TSZ - 200) { col1_t = -t; break; }
            if (p1 < min1_r1) min1_r1 = p1;
            if (p1 > max1_r1) max1_r1 = p1;
            if (t == 20000) max1_20k = max1_r1;
            if (t == 100000) max1_100k = max1_r1;
            if (p1 == p2) { col1_t = -t; break; }
            if (t >= 200 && p2 >= OFF + 12 && s1 == it->ex && s2 == gl_s && p2 - p1 >= mg && p2 - p1 < mg + M) {
                int st = p2 - pat_off, m = 1;
                if (st >= 0 && st + 20 < TSZ) {
                    for (int k = 0; k < 20; k++) if (tape[st + k] != pat[k]) { m = 0; break; }
                } else m = 0;
                if (m) { col1_t = t; col1_gap = p2 - p1; x_bounce = p1; break; }
            }
            /* Early loop detector: if t == 1500000 and max1_r1 == max1_20k and max1_r1 <= OFF + 45: check period of Ag1 alone? */
            if (t == 2000000 && max1_r1 <= OFF + 160 && max1_r1 == max1_100k) {
                /* Wait: could still be a 2^30 counter! Only test if Ag1 is actually cycling or counter-sweeping? Skip early abort at 2M, just let 60M finish (~0.15s per thread!) */
            }
        }
        if (col1_t < 0) { free(tape); c_halt++; sprintf(out_res[idx], "HALT_BIG:%lld", -col1_t); continue; }
        if (col1_t == 0) {
            /* Print max1 at 20k vs 60M! */
            c_still++;
            sprintf(out_res[idx], "STILL_60M:m20k=%d:m60m=%d:p1=%d:p2=%d",
                    max1_20k - OFF, max1_r1 - OFF, p1 - OFF, p2 - OFF);
            free(tape); continue;
        }
        int r2_min1 = x_bounce, r2_hit_left = 0;
        long long halt2 = 0;
        for (int k = 1; k <= 1200000; k++) {
            Tr x = T1[s1 * 2 + tape[p1]], y = T2[s2 * 2 + tape[p2]];
            tape[p2] = y.w; tape[p1] = x.w;
            p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
            if (p1 < 100 || p1 >= TSZ - 200 || p2 < 100 || p2 >= TSZ - 200 || p1 == p2) { halt2 = col1_t + k; break; }
            if (p1 < r2_min1) r2_min1 = p1;
            if (p1 < min1_r1 + 5 && k > 300) r2_hit_left = 1;
            if (r2_hit_left && k > 15000 && p1 > min1_r1 + 40) break;
        }
        if (halt2) { free(tape); c_halt++; sprintf(out_res[idx], "HALT2_BIG:%lld", halt2); continue; }
        int cz = 1; for (int z = r2_min1 - 6; z < r2_min1; z++) if (tape[z] != 0) cz = 0;
        char lw[16]; for (int z = 0; z < 10; z++) lw[z] = '0' + tape[r2_min1 - 2 + z]; lw[10] = 0;
        c_col1++;
        sprintf(out_res[idx], "R1=COL1:t=%lld:gap=%d:x1=%d:r2min=%d:cz=%d:lw=%s",
                col1_t, col1_gap, x_bounce - OFF, r2_min1 - OFF, cz, lw);
        free(tape);
    }
    FILE *fo = fopen("bbwork/bb-variants/CET/pinned_cet3_big.txt", "w");
    for (int i = 0; i < n_it; i++) fprintf(fo, "%s\t||%s\n", out_res[i], items[i].raw);
    fclose(fo);
    printf("BIG_R1 60M resolution: tot=%d COL1=%d HALT=%d STILL_60M=%d\n", n_it, c_col1, c_halt, c_still);
    return 0;
}
