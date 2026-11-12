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

static void check_file(const char *path, const char *out_path, int tsym, const char *label) {
    printf("=== Checking %s (tsym=%d, L=7 vs L=10) ===\n", label, tsym);
    FILE *f = fopen(path, "r");
    FILE *fout = fopen(out_path, "w");
    char line[256];
    int total = 0, engines = 0;
    while (fgets(line, sizeof(line), f)) {
        char spec[64];
        int span, lo, hi, last_e, nexp;
        if (sscanf(line, "%63s %d %d %d %d %d", spec, &span, &lo, &hi, &last_e, &nexp) < 6) continue;
        if (hi < 6) continue;
        total++;
        Tr T[12]; int NS, NSYM;
        parse_ag(spec, T, &NS, &NSYM);

        /* Record blank-tape configuration up to t=10000 and compute tape relative to bhi (right frontier) */
        uint8_t base_tp[256]; int OFF = 128;
        memset(base_tp, 0, sizeof(base_tp));
        int p0 = OFF, s0 = 0, blo = OFF, bhi = OFF;
        for (int t = 0; t < 10000; t++) {
            Tr x = T[s0 * NSYM + base_tp[p0]];
            base_tp[p0] = x.w; p0 += x.d; s0 = x.ns;
            if (p0 < blo) blo = p0;
            if (p0 > bhi) bhi = p0;
        }

        /* Chase check: does any state walk monotonically right on tsym^inf at speed > 0.25? */
        int chase_mask = 0;
        for (int st = 0; st < NS; st++) {
            uint8_t tp[128]; memset(tp, tsym, sizeof(tp));
            int pp = 32, ss = st, mn = pp;
            for (int t = 0; t < 40; t++) {
                Tr x = T[ss * NSYM + tp[pp]];
                tp[pp] = x.w; pp += x.d; ss = x.ns;
                if (pp < mn) mn = pp;
                if (pp < 2 || pp >= 126) break;
            }
            if (pp >= 32 + 12 && mn >= 28) chase_mask |= (1 << st);
        }
        if (!chase_mask) continue;

        /* Test bounce reset on L=8 vs L=11 */
        int ok_sr = -1, ok_am = 0;
        long long s8_best = 0, s11_best = 0;
        int exit_s = -1;
        for (int sr = 0; sr < NS; sr++) {
            for (int anchor_mode = 0; anchor_mode < 2; anchor_mode++) {
                long long steps[2] = {0, 0};
                int est[2] = {-1, -1};
                int valid = 1;
                for (int li = 0; li < 2; li++) {
                    int L = li == 0 ? 8 : 11;
                    uint8_t tp[512]; int TOFF = 256;
                    memset(tp, 0, sizeof(tp));
                    if (anchor_mode == 1) {
                        for (int z = blo; z <= bhi; z++) {
                            int dst = TOFF - 1 - (bhi - z);
                            if (dst >= 10 && dst < TOFF) tp[dst] = base_tp[z];
                        }
                    }
                    for (int z = 0; z < 200; z++) tp[TOFF + z] = tsym;
                    int pp = TOFF + L - 1, ss = sr;
                    long long step = 0;
                    for (step = 1; step <= 2000000; step++) {
                        Tr x = T[ss * NSYM + tp[pp]];
                        tp[pp] = x.w; pp += x.d; ss = x.ns;
                        if (pp < TOFF - 50) { valid = 0; break; }
                        if (pp >= TOFF + L) { est[li] = ss; break; }
                    }
                    if (step > 2000000) valid = 0;
                    steps[li] = step;
                }
                if (valid && steps[0] >= 80 && steps[1] >= 2 * steps[0] &&
                    (chase_mask & (1 << est[0])) && (chase_mask & (1 << est[1]))) {
                    ok_sr = sr; ok_am = anchor_mode;
                    s8_best = steps[0]; s11_best = steps[1];
                    exit_s = est[1];
                    break;
                }
            }
            if (ok_sr >= 0) break;
        }
        if (ok_sr >= 0) {
            engines++;
            if (fout) fprintf(fout, "%s\ttsym=%d\tsr=%c\texit=%c\tanchor=%d\tL8=%lld\tL11=%lld\tratio=%.2f\n",
                              spec, tsym, 'A'+ok_sr, 'A'+exit_s, ok_am, s8_best, s11_best, (double)s11_best/s8_best);
            if (engines <= 30) {
                printf("  ENGINE %-22s tsym=%d sr=%c exit=%c L8=%6lld L11=%7lld ratio=%.2f\n",
                       spec, tsym, 'A'+ok_sr, 'A'+exit_s, s8_best, s11_best, (double)s11_best/s8_best);
            }
        }
    }
    fclose(f);
    if (fout) fclose(fout);
    printf("Total %s (tsym=%d): checked=%d, engines=%d\n\n", label, tsym, total, engines);
}

int main(void) {
    check_file("bbwork/bb-variants/CET/counters_3x2_all.txt", "bbwork/bb-variants/CET/engines_3x2_t1.txt", 1, "CET(3)");
    check_file("bbwork/bb-variants/CET/counters_2x3_all.txt", "bbwork/bb-variants/CET/engines_2x3_t1.txt", 1, "CET(2,3)");
    check_file("bbwork/bb-variants/CET/counters_2x3_all.txt", "bbwork/bb-variants/CET/engines_2x3_t2.txt", 2, "CET(2,3)");
    return 0;
}
