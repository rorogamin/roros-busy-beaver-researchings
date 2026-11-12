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

static void inspect_file(const char *path, const char *label) {
    printf("=== Inspecting %s ===\n", label);
    FILE *f = fopen(path, "r");
    char line[256];
    int total = 0, exact_pow2 = 0, exact_pow3 = 0, other_exp = 0;
    int shown = 0;
    while (fgets(line, sizeof(line), f)) {
        char spec[64], sr_c, ex_c;
        int tsym, am; long long l8, l11; double rat;
        if (sscanf(line, "%63s tsym=%d sr=%c exit=%c anchor=%d L8=%lld L11=%lld ratio=%lf",
                   spec, &tsym, &sr_c, &ex_c, &am, &l8, &l11, &rat) < 8) continue;
        total++;
        if (am != 0) continue; /* check clean zero-anchor first */
        Tr T[12]; int NS, NSYM;
        parse_ag(spec, T, &NS, &NSYM);
        int sr = sr_c - 'A', ex = ex_c - 'A';
        /* Simulate L = 6..13 */
        long long steps[8]; int min_lo[8], exs[8];
        int ok = 1;
        for (int L = 6; L <= 13; L++) {
            uint8_t tp[512]; int TOFF = 256;
            memset(tp, 0, sizeof(tp));
            for (int z = 0; z < 200; z++) tp[TOFF + z] = tsym;
            int pp = TOFF + L - 1, ss = sr, mn = TOFF;
            long long stp = 0;
            for (stp = 1; stp <= 5000000; stp++) {
                Tr x = T[ss * NSYM + tp[pp]];
                tp[pp] = x.w; pp += x.d; ss = x.ns;
                if (pp < mn) mn = pp;
                if (pp < 10) { ok = 0; break; }
                if (pp >= TOFF + L) { exs[L-6] = ss; break; }
            }
            if (stp > 5000000) ok = 0;
            steps[L-6] = stp; min_lo[L-6] = mn - TOFF;
            if (!ok) break;
        }
        if (!ok) continue;
        /* Check if steps[i+1] - 2*steps[i] is constant or linear, or base 3 */
        long long d2_1 = steps[1] - 2*steps[0];
        long long d2_2 = steps[2] - 2*steps[1];
        long long d2_3 = steps[3] - 2*steps[2];
        long long d2_4 = steps[4] - 2*steps[3];
        long long d3_1 = steps[1] - 3*steps[0];
        long long d3_2 = steps[2] - 3*steps[1];
        long long d3_3 = steps[3] - 3*steps[2];
        int is2 = ((d2_4 - d2_3) == (d2_3 - d2_2)) && ((d2_3 - d2_2) == (d2_2 - d2_1));
        int is3 = ((d3_3 - d3_2) == (d3_2 - d3_1));
        if (is2) exact_pow2++;
        else if (is3) {
            exact_pow3++;
            if (shown < 12) {
                shown++;
                printf("  [BASE-3] %-22s tsym=%d sr=%c ex=%c min_lo=%d S(6..10)=%lld,%lld,%lld,%lld,%lld\n",
                       spec, tsym, sr_c, ex_c, min_lo[0], steps[0], steps[1], steps[2], steps[3], steps[4]);
            }
        } else {
            other_exp++;
            if (shown < 25) {
                shown++;
                printf("  [OTHER ] %-22s tsym=%d sr=%c ex=%c min_lo=%d S(6..12)=%lld,%lld,%lld,%lld,%lld,%lld,%lld\n",
                       spec, tsym, sr_c, ex_c, min_lo[0], steps[0], steps[1], steps[2], steps[3], steps[4], steps[5], steps[6]);
            }
        }
    }
    fclose(f);
    printf("  Summary: total=%d | pow2=%d pow3=%d other=%d\n\n", total, exact_pow2, exact_pow3, other_exp);
}

int main(void) {
    inspect_file("bbwork/bb-variants/CET/engines_3x2_t1.txt", "CET(3) tsym=1");
    inspect_file("bbwork/bb-variants/CET/engines_2x3_t1.txt", "CET(2,3) tsym=1");
    inspect_file("bbwork/bb-variants/CET/engines_2x3_t2.txt", "CET(2,3) tsym=2");
    return 0;
}
