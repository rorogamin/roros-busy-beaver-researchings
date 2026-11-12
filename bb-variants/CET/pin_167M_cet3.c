#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { int w, d, ns; } Tr;
static void parse3(const char *s, Tr T[6]) {
    for (int i = 0; i < 6; i++) {
        const char *p = s + i * 3 + (i / 2);
        T[i] = (Tr){p[0]-'0', p[1]=='R'?1:-1, p[2]-'A'};
    }
}

static void run_pair(const char *s1_spec, const char *s2_spec, long long max_t) {
    Tr T1[6], T2[6]; parse3(s1_spec, T1); parse3(s2_spec, T2);
    /* Get canon Ag2 pat at steady t=2000 (gl_s=0) */
    const int TSZ = 220000000;
    uint8_t *tp = calloc(TSZ, 1);
    const int OFF = 500;
    int p1 = OFF, s1 = 0, p2 = OFF + 2, s2 = 0;
    int min1 = OFF, gl_s = -1, pat_off = 20;
    uint8_t pat[32];

    for (long long t = 1; t <= max_t; t++) {
        Tr x = T1[s1 * 2 + tp[p1]], y = T2[s2 * 2 + tp[p2]];
        tp[p2] = y.w; tp[p1] = x.w;
        p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
        if (p1 < min1) min1 = p1;
        if (p1 == p2) {
            printf("%s|%s -> COLLIDE t=%lld x=%d\n", s1_spec, s2_spec, t, p1 - OFF);
            free(tp); return;
        }
        if (t == 2000) {
            gl_s = s2;
            memcpy(pat, tp + p2 - 12, 24);
        }
        if (t > 100000 && s1 == 1 && s2 == gl_s && p2 - p1 >= 8 && p2 - p1 <= 19) {
            /* check pat match around p2 - 12 .. p2 + 12 */
            int ok = 1;
            for (int k = 0; k < 24; k++) if (tp[p2 - 12 + k] != pat[k]) { ok = 0; break; }
            if (ok) {
                int gap = p2 - p1;
                int x1 = p1 - OFF;
                printf("%s|%s -> COL1 t=%lld gap=%d x1=%d min1=%d (L2_est=%d)\n",
                       s1_spec, s2_spec, t, gap, x1, min1 - OFF, x1 - (min1 - OFF) - 1);
                /* Continue 500 steps to inspect R2 min1 & cz */
                int r2min = p1;
                for (int k = 1; k <= 500; k++) {
                    Tr xx = T1[s1 * 2 + tp[p1]], yy = T2[s2 * 2 + tp[p2]];
                    tp[p2] = yy.w; tp[p1] = xx.w;
                    p1 += xx.d; s1 = xx.ns; p2 += yy.d; s2 = yy.ns;
                    if (p1 == p2) { printf("  -> R2 EARLY HALT at +%d\n", k); free(tp); return; }
                    if (p1 < r2min) r2min = p1;
                }
                printf("  -> after +500: p1=%d(%c) r2min=%d\n", p1 - OFF, 'A'+s1, r2min - OFF);
                free(tp); return;
            }
        }
    }
    printf("%s|%s -> TIMEOUT %lld\n", s1_spec, s2_spec, max_t);
    free(tp);
}

int main(void) {
    run_pair("0LB0LA_1LC1RB_0RB0LC", "1LB0RC_1RA0LC_1RB1RA", 250000000LL);
    run_pair("1LB0LA_1LC1RB_0RB0LC", "1LB0RC_1RA0LC_1RB1RA", 750000000LL);
    return 0;
}
