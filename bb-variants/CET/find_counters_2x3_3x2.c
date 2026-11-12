#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns; } Tr;

/* Check if from some state on an all-u tape it moves uniformly right (or left) across u's (speed 1 or >= 1/2) */
static int has_chase(const Tr *T, int NS, int NSYM, int sym, int dir) {
    for (int st = 0; st < NS; st++) {
        Tr x = T[st * NSYM + sym];
        if (x.d == dir && x.ns == st) return 1; /* pure speed-1 chase on sym! */
    }
    return 0;
}

static void scan(int NS, int NSYM, const char *label, const char *out_path) {
    printf("=== Scanning BOTH L/R %s (NS=%d, NSYM=%d) ===\n", label, NS, NSYM);
    fflush(stdout);
    FILE *fout = fopen(out_path, "w");
    int n_ent = NS * NSYM;
    int choices = NSYM * 2 * NS;
    long long sub_total = 1;
    for (int i = 1; i < n_ent; i++) sub_total *= choices;

    long long found = 0;

    for (int first_w = 0; first_w <= 1; first_w++) {
        for (int first_di = 0; first_di < 2; first_di++) {
            int first_d = first_di ? 1 : -1;
            int first_ns = 1; /* StB */
            #pragma omp parallel for schedule(dynamic, 4096)
            for (long long code = 0; code < sub_total; code++) {
                Tr T[6];
                T[0] = (Tr){first_w, first_d, first_ns};
                long long v = code;
                for (int i = 1; i < n_ent; i++) {
                    int c = v % choices; v /= choices;
                    int w = c % NSYM; c /= NSYM;
                    int d = (c % 2) ? 1 : -1; c /= 2;
                    int ns = c;
                    T[i] = (Tr){w, d, ns};
                }

                uint8_t tape[256];
                int OFF = 128;
                memset(tape, 0, sizeof(tape));
                int p = OFF, s = 0;
                int lo = p, hi = p;
                int last_exp = 0, prev_exp = 0, nexp = 0;
                int oob = 0;
                int last_dir_exp = 0;
                for (int step = 1; step <= 60000; step++) {
                    int r = tape[p];
                    Tr x = T[s * NSYM + r];
                    tape[p] = x.w;
                    p += x.d;
                    s = x.ns;
                    if (p < lo) {
                        lo = p;
                        if (lo < 8) { oob = 1; break; }
                        prev_exp = last_exp; last_exp = step; nexp++; last_dir_exp = -1;
                    } else if (p > hi) {
                        hi = p;
                        if (hi > 248) { oob = 1; break; }
                        prev_exp = last_exp; last_exp = step; nexp++; last_dir_exp = 1;
                    }
                }
                if (!oob) {
                    int span = hi - lo + 1;
                    if (span >= 6 && span <= 48 && last_exp >= 10000 && nexp <= 65) {
                        char buf[64], *bp = buf;
                        for (int q = 0; q < NS; q++) {
                            if (q) *bp++ = '_';
                            for (int sym = 0; sym < NSYM; sym++) {
                                Tr x = T[q * NSYM + sym];
                                bp += sprintf(bp, "%d%c%c", x.w, x.d > 0 ? 'R' : 'L', 'A' + x.ns);
                            }
                        }
                        int ch1R = has_chase(T, NS, NSYM, 1, 1);
                        int ch2R = (NSYM >= 3) ? has_chase(T, NS, NSYM, 2, 1) : 0;
                        int ch1L = has_chase(T, NS, NSYM, 1, -1);
                        int ch2L = (NSYM >= 3) ? has_chase(T, NS, NSYM, 2, -1) : 0;
                        #pragma omp critical
                        {
                            if (fout) fprintf(fout, "%s\t%d\t%d\t%d\t%d\t%d\t%d%d%d%d\n",
                                              buf, span, lo - OFF, hi - OFF, last_exp, nexp,
                                              ch1R, ch2R, ch1L, ch2L);
                            found++;
                        }
                    }
                }
            }
        }
    }
    if (fout) fclose(fout);
    printf("Total exponential/slow-expanding found for %s: %lld\n\n", label, found);
    fflush(stdout);
}

int main(void) {
    scan(2, 3, "BB(2,3) single agents", "bbwork/bb-variants/CET/counters_2x3_all.txt");
    scan(3, 2, "BB(3,2) single agents", "bbwork/bb-variants/CET/counters_3x2_all.txt");
    return 0;
}
