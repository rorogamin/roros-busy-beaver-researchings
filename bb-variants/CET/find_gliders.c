#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns; } Tr;

/* Check if Ag2 becomes a translated cycler moving rightward with speed 0 < D/P < 1
   when started at x=0 on (wall^300) | (seed_bits) | (0^inf). */
static int check_glider_mode(const Tr *T, int NS, int NSYM, int wall, const uint8_t *seed, int seed_len,
                             int *out_P, int *out_D, int *out_tail_uniform, int *out_tail_sym) {
    uint8_t tape[2048];
    int OFF = 512;
    for (int i = 0; i < OFF; i++) tape[i] = wall;
    for (int i = 0; i < seed_len; i++) tape[OFF + i] = seed[i];
    for (int i = OFF + seed_len; i < 2048; i++) tape[i] = 0;

    int p = OFF, s = 0;
    int ph[1200], ps[1200];
    for (int t = 0; t < 1200; t++) {
        ph[t] = p;
        ps[t] = s;
        int r = tape[p];
        Tr x = T[s * NSYM + r];
        tape[p] = x.w;
        p += x.d;
        s = x.ns;
        if (p < 16 || p >= 1980) return 0;
        /* Early reject pure stationary or backward runaway after settling */
        if (t == 600 && p < OFF - 40) return 0;
    }
    for (int P = 2; P <= 60; P++) {
        int D = ph[1199] - ph[1199 - P];
        if (D <= 0 || D >= P) continue;
        int ok = 1;
        for (int t = 1200 - 2 * P; t < 1200; t++) {
            if (ph[t] - ph[t - P] != D || ps[t] != ps[t - P]) { ok = 0; break; }
        }
        if (!ok) continue;
        if (ph[1199] < OFF + 12) continue;
        /* Verify tail behind the head zone */
        int min_head = ph[1199];
        for (int t = 1200 - P; t < 1200; t++) if (ph[t] < min_head) min_head = ph[t];
        int lo_chk = OFF + 6, hi_chk = min_head - 2;
        if (hi_chk <= lo_chk + 3) continue;
        int sym0 = tape[lo_chk], unif = 1;
        for (int z = lo_chk; z <= hi_chk; z++) {
            if (tape[z] != sym0) { unif = 0; break; }
        }
        *out_P = P; *out_D = D; *out_tail_uniform = unif; *out_tail_sym = sym0;
        return 1;
    }
    return 0;
}

static void scan_gliders(int NS, int NSYM, const char *label, const char *out_path) {
    printf("=== Scanning Gliders (1200 steps) for %s (NS=%d, NSYM=%d) ===\n", label, NS, NSYM);
    fflush(stdout);
    FILE *fout = fopen(out_path, "w");
    int n_ent = NS * NSYM;
    int choices = NSYM * 2 * NS;
    long long total = 1;
    for (int i = 0; i < n_ent; i++) total *= choices;

    long long count = 0, unif_count = 0;
    uint8_t s0[1] = {0};
    uint8_t s1[3] = {0, 1, 1};
    uint8_t s2[3] = {0, 2, 2};
    uint8_t s3[2] = {0, 1};

    #pragma omp parallel for schedule(dynamic, 4096)
    for (long long code = 0; code < total; code++) {
        Tr T[6];
        long long v = code;
        for (int i = 0; i < n_ent; i++) {
            int c = v % choices; v /= choices;
            int w = c % NSYM; c /= NSYM;
            int d = (c % 2) ? 1 : -1; c /= 2;
            int ns = c;
            T[i] = (Tr){w, d, ns};
        }
        int P = 0, D = 0, unif = 0, tsym = 0;
        int found = check_glider_mode(T, NS, NSYM, 0, s0, 1, &P, &D, &unif, &tsym);
        if (!found) found = check_glider_mode(T, NS, NSYM, 1, s0, 1, &P, &D, &unif, &tsym);
        if (!found) found = check_glider_mode(T, NS, NSYM, 1, s1, 3, &P, &D, &unif, &tsym);
        if (!found && NSYM == 3) found = check_glider_mode(T, NS, NSYM, 2, s2, 3, &P, &D, &unif, &tsym);
        if (!found) found = check_glider_mode(T, NS, NSYM, 1, s3, 2, &P, &D, &unif, &tsym);

        if (found) {
            char buf[64], *bp = buf;
            for (int q = 0; q < NS; q++) {
                if (q) *bp++ = '_';
                for (int sym = 0; sym < NSYM; sym++) {
                    Tr x = T[q * NSYM + sym];
                    bp += sprintf(bp, "%d%c%c", x.w, x.d > 0 ? 'R' : 'L', 'A' + x.ns);
                }
            }
            #pragma omp critical
            {
                count++;
                if (unif) unif_count++;
                if (fout) fprintf(fout, "%s\tP=%d\tD=%d\tunif=%d\ttsym=%d\n", buf, P, D, unif, tsym);
            }
        }
    }
    if (fout) fclose(fout);
    printf("Done %s: total slow right-gliders=%lld (uniform trail=%lld)\n\n", label, count, unif_count);
    fflush(stdout);
}

int main(void) {
    scan_gliders(2, 3, "BB(2,3)", "bbwork/bb-variants/CET/gliders_2x3.txt");
    scan_gliders(3, 2, "BB(3,2)", "bbwork/bb-variants/CET/gliders_3x2.txt");
    return 0;
}
