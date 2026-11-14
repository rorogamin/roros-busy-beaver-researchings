#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct {
    uint8_t w;
    int8_t d;
    int8_t ns; /* -1 for undef --- */
} Trans;

static int parse_agent(const char *s, Trans a[3][2]) {
    const char *p = s;
    for (int st = 0; st < 3; st++) {
        for (int sym = 0; sym < 2; sym++) {
            if (p[0] == '-' && p[1] == '-' && p[2] == '-') {
                a[st][sym].w = 0; a[st][sym].d = 0; a[st][sym].ns = -1;
            } else if ((p[0] == '0' || p[0] == '1') &&
                       (p[1] == 'L' || p[1] == 'R') &&
                       (p[2] >= 'A' && p[2] <= 'C')) {
                a[st][sym].w = (uint8_t)(p[0] - '0');
                a[st][sym].d = (p[1] == 'R') ? 1 : -1;
                a[st][sym].ns = (int8_t)(p[2] - 'A');
            } else {
                return -1;
            }
            p += 3;
        }
        if (st < 2) {
            if (*p != '_') return -1;
            p++;
        }
    }
    return 0;
}

#define TAPE_SIZE (1 << 20)
#define TAPE_OFF  (1 << 19)

int main(int argc, char **argv) {
    const char *path = (argc > 1) ? argv[1] : "bbwork/bb-variants/CET/s18/residue_s18.txt";
    int max_steps = (argc > 2) ? atoi(argv[2]) : 2000000;
    FILE *f = fopen(path, "r");
    if (!f) { perror("fopen"); return 1; }

    uint8_t *tape = (uint8_t *)calloc(TAPE_SIZE, 1);
    char line[256];
    int idx = 0;
    int n_halt = 0, n_undef = 0, n_oob = 0, n_bounded = 0, n_linsep = 0, n_rem = 0;
    int max_halt_steps = 0, max_halt_idx = -1;
    char max_halt_spec[128] = "";

    int lo_clr = TAPE_OFF, hi_clr = TAPE_OFF + 2;

    while (fgets(line, sizeof(line), f)) {
        size_t len = strlen(line);
        while (len > 0 && (line[len-1] == '\n' || line[len-1] == '\r' || line[len-1] == ' '))
            line[--len] = '\0';
        if (len == 0) continue;
        idx++;

        char *sep = strstr(line, "  ");
        if (!sep) sep = strchr(line, '|');
        if (!sep) continue;
        char a1s[64], a2s[64];
        size_t l1 = (size_t)(sep - line);
        memcpy(a1s, line, l1); a1s[l1] = '\0';
        const char *p2str = (*sep == '|') ? sep + 1 : sep + 2;
        strcpy(a2s, p2str);

        Trans a1[3][2], a2[3][2];
        if (parse_agent(a1s, a1) != 0 || parse_agent(a2s, a2) != 0) continue;

        /* Only clear previously touched range [lo_clr .. hi_clr] */
        memset(tape + lo_clr, 0, (size_t)(hi_clr - lo_clr + 1));

        int p1 = 0, p2 = 2, s1 = 0, s2 = 0;
        int min1 = 0, max1 = 0, min2 = 2, max2 = 2;
        int prev_max1 = 0, prev_min2 = 2;
        int lo = TAPE_OFF, hi = TAPE_OFF + 2;
        int status = 0; /* 0=timeout, 1=halt, 2=undef, 3=oob, 4=sep_monotone */
        int halt_t = 0;

        /* Also keep a bounded early-check step (400k), then extend up to max_steps
           if bounded/expanding without clear monotone separation */
        for (int t = 1; t <= max_steps; t++) {
            int i1 = p1 + TAPE_OFF, i2 = p2 + TAPE_OFF;
            if (i1 < 16 || i1 >= TAPE_SIZE - 16 || i2 < 16 || i2 >= TAPE_SIZE - 16) {
                status = 3;
                break;
            }
            if (i1 < lo) lo = i1; if (i1 > hi) hi = i1;
            if (i2 < lo) lo = i2; if (i2 > hi) hi = i2;

            uint8_t r1 = tape[i1];
            uint8_t r2 = tape[i2];
            Trans tr1 = a1[s1][r1];
            Trans tr2 = a2[s2][r2];
            if (tr1.ns < 0 || tr2.ns < 0) {
                status = 2; halt_t = t;
                break;
            }
            tape[i2] = tr2.w;
            tape[i1] = tr1.w;
            p1 += tr1.d;
            p2 += tr2.d;
            s1 = tr1.ns;
            s2 = tr2.ns;
            if (p1 < min1) min1 = p1; if (p1 > max1) max1 = p1;
            if (p2 < min2) min2 = p2; if (p2 > max2) max2 = p2;

            if (p1 == p2) {
                status = 1; halt_t = t;
                break;
            }
            if (t == 20000) { prev_max1 = max1; prev_min2 = min2; }
        }
        lo_clr = lo; hi_clr = hi;

        int min_x = min1 < min2 ? min1 : min2;
        int max_x = max1 > max2 ? max1 : max2;

        if (status == 1) {
            n_halt++;
            if (halt_t > max_halt_steps) {
                max_halt_steps = halt_t;
                max_halt_idx = idx;
                snprintf(max_halt_spec, sizeof(max_halt_spec), "%s|%s", a1s, a2s);
            }
            printf("HALT #%d (%s|%s): steps=%d\n", idx, a1s, a2s, halt_t);
            fflush(stdout);
        } else if (status == 2) {
            n_undef++;
        } else if (status == 3) {
            n_oob++;
        } else {
            if (max_x - min_x <= 300) {
                n_bounded++;
            } else if ((prev_max1 < prev_min2) && (max1 == prev_max1 || min2 == prev_min2) && (p2 - p1 > 1000)) {
                /* Wait: only classify separated if max1 never increased OR min2 never decreased? No: check separately! */
                n_rem++;
            } else {
                n_rem++;
            }
            (void)n_linsep;
        }
    }
    fclose(f);
    free(tape);
    printf("\n=== SUMMARY (%d machines, max_steps=%d) ===\n", idx, max_steps);
    printf("HALT (head collision): %d (max=%d at #%d: %s)\n", n_halt, max_halt_steps, max_halt_idx, max_halt_spec);
    printf("UNDEF (reached ---):   %d\n", n_undef);
    printf("OOB (> +-524288 cells):%d\n", n_oob);
    printf("BOUNDED (span<=300):   %d\n", n_bounded);
    printf("REMAINING (expanding): %d\n", n_rem);
    return 0;
}
