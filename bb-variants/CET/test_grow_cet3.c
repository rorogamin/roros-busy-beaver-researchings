/* Fast SOLO Ag1 runner to resolve 0LB.../1LB* + 1LB0RC_1RA0LC_1RB1RA up to 2B steps! */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns; } Tr;
static void parse3(const char *s, Tr T[6]) {
    for (int i = 0; i < 6; i++) {
        const char *p = s + i * 3 + (i / 2);
        T[i] = (Tr){p[0]-'0', p[1]=='R'?1:-1, p[2]-'A'};
    }
}

int main(void) {
    /* Load ALL unique CET3 MAXR>=5 pairs from pinned_cet3_big.txt! */
    FILE *fi = fopen("bbwork/bb-variants/CET/pinned_cet3_big.txt", "r");
    char *line = malloc(65536);
    static char pairs[1200][64];
    static int maxrs[1200];
    int n = 0;
    while (fgets(line, 65536, fi) && n < 1200) {
        if (strncmp(line, "STILL_60M:", 10) != 0) continue;
        char *sep = strstr(line, "\t||"); if (!sep) continue;
        char *raw = sep + 3;
        int mr = atoi(raw + 5);
        char *tab = strchr(raw, '\t'); if (!tab) continue;
        char pair[64]; sscanf(tab + 1, "%63[^\t]", pair);
        int dup = 0; for (int i = 0; i < n; i++) if (strcmp(pairs[i], pair) == 0) { dup = 1; break; }
        if (!dup) { strcpy(pairs[n], pair); maxrs[n] = mr; n++; }
    }
    fclose(fi); free(line);
    printf("Running solo Ag1 on %d unique STILL_60M CET3 pairs up to 500M steps...\n", n); fflush(stdout);

    #pragma omp parallel for schedule(dynamic, 1)
    for (int idx = 0; idx < n; idx++) {
        char ce[32], cg[32];
        const char *bar = strchr(pairs[idx], '|');
        int el = (int)(bar - pairs[idx]);
        memcpy(ce, pairs[idx], el); ce[el] = 0; strcpy(cg, bar + 1);
        Tr T1[6], T2[6]; parse3(ce, T1); parse3(cg, T2);

        /* Simulate Ag1+Ag2 up to 100k first (so Ag2 clears >=1000 cells of tape with tsym=1!) */
        uint8_t *tp = calloc(65536, 1);
        const int OFF = 200;
        int p1 = OFF, s1 = 0, p2 = OFF + 2, s2 = 0, max1 = OFF;
        for (int t = 1; t <= 100000; t++) {
            Tr x = T1[s1 * 2 + tp[p1]], y = T2[s2 * 2 + tp[p2]];
            tp[p2] = y.w; tp[p1] = x.w; p1 += x.d; s1 = x.ns; p2 += y.d; s2 = y.ns;
            if (p1 > max1) max1 = p1;
            if (p1 < 10 || p1 >= 60000) break;
        }
        if (max1 > p2 - 100) { free(tp); continue; }
        /* Now Ag2 is 20k+ cells ahead leaving tsym=1 trail, check Ag1 solo up to 2,000,000,000 steps until p1 > max1 + 200! */
        long long t_exit = 0;
        for (long long t = 100001; t <= 2000000000LL; t++) {
            Tr x = T1[s1 * 2 + tp[p1]];
            tp[p1] = x.w; p1 += x.d; s1 = x.ns;
            if (p1 < 10 || p1 >= 60000) break;
            if (p1 > max1 + 200) { t_exit = t; break; }
            /* Fast exit if bounded below 18 for 50M steps */
            if (t == 60000000LL && p1 <= max1 && max1 < OFF + 18) break;
        }
        if (t_exit > 0) {
            #pragma omp critical
            printf("EXITED SOLO!! t_exit=%lld p1_rel=%d(%c) MAXR=%d pair=%s\n", t_exit, p1 - OFF, 'A'+s1, maxrs[idx], pairs[idx]);
        }
        free(tp);
    }
    printf("Done solo BIG check.\n");
    return 0;
}
