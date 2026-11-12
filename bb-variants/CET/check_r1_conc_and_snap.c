#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int w, d, ns; } Tr;

int parse_pair(const char *s, int nS, Tr tbl1[][3], Tr tbl2[][3], int nSym) {
    char buf[256]; strncpy(buf, s, 255); buf[255] = 0;
    char *bar = strchr(buf, '|');
    if (!bar) return 0;
    *bar = 0;
    const char *sides[2] = {buf, bar + 1};
    for (int ag = 0; ag < 2; ag++) {
        Tr (*tbl)[3] = ag == 0 ? tbl1 : tbl2;
        char copy[128]; strncpy(copy, sides[ag], 127); copy[127] = 0;
        char *p = copy;
        for (int st = 0; st < nS; st++) {
            char *next = strchr(p, '_');
            if (next) *next = 0;
            for (int sym = 0; sym < nSym; sym++) {
                const char *q = p + sym * 3;
                if (q[0] == '-') tbl[st][sym] = (Tr){-1, 0, 0};
                else tbl[st][sym] = (Tr){q[0]-'0', q[1]=='L'?-1:1, q[2]-'A'};
            }
            if (next) p = next + 1;
        }
    }
    return 1;
}

#define TAPESZ 2097152
#define OFF 262144
static unsigned char tape[TAPESZ];

void analyze_file(const char *fname, int nS, int nSym, int tsym, const char *outname) {
    FILE *fp = fopen(fname, "r");
    FILE *fo = fopen(outname, "w");
    if (!fp || !fo) { fprintf(stderr, "Cannot open %s\n", fname); return; }
    char line[2048];
    int conc_hits = 0, big_cnt = 0, u_halt = 0, u_left = 0, u_right = 0, total = 0;
    while (fgets(line, sizeof(line), fp)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0]) continue;
        total++;
        char copy[2048]; strcpy(copy, line);
        char *toks[20]; int nt = 0;
        char *p = copy;
        while (*p && nt < 20) {
            toks[nt++] = p;
            char *tab = strchr(p, '\t');
            if (tab) { *tab = 0; p = tab + 1; } else break;
        }
        // Format: MAXR=... \t c_pair \t full_e \t P=...
        if (nt < 10) continue;
        const char *c_pair = toks[1];
        int P = atoi(toks[3]+2), D = atoi(toks[4]+2), M = atoi(toks[5]+2), mg = atoi(toks[6]+3);
        Tr tbl1[4][3], tbl2[4][3];
        parse_pair(c_pair, nS, tbl1, tbl2, nSym);

        memset(tape, 0, TAPESZ);
        int p1 = OFF, s1 = 0, p2 = OFF + 2, s2 = 0;
        int min1 = p1, max1 = p1, col1 = 0, undef_why = 0;
        long long col_t = 0;
        int max1_20k = p1, min1_20k = p1;
        int p1_20k = 0, s1_20k = 0, p2_20k = 0, s2_20k = 0;
        for (long long t = 1; t <= 2500000; t++) {
            Tr t1 = tbl1[s1][tape[p1]], t2 = tbl2[s2][tape[p2]];
            if (t1.w < 0 || t2.w < 0) { undef_why = 1; break; }
            tape[p2] = t2.w; tape[p1] = t1.w;
            p1 += t1.d; s1 = t1.ns;
            p2 += t2.d; s2 = t2.ns;
            if (p1 < min1) min1 = p1;
            if (p1 > max1) max1 = p1;
            if (t == 20000) {
                max1_20k = max1; min1_20k = min1;
                p1_20k = p1; s1_20k = s1; p2_20k = p2; s2_20k = s2;
            }
            if (p1 == p2) { col1 = 1; col_t = t; break; }
            if (p1 < OFF - 5000) { undef_why = 2; break; }
            if (p1 >= TAPESZ - 10 || p2 >= TAPESZ - 10) { undef_why = 3; break; }
        }
        if (undef_why == 1) { u_halt++; continue; }
        if (undef_why == 2) { u_left++; continue; }
        if (undef_why == 3) { u_right++; continue; }
        if (col1) {
            conc_hits++;
            // Scan left of p1 for zero gap after Ag1 min/remnant or find zeros immediately left?
            // Output exact r2min and x1 and col_t
            // Wait: wait to find rightmost nonzero or r2min? Actually we re-compute r2min!
            // Re-run up to col_t tracking r2min starting from step after Ag1 exits or simply track r1_min!
            memset(tape, 0, TAPESZ);
            p1 = OFF; s1 = 0; p2 = OFF + 2; s2 = 0;
            int r2min = 1000000000;
            for (long long t = 1; t <= col_t; t++) {
                Tr t1 = tbl1[s1][tape[p1]], t2 = tbl2[s2][tape[p2]];
                tape[p2] = t2.w; tape[p1] = t1.w;
                p1 += t1.d; s1 = t1.ns; p2 += t2.d; s2 = t2.ns;
                if (t == col_t) break;
                if (p1 < r2min) r2min = p1; // Wait: we need x1 at col_t, and min1 over ALL steps before col_t? Wait: if R1 stayed near 0 then chased right, min1 IS left wall!
            }
            // Wait: check if all zeros in [OFF+20 .. p1-M] or just match find_multiround_candidates convention!
            int gap = 0;
            // Count non-blank? No, gap = M + ((...) wait: how is G defined? In COL1: x1 - pos_where_trail_changed, or find gap via bounce probe?
            // Better: simulate 50 steps PAST col_t and check whether Ag1 hits H or settles into Ag2 trail bounce!
            int bounce_ok = 0, b_t = 0;
            int x1 = p1 - OFF;
            // Wait: also scan zeros in [OFF .. p1-1] to see zero_run left of p1!
            int zr = 0; while (p1 - 1 - zr >= min1 && tape[p1 - 1 - zr] == 0) zr++;
            fprintf(fo, "CONC\t%s\tt=%lld\tx1=%d\tmin1=%d\tzr=%d\ts1=%c\ts2=%c\t|%s\n",
                    line, col_t, x1, min1-OFF, zr, 'A'+s1, 'A'+s2, "OK");
        } else {
            big_cnt++;
            // Inspect 20k snapshot cleanly! Re-run to 20k to examine tape between max1_20k and p2_20k!
            memset(tape, 0, TAPESZ);
            p1 = OFF; s1 = 0; p2 = OFF + 2; s2 = 0;
            int max1k = OFF, min1k = OFF;
            for (long long t = 1; t <= 20000; t++) {
                Tr t1 = tbl1[s1][tape[p1]], t2 = tbl2[s2][tape[p2]];
                tape[p2] = t2.w; tape[p1] = t1.w;
                p1 += t1.d; s1 = t1.ns; p2 += t2.d; s2 = t2.ns;
                if (p1 > max1k) max1k = p1;
                if (p1 < min1k) min1k = p1;
            }
            // Check how far trail of tsym reaches from p2 leftward
            int trail_left = p2 - 1;
            while (trail_left > OFF && tape[trail_left] == tsym) trail_left--;
            // Wait: trail might have periodic non-tsym? Search leftmost cell > max1k where tape[x] != 0
            int first_nz = max1k + 1;
            while (first_nz < p2 && tape[first_nz] == 0) first_nz++;
            int zero_gap = first_nz - (max1k + 1);
            int all_tsym_after = 1;
            // Count non-tsym in [first_nz .. p2-P]
            int non_ts = 0;
            for (int x = first_nz; x < p2 - P; x++) if (tape[x] != tsym) non_ts++;
            fprintf(fo, "BIG\t%s\tmax1=%d\tmin1=%d\tp2=%d\tfirst_nz=%d\tzgap=%d\tnonts=%d\n",
                    line, max1k-OFF, min1k-OFF, p2-OFF, first_nz-OFF, zero_gap, non_ts);
        }
    }
    fclose(fp); fclose(fo);
    printf("%s: total=%d conc=%d big=%d u_halt=%d u_left=%d u_right=%d -> %s\n",
           fname, total, conc_hits, big_cnt, u_halt, u_left, u_right, outname);
}

int main() {
    analyze_file("bbwork/bb-variants/CET/deep_cet3.txt", 3, 2, 1, "bbwork/bb-variants/CET/r1_cet3.txt");
    analyze_file("bbwork/bb-variants/CET/deep_cet23_t1.txt", 2, 3, 1, "bbwork/bb-variants/CET/r1_cet23_t1.txt");
    analyze_file("bbwork/bb-variants/CET/deep_cet23_t2.txt", 2, 3, 2, "bbwork/bb-variants/CET/r1_cet23_t2.txt");
    return 0;
}
