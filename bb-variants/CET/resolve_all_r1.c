#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

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

typedef struct {
    char pair[128];
    char line[2048];
    int nS, nSym, tsym, P, D, M, mg, bt;
} Cand;

static Cand cands[2000];
static char results[2000][1024];

void process_one(int idx) {
    Cand *c = &cands[idx];
    Tr tbl1[4][3], tbl2[4][3];
    parse_pair(c->pair, c->nS, tbl1, tbl2, c->nSym);

    // 1. Concrete simulation up to 10,000,000 steps looking for FIRST post-boot close approach (t > 1000, d <= mg + M)
    // Dynamic small tape: max p2 in 10M steps with D/P <= 1/2 is 5,000,000 -> use 6M malloc per thread!
    const int TAPESZ = 6000000;
    const int OFF = 50000;
    unsigned char *tape = calloc(TAPESZ, 1);
    int p1 = OFF, s1 = 0, p2 = OFF + 2, s2 = 0;
    int min1 = OFF, max1 = OFF;
    long long first_close_t = -1;
    int close_d = -1, close_p1 = 0, close_s1 = 0, close_s2 = 0;
    int halt_in_r1 = 0;
    int min1_20k = OFF, max1_postboot = OFF;
    int snap_p1 = 0, snap_s1 = 0, snap_p2 = 0, snap_s2 = 0;

    for (long long t = 1; t <= 10000000LL; t++) {
        Tr t1 = tbl1[s1][tape[p1]], t2 = tbl2[s2][tape[p2]];
        if (t1.w < 0 || t2.w < 0) { halt_in_r1 = -1; break; }
        tape[p2] = t2.w; tape[p1] = t1.w;
        p1 += t1.d; s1 = t1.ns; p2 += t2.d; s2 = t2.ns;
        if (p1 < min1) min1 = p1;
        if (p1 > max1) max1 = p1;
        if (t > 500 && p1 > max1_postboot) max1_postboot = p1;
        if (p1 == p2) { halt_in_r1 = 1; first_close_t = t; break; }
        if (t > 500 && p2 - p1 <= c->mg + c->M && p2 - p1 >= 0) {
            if (first_close_t < 0) {
                first_close_t = t; close_d = p2 - p1; close_p1 = p1; close_s1 = s1; close_s2 = s2;
                // Keep simulating 300 more steps to verify whether it bounces left vs halts!
                int p1b = p1, s1b = s1, p2b = p2, s2b = s2;
                int b_halt = 0, b_min_d = close_d, min_b = p1;
                int b_step = 0;
                for (int dt = 1; dt <= 300; dt++) {
                    Tr u1 = tbl1[s1b][tape[p1b]], u2 = tbl2[s2b][tape[p2b]];
                    if (u1.w < 0 || u2.w < 0) { b_halt = -1; break; }
                    tape[p2b] = u2.w; tape[p1b] = u1.w;
                    p1b += u1.d; s1b = u1.ns; p2b += u2.d; s2b = u2.ns;
                    if (p1b < min_b) min_b = p1b;
                    if (p1b == p2b) { b_halt = 1; b_step = dt; break; }
                    if (p2b - p1b < b_min_d) b_min_d = p2b - p1b;
                }
                if (b_halt == 1) {
                    snprintf(results[idx], 1024, "HALT_R1\tt=%lld\tdt=%d\tg_enter=%d\tx1=%d\tmin1=%d\t%s",
                             first_close_t, b_step, close_d, close_p1 - OFF, min1 - OFF, c->pair);
                } else if (b_halt == 0 && min_b < close_p1 - 15) {
                    // Clean R1 BOUNCE! Compute exact G1 by checking p2's periodic phase!
                    // Find steady phase offset vs mg..mg+M-1: match exact bounce signature!
                    // Simpler: record exact (p2 - p1, s1, s2) trajectory from first_close_t for 40 steps, wait already mutated tape!
                    // We have first_close_t and close_d and exact post-return min1!
                    snprintf(results[idx], 1024, "BOUNCE_R1\tt=%lld\td_enter=%d\tmin_d=%d\tx1=%d\tmin1=%d\tret_p1=%d\t%s",
                             first_close_t, close_d, b_min_d, close_p1 - OFF, min1 - OFF, p1b - OFF, c->pair);
                } else {
                    snprintf(results[idx], 1024, "WEIRD_R1\tt=%lld\tb_halt=%d\tmin_b=%d\t%s",
                             first_close_t, b_halt, min_b - close_p1, c->pair);
                }
                free(tape);
                return;
            }
        }
        if (p1 < 100 || p2 >= TAPESZ - 10) {
            snprintf(results[idx], 1024, "OOB\tt=%lld\tp1=%d\tp2=%d\t%s", t, p1-OFF, p2-OFF, c->pair);
            free(tape); return;
        }
    }
    if (halt_in_r1) {
        snprintf(results[idx], 1024, "EARLY_HALT\tt=%lld\t%s", first_close_t, c->pair);
        free(tape); return;
    }

    // 2. t > 10M without catching Ag2 -> BIG R1! Analyze 20k snapshot for clean zero gap!
    memset(tape, 0, 200000);
    p1 = OFF; s1 = 0; p2 = OFF + 2; s2 = 0;
    max1 = OFF; min1 = OFF; max1_postboot = OFF;
    for (int t = 1; t <= 20000; t++) {
        Tr t1 = tbl1[s1][tape[p1]], t2 = tbl2[s2][tape[p2]];
        tape[p2] = t2.w; tape[p1] = t1.w;
        p1 += t1.d; s1 = t1.ns; p2 += t2.d; s2 = t2.ns;
        if (p1 < min1) min1 = p1;
        if (p1 > max1) max1 = p1;
        if (t > 2000 && p1 > max1_postboot) max1_postboot = p1;
    }
    // Find first nonzero >= max1_postboot + 1 (or check tape[OFF..p2-20])
    int first_nz = max1_postboot + 1;
    while (first_nz < p2 && tape[first_nz] == 0) first_nz++;
    int z_len = first_nz - (max1_postboot + 1);
    int last_nz_before_20k = max1_postboot;
    while (last_nz_before_20k > min1 && tape[last_nz_before_20k] == 0) last_nz_before_20k--;
    int z_clean_total = first_nz - (last_nz_before_20k + 1);
    snprintf(results[idx], 1024, "BIG_R1\tmin1=%d\tmax1_20k=%d\tlast_nz=%d\tfirst_nz=%d\tz_clean=%d\tp2_20k=%d\t%s",
             min1 - OFF, max1_postboot - OFF, last_nz_before_20k - OFF, first_nz - OFF, z_clean_total, p2 - OFF, c->pair);
    free(tape);
}

int main() {
    struct { const char *fn; const char *out; int nS, nSym, tsym; } jobs[3] = {
        {"bbwork/bb-variants/CET/deep_cet3.txt", "bbwork/bb-variants/CET/r1_exact_cet3.txt", 3, 2, 1},
        {"bbwork/bb-variants/CET/deep_cet23_t1.txt", "bbwork/bb-variants/CET/r1_exact_cet23_t1.txt", 2, 3, 1},
        {"bbwork/bb-variants/CET/deep_cet23_t2.txt", "bbwork/bb-variants/CET/r1_exact_cet23_t2.txt", 2, 3, 2},
    };
    for (int j = 0; j < 3; j++) {
        FILE *fp = fopen(jobs[j].fn, "r");
        int nc = 0;
        char line[2048];
        while (fgets(line, sizeof(line), fp) && nc < 2000) {
            line[strcspn(line, "\r\n")] = 0;
            if (!line[0]) continue;
            strcpy(cands[nc].line, line);
            char copy[2048]; strcpy(copy, line);
            char *toks[20]; int nt = 0; char *p = copy;
            while (*p && nt < 20) { toks[nt++] = p; char *tb = strchr(p, '\t'); if (tb) { *tb = 0; p = tb + 1; } else break; }
            strcpy(cands[nc].pair, toks[1]);
            cands[nc].nS = jobs[j].nS; cands[nc].nSym = jobs[j].nSym; cands[nc].tsym = jobs[j].tsym;
            cands[nc].P = atoi(toks[3]+2); cands[nc].D = atoi(toks[4]+2);
            cands[nc].M = atoi(toks[5]+2); cands[nc].mg = atoi(toks[6]+3);
            cands[nc].bt = atoi(toks[7]+3);
            nc++;
        }
        fclose(fp);
        #pragma omp parallel for schedule(dynamic, 4)
        for (int i = 0; i < nc; i++) process_one(i);

        FILE *fo = fopen(jobs[j].out, "w");
        int cnt_h=0, cnt_b=0, cnt_big=0;
        for (int i = 0; i < nc; i++) {
            fprintf(fo, "%s\t||%s\n", results[i], cands[i].line);
            if (strncmp(results[i], "HALT_R1", 7) == 0) cnt_h++;
            else if (strncmp(results[i], "BOUNCE_R1", 9) == 0) cnt_b++;
            else if (strncmp(results[i], "BIG_R1", 6) == 0) cnt_big++;
        }
        fclose(fo);
        printf("%s: nc=%d HALT_R1=%d BOUNCE_R1=%d BIG_R1=%d\n", jobs[j].out, nc, cnt_h, cnt_b, cnt_big);
    }
    return 0;
}
