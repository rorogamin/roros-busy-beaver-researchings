#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

// ============================================================================
// COLAB 8-THREAD HIGH-RAM MEGA MULTI-DOMAIN ENGINE
//   - Threads 0-2 (3 threads): CET(3)       [Record: 3,746,207]
//   - Threads 3-5 (3 threads): CET(2,3)     [Record: 20,350]
//   - Threads 6-7 (2 threads): CET(4)       [Record: 65,579,412]
// ============================================================================

static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

typedef struct { int8_t w, mv, ns; } Tr;

// ----------------------------------------------------------------------------
// DOMAIN 1: CET(3) [Tree Normal Form Sampling]
// ----------------------------------------------------------------------------
#define CET3_S1_SIZE 65536
#define CET3_S1_OFF  32768
#define CET3_S2_SIZE 1048576
#define CET3_S2_OFF  524288
#define CET3_S3_SIZE 16777216
#define CET3_S3_OFF  8388608

typedef struct { Tr t[2][3][2]; } Cet3Machine;

static void fmt_cet3(const Cet3Machine *m, char *b) {
    char *p = b;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                Tr x = m->t[a][s][r];
                *p++ = '0' + x.w; *p++ = x.mv > 0 ? 'R' : 'L'; *p++ = 'A' + x.ns;
            }
        }
    }
    *p = 0;
}

static inline void gen_cet3_tnf(Cet3Machine *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
        int max_s = 0;
        for (int s = 0; s < 3; s++) {
            for (int r = 0; r < 2; r++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][r].w = v & 1;
                m->t[a][s][r].mv = (v & 2) ? 1 : -1;
                int lim = max_s + 1;
                if (lim > 2) lim = 2;
                int ns = (v >> 2) % (lim + 1);
                m->t[a][s][r].ns = ns;
                if (ns > max_s) max_s = ns;
            }
        }
    }
}

static inline int eval_cet3_s1(const Cet3Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = CET3_S1_OFF, p2 = CET3_S1_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    for (int step = 1; step <= 15000; step++) {
        if (p1 <= 20 || p1 >= CET3_S1_SIZE - 20 || p2 <= 20 || p2 >= CET3_S1_SIZE - 20) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - CET3_S1_OFF; return step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 100) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }
        if (step > 4000 && (step - last_exp > 4000)) return -3;
    }
    return -2;
}

static inline int eval_cet3_s2(const Cet3Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = CET3_S2_OFF, p2 = CET3_S2_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    for (int step = 1; step <= 300000; step++) {
        if (p1 <= 30 || p1 >= CET3_S2_SIZE - 30 || p2 <= 30 || p2 >= CET3_S2_SIZE - 30) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - CET3_S2_OFF; return step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 450) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }
        if (step > 40000 && (step - last_exp > 40000)) return -3;
    }
    return -2;
}

static int eval_cet3_deep(const Cet3Machine *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = CET3_S3_OFF, p2 = CET3_S3_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    for (uint64_t step = 1; step <= 250000000ULL; step++) {
        if (p1 <= 100 || p1 >= CET3_S3_SIZE - 100 || p2 <= 100 || p2 >= CET3_S3_SIZE - 100) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - CET3_S3_OFF; return (int)step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 6000) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = (int)step; }
        if (h > hi) { hi = h; last_exp = (int)step; }
        if (step > 1000000 && ((int)step - last_exp > 1000000)) return -3;
    }
    return -2;
}

// ----------------------------------------------------------------------------
// DOMAIN 2: CET(2,3) [2 States, 3 Symbols]
// ----------------------------------------------------------------------------
#define CET23_S1_SIZE 65536
#define CET23_S1_OFF  32768
#define CET23_S2_SIZE 2097152
#define CET23_S2_OFF  1048576

typedef struct { Tr t[2][2][3]; } Cet23Machine;

static void fmt_cet23(const Cet23Machine *m, char *b) {
    char *p = b;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 2; s++) {
            if (s) *p++ = '_';
            for (int r = 0; r < 3; r++) {
                Tr x = m->t[a][s][r];
                *p++ = '0' + x.w; *p++ = x.mv > 0 ? 'R' : 'L'; *p++ = 'A' + x.ns;
            }
        }
    }
    *p = 0;
}

static inline void gen_cet23_tnf(Cet23Machine *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
        for (int s = 0; s < 2; s++) {
            for (int r = 0; r < 3; r++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][r].w = v % 3;
                m->t[a][s][r].mv = (v & 4) ? 1 : -1;
                m->t[a][s][r].ns = (s == 0 && r == 0) ? ((v & 8) ? 1 : 0) : ((v >> 4) & 1);
            }
        }
    }
}

static inline int eval_cet23_s1(const Cet23Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = CET23_S1_OFF, p2 = CET23_S1_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    for (int step = 1; step <= 25000; step++) {
        if (p1 <= 20 || p1 >= CET23_S1_SIZE - 20 || p2 <= 20 || p2 >= CET23_S1_SIZE - 20) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - CET23_S1_OFF; return step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 120) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }
        if (step > 4000 && (step - last_exp > 4000)) return -3;
    }
    return -2;
}

static inline int eval_cet23_deep(const Cet23Machine *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = CET23_S2_OFF, p2 = CET23_S2_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    for (uint64_t step = 1; step <= 20000000; step++) {
        if (p1 <= 50 || p1 >= CET23_S2_SIZE - 50 || p2 <= 50 || p2 >= CET23_S2_SIZE - 50) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - CET23_S2_OFF; return step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 3500) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }
        if (step > 80000 && (step - last_exp > 80000)) return -3;
    }
    return -2;
}

// ----------------------------------------------------------------------------
// DOMAIN 3: CET(4) [4 States, 2 Symbols — High-Ram 67M Tape Simulation]
// ----------------------------------------------------------------------------
#define CET4_S1_SIZE 65536
#define CET4_S1_OFF  32768
#define CET4_DEEP_SIZE 80000000
#define CET4_DEEP_OFF  40000000

typedef struct { Tr t[2][4][2]; } Cet4Machine;

static void fmt_cet4(const Cet4Machine *m, char *b) {
    char *p = b;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 4; s++) {
            if (s) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                Tr x = m->t[a][s][r];
                *p++ = '0' + x.w; *p++ = x.mv > 0 ? 'R' : 'L'; *p++ = 'A' + x.ns;
            }
        }
    }
    *p = 0;
}

static inline void gen_cet4_tnf(Cet4Machine *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
        int max_s = 0;
        for (int s = 0; s < 4; s++) {
            for (int r = 0; r < 2; r++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][r].w = v & 1;
                m->t[a][s][r].mv = (v & 2) ? 1 : -1;
                int lim = max_s + 1;
                if (lim > 3) lim = 3;
                int ns = (v >> 2) % (lim + 1);
                m->t[a][s][r].ns = ns;
                if (ns > max_s) max_s = ns;
            }
        }
    }
}

static inline int eval_cet4_s1(const Cet4Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = CET4_S1_OFF, p2 = CET4_S1_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    for (int step = 1; step <= 25000; step++) {
        if (p1 <= 20 || p1 >= CET4_S1_SIZE - 20 || p2 <= 20 || p2 >= CET4_S1_SIZE - 20) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - CET4_S1_OFF; return step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 140) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }
        if (step > 6000 && (step - last_exp > 6000)) return -3;
    }
    return -2;
}

static int eval_cet4_deep(const Cet4Machine *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = CET4_DEEP_OFF, p2 = CET4_DEEP_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    for (uint64_t step = 1; step <= 100000000ULL; step++) {
        if (p1 <= 200 || p1 >= CET4_DEEP_SIZE - 200 || p2 <= 200 || p2 >= CET4_DEEP_SIZE - 200) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - CET4_DEEP_OFF; return (int)step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 10000) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = (int)step; }
        if (h > hi) { hi = h; last_exp = (int)step; }
        if (step > 1500000 && ((int)step - last_exp > 1500000)) return -3;
    }
    return -2;
}

// ============================================================================
// MAIN CONTROLLER (8 THREADS FOR COLAB HIGH-RAM)
// ============================================================================
int main(int argc, char **argv) {
    int duration = 3600; // default 1 hour
    if (argc > 1) duration = atoi(argv[1]);

    printf("=========================================================================================================\n");
    printf("🪐⚡🌌 GOOGLE COLAB 8-THREAD HIGH-RAM MEGA EXPEDITION: CET(3), CET(2,3), CET(4) (%d s) 🌌⚡🪐\n", duration);
    printf("=========================================================================================================\n");
    printf("Hardware: Google Colab High-RAM Instance (8 vCPUs, 52GB RAM)\n");
    printf("Partitioning:\n");
    printf("  - Threads 0-2 (3 threads): CET(3)   [Target: >3,746,207 Steps]\n");
    printf("  - Threads 3-5 (3 threads): CET(2,3) [Target: >20,350 Steps]\n");
    printf("  - Threads 6-7 (2 threads): CET(4)   [Target: >65,579,412 Steps (80M Tape)]\n");
    fflush(stdout);

    int best_cet3 = 3746207, best_cet3_pos = -9;
    char bb_cet3[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    int best_cet23 = 20350, best_cet23_pos = -78;
    char bb_cet23[128] = "2LB1LA2LA_2RB2LA0LB|1RB0LB1RB_2LA2LA1RA";

    int best_cet4 = 65579412, best_cet4_pos = -32789706;
    char bb_cet4[128] = "0LC0RA_0LD0RA_0LB0RA_0RA0RA|1RB1LD_1RC1RB_1LC1LA_0RC0RD";

    long long cnt_cet3 = 0, cnt_cet23 = 0, cnt_cet4 = 0;
    double t0 = omp_get_wtime();

    #pragma omp parallel num_threads(8)
    {
        int tid = omp_get_thread_num();
        uint64_t seed = (uint64_t)time(NULL) * 6364136223846793005ULL + ((uint64_t)tid * 104729ULL + 1ULL);
        for (int i = 0; i < 20; i++) splitmix64(&seed);

        long long local_cnt = 0;

        if (tid < 3) {
            // CET(3)
            uint8_t *tape1 = calloc(CET3_S1_SIZE, 1);
            uint16_t *vis1 = calloc(CET3_S1_SIZE, 2);
            uint8_t *tape2 = calloc(CET3_S2_SIZE, 1);
            uint16_t *vis2 = calloc(CET3_S2_SIZE, 2);
            uint8_t *tape3 = calloc(CET3_S3_SIZE, 1);
            uint32_t *vis3 = calloc(CET3_S3_SIZE, 4);
            uint16_t mk1 = 1, mk2 = 1;
            uint32_t mk3 = 1;

            Cet3Machine c;
            while (omp_get_wtime() - t0 < duration) {
                gen_cet3_tnf(&c, &seed);
                if (c.t[0][0][0].mv == -1 && c.t[1][0][0].mv == 1 && c.t[0][0][0].w == 0 && c.t[1][0][0].w == 0) continue;
                local_cnt++;

                if (++mk1 == 0) { memset(vis1, 0, CET3_S1_SIZE * 2); mk1 = 1; }
                int pos = 0;
                int s = eval_cet3_s1(&c, tape1, vis1, mk1, &pos);
                if (s == -2 || s > 12000) {
                    if (++mk2 == 0) { memset(vis2, 0, CET3_S2_SIZE * 2); mk2 = 1; }
                    s = eval_cet3_s2(&c, tape2, vis2, mk2, &pos);
                    if (s == -2 || s > 250000) {
                        if (++mk3 == 0) { memset(vis3, 0, CET3_S3_SIZE * 4); mk3 = 1; }
                        s = eval_cet3_deep(&c, tape3, vis3, mk3, &pos);
                        if (s > best_cet3) {
                            #pragma omp critical
                            {
                                if (s > best_cet3) {
                                    best_cet3 = s; best_cet3_pos = pos;
                                    fmt_cet3(&c, bb_cet3);
                                    printf("\n🔥🏆 [NEW CET(3) WORLD RECORD: %d STEPS at cell %d!] 🏆🔥\n", s, pos);
                                    printf("bbchallenge: %s\n\n", bb_cet3);
                                    fflush(stdout);
                                }
                            }
                        } else if (s > 1000000) {
                            #pragma omp critical
                            {
                                char b[128]; fmt_cet3(&c, b);
                                printf("  [CET(3) >1M Holdout]: %d steps at cell %d | %s\n", s, pos, b);
                                fflush(stdout);
                            }
                        }
                    }
                }
            }
            #pragma omp atomic
            cnt_cet3 += local_cnt;
            free(tape1); free(vis1); free(tape2); free(vis2); free(tape3); free(vis3);
        } else if (tid < 6) {
            // CET(2,3)
            uint8_t *tape1 = calloc(CET23_S1_SIZE, 1);
            uint16_t *vis1 = calloc(CET23_S1_SIZE, 2);
            uint8_t *tape2 = calloc(CET23_S2_SIZE, 1);
            uint32_t *vis2 = calloc(CET23_S2_SIZE, 4);
            uint16_t mk1 = 1;
            uint32_t mk2 = 1;

            Cet23Machine c;
            while (omp_get_wtime() - t0 < duration) {
                gen_cet23_tnf(&c, &seed);
                local_cnt++;

                if (++mk1 == 0) { memset(vis1, 0, CET23_S1_SIZE * 2); mk1 = 1; }
                int pos = 0;
                int s = eval_cet23_s1(&c, tape1, vis1, mk1, &pos);
                if (s == -2 || s > 15000) {
                    if (++mk2 == 0) { memset(vis2, 0, CET23_S2_SIZE * 4); mk2 = 1; }
                    s = eval_cet23_deep(&c, tape2, vis2, mk2, &pos);
                    if (s > best_cet23) {
                        #pragma omp critical
                        {
                            if (s > best_cet23) {
                                best_cet23 = s; best_cet23_pos = pos;
                                fmt_cet23(&c, bb_cet23);
                                printf("\n🔥🏆 [NEW CET(2,3) WORLD RECORD: %d STEPS at cell %d!] 🏆🔥\n", s, pos);
                                printf("bbchallenge: %s\n\n", bb_cet23);
                                fflush(stdout);
                            }
                        }
                    } else if (s > 10000) {
                        #pragma omp critical
                        {
                            char b[128]; fmt_cet23(&c, b);
                            printf("  [CET(2,3) High Collider]: %d steps at cell %d | %s\n", s, pos, b);
                            fflush(stdout);
                        }
                    }
                }
            }
            #pragma omp atomic
            cnt_cet23 += local_cnt;
            free(tape1); free(vis1); free(tape2); free(vis2);
        } else {
            // CET(4) — High-RAM (80MB Tape allocated per thread)
            uint8_t *tape1 = calloc(CET4_S1_SIZE, 1);
            uint16_t *vis1 = calloc(CET4_S1_SIZE, 2);
            uint8_t *tape2 = calloc(CET4_DEEP_SIZE, 1);
            uint32_t *vis2 = calloc(CET4_DEEP_SIZE, 4);
            uint16_t mk1 = 1;
            uint32_t mk2 = 1;

            Cet4Machine c;
            while (omp_get_wtime() - t0 < duration) {
                gen_cet4_tnf(&c, &seed);
                if (c.t[0][0][0].mv == -1 && c.t[1][0][0].mv == 1 && c.t[0][0][0].w == 0 && c.t[1][0][0].w == 0) continue;
                local_cnt++;

                if (++mk1 == 0) { memset(vis1, 0, CET4_S1_SIZE * 2); mk1 = 1; }
                int pos = 0;
                int s = eval_cet4_s1(&c, tape1, vis1, mk1, &pos);
                if (s == -2 || s > 20000) {
                    if (++mk2 == 0) { memset(vis2, 0, CET4_DEEP_SIZE * 4); mk2 = 1; }
                    s = eval_cet4_deep(&c, tape2, vis2, mk2, &pos);
                    if (s > best_cet4) {
                        #pragma omp critical
                        {
                            if (s > best_cet4) {
                                best_cet4 = s; best_cet4_pos = pos;
                                fmt_cet4(&c, bb_cet4);
                                printf("\n🔥👑 [NEW CET(4) MEGA WORLD RECORD: %d STEPS at cell %d!] 👑🔥\n", s, pos);
                                printf("bbchallenge: %s\n\n", bb_cet4);
                                fflush(stdout);
                            }
                        }
                    } else if (s > 1000000) {
                        #pragma omp critical
                        {
                            char b[128]; fmt_cet4(&c, b);
                            printf("  [CET(4) Mega Collider >1M]: %d steps at cell %d | %s\n", s, pos, b);
                            fflush(stdout);
                        }
                    }
                }
            }
            #pragma omp atomic
            cnt_cet4 += local_cnt;
            free(tape1); free(vis1); free(tape2); free(vis2);
        }

        // Heartbeat on Thread 0
        if (tid == 0) {
            while (omp_get_wtime() - t0 < duration) {
                struct timespec ts = { .tv_sec = 60, .tv_nsec = 0 };
                nanosleep(&ts, NULL);
                double el = omp_get_wtime() - t0;
                #pragma omp critical
                {
                    printf("[T+%.0fs / %ds] Screened: CET(3)=%lldk, CET(2,3)=%lldk, CET(4)=%lldk | Bests: CET(3)=%d, CET(2,3)=%d, CET(4)=%d\n",
                           el, duration, cnt_cet3 / 1000, cnt_cet23 / 1000, cnt_cet4 / 1000,
                           best_cet3, best_cet23, best_cet4);
                    fflush(stdout);
                }
            }
        }
    }

    double total_elapsed = omp_get_wtime() - t0;
    printf("\n=========================================================================================================\n");
    printf("🏁 COLAB HIGH-RAM EXPEDITION COMPLETE in %.1fs\n", total_elapsed);
    printf("Total Screened: %lld machines\n", cnt_cet3 + cnt_cet23 + cnt_cet4);
    printf("  - CET(3) Screened: %lld (Best: %d steps at cell %d)\n", cnt_cet3, best_cet3, best_cet3_pos);
    printf("  - CET(2,3) Screened: %lld (Best: %d steps at cell %d)\n", cnt_cet23, best_cet23, best_cet23_pos);
    printf("  - CET(4) Screened: %lld (Best: %d steps at cell %d)\n", cnt_cet4, best_cet4, best_cet4_pos);
    printf("=========================================================================================================\n");

    return 0;
}
