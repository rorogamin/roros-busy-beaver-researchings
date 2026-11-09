#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

// 6 Threads for CET(3)
// 6 Threads for MCET(3) All-Agent
// 4 Threads for CET(2,3)

// ============================================================================
// Shared SplitMix64 RNG
// ============================================================================
static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

typedef struct { int8_t w, mv, ns; } Tr;

// ============================================================================
// DOMAIN 1: CET(3) [2 Agents, 3 States, 2 Symbols]
// ============================================================================
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
    for (uint64_t step = 1; step <= 200000000ULL; step++) {
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

// ============================================================================
// DOMAIN 2: MCET(3) All-Agent Simultaneous Collision [3 Agents, 3 States, 2 Symbols]
// ============================================================================
#define MCET3_S1_SIZE 131072
#define MCET3_S1_OFF  65536
#define MCET3_S2_SIZE 1048576
#define MCET3_S2_OFF  524288

typedef struct { Tr t[3][3][2]; } Mcet3Machine;

static void fmt_mcet3(const Mcet3Machine *m, char *b) {
    char *p = b;
    for (int a = 0; a < 3; a++) {
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

static inline int eval_mcet3_s1(const Mcet3Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = MCET3_S1_OFF + 0, p2 = MCET3_S1_OFF + 2, p3 = MCET3_S1_OFF + 4;
    int s1 = 0, s2 = 0, s3 = 0;
    for (int step = 1; step <= 25000; step++) {
        if (p1 <= 20 || p1 >= MCET3_S1_SIZE - 20 || p2 <= 20 || p2 >= MCET3_S1_SIZE - 20 || p3 <= 20 || p3 >= MCET3_S1_SIZE - 20) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        uint8_t r3 = (vis[p3] == mk) ? tape[p3] : 0;
        Tr tr1 = m->t[0][s1][r1], tr2 = m->t[1][s2][r2], tr3 = m->t[2][s3][r3];
        vis[p3] = mk; tape[p3] = tr3.w;
        vis[p2] = mk; tape[p2] = tr2.w;
        vis[p1] = mk; tape[p1] = tr1.w;
        p1 += tr1.mv; p2 += tr2.mv; p3 += tr3.mv;
        s1 = tr1.ns; s2 = tr2.ns; s3 = tr3.ns;
        // ALL 3 COLLIDE SIMULTANEOUSLY
        if (p1 == p2 && p2 == p3) { *pos = p1 - MCET3_S1_OFF; return step; }
        int min_p = p1 < p2 ? (p1 < p3 ? p1 : p3) : (p2 < p3 ? p2 : p3);
        int max_p = p1 > p2 ? (p1 > p3 ? p1 : p3) : (p2 > p3 ? p2 : p3);
        if (max_p - min_p > 350) return -1;
    }
    return -2;
}

static inline int eval_mcet3_deep(const Mcet3Machine *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = MCET3_S2_OFF + 0, p2 = MCET3_S2_OFF + 2, p3 = MCET3_S2_OFF + 4;
    int s1 = 0, s2 = 0, s3 = 0;
    for (int step = 1; step <= 2000000; step++) {
        if (p1 <= 50 || p1 >= MCET3_S2_SIZE - 50 || p2 <= 50 || p2 >= MCET3_S2_SIZE - 50 || p3 <= 50 || p3 >= MCET3_S2_SIZE - 50) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        uint8_t r3 = (vis[p3] == mk) ? tape[p3] : 0;
        Tr tr1 = m->t[0][s1][r1], tr2 = m->t[1][s2][r2], tr3 = m->t[2][s3][r3];
        vis[p3] = mk; tape[p3] = tr3.w;
        vis[p2] = mk; tape[p2] = tr2.w;
        vis[p1] = mk; tape[p1] = tr1.w;
        p1 += tr1.mv; p2 += tr2.mv; p3 += tr3.mv;
        s1 = tr1.ns; s2 = tr2.ns; s3 = tr3.ns;
        if (p1 == p2 && p2 == p3) { *pos = p1 - MCET3_S2_OFF; return step; }
        int min_p = p1 < p2 ? (p1 < p3 ? p1 : p3) : (p2 < p3 ? p2 : p3);
        int max_p = p1 > p2 ? (p1 > p3 ? p1 : p3) : (p2 > p3 ? p2 : p3);
        if (max_p - min_p > 3000) return -1;
    }
    return -2;
}

// ============================================================================
// DOMAIN 3: CET(2, 3-symbol) [2 Agents, 2 States, 3 Symbols]
// ============================================================================
#define CET23_S1_SIZE 65536
#define CET23_S1_OFF  32768
#define CET23_S2_SIZE 1048576
#define CET23_S2_OFF  524288

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
    for (int step = 1; step <= 5000000; step++) {
        if (p1 <= 50 || p1 >= CET23_S2_SIZE - 50 || p2 <= 50 || p2 >= CET23_S2_SIZE - 50) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - CET23_S2_OFF; return step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 2500) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }
        if (step > 60000 && (step - last_exp > 60000)) return -3;
    }
    return -2;
}

// ============================================================================
// MAIN MULTI-DOMAIN EXPEDITION CONTROLLER
// ============================================================================
int main(int argc, char **argv) {
    int duration = 1800; // 30 minutes default
    if (argc > 1) duration = atoi(argv[1]);

    printf("=========================================================================================================\n");
    printf("🔱⚡🌌 ULTIMATE 30-MINUTE MULTI-DOMAIN RECORD EXPEDITION (%d s) 🌌⚡🔱\n", duration);
    printf("=========================================================================================================\n");
    printf("Hardware: 16 AMD Ryzen Threads | Partitioning:\n");
    printf("  - Threads 0-5  (6 threads) -> CET(3)       [Current Champion: 3,746,207 Steps]\n");
    printf("  - Threads 6-11 (6 threads) -> MCET(3) All  [Current Champion: 14,417 Steps]\n");
    printf("  - Threads 12-15(4 threads) -> CET(2,3)     [Current Champion: 20,350 Steps]\n");
    printf("Targeting: Record Shattering Across All Frontiers simultaneously!\n");
    fflush(stdout);

    // Global best tracking
    int best_cet3 = 3746207, best_cet3_pos = -9;
    char bb_cet3[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    int best_mcet3 = 14417, best_mcet3_pos = -7205;
    char bb_mcet3[128] = "1RC0RB_1RB1LA_1LA0LC|0RA0RC_0LC1LA_1LB0RB|1LA1RC_0LB1LA_0LB1RA";

    int best_cet23 = 20350, best_cet23_pos = -78;
    char bb_cet23[128] = "2LB1LA2LA_2RB2LA0LB|1RB0LB1RB_2LA2LA1RA";

    long long count_cet3 = 0, count_mcet3 = 0, count_cet23 = 0;
    double t0 = omp_get_wtime();

    #pragma omp parallel num_threads(16)
    {
        int tid = omp_get_thread_num();
        uint64_t seed = (uint64_t)time(NULL) * 6364136223846793005ULL + ((uint64_t)tid * 104729ULL + 1ULL);
        for (int i = 0; i < 20; i++) splitmix64(&seed);

        double last_hb = omp_get_wtime();
        long long local_cnt = 0;

        if (tid < 6) {
            // ================= CET(3) Worker =================
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
                for (int a = 0; a < 2; a++) {
                    for (int s = 0; s < 3; s++) {
                        for (int r = 0; r < 2; r++) {
                            uint64_t v = splitmix64(&seed);
                            c.t[a][s][r].w = v & 1;
                            c.t[a][s][r].mv = (v & 2) ? 1 : -1;
                            c.t[a][s][r].ns = (v >> 2) % 3;
                        }
                    }
                }
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
            count_cet3 += local_cnt;
            free(tape1); free(vis1); free(tape2); free(vis2); free(tape3); free(vis3);
        } else if (tid < 12) {
            // ================= MCET(3) Worker =================
            uint8_t *tape1 = calloc(MCET3_S1_SIZE, 1);
            uint16_t *vis1 = calloc(MCET3_S1_SIZE, 2);
            uint8_t *tape2 = calloc(MCET3_S2_SIZE, 1);
            uint32_t *vis2 = calloc(MCET3_S2_SIZE, 4);
            uint16_t mk1 = 1;
            uint32_t mk2 = 1;

            Mcet3Machine c;
            while (omp_get_wtime() - t0 < duration) {
                // Mix random and guided mutations
                uint64_t rtype = splitmix64(&seed);
                for (int a = 0; a < 3; a++) {
                    for (int s = 0; s < 3; s++) {
                        for (int r = 0; r < 2; r++) {
                            uint64_t v = splitmix64(&seed);
                            c.t[a][s][r].w = v & 1;
                            c.t[a][s][r].mv = (v & 2) ? 1 : -1;
                            c.t[a][s][r].ns = (v >> 2) % 3;
                        }
                    }
                }
                local_cnt++;

                if (++mk1 == 0) { memset(vis1, 0, MCET3_S1_SIZE * 2); mk1 = 1; }
                int pos = 0;
                int s = eval_mcet3_s1(&c, tape1, vis1, mk1, &pos);
                if (s == -2 || s > 10000) {
                    if (++mk2 == 0) { memset(vis2, 0, MCET3_S2_SIZE * 4); mk2 = 1; }
                    s = eval_mcet3_deep(&c, tape2, vis2, mk2, &pos);
                    if (s > best_mcet3) {
                        #pragma omp critical
                        {
                            if (s > best_mcet3) {
                                best_mcet3 = s; best_mcet3_pos = pos;
                                fmt_mcet3(&c, bb_mcet3);
                                printf("\n🔥👑 [NEW MCET(3) ALL-AGENT RECORD: %d STEPS at cell %d!] 👑🔥\n", s, pos);
                                printf("bbchallenge: %s\n\n", bb_mcet3);
                                fflush(stdout);
                            }
                        }
                    } else if (s > 8000) {
                        #pragma omp critical
                        {
                            char b[128]; fmt_mcet3(&c, b);
                            printf("  [MCET(3) High Collider]: %d steps at cell %d | %s\n", s, pos, b);
                            fflush(stdout);
                        }
                    }
                }
            }
            #pragma omp atomic
            count_mcet3 += local_cnt;
            free(tape1); free(vis1); free(tape2); free(vis2);
        } else {
            // ================= CET(2,3) Worker =================
            uint8_t *tape1 = calloc(CET23_S1_SIZE, 1);
            uint16_t *vis1 = calloc(CET23_S1_SIZE, 2);
            uint8_t *tape2 = calloc(CET23_S2_SIZE, 1);
            uint32_t *vis2 = calloc(CET23_S2_SIZE, 4);
            uint16_t mk1 = 1;
            uint32_t mk2 = 1;

            Cet23Machine c;
            while (omp_get_wtime() - t0 < duration) {
                for (int a = 0; a < 2; a++) {
                    for (int s = 0; s < 2; s++) {
                        for (int r = 0; r < 3; r++) {
                            uint64_t v = splitmix64(&seed);
                            c.t[a][s][r].w = v % 3;
                            c.t[a][s][r].mv = (v & 4) ? 1 : -1;
                            c.t[a][s][r].ns = (v >> 3) & 1;
                        }
                    }
                }
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
            count_cet23 += local_cnt;
            free(tape1); free(vis1); free(tape2); free(vis2);
        }

        // Heartbeat on Thread 0
        if (tid == 0) {
            while (omp_get_wtime() - t0 < duration) {
                struct timespec ts = { .tv_sec = 30, .tv_nsec = 0 };
                nanosleep(&ts, NULL);
                double el = omp_get_wtime() - t0;
                #pragma omp critical
                {
                    printf("[T+%.0fs / %ds] Screened: CET(3)=%lldM, MCET(3)=%lldM, CET(2,3)=%lldM | Best: CET(3)=%d, MCET(3)=%d, CET(2,3)=%d\n",
                           el, duration, count_cet3 / 1000000, count_mcet3 / 1000000, count_cet23 / 1000000,
                           best_cet3, best_mcet3, best_cet23);
                    fflush(stdout);
                }
            }
        }
    }

    double total_elapsed = omp_get_wtime() - t0;
    printf("\n=========================================================================================================\n");
    printf("🏁 30-MINUTE MULTI-DOMAIN EXPEDITION COMPLETE in %.1fs\n", total_elapsed);
    printf("Total Candidates Screened Across All 16 Threads: %lld\n", count_cet3 + count_mcet3 + count_cet23);
    printf("  - CET(3) Screened: %lld (Best: %d steps at cell %d)\n", count_cet3, best_cet3, best_cet3_pos);
    printf("  - MCET(3) Screened: %lld (Best: %d steps at cell %d)\n", count_mcet3, best_mcet3, best_mcet3_pos);
    printf("  - CET(2,3) Screened: %lld (Best: %d steps at cell %d)\n", count_cet23, best_cet23, best_cet23_pos);
    printf("=========================================================================================================\n");

    return 0;
}
