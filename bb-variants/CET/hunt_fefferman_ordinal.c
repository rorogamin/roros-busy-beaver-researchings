#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define STAGE1_SIZE 65536
#define STAGE1_OFF  32768
#define STAGE1_STEPS 15000

#define STAGE2_SIZE 262144
#define STAGE2_OFF  131072
#define STAGE2_STEPS 300000

#define DEEP_SIZE   16777216
#define DEEP_OFF    8388608
#define DEEP_LIMIT  500000000ULL

typedef struct { int8_t w, mv, ns; } Tr;
typedef struct { Tr t[2][3][2]; } M;

static void fmt(const M *m, char *b) {
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

static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

// STAGE 1: Fast filter with boundary checks
static inline int eval_stage1(const M *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = STAGE1_OFF, p2 = STAGE1_OFF + 2;
    int s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;

    for (int step = 1; step <= STAGE1_STEPS; step++) {
        if (p1 <= 20 || p1 >= STAGE1_SIZE - 20 || p2 <= 20 || p2 >= STAGE1_SIZE - 20) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1];
        Tr b = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv; p2 += b.mv;
        s1 = a.ns; s2 = b.ns;

        if (p1 == p2) { *pos = p1 - STAGE1_OFF; return step; }

        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 100) return -1; // Fast divergence prune

        int l = p1 < p2 ? p1 : p2;
        int h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }

        if (step > 4000 && (step - last_exp > 4000)) return -3;
    }
    return -2; // Promising holdout!
}

// STAGE 2: Intermediate filter up to 300,000 steps
static inline int eval_stage2(const M *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = STAGE2_OFF, p2 = STAGE2_OFF + 2;
    int s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;

    for (int step = 1; step <= STAGE2_STEPS; step++) {
        if (p1 <= 30 || p1 >= STAGE2_SIZE - 30 || p2 <= 30 || p2 >= STAGE2_SIZE - 30) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1];
        Tr b = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv; p2 += b.mv;
        s1 = a.ns; s2 = b.ns;

        if (p1 == p2) { *pos = p1 - STAGE2_OFF; return step; }

        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 450) return -1;

        int l = p1 < p2 ? p1 : p2;
        int h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }

        if (step > 40000 && (step - last_exp > 40000)) return -3;
    }
    return -2;
}

// STAGE 3: Super Deep Ordinal Horizon (Up to 500,000,000 Steps)
static int eval_stage3_deep(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = DEEP_OFF, p2 = DEEP_OFF + 2;
    int s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;

    for (uint64_t step = 1; step <= DEEP_LIMIT; step++) {
        if (p1 <= 100 || p1 >= DEEP_SIZE - 100 || p2 <= 100 || p2 >= DEEP_SIZE - 100) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr a = m->t[0][s1][r1];
        Tr b = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;

        p1 += a.mv; p2 += b.mv;
        s1 = a.ns; s2 = b.ns;

        if (p1 == p2) { *pos = p1 - DEEP_OFF; return (int)step; }

        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 6000) return -1;

        int l = p1 < p2 ? p1 : p2;
        int h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = (int)step; }
        if (h > hi) { hi = h; last_exp = (int)step; }

        if (step > 1000000 && ((int)step - last_exp > 1000000)) return -3;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 90;
    if (argc > 1) duration = atoi(argv[1]);

    printf("=========================================================================================\n");
    printf("🔱⚡🌌 SUPER OMEGA OMEAGLE EPSILON ZETA ETA IOTA ORDINAL CET ENGINE (%d s) 🌌⚡🔱\n", duration);
    printf("=========================================================================================\n");
    printf("16 AMD Ryzen Threads | 3-Tier L1/L2/RAM Cache Pipeline | 500,000,000 Step Horizon\n");
    printf("Target Champion: 3,746,207 Steps\n");
    fflush(stdout);

    uint8_t *t1_pool[16]; uint16_t *v1_pool[16];
    uint8_t *t2_pool[16]; uint16_t *v2_pool[16];
    uint8_t *t3_pool[16]; uint32_t *v3_pool[16];

    for (int i = 0; i < 16; i++) {
        t1_pool[i] = calloc(STAGE1_SIZE, 1);
        v1_pool[i] = calloc(STAGE1_SIZE, 2);
        t2_pool[i] = calloc(STAGE2_SIZE, 1);
        v2_pool[i] = calloc(STAGE2_SIZE, 2);
        t3_pool[i] = calloc(DEEP_SIZE, 1);
        v3_pool[i] = calloc(DEEP_SIZE, 4);
    }

    double t0 = omp_get_wtime();
    long long total_screened = 0;
    long long stage2_passed = 0;
    long long deep_passed = 0;
    int global_best = 3746207;
    int global_best_pos = -9;
    char global_best_bb[128] = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";

    #pragma omp parallel num_threads(16)
    {
        int tid = omp_get_thread_num();
        uint8_t *tape1 = t1_pool[tid]; uint16_t *vis1 = v1_pool[tid]; uint16_t mk1 = 1;
        uint8_t *tape2 = t2_pool[tid]; uint16_t *vis2 = v2_pool[tid]; uint16_t mk2 = 1;
        uint8_t *tape3 = t3_pool[tid]; uint32_t *vis3 = v3_pool[tid]; uint32_t mk3 = 1;

        uint64_t seed = (uint64_t)time(NULL) * 6364136223846793005ULL + ((uint64_t)tid * 104729ULL + 1ULL);
        for (int i = 0; i < 20; i++) splitmix64(&seed);

        M c;
        long long local_screened = 0;
        long long local_s2 = 0;
        long long local_deep = 0;
        double last_hb = omp_get_wtime();

        while (omp_get_wtime() - t0 < duration) {
            // Full unseeded random machine generation
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

            local_screened++;

            // STAGE 1 (L1 Cache)
            if (++mk1 == 0) { memset(vis1, 0, STAGE1_SIZE * 2); mk1 = 1; }
            int pos = 0;
            int s = eval_stage1(&c, tape1, vis1, mk1, &pos);

            if (s == -2 || s > 12000) {
                local_s2++;
                // STAGE 2 (L2 Cache)
                if (++mk2 == 0) { memset(vis2, 0, STAGE2_SIZE * 2); mk2 = 1; }
                s = eval_stage2(&c, tape2, vis2, mk2, &pos);

                if (s == -2 || s > 250000) {
                    local_deep++;
                    // STAGE 3 (Deep 500M Horizon)
                    if (++mk3 == 0) { memset(vis3, 0, DEEP_SIZE * 4); mk3 = 1; }
                    s = eval_stage3_deep(&c, tape3, vis3, mk3, &pos);

                    if (s > global_best) {
                        #pragma omp critical
                        {
                            if (s > global_best) {
                                global_best = s;
                                global_best_pos = pos;
                                fmt(&c, global_best_bb);
                                printf("\n🔥🔥🔥💥💥💥 [NEW FEFFERMAN-ORDINAL CHAMPION: %d STEPS at cell %d!] 💥💥💥🔥🔥🔥\n", s, pos);
                                printf("bbchallenge: %s\n\n", global_best_bb);
                                fflush(stdout);
                            }
                        }
                    } else if (s > 1000000) {
                        #pragma omp critical
                        {
                            char bb[128]; fmt(&c, bb);
                            printf("  [Ordinal Holdout >1M Steps]: %d steps at cell %d | %s\n", s, pos, bb);
                            fflush(stdout);
                        }
                    }
                }
            }

            if (tid == 0 && omp_get_wtime() - last_hb > 10.0) {
                last_hb = omp_get_wtime();
                #pragma omp critical
                {
                    printf("[T+%.0fs] Screened %lld machines (%.0f/s) | S2: %lld | Deep: %lld | Champ: %d\n",
                           omp_get_wtime() - t0, total_screened + local_screened,
                           (total_screened + local_screened) / (omp_get_wtime() - t0),
                           stage2_passed + local_s2, deep_passed + local_deep, global_best);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_screened += local_screened;
        #pragma omp atomic
        stage2_passed += local_s2;
        #pragma omp atomic
        deep_passed += local_deep;
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n=========================================================================================\n");
    printf("🏁 ORDINAL EXPEDITION FINISHED in %.1fs\n", elapsed);
    printf("Total Fresh Candidates Screened: %lld (%.0f candidates/sec)\n", total_screened, total_screened / elapsed);
    printf("Filtered through Stage 2: %lld | Pushed through Deep 500M Horizon: %lld\n", stage2_passed, deep_passed);
    printf("Best CET(3) Champion: %d steps at cell %d\n", global_best, global_best_pos);
    printf("bbchallenge: %s\n", global_best_bb);
    printf("=========================================================================================\n");

    for (int i = 0; i < 16; i++) {
        free(t1_pool[i]); free(v1_pool[i]);
        free(t2_pool[i]); free(v2_pool[i]);
        free(t3_pool[i]); free(v3_pool[i]);
    }

    return 0;
}
