#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

// ============================================================================
// COLAB A100 TRIPLE-RECORD EXPEDITION ENGINE
// 1. CET_1(2): 2 states, 2 symbols, quasi-halting (beats 110)
// 2. CET_1(2, 3): 2 states, 3 symbols, quasi-halting (beats 110)
// 3. CET(3): 3 states, 2 symbols, normal collision (beats 4,657,368)
// ============================================================================

typedef struct { int8_t w, mv, ns; } Tr;

static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

// ----------------------------------------------------------------------------
// DOMAIN 1: CET_1(2) Translated & Stationary Cyclers
// ----------------------------------------------------------------------------
typedef struct { Tr t[2][2]; } Agent2x2;

static inline void fmt_agent2x2(const Agent2x2 *ag, char *buf) {
    char *p = buf;
    for (int s = 0; s < 2; s++) {
        if (s) *p++ = '_';
        for (int r = 0; r < 2; r++) {
            *p++ = '0' + ag->t[s][r].w;
            *p++ = ag->t[s][r].mv > 0 ? 'R' : 'L';
            *p++ = 'A' + ag->t[s][r].ns;
        }
    }
    *p = 0;
}

#define TAPE_SIZE 65536
#define TAPE_OFF  32768

typedef struct {
    int16_t rel, p1, p2;
    uint8_t s1, s2;
    uint16_t step, cols;
} Snap2;

static int eval_cet1_2(const Agent2x2 *a1, const Agent2x2 *a2, uint8_t *tape, uint16_t *vis, uint16_t mk, Snap2 *hist, int *out_tot_col, int *out_cyc, int *out_drift) {
    int p1 = TAPE_OFF + 0, p2 = TAPE_OFF + 2;
    int s1 = 0, s2 = 0;
    int last_col = 0, cols = 0;

    for (int step = 1; step <= 1500; step++) {
        if (p1 <= 20 || p1 >= TAPE_SIZE - 20 || p2 <= 20 || p2 >= TAPE_SIZE - 20) return 0;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr t1 = a1->t[s1][r1];
        Tr t2 = a2->t[s2][r2];

        vis[p2] = mk; tape[p2] = t2.w;
        vis[p1] = mk; tape[p1] = t1.w;

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        if (p1 == p2) {
            cols++;
            last_col = step;
        }

        if (last_col > 0 && step > last_col) {
            int slot = step & 511;
            hist[slot].rel = p2 - p1;
            hist[slot].p1 = p1; hist[slot].p2 = p2;
            hist[slot].s1 = s1; hist[slot].s2 = s2;
            hist[slot].step = step; hist[slot].cols = cols;

            for (int past = step - 1; past >= step - 128 && past > last_col; past--) {
                Snap2 *old = &hist[past & 511];
                if (old->step == past && old->rel == (p2 - p1) && old->s1 == s1 && old->s2 == s2) {
                    int dp1 = p1 - old->p1;
                    int dp2 = p2 - old->p2;
                    if (dp1 == dp2 && old->cols == cols) {
                        *out_tot_col = cols;
                        *out_cyc = step - past;
                        *out_drift = dp1;
                        return last_col;
                    }
                }
            }
        }
    }
    return 0;
}

// ----------------------------------------------------------------------------
// DOMAIN 2: CET_1(2, 3) 2 States, 3 Symbols Quasi-Halting
// ----------------------------------------------------------------------------
typedef struct { Tr t[2][3]; } Agent2x3;

static inline void fmt_agent2x3(const Agent2x3 *ag, char *buf) {
    char *p = buf;
    for (int s = 0; s < 2; s++) {
        if (s) *p++ = '_';
        for (int r = 0; r < 3; r++) {
            *p++ = '0' + ag->t[s][r].w;
            *p++ = ag->t[s][r].mv > 0 ? 'R' : 'L';
            *p++ = 'A' + ag->t[s][r].ns;
        }
    }
    *p = 0;
}

static int eval_cet1_2x3(const Agent2x3 *a1, const Agent2x3 *a2, uint8_t *tape, uint16_t *vis, uint16_t mk, Snap2 *hist, int *out_tot_col, int *out_cyc, int *out_drift) {
    int p1 = TAPE_OFF + 0, p2 = TAPE_OFF + 2;
    int s1 = 0, s2 = 0;
    int last_col = 0, cols = 0;

    for (int step = 1; step <= 2500; step++) {
        if (p1 <= 20 || p1 >= TAPE_SIZE - 20 || p2 <= 20 || p2 >= TAPE_SIZE - 20) return 0;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr t1 = a1->t[s1][r1];
        Tr t2 = a2->t[s2][r2];

        vis[p2] = mk; tape[p2] = t2.w;
        vis[p1] = mk; tape[p1] = t1.w;

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        if (p1 == p2) {
            cols++;
            last_col = step;
        }

        if (last_col > 0 && step > last_col) {
            int slot = step & 511;
            hist[slot].rel = p2 - p1;
            hist[slot].p1 = p1; hist[slot].p2 = p2;
            hist[slot].s1 = s1; hist[slot].s2 = s2;
            hist[slot].step = step; hist[slot].cols = cols;

            for (int past = step - 1; past >= step - 128 && past > last_col; past--) {
                Snap2 *old = &hist[past & 511];
                if (old->step == past && old->rel == (p2 - p1) && old->s1 == s1 && old->s2 == s2) {
                    int dp1 = p1 - old->p1;
                    int dp2 = p2 - old->p2;
                    if (dp1 == dp2 && old->cols == cols) {
                        *out_tot_col = cols;
                        *out_cyc = step - past;
                        *out_drift = dp1;
                        return last_col;
                    }
                }
            }
        }
    }
    return 0;
}

// ----------------------------------------------------------------------------
// DOMAIN 3: CET(3) Mega Hunter (3 States, 2 Symbols Normal Collision)
// ----------------------------------------------------------------------------
typedef struct { Tr t[3][2]; } Agent3x2;

static inline void fmt_agent3x2(const Agent3x2 *ag, char *buf) {
    char *p = buf;
    for (int s = 0; s < 3; s++) {
        if (s) *p++ = '_';
        for (int r = 0; r < 2; r++) {
            *p++ = '0' + ag->t[s][r].w;
            *p++ = ag->t[s][r].mv > 0 ? 'R' : 'L';
            *p++ = 'A' + ag->t[s][r].ns;
        }
    }
    *p = 0;
}

static inline int eval_cet3(const Agent3x2 *a1, const Agent3x2 *a2, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = TAPE_OFF + 0, p2 = TAPE_OFF + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= 250000; step++) {
        if (p1 <= 20 || p1 >= TAPE_SIZE - 20 || p2 <= 20 || p2 >= TAPE_SIZE - 20) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr t1 = a1->t[s1][r1];
        Tr t2 = a2->t[s2][r2];

        vis[p2] = mk; tape[p2] = t2.w;
        vis[p1] = mk; tape[p1] = t1.w;

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        if (p1 == p2) {
            *pos = p1 - TAPE_OFF;
            return step;
        }

        int d = p1 - p2;
        if (d > 3500 || d < -3500) return -1;
    }
    return -2; // Deep candidate
}

// Main Tri-Campaign Runner
int main(int argc, char **argv) {
    int duration = 3600; // 1 hour default
    if (argc > 1) duration = atoi(argv[1]);

    printf("=========================================================================================================\n");
    printf("🪐⚡ COLAB A100 TRIPLE RECORD EXPEDITION (%d s) ⚡🪐\n", duration);
    printf("=========================================================================================================\n");
    printf("Targets:\n");
    printf("  1. CET_1(2): Beat Nath76's 110-step Translated Cycler WR\n");
    printf("  2. CET_1(2, 3): Discover new 3-symbol Quasi-Halting Champion (> 110)\n");
    printf("  3. CET(3): Break Nath76's 4,657,368 World Record\n");
    printf("=========================================================================================================\n");
    fflush(stdout);

    int num_t = 12; // Dedicated worker threads
    omp_set_num_threads(num_t);

    uint8_t *tape_pool[12];
    uint16_t *vis_pool[12];
    Snap2 *snap_pool[12];
    for (int i = 0; i < num_t; i++) {
        tape_pool[i] = calloc(TAPE_SIZE, 1);
        vis_pool[i] = calloc(TAPE_SIZE, 2);
        snap_pool[i] = calloc(512, sizeof(Snap2));
    }

    int best_cet1_2 = 110;
    int best_cet1_2x3 = 110;
    int best_cet3 = 100000;

    double t0 = omp_get_wtime();
    long long total_cet1_2 = 0;
    long long total_cet1_2x3 = 0;
    long long total_cet3 = 0;

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        uint8_t *tape = tape_pool[tid];
        uint16_t *vis = vis_pool[tid];
        Snap2 *hist = snap_pool[tid];
        uint16_t mk = 1;

        uint64_t seed = (uint64_t)time(NULL) * 6364136223846793005ULL + ((uint64_t)tid * 104729ULL + 1ULL);
        for (int i = 0; i < 20; i++) splitmix64(&seed);

        long long l_c1 = 0, l_c2 = 0, l_c3 = 0;
        double last_report = omp_get_wtime();

        while (omp_get_wtime() - t0 < duration) {
            // Task A: CET_1(2)
            if (tid % 3 == 0) {
                Agent2x2 a1, a2;
                for (int s = 0; s < 2; s++) {
                    for (int r = 0; r < 2; r++) {
                        uint64_t v = splitmix64(&seed);
                        a1.t[s][r].w = v & 1; a1.t[s][r].mv = (v & 2) ? 1 : -1; a1.t[s][r].ns = (v & 4) ? 1 : 0;
                        v = splitmix64(&seed);
                        a2.t[s][r].w = v & 1; a2.t[s][r].mv = (v & 2) ? 1 : -1; a2.t[s][r].ns = (v & 4) ? 1 : 0;
                    }
                }
                l_c1++;
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 2); mk = 1; }
                int tot_c = 0, cyc = 0, drift = 0;
                int s = eval_cet1_2(&a1, &a2, tape, vis, mk, hist, &tot_c, &cyc, &drift);
                if (s > best_cet1_2) {
                    #pragma omp critical
                    {
                        if (s > best_cet1_2) {
                            best_cet1_2 = s;
                            char s1[32], s2[32];
                            fmt_agent2x2(&a1, s1); fmt_agent2x2(&a2, s2);
                            printf("\n🔥👑 [COLAB A100] NEW CET_1(2) RECORD: LAST COLLISION AT STEP %d! 👑🔥\n", s);
                            printf("bbchallenge: %s|%s\n", s1, s2);
                            printf("Collisions: %d | Period: %d | Drift: %d cells\n\n", tot_c, cyc, drift);
                            fflush(stdout);
                        }
                    }
                }
            }
            // Task B: CET_1(2, 3)
            else if (tid % 3 == 1) {
                Agent2x3 a1, a2;
                for (int s = 0; s < 2; s++) {
                    for (int r = 0; r < 3; r++) {
                        uint64_t v = splitmix64(&seed);
                        a1.t[s][r].w = v % 3; a1.t[s][r].mv = (v & 4) ? 1 : -1; a1.t[s][r].ns = (v >> 3) & 1;
                        v = splitmix64(&seed);
                        a2.t[s][r].w = v % 3; a2.t[s][r].mv = (v & 4) ? 1 : -1; a2.t[s][r].ns = (v >> 3) & 1;
                    }
                }
                l_c2++;
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 2); mk = 1; }
                int tot_c = 0, cyc = 0, drift = 0;
                int s = eval_cet1_2x3(&a1, &a2, tape, vis, mk, hist, &tot_c, &cyc, &drift);
                if (s > best_cet1_2x3) {
                    #pragma omp critical
                    {
                        if (s > best_cet1_2x3) {
                            best_cet1_2x3 = s;
                            char s1[32], s2[32];
                            fmt_agent2x3(&a1, s1); fmt_agent2x3(&a2, s2);
                            printf("\n🔥🌈 [COLAB A100] NEW CET_1(2, 3) RECORD: LAST COLLISION AT STEP %d! 🌈🔥\n", s);
                            printf("bbchallenge: %s|%s\n", s1, s2);
                            printf("Collisions: %d | Period: %d | Drift: %d cells\n\n", tot_c, cyc, drift);
                            fflush(stdout);
                        }
                    }
                }
            }
            // Task C: CET(3) Mega Hunter
            else {
                Agent3x2 a1, a2;
                int max1 = 0, max2 = 0;
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        uint64_t v = splitmix64(&seed);
                        a1.t[s][r].w = v & 1; a1.t[s][r].mv = (v & 2) ? 1 : -1;
                        int ns1 = (v >> 3) % (max1 < 2 ? max1 + 2 : 3);
                        if (ns1 > max1) max1 = ns1; a1.t[s][r].ns = ns1;

                        v = splitmix64(&seed);
                        a2.t[s][r].w = v & 1; a2.t[s][r].mv = (v & 2) ? 1 : -1;
                        int ns2 = (v >> 3) % (max2 < 2 ? max2 + 2 : 3);
                        if (ns2 > max2) max2 = ns2; a2.t[s][r].ns = ns2;
                    }
                }
                l_c3++;
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 2); mk = 1; }
                int pos = 0;
                int s = eval_cet3(&a1, &a2, tape, vis, mk, &pos);
                if (s > best_cet3) {
                    #pragma omp critical
                    {
                        if (s > best_cet3) {
                            best_cet3 = s;
                            char s1[32], s2[32];
                            fmt_agent3x2(&a1, s1); fmt_agent3x2(&a2, s2);
                            printf("\n🔥🏆 [COLAB A100] HIGH CET(3) DISCOVERY: %d STEPS at cell %d! 🏆🔥\n", s, pos);
                            printf("bbchallenge: %s|%s\n\n", s1, s2);
                            fflush(stdout);
                        }
                    }
                }
            }

            if (tid == 0 && omp_get_wtime() - last_report > 15.0) {
                last_report = omp_get_wtime();
                #pragma omp critical
                {
                    double el = omp_get_wtime() - t0;
                    printf("[T+%.0fs / %ds] Screened: CET_1(2): %lld | CET_1(2,3): %lld | CET(3): %lld | Best: [C1: %d | C1(2,3): %d | C3: %d]\n",
                           el, duration, total_cet1_2 + l_c1, total_cet1_2x3 + l_c2, total_cet3 + l_c3,
                           best_cet1_2, best_cet1_2x3, best_cet3);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_cet1_2 += l_c1;
        #pragma omp atomic
        total_cet1_2x3 += l_c2;
        #pragma omp atomic
        total_cet3 += l_c3;
    }

    printf("\n=========================================================================================================\n");
    printf("🏁 COLAB A100 EXPEDITION FINISHED in %.1fs\n", omp_get_wtime() - t0);
    printf("Final High Watermarks: CET_1(2): %d | CET_1(2,3): %d | CET(3): %d\n", best_cet1_2, best_cet1_2x3, best_cet3);
    printf("=========================================================================================================\n");
    return 0;
}
