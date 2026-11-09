#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

// ============================================================================
// CET(3) RECORD EXPEDITION HUNTER
// 2 Agents, 3 States (A, B, C), 2 Symbols (0, 1)
// Priority: Agent 1 > Agent 2
// Goal: Hunt to break Nath76's 4,657,368 Record
// ============================================================================

#define S1_TAPE_SIZE 262144
#define S1_TAPE_OFF  131072
#define S1_STEPS     200000

#define S2_TAPE_SIZE 4194304
#define S2_TAPE_OFF  2097152
#define S2_STEPS     3000000

#define S3_TAPE_SIZE 33554432
#define S3_TAPE_OFF  16777216
#define S3_LIMIT     100000000ULL // 100M steps

typedef struct { int8_t w, mv, ns; } Tr;
typedef struct { Tr t[2][3][2]; } Cet3Machine; // [agent 0..1][state 0..2][read 0..1]

static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static void fmt_cet3(const Cet3Machine *m, char *b) {
    char *p = b;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                Tr x = m->t[a][s][r];
                *p++ = '0' + x.w;
                *p++ = x.mv > 0 ? 'R' : 'L';
                *p++ = 'A' + x.ns;
            }
        }
    }
    *p = 0;
}

static inline int eval_cet3_s1(const Cet3Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = S1_TAPE_OFF + 0;
    int p2 = S1_TAPE_OFF + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= S1_STEPS; step++) {
        if (p1 <= 20 || p1 >= S1_TAPE_SIZE - 20 || p2 <= 20 || p2 >= S1_TAPE_SIZE - 20) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr t1 = m->t[0][s1][r1];
        Tr t2 = m->t[1][s2][r2];

        // Write: Agent 2 writes, then Agent 1
        vis[p2] = mk; tape[p2] = t2.w;
        vis[p1] = mk; tape[p1] = t1.w;

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        if (p1 == p2) {
            *pos = p1 - S1_TAPE_OFF;
            return step;
        }

        // Broad span window (allow up to 2,500 cells)
        int dist = p1 - p2;
        if (dist > 2500 || dist < -2500) return -1;
    }
    return -2;
}

static inline int eval_cet3_s2(const Cet3Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p1 = S2_TAPE_OFF + 0;
    int p2 = S2_TAPE_OFF + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= S2_STEPS; step++) {
        if (p1 <= 50 || p1 >= S2_TAPE_SIZE - 50 || p2 <= 50 || p2 >= S2_TAPE_SIZE - 50) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr t1 = m->t[0][s1][r1];
        Tr t2 = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = t2.w;
        vis[p1] = mk; tape[p1] = t1.w;

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        if (p1 == p2) {
            *pos = p1 - S2_TAPE_OFF;
            return step;
        }

        int dist = p1 - p2;
        if (dist > 12000 || dist < -12000) return -1;
    }
    return -2;
}

static int eval_cet3_deep(const Cet3Machine *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = S3_TAPE_OFF + 0;
    int p2 = S3_TAPE_OFF + 2;
    int s1 = 0, s2 = 0;

    for (uint64_t step = 1; step <= S3_LIMIT; step++) {
        if (p1 <= 100 || p1 >= S3_TAPE_SIZE - 100 || p2 <= 100 || p2 >= S3_TAPE_SIZE - 100) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr t1 = m->t[0][s1][r1];
        Tr t2 = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = t2.w;
        vis[p1] = mk; tape[p1] = t1.w;

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        if (p1 == p2) {
            *pos = p1 - S3_TAPE_OFF;
            return (int)step;
        }

        int dist = p1 - p2;
        if (dist > 60000 || dist < -60000) return -1;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 30; // 30s benchmark default
    if (argc > 1) duration = atoi(argv[1]);

    printf("=========================================================================================================\n");
    printf("🪐⚡ CET(3) NATH76 RECORD EXPEDITION HUNTER (%d s) ⚡🪐\n", duration);
    printf("=========================================================================================================\n");
    printf("Current World Record: 4,657,368 steps (Nath76)\n");
    printf("Hardware: 16 AMD Ryzen OpenMP Threads | 100,000,000 Step Horizon\n");
    fflush(stdout);

    uint8_t *t1_pool[16]; uint16_t *v1_pool[16];
    uint8_t *t2_pool[16]; uint16_t *v2_pool[16];
    uint8_t *t3_pool[16]; uint32_t *v3_pool[16];

    for (int i = 0; i < 16; i++) {
        t1_pool[i] = calloc(S1_TAPE_SIZE, 1);
        v1_pool[i] = calloc(S1_TAPE_SIZE, 2);
        t2_pool[i] = calloc(S2_TAPE_SIZE, 1);
        v2_pool[i] = calloc(S2_TAPE_SIZE, 2);
        t3_pool[i] = calloc(S3_TAPE_SIZE, 1);
        v3_pool[i] = calloc(S3_TAPE_SIZE, 4);
    }

    int best_step = 100000;
    int best_pos = 0;
    char best_bb[128] = "";

    double t0 = omp_get_wtime();
    long long total_screened = 0;
    long long s2_passed = 0;
    long long s3_passed = 0;

    #pragma omp parallel num_threads(16)
    {
        int tid = omp_get_thread_num();
        uint8_t *tape1 = t1_pool[tid]; uint16_t *vis1 = v1_pool[tid]; uint16_t mk1 = 1;
        uint8_t *tape2 = t2_pool[tid]; uint16_t *vis2 = v2_pool[tid]; uint16_t mk2 = 1;
        uint8_t *tape3 = t3_pool[tid]; uint32_t *vis3 = v3_pool[tid]; uint32_t mk3 = 1;

        uint64_t seed = (uint64_t)time(NULL) * 6364136223846793005ULL + ((uint64_t)tid * 104729ULL + 1ULL);
        for (int i = 0; i < 20; i++) splitmix64(&seed);

        Cet3Machine c;
        long long local_screened = 0;
        long long local_s2 = 0;
        long long local_s3 = 0;
        double last_hb = omp_get_wtime();

        while (omp_get_wtime() - t0 < duration) {
            // Generate CET(3) machine in TNF
            for (int a = 0; a < 2; a++) {
                int max_seen = 0;
                for (int s = 0; s < 3; s++) {
                    for (int r = 0; r < 2; r++) {
                        uint64_t v = splitmix64(&seed);
                        c.t[a][s][r].w = v & 1;
                        c.t[a][s][r].mv = (v & 2) ? 1 : -1;
                        int lim = max_seen + 1;
                        if (lim > 2) lim = 2;
                        int ns = (v >> 3) % (lim + 1);
                        if (ns > max_seen) max_seen = ns;
                        c.t[a][s][r].ns = ns;
                    }
                }
            }

            local_screened++;

            if (++mk1 == 0) { memset(vis1, 0, S1_TAPE_SIZE * 2); mk1 = 1; }
            int pos = 0;
            int s = eval_cet3_s1(&c, tape1, vis1, mk1, &pos);

            if (s > 0) {
                if (s > best_step) {
                    #pragma omp critical
                    {
                        if (s > best_step) {
                            best_step = s; best_pos = pos;
                            fmt_cet3(&c, best_bb);
                            printf("\n🔥👑 [HIGH CET(3) DISCOVERY: %d STEPS at cell %d!] 👑🔥\n", s, pos);
                            printf("bbchallenge: %s\n\n", best_bb);
                            fflush(stdout);
                        }
                    }
                }
            } else if (s == -2) {
                local_s2++;
                if (++mk2 == 0) { memset(vis2, 0, S2_TAPE_SIZE * 2); mk2 = 1; }
                s = eval_cet3_s2(&c, tape2, vis2, mk2, &pos);

                if (s > 0) {
                    if (s > best_step) {
                        #pragma omp critical
                        {
                            if (s > best_step) {
                                best_step = s; best_pos = pos;
                                fmt_cet3(&c, best_bb);
                                printf("\n🔥👑 [TIER-2 CET(3) DISCOVERY: %d STEPS at cell %d!] 👑🔥\n", s, pos);
                                printf("bbchallenge: %s\n\n", best_bb);
                                fflush(stdout);
                            }
                        }
                    }
                } else if (s == -2) {
                    local_s3++;
                    if (++mk3 == 0) { memset(vis3, 0, S3_TAPE_SIZE * 4); mk3 = 1; }
                    s = eval_cet3_deep(&c, tape3, vis3, mk3, &pos);

                    if (s > 0) {
                        #pragma omp critical
                        {
                            if (s > best_step) {
                                best_step = s; best_pos = pos;
                                fmt_cet3(&c, best_bb);
                                printf("\n🔥👑 [DEEP 100M HORIZON CET(3) RECORD: %d STEPS at cell %d!] 👑🔥\n", s, pos);
                                printf("bbchallenge: %s\n\n", best_bb);
                                fflush(stdout);
                            }
                        }
                    }
                }
            }

            if (tid == 0 && omp_get_wtime() - last_hb > 10.0) {
                last_hb = omp_get_wtime();
                #pragma omp critical
                {
                    double el = omp_get_wtime() - t0;
                    printf("[%.1fs / %ds] Screened %lld machines (%.0f/s) | S2: %lld | S3: %lld | Best: %d steps\n",
                           el, duration, total_screened + local_screened,
                           (total_screened + local_screened) / (el > 0 ? el : 1),
                           s2_passed + local_s2, s3_passed + local_s3, best_step);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        total_screened += local_screened;
        #pragma omp atomic
        s2_passed += local_s2;
        #pragma omp atomic
        s3_passed += local_s3;
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n=========================================================================================================\n");
    printf("🏁 CET(3) EXPEDITION COMPLETE in %.1fs\n", elapsed);
    printf("Total Configurations Screened: %lld (%.0f/sec)\n", total_screened, total_screened / elapsed);
    printf("Pushed into 100M Horizon: %lld\n", s3_passed);
    printf("=========================================================================================================\n");

    return 0;
}
