#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

// ============================================================================
// MCET(4, 4-States) EXPEDITION ENGINE
// 4 Agents, 4 States (A, B, C, D), 2 Symbols (0, 1)
// Initial positions: [0, 2, 4, 6]
// Halting Condition: ALL 4 AGENTS SIMULTANEOUSLY COLLIDE ON THE SAME CELL
// Priority: Agent 1 > Agent 2 > Agent 3 > Agent 4
// ============================================================================

#define S1_TAPE_SIZE 262144
#define S1_TAPE_OFF  131072
#define S1_STEPS     100000

#define S2_TAPE_SIZE 4194304
#define S2_TAPE_OFF  2097152
#define S2_STEPS     2000000

#define S3_TAPE_SIZE 33554432
#define S3_TAPE_OFF  16777216
#define S3_LIMIT     500000000ULL // 500M Steps

typedef struct { int8_t w, mv, ns; } Tr;
// 4 agents, 4 states (0..3), 2 symbols (0..1)
typedef struct { Tr t[4][4][2]; } Mcet4x4Machine;

static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static void fmt_mcet4x4(const Mcet4x4Machine *m, char *b) {
    char *p = b;
    for (int a = 0; a < 4; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 4; s++) {
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

// Stage 1 Fast Filter (up to 100k steps, span allowed up to 1500)
static inline int eval_s1(const Mcet4x4Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p[4] = { S1_TAPE_OFF + 0, S1_TAPE_OFF + 2, S1_TAPE_OFF + 4, S1_TAPE_OFF + 6 };
    int s[4] = { 0, 0, 0, 0 };

    for (int step = 1; step <= S1_STEPS; step++) {
        for (int i = 0; i < 4; i++) {
            if (p[i] <= 20 || p[i] >= S1_TAPE_SIZE - 20) return -1;
        }

        uint8_t r[4];
        Tr tr[4];
        for (int i = 0; i < 4; i++) {
            r[i] = (vis[p[i]] == mk) ? tape[p[i]] : 0;
            tr[i] = m->t[i][s[i]][r[i]];
        }

        for (int i = 3; i >= 0; i--) {
            vis[p[i]] = mk;
            tape[p[i]] = tr[i].w;
        }

        for (int i = 0; i < 4; i++) {
            p[i] += tr[i].mv;
            s[i] = tr[i].ns;
        }

        if (p[0] == p[1] && p[1] == p[2] && p[2] == p[3]) {
            *pos = p[0] - S1_TAPE_OFF;
            return step;
        }

        int min_p = p[0], max_p = p[0];
        for (int i = 1; i < 4; i++) {
            if (p[i] < min_p) min_p = p[i];
            if (p[i] > max_p) max_p = p[i];
        }
        if (max_p - min_p > 1500) return -1;
    }
    return -2;
}

// Stage 2 Medium Filter (up to 2M steps, span allowed up to 8000)
static inline int eval_s2(const Mcet4x4Machine *m, uint8_t *tape, uint16_t *vis, uint16_t mk, int *pos) {
    int p[4] = { S2_TAPE_OFF + 0, S2_TAPE_OFF + 2, S2_TAPE_OFF + 4, S2_TAPE_OFF + 6 };
    int s[4] = { 0, 0, 0, 0 };

    for (int step = 1; step <= S2_STEPS; step++) {
        for (int i = 0; i < 4; i++) {
            if (p[i] <= 50 || p[i] >= S2_TAPE_SIZE - 50) return -1;
        }

        uint8_t r[4];
        Tr tr[4];
        for (int i = 0; i < 4; i++) {
            r[i] = (vis[p[i]] == mk) ? tape[p[i]] : 0;
            tr[i] = m->t[i][s[i]][r[i]];
        }

        for (int i = 3; i >= 0; i--) {
            vis[p[i]] = mk;
            tape[p[i]] = tr[i].w;
        }

        for (int i = 0; i < 4; i++) {
            p[i] += tr[i].mv;
            s[i] = tr[i].ns;
        }

        if (p[0] == p[1] && p[1] == p[2] && p[2] == p[3]) {
            *pos = p[0] - S2_TAPE_OFF;
            return step;
        }

        int min_p = p[0], max_p = p[0];
        for (int i = 1; i < 4; i++) {
            if (p[i] < min_p) min_p = p[i];
            if (p[i] > max_p) max_p = p[i];
        }
        if (max_p - min_p > 8000) return -1;
    }
    return -2;
}

// Stage 3 Deep 500M Horizon (span up to 50,000)
static int eval_s3(const Mcet4x4Machine *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p[4] = { S3_TAPE_OFF + 0, S3_TAPE_OFF + 2, S3_TAPE_OFF + 4, S3_TAPE_OFF + 6 };
    int s[4] = { 0, 0, 0, 0 };

    for (uint64_t step = 1; step <= S3_LIMIT; step++) {
        for (int i = 0; i < 4; i++) {
            if (p[i] <= 100 || p[i] >= S3_TAPE_SIZE - 100) return -1;
        }

        uint8_t r[4];
        Tr tr[4];
        for (int i = 0; i < 4; i++) {
            r[i] = (vis[p[i]] == mk) ? tape[p[i]] : 0;
            tr[i] = m->t[i][s[i]][r[i]];
        }

        for (int i = 3; i >= 0; i--) {
            vis[p[i]] = mk;
            tape[p[i]] = tr[i].w;
        }

        for (int i = 0; i < 4; i++) {
            p[i] += tr[i].mv;
            s[i] = tr[i].ns;
        }

        if (p[0] == p[1] && p[1] == p[2] && p[2] == p[3]) {
            *pos = p[0] - S3_TAPE_OFF;
            return (int)step;
        }

        int min_p = p[0], max_p = p[0];
        for (int i = 1; i < 4; i++) {
            if (p[i] < min_p) min_p = p[i];
            if (p[i] > max_p) max_p = p[i];
        }
        if (max_p - min_p > 50000) return -1;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 120; // Default 2 minutes
    if (argc > 1) duration = atoi(argv[1]);

    printf("=========================================================================================================\n");
    printf("🪐⚡🌌 MCET(4, 4-STATES) ALL-AGENT SIMULTANEOUS EXPEDITION (%d s) 🌌⚡🪐\n", duration);
    printf("=========================================================================================================\n");
    printf("Hardware: 16 AMD Threads | 4 Agents at [0, 2, 4, 6] | 4 States (A, B, C, D) | 500M Horizon\n");
    printf("Target: Simultaneous 4-Agent Coincidence on the Same Cell\n");
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

    int best_step = 0, best_pos = 0;
    char best_bb[256] = "";

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

        Mcet4x4Machine c;
        long long local_screened = 0;
        long long local_s2 = 0;
        long long local_s3 = 0;
        double last_hb = omp_get_wtime();

        while (omp_get_wtime() - t0 < duration) {
            // Generate 4-agent machine with 4 states in Tree Normal Form (TNF)
            for (int a = 0; a < 4; a++) {
                int max_seen = 0; // State 0 is active initially
                for (int s = 0; s < 4; s++) {
                    for (int r = 0; r < 2; r++) {
                        uint64_t v = splitmix64(&seed);
                        c.t[a][s][r].w = v & 1;
                        c.t[a][s][r].mv = (v & 2) ? 1 : -1;
                        
                        // TNF state generation: can only transition to seen states or at most max_seen + 1
                        int lim = max_seen + 1;
                        if (lim > 3) lim = 3;
                        int ns = (v >> 3) % (lim + 1);
                        if (ns > max_seen) max_seen = ns;
                        c.t[a][s][r].ns = ns;
                    }
                }
            }

            local_screened++;

            if (++mk1 == 0) { memset(vis1, 0, S1_TAPE_SIZE * 2); mk1 = 1; }
            int pos = 0;
            int s = eval_s1(&c, tape1, vis1, mk1, &pos);

            if (s > 0) {
                #pragma omp critical
                {
                    if (s > best_step) {
                        best_step = s; best_pos = pos;
                        fmt_mcet4x4(&c, best_bb);
                        printf("\n🔥👑 [MCET(4, 4-States) RECORD: %d STEPS at cell %d!] 👑🔥\n", s, pos);
                        printf("bbchallenge: %s\n\n", best_bb);
                        fflush(stdout);
                    }
                }
            } else if (s == -2) {
                local_s2++;
                if (++mk2 == 0) { memset(vis2, 0, S2_TAPE_SIZE * 2); mk2 = 1; }
                s = eval_s2(&c, tape2, vis2, mk2, &pos);

                if (s > 0) {
                    #pragma omp critical
                    {
                        if (s > best_step) {
                            best_step = s; best_pos = pos;
                            fmt_mcet4x4(&c, best_bb);
                            printf("\n🔥👑 [MCET(4, 4-States) TIER-2 RECORD: %d STEPS at cell %d!] 👑🔥\n", s, pos);
                            printf("bbchallenge: %s\n\n", best_bb);
                            fflush(stdout);
                        }
                    }
                } else if (s == -2) {
                    local_s3++;
                    if (++mk3 == 0) { memset(vis3, 0, S3_TAPE_SIZE * 4); mk3 = 1; }
                    s = eval_s3(&c, tape3, vis3, mk3, &pos);

                    if (s > 0) {
                        #pragma omp critical
                        {
                            if (s > best_step) {
                                best_step = s; best_pos = pos;
                                fmt_mcet4x4(&c, best_bb);
                                printf("\n🔥👑 [ALL-TIME MCET(4, 4-States) DEEP RECORD: %d STEPS at cell %d!] 👑🔥\n", s, pos);
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
                    printf("[T+%.0fs / %ds] Screened %lld machines | S2: %lld | S3: %lld | Best: %d steps\n",
                           omp_get_wtime() - t0, duration, total_screened + local_screened,
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
    printf("🏁 MCET(4, 4-States) EXPEDITION COMPLETE in %.1fs\n", elapsed);
    printf("Total Configurations Screened: %lld (%.0f/sec)\n", total_screened, total_screened / elapsed);
    printf("Stage 2 Passed: %lld | Pushed into 500M Horizon: %lld\n", s2_passed, s3_passed);
    printf("Best Simultaneous Champion: %d steps at cell %d\n", best_step, best_pos);
    printf("bbchallenge: %s\n", best_bb);
    printf("=========================================================================================================\n");

    return 0;
}
