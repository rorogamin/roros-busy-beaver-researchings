#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 33554432
#define TAPE_OFFSET 16777216

typedef struct {
    uint8_t w;
    int8_t m;
    uint8_t n;
} Trans;

typedef struct {
    Trans t[2][3][2];
} TM3;

static void format_tm3(const TM3 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int q = 0; q < 3; q++) {
            if (q > 0) *p++ = '_';
            for (int s = 0; s < 2; s++) {
                Trans tr = m->t[a][q][s];
                *p++ = '0' + tr.w;
                *p++ = tr.m > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.n;
            }
        }
    }
    *p = '\0';
}

static int parse_tm3(const char *spec, TM3 *tm) {
    memset(tm, 0, sizeof(*tm));
    const char *p = spec;
    for (int a = 0; a < 2; a++) {
        for (int q = 0; q < 3; q++) {
            for (int s = 0; s < 2; s++) {
                while (*p == '_' || *p == '|' || *p == ' ' || *p == '\r' || *p == '\n') p++;
                if (!*p) return -1;
                tm->t[a][q][s].w = p[0] - '0';
                tm->t[a][q][s].m = (p[1] == 'R') ? 1 : -1;
                tm->t[a][q][s].n = p[2] - 'A';
                p += 3;
            }
        }
    }
    return 0;
}

// Simulates machine with distance and inactive limits.
// Returns:
//   > 0: collision step (normal halt)
//    -1: distance exceeded or tape edge
//    -2: reached max_steps
//    -3: bounded cycler (no tape expansion for inactive_limit steps)
static int64_t sim_bounded(const TM3 *m, uint8_t *tape, uint32_t *vis, uint32_t mk,
                           uint64_t max_steps, int max_dist, uint64_t inactive_limit, int *out_pos) {
    int p0 = TAPE_OFFSET;
    int p1 = TAPE_OFFSET + 2;
    int q0 = 0, q1 = 0;
    int min_p = p0, max_p = p1;
    uint64_t last_expand = 0;

    for (uint64_t step = 1; step <= max_steps; step++) {
        if (p0 < 1000 || p0 >= TAPE_SIZE - 1000 || p1 < 1000 || p1 >= TAPE_SIZE - 1000) return -1;

        uint8_t s0 = (vis[p0] == mk) ? tape[p0] : 0;
        uint8_t s1 = (vis[p1] == mk) ? tape[p1] : 0;

        Trans t0 = m->t[0][q0][s0];
        Trans t1 = m->t[1][q1][s1];

        vis[p1] = mk; tape[p1] = t1.w;
        vis[p0] = mk; tape[p0] = t0.w;

        p0 += t0.m;
        p1 += t1.m;

        q0 = t0.n;
        q1 = t1.n;

        if (p0 == p1) {
            *out_pos = p0 - TAPE_OFFSET;
            return (int64_t)step;
        }

        int d = abs(p1 - p0);
        if (d > max_dist) return -1;

        int exp = 0;
        if (p0 < min_p) { min_p = p0; exp = 1; }
        if (p1 < min_p) { min_p = p1; exp = 1; }
        if (p0 > max_p) { max_p = p0; exp = 1; }
        if (p1 > max_p) { max_p = p1; exp = 1; }
        if (exp) last_expand = step;

        if (inactive_limit > 0 && step > inactive_limit && (step - last_expand > inactive_limit)) return -3;
    }

    *out_pos = p0 - TAPE_OFFSET;
    return -2;
}

int main(int argc, char **argv) {
    const char *seed_specs[] = {
        "0LB0LC_1RB1LA_1RC0LA|1LB0RC_1RA1LB_0LB1RC", // 3.092B champion
        "1RB0LC_1LA1RB_0RB1LC|1RB0RB_1LB0LC_1RB0RA"  // 2.755B champion
    };
    int num_seeds = 2;

    printf("========================================================================\n");
    printf("🧬 EXHAUSTIVE 1- & 2-MUTATION SWEEP AROUND 3.092B & 2.755B CHAMPIONS\n");
    printf("   Threads: %d\n", omp_get_max_threads());
    printf("========================================================================\n");
    fflush(stdout);

    // Generate mutant list
    TM3 *mutants = malloc(20000 * sizeof(TM3));
    int total_mutants = 0;

    for (int s_idx = 0; s_idx < num_seeds; s_idx++) {
        TM3 seed;
        parse_tm3(seed_specs[s_idx], &seed);

        // 1-mutations: 12 transitions, each has 11 alternative (w, m, n) tuples
        for (int a = 0; a < 2; a++) {
            for (int q = 0; q < 3; q++) {
                for (int s = 0; s < 2; s++) {
                    Trans orig = seed.t[a][q][s];
                    for (int nw = 0; nw < 2; nw++) {
                        for (int nm = 0; nm < 2; nm++) {
                            for (int nn = 0; nn < 3; nn++) {
                                int8_t dir = nm ? 1 : -1;
                                if (nw == orig.w && dir == orig.m && nn == orig.n) continue;
                                TM3 m = seed;
                                m.t[a][q][s].w = nw;
                                m.t[a][q][s].m = dir;
                                m.t[a][q][s].n = nn;
                                mutants[total_mutants++] = m;
                            }
                        }
                    }
                }
            }
        }

        // 2-mutations: sample across distinct pairs
        for (int a1 = 0; a1 < 2; a1++) {
            for (int q1 = 0; q1 < 3; q1++) {
                for (int s1 = 0; s1 < 2; s1++) {
                    for (int a2 = 0; a2 < 2; a2++) {
                        for (int q2 = 0; q2 < 3; q2++) {
                            for (int s2 = 0; s2 < 2; s2++) {
                                if (a1 > a2 || (a1 == a2 && q1 > q2) || (a1 == a2 && q1 == q2 && s1 >= s2)) continue;
                                // For each pair, mutate each in 1 or 2 ways
                                for (int d1 = 0; d1 < 2; d1++) {
                                    for (int d2 = 0; d2 < 2; d2++) {
                                        TM3 m = seed;
                                        m.t[a1][q1][s1].m = d1 ? 1 : -1;
                                        m.t[a2][q2][s2].m = d2 ? 1 : -1;
                                        mutants[total_mutants++] = m;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    printf("Generated %d mutants to evaluate across all cores.\n", total_mutants);
    fflush(stdout);

    FILE *fout = fopen("champ_neighborhood_halts.txt", "w");
    double t0 = omp_get_wtime();

    int l1_halts = 0, l2_halts = 0, l3_halts = 0;
    int64_t best_step = 0;
    char best_spec[256] = "";

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;

        #pragma omp for schedule(dynamic, 16)
        for (int i = 0; i < total_mutants; i++) {
            TM3 m = mutants[i];

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;

            // Level 1: 200,000 steps (fast prune: dist 3000, inactive 60k)
            int64_t s = sim_bounded(&m, tape, vis, mk, 200000ULL, 3000, 60000ULL, &pos);

            if (s > 0) {
                #pragma omp critical
                {
                    l1_halts++;
                    if (s > best_step) { best_step = s; format_tm3(&m, best_spec); }
                    if (s >= 50000) {
                        char spec[128]; format_tm3(&m, spec);
                        printf("  [L1 Halt] %lld steps at x=%d | %s\n", (long long)s, pos, spec);
                        fflush(stdout);
                        if (fout) { fprintf(fout, "%lld\t%d\t%s\n", (long long)s, pos, spec); fflush(fout); }
                    }
                }
                continue;
            }

            if (s == -2) {
                // Survived Level 1! Level 2: 50,000,000 steps
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = sim_bounded(&m, tape, vis, mk, 50000000ULL, 25000, 1000000ULL, &pos);

                if (s > 0) {
                    #pragma omp critical
                    {
                        l2_halts++;
                        if (s > best_step) { best_step = s; format_tm3(&m, best_spec); }
                        char spec[128]; format_tm3(&m, spec);
                        printf("🔥 [L2 DEEP HALT] %lld steps at x=%d! %s\n", (long long)s, pos, spec);
                        fflush(stdout);
                        if (fout) { fprintf(fout, "%lld\t%d\t%s\n", (long long)s, pos, spec); fflush(fout); }
                    }
                    continue;
                }

                if (s == -2) {
                    // Survived Level 2 (50M steps)! Level 3: 5,000,000,000 steps!
                    char spec[128]; format_tm3(&m, spec);
                    printf("🚀 [L3 BILLION RUN] Survived 50M steps! Starting 5B simulation: %s\n", spec);
                    fflush(stdout);

                    if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                    s = sim_bounded(&m, tape, vis, mk, 5000000000ULL, 120000, 5000000ULL, &pos);

                    if (s > 0) {
                        #pragma omp critical
                        {
                            l3_halts++;
                            if (s > best_step) { best_step = s; format_tm3(&m, best_spec); }
                            printf("💥💥💥 [L3 WORLD CLASS RECORD] %lld steps at x=%d! %s 💥💥💥\n",
                                   (long long)s, pos, spec);
                            fflush(stdout);
                            if (fout) { fprintf(fout, "%lld\t%d\t%s\n", (long long)s, pos, spec); fflush(fout); }
                        }
                    } else if (s == -2) {
                        printf("🌟 [HOLDOUT >5 BILLION STEPS]: %s\n", spec);
                        fflush(stdout);
                    }
                }
            }
        }

        free(tape);
        free(vis);
    }

    if (fout) fclose(fout);

    double el = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 NEIGHBORHOOD SWEEP COMPLETE in %.1fs (%.0f mutants/sec)\n", el, total_mutants / el);
    printf("   Level 1 Halts (50k-200k)   : %d\n", l1_halts);
    printf("   Level 2 Halts (200k-50M)   : %d\n", l2_halts);
    printf("   Level 3 Halts (>50M)       : %d\n", l3_halts);
    printf("   Best Step Count Found      : %lld\n", (long long)best_step);
    if (best_step > 0) {
        printf("   Best Spec                  : %s\n", best_spec);
    }
    printf("========================================================================\n");

    free(mutants);
    return 0;
}
