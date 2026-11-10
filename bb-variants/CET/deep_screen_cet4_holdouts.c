#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 4194304
#define TAPE_OFFSET 2097152
#define MAX_STEPS 20000000ULL
#define MAX_DIST 1200
#define INACTIVE_LIMIT 500000

typedef struct {
    uint8_t w;
    int8_t m;
    uint8_t ns;
} Tr;

typedef struct {
    Tr t[2][4][2];
} TM4;

static int parse_tm4(const char *spec, TM4 *m) {
    const char *p = spec;
    for (int a = 0; a < 2; a++) {
        for (int q = 0; q < 4; q++) {
            for (int s = 0; s < 2; s++) {
                while (*p == '_' || *p == '|' || *p == ' ' || *p == '\r' || *p == '\n') p++;
                if (!*p) return -1;
                m->t[a][q][s].w = p[0] - '0';
                m->t[a][q][s].m = (p[1] == 'R') ? 1 : -1;
                m->t[a][q][s].ns = p[2] - 'A';
                p += 3;
            }
        }
    }
    return 0;
}

// Simulates machine.
// Returns:
//   > 0: Exact collision step (normal halt!)
//    -1: Diverged (distance > MAX_DIST or tape edge reached)
//    -2: Reached MAX_STEPS without halting (super holdout!)
//    -3: Bounded cycler (no tape expansion for INACTIVE_LIMIT steps)
static int64_t run_candidate(const TM4 *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *out_pos) {
    int p1 = TAPE_OFFSET;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;
    int min_pos = p1, max_pos = p2;
    uint64_t last_expand = 0;

    for (uint64_t step = 1; step <= MAX_STEPS; step++) {
        if (p1 < 500 || p1 >= TAPE_SIZE - 500 || p2 < 500 || p2 >= TAPE_SIZE - 500) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Tr t1 = m->t[0][s1][r1];
        Tr t2 = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = t2.w;
        vis[p1] = mk; tape[p1] = t1.w;

        p1 += t1.m;
        p2 += t2.m;
        s1 = t1.ns;
        s2 = t2.ns;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            return (int64_t)step;
        }

        int d = abs(p2 - p1);
        if (d > MAX_DIST) return -1;

        int exp = 0;
        if (p1 < min_pos) { min_pos = p1; exp = 1; }
        if (p2 < min_pos) { min_pos = p2; exp = 1; }
        if (p1 > max_pos) { max_pos = p1; exp = 1; }
        if (p2 > max_pos) { max_pos = p2; exp = 1; }
        if (exp) last_expand = step;

        if (step > INACTIVE_LIMIT && (step - last_expand > INACTIVE_LIMIT)) return -3;
    }

    *out_pos = p1 - TAPE_OFFSET;
    return -2;
}

int main(int argc, char **argv) {
    const char *infile = "all_holdouts_cet4.txt";
    if (argc > 1) infile = argv[1];

    FILE *f = fopen(infile, "r");
    if (!f) {
        printf("ERROR: Could not open %s\n", infile);
        return 1;
    }

    // Read all lines into memory
    char **lines = malloc(100000 * sizeof(char *));
    int count = 0;
    char buf[256];
    while (fgets(buf, sizeof(buf), f)) {
        // Strip trailing whitespace
        char *p = buf + strlen(buf) - 1;
        while (p >= buf && (*p == '\n' || *p == '\r' || *p == ' ')) *p-- = '\0';
        if (strlen(buf) > 10) {
            lines[count++] = strdup(buf);
        }
    }
    fclose(f);

    printf("========================================================================\n");
    printf("🔍 CET(4) DEEP HOLDOUT SCREENER: %d candidates loaded from %s\n", count, infile);
    printf("   Cutoff: %llu steps | Max Dist: %d | Threads: %d\n", (unsigned long long)MAX_STEPS, MAX_DIST, omp_get_max_threads());
    printf("========================================================================\n");
    fflush(stdout);

    FILE *fout = fopen("cet4_holdout_halts.txt", "a");
    FILE *fhold = fopen("cet4_super_holdouts_20m.txt", "a");

    double t0 = omp_get_wtime();
    int64_t best_step = 0;
    int halts_found = 0;
    int super_holdouts = 0;
    int cyclers = 0;
    int diverged = 0;

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;

        #pragma omp for schedule(dynamic, 16)
        for (int i = 0; i < count; i++) {
            TM4 m;
            if (parse_tm4(lines[i], &m) != 0) continue;

            if (++mk == 0) {
                memset(vis, 0, TAPE_SIZE * 4);
                mk = 1;
            }

            int pos = 0;
            int64_t s = run_candidate(&m, tape, vis, mk, &pos);

            #pragma omp critical
            {
                if (s > 0) {
                    halts_found++;
                    if (s > best_step) best_step = s;
                    if (s >= 500000) {
                        printf("⭐ [HALT] Candidate %d: %lld steps at cell %d | %s\n", i, (long long)s, pos, lines[i]);
                        fflush(stdout);
                    }
                    if (fout) {
                        fprintf(fout, "%lld\t%d\t%s\n", (long long)s, pos, lines[i]);
                        fflush(fout);
                    }
                } else if (s == -2) {
                    super_holdouts++;
                    printf("🚀 [SUPER HOLDOUT >20M]: Candidate %d at cell %d | %s\n", i, pos, lines[i]);
                    fflush(stdout);
                    if (fhold) {
                        fprintf(fhold, "%s\n", lines[i]);
                        fflush(fhold);
                    }
                } else if (s == -3) {
                    cyclers++;
                } else {
                    diverged++;
                }

                if ((i + 1) % 5000 == 0 || i + 1 == count) {
                    double el = omp_get_wtime() - t0;
                    printf("Progress: %d/%d (%.1f%%) in %.1fs (%.0f cand/s) | Halts: %d, Best: %lld, >20M: %d\n",
                           i + 1, count, 100.0 * (i + 1) / count, el, (i + 1) / el, halts_found, (long long)best_step, super_holdouts);
                    fflush(stdout);
                }
            }
        }

        free(tape);
        free(vis);
    }

    if (fout) fclose(fout);
    if (fhold) fclose(fhold);

    double total_time = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 SCREENING COMPLETE in %.1fs\n", total_time);
    printf("   Total Halts Found : %d\n", halts_found);
    printf("   Super Holdouts    : %d (survived 20,000,000 steps)\n", super_holdouts);
    printf("   Bounded Cyclers   : %d\n", cyclers);
    printf("   Diverged/Escaped  : %d\n", diverged);
    printf("   Best Step Count   : %lld\n", (long long)best_step);
    printf("========================================================================\n");

    for (int i = 0; i < count; i++) free(lines[i]);
    free(lines);

    return 0;
}
