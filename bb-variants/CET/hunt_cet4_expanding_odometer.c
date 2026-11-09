#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define STAGE1_STEPS 300000
#define STAGE2_STEPS 100000000ULL

typedef struct {
    uint8_t w;      // 0 or 1
    int8_t d;       // -1 or +1
    uint8_t ns;     // 0..3
} Trans4;

typedef struct {
    Trans4 t[2][4][2];
} Machine4;

void format_bb4(const Machine4 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 4; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 2; sym++) {
                Trans4 tr = m->t[a][s][sym];
                *p++ = '0' + tr.w;
                *p++ = tr.d > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.ns;
            }
        }
    }
    *p = '\0';
}

static inline uint32_t rnd(uint32_t *s) {
    uint32_t x = *s; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *s = x;
}

// Check if candidate is an expanding shuttle/odometer (not a tiny static cycler)
int simulate_expanding_odometer(const Machine4 *m, uint8_t *tape, uint32_t *vis, uint32_t mk, uint64_t max_steps, int *out_pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int min_pos = TAPE_OFFSET, max_pos = TAPE_OFFSET + 2;
    int last_expand = 0;

    for (uint64_t step = 1; step <= max_steps; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Trans4 tr1 = m->t[0][s1][r1], tr2 = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = tr2.w;
        vis[p1] = mk; tape[p1] = tr1.w;

        p1 += tr1.d; p2 += tr2.d;
        s1 = tr1.ns; s2 = tr2.ns;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            return (int)(step > 2147483647 ? 2147483647 : step);
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        if (dist > 3000) return -1; // Diverged

        int lo = p1 < p2 ? p1 : p2;
        int hi = p1 > p2 ? p1 : p2;
        if (lo < min_pos) { min_pos = lo; last_expand = (int)step; }
        if (hi > max_pos) { max_pos = hi; last_expand = (int)step; }

        // Prune static periodic cyclers: must expand tape at least once every 50k steps
        if (step > 50000 && (step - last_expand > 50000)) return -3;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 40;
    if (argc > 1) duration = atoi(argv[1]);

    printf("=== CET(4) Expanding Shuttle / Late-Collision Hunter (%d s) ===\n", duration);
    printf("Criteria: Tape span must grow steadily like the 49.18M champion, filtering out periodic static loops.\n");
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long tested = 0;
    int best = 49184559;
    char best_bb[256] = "0LB0LC_0LD0RA_0RA0RA_0RA0RA|1RB1LD_1RC1RB_1LC1LA_0RC0RD";

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint32_t seed = (uint32_t)time(NULL) * 2654435761u ^ (omp_get_thread_num() + 1) * 40503u;

        Machine4 m;
        long long local_tested = 0;

        while (omp_get_wtime() - t0 < duration) {
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 4; s++) {
                    for (int sym = 0; sym < 2; sym++) {
                        m.t[a][s][sym].w = rnd(&seed) & 1;
                        m.t[a][s][sym].d = (rnd(&seed) & 1) ? 1 : -1;
                        m.t[a][s][sym].ns = rnd(&seed) & 3;
                    }
                }
            }
            local_tested++;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            int s = simulate_expanding_odometer(&m, tape, vis, mk, STAGE1_STEPS, &pos);
            if (s > 100000 || s == -2) {
                // If it halted very late or survived 300k expanding steps, deep test to 100M
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = simulate_expanding_odometer(&m, tape, vis, mk, STAGE2_STEPS, &pos);
                if (s > best) {
                    #pragma omp critical
                    {
                        if (s > best) {
                            best = s;
                            format_bb4(&m, best_bb);
                            printf("\n🌟🌟🌟 >>> NEW CET(4) EXPANDING HALT RECORD: %d STEPS at cell %d! <<< 🌟🌟🌟\n", s, pos);
                            printf("bbchallenge: %s\n", best_bb);
                            fflush(stdout);
                        }
                    }
                } else if (s > 500000) {
                    char bb[256]; format_bb4(&m, bb);
                    printf("  Notable late halt: %d steps at cell %d | %s\n", s, pos, bb);
                    fflush(stdout);
                }
            }
        }

        #pragma omp atomic
        tested += local_tested;

        free(tape); free(vis);
    }

    printf("\nFinished in %.1f s. Tested %lld machines.\n", omp_get_wtime() - t0, tested);
    printf("Best CET(4) Champion: %d steps | %s\n", best, best_bb);
    return 0;
}
