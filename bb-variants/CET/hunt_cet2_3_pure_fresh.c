#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define SCREEN_STEPS 60000
#define DEEP_CEILING 50000000ULL

typedef struct {
    uint8_t write; // 0, 1, 2
    int8_t move;   // -1 or +1
    uint8_t next_state; // 0 or 1
} Transition;

typedef struct {
    Transition t[2][2][3];
} Machine2_3;

static void fmt_3sym(const Machine2_3 *m, char *b) {
    char *p = b;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 2; s++) {
            if (s) *p++ = '_';
            for (int r = 0; r < 3; r++) {
                Transition x = m->t[a][s][r];
                *p++ = '0' + x.write; *p++ = x.move > 0 ? 'R' : 'L'; *p++ = 'A' + x.next_state;
            }
        }
    }
    *p = 0;
}

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static inline int screen_2_3(const Machine2_3 *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_expand = 0;
    int rev1 = 0, rev2 = 0, pm1 = 0, pm2 = 0;

    for (int step = 1; step <= SCREEN_STEPS; step++) {
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Transition a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.write;
        vis[p1] = mk; tape[p1] = a.write;

        p1 += a.move; p2 += b.move; s1 = a.next_state; s2 = b.next_state;

        if (a.move != pm1) { rev1++; pm1 = a.move; }
        if (b.move != pm2) { rev2++; pm2 = b.move; }

        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return step; }

        int dist = p2 - p1; if (dist < 0) dist = -dist;
        if (dist > 350) return -1;

        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_expand = step; }
        if (h > hi) { hi = h; last_expand = step; }

        if (step > 25000 && (step - last_expand > 25000)) return -3;
    }
    if (rev1 < 8 && rev2 < 8) return -3;
    return -2;
}

int simulate_deep_2_3(const Machine2_3 *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    for (uint64_t step = 1; step <= DEEP_CEILING; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Transition a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.write;
        vis[p1] = mk; tape[p1] = a.write;

        p1 += a.move; p2 += b.move; s1 = a.next_state; s2 = b.next_state;

        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return (int)step; }

        int dist = p2 - p1; if (dist < 0) dist = -dist;
        if (dist > 3000) return -1;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 90;
    if (argc > 1) duration = atoi(argv[1]);

    printf("========================================================================\n");
    printf("🌈 CET(2,3) FRESH RANDOM ULTRA-SEARCH (Target > 20,350 Steps)\n");
    printf("========================================================================\n");
    printf("Duration: %d s | Threads: %d\n", duration, omp_get_max_threads());
    fflush(stdout);

    double t0 = omp_get_wtime();
    long long total_searched = 0;
    int best = 20350;
    int best_pos = -78;
    char bestbb[128] = "2LB1LA2LA_2RB2LA0LB|1RB0LB1RB_2LA2LA1RA";

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;
        uint64_t rng = (uint64_t)time(NULL) * 2654435761ULL ^ ((uint64_t)omp_get_thread_num() + 1) * 40503ULL;

        Machine2_3 c;
        long long local_count = 0;

        while (omp_get_wtime() - t0 < duration) {
            for (int a = 0; a < 2; a++) {
                for (int s = 0; s < 2; s++) {
                    for (int sym = 0; sym < 3; sym++) {
                        uint64_t v = splitmix64(&rng);
                        c.t[a][s][sym].write = v % 3;
                        c.t[a][s][sym].move = ((v >> 4) & 1) ? 1 : -1;
                        c.t[a][s][sym].next_state = (v >> 5) % 2;
                    }
                }
            }

            local_count++;

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
            int pos = 0;
            int s = screen_2_3(&c, tape, vis, mk, &pos);

            if (s > best || s == -2) {
                if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                s = simulate_deep_2_3(&c, tape, vis, mk, &pos);

                if (s > best) {
                    #pragma omp critical
                    {
                        if (s > best) {
                            best = s;
                            best_pos = pos;
                            fmt_3sym(&c, bestbb);
                            printf("\n🌟🌟🌟 NEW CET(2,3) RECORD: %d STEPS at cell %d! 🌟🌟🌟\n", s, pos);
                            printf("bbchallenge: %s\n", bestbb);
                            fflush(stdout);
                        }
                    }
                }
            }
        }

        #pragma omp atomic
        total_searched += local_count;

        free(tape); free(vis);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\n========================================================================\n");
    printf("🏁 Screened %lld fresh CET(2,3) machines in %.1fs (%.0f machines/sec)\n",
           total_searched, elapsed, total_searched / elapsed);
    printf("Final Best CET(2,3): %d steps at cell %d | %s\n", best, best_pos, bestbb);
    printf("========================================================================\n");

    return 0;
}
