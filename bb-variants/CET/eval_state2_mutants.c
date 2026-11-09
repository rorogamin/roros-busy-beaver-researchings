#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define CUTOFF 10000000ULL

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

int simulate_cet3(const M *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
    for (uint64_t step = 1; step <= CUTOFF; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) return -1;
        uint8_t r1 = vis[p1] == mk ? tape[p1] : 0;
        uint8_t r2 = vis[p2] == mk ? tape[p2] : 0;
        Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - TAPE_OFFSET; return (int)step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 4500) return -1;
    }
    return -2;
}

int main(void) {
    printf("Evaluating all 3-state mutations of Agent 2 that activate state 2...\n");

    // Base 3.74M machine:
    // A1: 1LC1LA_1LA0LC_1RC0LB
    // A2: 0LB0RA_1RA1LB_0RA0LB
    M base = {
        .t = {
            // A1
            {
                { {1, -1, 2}, {1, -1, 0} },
                { {1, -1, 0}, {0, -1, 2} },
                { {1,  1, 2}, {0, -1, 1} }
            },
            // A2
            {
                { {0, -1, 1}, {0,  1, 0} },
                { {1,  1, 0}, {1, -1, 1} },
                { {0,  1, 0}, {0, -1, 1} }
            }
        }
    };

    int best_step = 3746207;
    int best_pos = -9;
    char best_bb[128];
    fmt(&base, best_bb);

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;

        #pragma omp for collapse(3) schedule(dynamic)
        for (int entry_slot = 0; entry_slot < 4; entry_slot++) {
            for (int s2_sym0 = 0; s2_sym0 < 12; s2_sym0++) {
                for (int s2_sym1 = 0; s2_sym1 < 12; s2_sym1++) {
                    M cand = base;

                    // Configure state 2 transitions
                    cand.t[1][2][0].w = s2_sym0 % 2;
                    cand.t[1][2][0].mv = ((s2_sym0 / 2) % 2) ? 1 : -1;
                    cand.t[1][2][0].ns = s2_sym0 / 4;

                    cand.t[1][2][1].w = s2_sym1 % 2;
                    cand.t[1][2][1].mv = ((s2_sym1 / 2) % 2) ? 1 : -1;
                    cand.t[1][2][1].ns = s2_sym1 / 4;

                    // Redirect entry slot to state 2 (C)
                    int s_in = entry_slot / 2;
                    int r_in = entry_slot % 2;
                    cand.t[1][s_in][r_in].ns = 2;

                    if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }
                    int pos = 0;
                    int s = simulate_cet3(&cand, tape, vis, mk, &pos);

                    if (s > 100000) {
                        #pragma omp critical
                        {
                            if (s > best_step) {
                                best_step = s;
                                best_pos = pos;
                                fmt(&cand, best_bb);
                                printf("\n💥💥💥 NEW CET(3) RECORD: %d STEPS at cell %d! 💥💥💥\n", s, pos);
                                printf("bbchallenge: %s\n", best_bb);
                                fflush(stdout);
                            } else if (s > 500000) {
                                char bb[128]; fmt(&cand, bb);
                                printf("  Halt: %d steps | %s\n", s, bb);
                                fflush(stdout);
                            }
                        }
                    }
                }
            }
        }
        free(tape); free(vis);
    }

    printf("\nFinished evaluation. Best CET(3): %d steps | %s\n", best_step, best_bb);
    return 0;
}
