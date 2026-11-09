#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

#define TAPE_SIZE 65536
#define CENTER    32768
#define MAX_STEPS 30000000LL

typedef struct { int8_t w, d, ns; } Tr;

// Seeds:
// Seed 0: Nath76 9,448,838: 0RB0LC_0LC1RA_1LA0LB | 1RB1LC_0LC0RC_1RA1LA
// Seed 1: Nath76 4,657,368: 0LB0LB_0RC1LA_1LB1RC | 0RB1RC_1RC0RA_1LC0LB
// Seed 2: 3,746,207: let's include all known champions

typedef struct {
    const char *name;
    Tr a0[3][2];
    Tr a1[3][2];
} SeedMachine;

static const SeedMachine seeds[] = {
    {
        "Nath76_9.44M",
        { { {0,  1, 1}, {0, -1, 2} }, { {0, -1, 2}, {1,  1, 0} }, { {1, -1, 0}, {0, -1, 1} } },
        { { {1,  1, 1}, {1, -1, 2} }, { {0, -1, 2}, {0,  1, 2} }, { {1,  1, 0}, {1, -1, 0} } }
    },
    {
        "Nath76_4.65M",
        { { {0, -1, 1}, {0, -1, 1} }, { {0,  1, 2}, {1, -1, 0} }, { {1, -1, 1}, {1,  1, 2} } },
        { { {0,  1, 1}, {1,  1, 2} }, { {1,  1, 2}, {0,  1, 0} }, { {1, -1, 2}, {0, -1, 1} } }
    }
};

void decode_slot(int code, Tr *tr) {
    // code in 0..11: w (0..1), d (0->-1, 1->+1), ns (0..2)
    tr->w = code & 1;
    tr->d = ((code >> 1) & 1) ? 1 : -1;
    tr->ns = code >> 2;
}

void fmt_agent(const Tr t[3][2], char *buf) {
    char *p = buf;
    for (int s = 0; s < 3; s++) {
        if (s > 0) *p++ = '_';
        for (int sym = 0; sym < 2; sym++) {
            *p++ = '0' + t[s][sym].w;
            *p++ = t[s][sym].d > 0 ? 'R' : 'L';
            *p++ = 'A' + t[s][sym].ns;
        }
    }
    *p = 0;
}

long long run_fast(const Tr a0[3][2], const Tr a1[3][2], uint8_t *tape, uint32_t *vis, uint32_t mk) {
    int p0 = CENTER;
    int p1 = CENTER + 2;
    int s0 = 0, s1 = 0;
    int last_dist = 2;
    int streak = 0;

    for (long long step = 1; step <= MAX_STEPS; step++) {
        uint8_t r0 = (vis[p0] == mk) ? tape[p0] : 0;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;

        Tr t0 = a0[s0][r0];
        Tr t1 = a1[s1][r1];

        tape[p1] = t1.w; vis[p1] = mk;
        tape[p0] = t0.w; vis[p0] = mk;

        p0 += t0.d; s0 = t0.ns;
        p1 += t1.d; s1 = t1.ns;

        if (p0 == p1) return step;

        if ((p0 <= 16) | (p0 >= TAPE_SIZE - 16) | (p1 <= 16) | (p1 >= TAPE_SIZE - 16)) {
            return -1; // Out of compact bounds -> escaped glider
        }

        // Fast linear escape pruning every 4096 steps
        if ((step & 4095) == 0) {
            int dist = abs(p1 - p0);
            int delta = dist - last_dist;
            if (delta > 3600) {
                streak++;
                if (streak >= 4) return -2; // Monotonic linear divergence
            } else {
                streak = 0;
            }
            last_dist = dist;
        }
    }
    return -3; // Holdout > MAX_STEPS
}

typedef struct {
    int slot1, code1;
    int slot2, code2;
} Task2;

int main() {
    printf("=== CET(3) 1-MUTANT AND 2-MUTANT NEIGHBORHOOD SWEEP ===\n");
    fflush(stdout);

    long long global_best = 9448838LL;

    for (int s_idx = 0; s_idx < 2; s_idx++) {
        const SeedMachine *seed = &seeds[s_idx];
        printf("\n--- Sweeping 1-mutants and 2-mutants of %s ---\n", seed->name);
        fflush(stdout);

        // Generate all 1-mutants and 2-mutants
        // 12 slots total (0..5 in a0, 6..11 in a1), 12 choices per slot
        int cap = 12000;
        Task2 *tasks = (Task2 *)malloc(sizeof(Task2) * cap);
        int n_tasks = 0;

        // 1-mutants
        for (int i = 0; i < 12; i++) {
            for (int c1 = 0; c1 < 12; c1++) {
                tasks[n_tasks++] = (Task2){i, c1, -1, -1};
            }
        }
        // 2-mutants
        for (int i = 0; i < 12; i++) {
            for (int j = i + 1; j < 12; j++) {
                for (int c1 = 0; c1 < 12; c1++) {
                    for (int c2 = 0; c2 < 12; c2++) {
                        tasks[n_tasks++] = (Task2){i, c1, j, c2};
                    }
                }
            }
        }

        printf("Total mutant configurations queued: %d\n", n_tasks);
        fflush(stdout);

        #pragma omp parallel
        {
            uint8_t *tape = (uint8_t *)calloc(TAPE_SIZE, 1);
            uint32_t *vis = (uint32_t *)calloc(TAPE_SIZE, sizeof(uint32_t));
            uint32_t mk = 1;

            #pragma omp for schedule(dynamic, 32)
            for (int t = 0; t < n_tasks; t++) {
                Tr a0[3][2], a1[3][2];
                memcpy(a0, seed->a0, sizeof(a0));
                memcpy(a1, seed->a1, sizeof(a1));

                int s1 = tasks[t].slot1;
                if (s1 < 6) decode_slot(tasks[t].code1, &a0[s1 / 2][s1 % 2]);
                else        decode_slot(tasks[t].code1, &a1[(s1 - 6) / 2][(s1 - 6) % 2]);

                int s2 = tasks[t].slot2;
                if (s2 >= 0) {
                    if (s2 < 6) decode_slot(tasks[t].code2, &a0[s2 / 2][s2 % 2]);
                    else        decode_slot(tasks[t].code2, &a1[(s2 - 6) / 2][(s2 - 6) % 2]);
                }

                mk++;
                long long steps = run_fast(a0, a1, tape, vis, mk);

                if (steps >= 4000000LL) {
                    char str0[32], str1[32];
                    fmt_agent(a0, str0);
                    fmt_agent(a1, str1);
                    #pragma omp critical
                    {
                        if (steps > global_best) {
                            global_best = steps;
                            printf("\n🔥🏆 NEW WORLD RECORD: %lld steps! | %s|%s\n", steps, str0, str1);
                        } else if (steps > 4657368LL && steps != 9448838LL) {
                            printf("★ High Step Mutant: %lld steps | %s|%s\n", steps, str0, str1);
                        }
                        fflush(stdout);
                    }
                }
            }

            free(tape);
            free(vis);
        }

        free(tasks);
    }

    printf("\nMutant neighborhood sweep complete!\n");
    return 0;
}
