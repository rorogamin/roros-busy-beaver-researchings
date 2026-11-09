#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define CUTOFF 10000000ULL

typedef struct {
    uint8_t w;
    int8_t d;
    uint8_t ns;
} Tr3;

typedef struct {
    Tr3 t[3][2];
} Agent3;

// Decode integer in 0..2985983 to 3-state agent table
void decode_agent3(int code, Agent3 *a) {
    int c = code;
    for (int s = 0; s < 3; s++) {
        for (int sym = 0; sym < 2; sym++) {
            int val = c % 12;
            c /= 12;
            a->t[s][sym].w = val % 2;
            a->t[s][sym].d = ((val / 2) % 2) ? 1 : -1;
            a->t[s][sym].ns = val / 4;
        }
    }
}

// Fixed 3-state Agent 1: cruises left at speed 1/3 (1 cell every 3 steps)
// 0: (0, LEFT, 1), 1: (0, LEFT, 2), 2: (0, RIGHT, 0)
static inline int get_p1(uint64_t t) {
    int k = (int)(t / 3);
    int rem = (int)(t % 3);
    if (rem == 0) return -k;
    if (rem == 1) return -(k + 1);
    return -(k + 2);
}

int main(int argc, char **argv) {
    printf("========================================================================\n");
    printf("⚡ EXHAUSTIVE ENUMERATION OF ALL 2,985,984 CET(3) AGENT 2 MACHINES\n");
    printf("========================================================================\n");
    printf("Agent 1 fixed as speed-1/3 leftward cruiser | threads=%d\n", omp_get_max_threads());
    fflush(stdout);

    int total_machines = 2985984;
    int global_best_steps = 3746207;
    int global_best_code = -1;
    int global_best_pos = 0;

    double t0 = omp_get_wtime();

    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        uint32_t mk = 0;

        #pragma omp for schedule(dynamic, 1024)
        for (int code = 0; code < total_machines; code++) {
            Agent3 a2;
            decode_agent3(code, &a2);

            if (++mk == 0) { memset(vis, 0, TAPE_SIZE * 4); mk = 1; }

            int p2 = TAPE_OFFSET + 2;
            int s2 = 0;
            int halted = 0;
            uint64_t halt_step = 0;
            int halt_pos = 0;

            for (uint64_t step = 1; step <= CUTOFF; step++) {
                if (p2 <= 100 || p2 >= TAPE_SIZE - 100) break;

                uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
                Tr3 tr2 = a2.t[s2][r2];
                vis[p2] = mk; tape[p2] = tr2.w;
                p2 += tr2.d;
                s2 = tr2.ns;

                int p1 = get_p1(step);
                if (p2 - TAPE_OFFSET == p1) {
                    halted = 1;
                    halt_step = step;
                    halt_pos = p1;
                    break;
                }

                // If A2 runs to the far right (> 5000), it will never catch A1
                if (p2 - TAPE_OFFSET > 4000) break;
            }

            if (halted && halt_step > 500000) {
                #pragma omp critical
                {
                    if (halt_step > global_best_steps) {
                        global_best_steps = (int)halt_step;
                        global_best_code = code;
                        global_best_pos = halt_pos;
                        printf("\n💥💥💥 >>> NEW CET(3) RECORD: %llu STEPS at cell %d (code %d)! <<< 💥💥💥\n", halt_step, halt_pos, code);
                        fflush(stdout);
                    } else if (halt_step > 1000000) {
                        printf("  Notable 1M+ halt: %llu steps at cell %d (code %d)\n", halt_step, halt_pos, code);
                        fflush(stdout);
                    }
                }
            }
        }
        free(tape); free(vis);
    }

    double elapsed = omp_get_wtime() - t0;
    printf("\nExhaustive search finished in %.2f s.\n", elapsed);
    printf("Best CET(3) Step Count: %d steps\n", global_best_steps);
    return 0;
}
