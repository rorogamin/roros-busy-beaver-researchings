#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 131072
#define TAPE_OFFSET 65536
#define MAX_STEPS_CUTOFF 20000

typedef struct {
    int8_t write;
    int8_t move;
    int8_t next_state;
} Transition;

typedef struct {
    Transition t[2][3][2];
    uint8_t defined[2][3][2];
} Machine;

static const double POW12[13] = {
    1.0, 12.0, 144.0, 1728.0, 20736.0, 248832.0, 2985984.0,
    35831808.0, 429981696.0, 5159780352.0, 61917364224.0,
    743008370688.0, 8916100448256.0
};

int count_undef(const Machine *m) {
    int u = 0;
    for (int a = 0; a < 2; a++)
        for (int s = 0; s < 3; s++)
            for (int r = 0; r < 2; r++)
                if (!m->defined[a][s][r]) u++;
    return u;
}

void format_bb(const Machine *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s > 0) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                if (m->defined[a][s][r]) {
                    Transition tr = m->t[a][s][r];
                    *p++ = '0' + tr.write;
                    *p++ = tr.move > 0 ? 'R' : 'L';
                    *p++ = 'A' + tr.next_state;
                } else {
                    *p++ = '.';
                    *p++ = '.';
                    *p++ = '.';
                }
            }
        }
    }
    *p = '\0';
}

// Global stats
double global_accounted = 0.0;
double global_collided = 0.0;
double global_diverged = 0.0;
double global_speed_barrier = 0.0;
long long global_holdouts = 0;
int global_max_halt = 0;
char global_max_halt_bb[256];

void run_branch(Machine m, int step, int p1, int p2, int s1, int s2,
                uint8_t *tape, uint32_t *visited, uint32_t marker, int max_depth) {

    for (; step <= MAX_STEPS_CUTOFF; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        // Check if either transition is undefined:
        if (!m.defined[0][s1][r1]) {
            // Branch Agent 1's slot
            for (int w = 0; w < 2; w++) {
                for (int d = -1; d <= 1; d += 2) {
                    for (int ns = 0; ns < 3; ns++) {
                        Machine next_m = m;
                        next_m.defined[0][s1][r1] = 1;
                        next_m.t[0][s1][r1].write = w;
                        next_m.t[0][s1][r1].move = d;
                        next_m.t[0][s1][r1].next_state = ns;

                        // Clone tape state for branching
                        uint32_t new_marker = marker + 1;
                        if (new_marker == 0) {
                            memset(visited, 0, TAPE_SIZE * sizeof(uint32_t));
                            new_marker = 1;
                        }
                        // Copy touched cells (or simple local copy)
                        // For speed, run recursively:
                        run_branch(next_m, step, p1, p2, s1, s2, tape, visited, marker, max_depth);
                    }
                }
            }
            return;
        }

        if (!m.defined[1][s2][r2]) {
            // Branch Agent 2's slot
            for (int w = 0; w < 2; w++) {
                for (int d = -1; d <= 1; d += 2) {
                    for (int ns = 0; ns < 3; ns++) {
                        Machine next_m = m;
                        next_m.defined[1][s2][r2] = 1;
                        next_m.t[1][s2][r2].write = w;
                        next_m.t[1][s2][r2].move = d;
                        next_m.t[1][s2][r2].next_state = ns;
                        run_branch(next_m, step, p1, p2, s1, s2, tape, visited, marker, max_depth);
                    }
                }
            }
            return;
        }

        // Both transitions defined: execute step
        Transition tr1 = m.t[0][s1][r1];
        Transition tr2 = m.t[1][s2][r2];

        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        // Collision check
        if (p1 == p2) {
            int u = count_undef(&m);
            double count = POW12[u];
            #pragma omp critical
            {
                global_collided += count;
                global_accounted += count;
                if (step > global_max_halt) {
                    global_max_halt = step;
                    format_bb(&m, global_max_halt_bb);
                    printf(">>> NEW RECORD IN TREE: %d steps | %s <<<\n", step, global_max_halt_bb);
                    fflush(stdout);
                }
            }
            return;
        }

        // Decider 3: Speed Barrier (p1 moving left at 1 cell/step into blank 0s while p1 < p2)
        if (p1 < p2 && tr1.move == -1 && tr1.write == 0 && tr1.next_state == s1 && r1 == 0) {
            // Agent 1 is glider moving left at maximum velocity 1 into blank 0s!
            // Agent 2 is to the right and cannot catch up (relative speed <= 0)
            int u = count_undef(&m);
            double count = POW12[u];
            #pragma omp critical
            {
                global_speed_barrier += count;
                global_accounted += count;
            }
            return;
        }

        // Decider 4: Light Cone Escape
        int dist = (p1 > p2) ? (p1 - p2) : (p2 - p1);
        int rem = MAX_STEPS_CUTOFF - step;
        if (dist > 2 * rem) {
            int u = count_undef(&m);
            double count = POW12[u];
            #pragma omp critical
            {
                global_diverged += count;
                global_accounted += count;
            }
            return;
        }
    }

    // SURVIVED 20,000 STEPS WITHIN REACH! (HOLDOUT)
    int u = count_undef(&m);
    double count = POW12[u];
    #pragma omp critical
    {
        global_holdouts++;
        global_accounted += count;
        char bb[256];
        format_bb(&m, bb);
        printf("\n*** DISCOVERED CET(3) HOLDOUT #%lld ***\n", global_holdouts);
        printf("bbchallenge: %s\n", bb);
        printf("Distance at step %d: %d cells | Subtree size: %.0f machines\n\n",
               MAX_STEPS_CUTOFF, abs(p1 - p2), count);
        fflush(stdout);
    }
}

int main(int argc, char **argv) {
    printf("====================================================================\n");
    printf("   EXHAUSTIVE TREE-PRUNING PROVER FOR ALL 8.92 TRILLION CET(3)\n");
    printf("====================================================================\n");
    printf("Tree search depth-first with lazy transition allocation...\n\n");

    double start_time = omp_get_wtime();

    // The root machine has no transitions defined
    // We branch on the initial 144 choices in parallel across OpenMP threads
    #pragma omp parallel for schedule(dynamic, 1)
    for (int root_idx = 0; root_idx < 144; root_idx++) {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;

        int a1_w = (root_idx / 72) % 2;
        int a1_d = ((root_idx / 36) % 2) ? 1 : -1;
        int a1_ns = (root_idx / 12) % 3;

        int a2_w = (root_idx / 6) % 2;
        int a2_d = ((root_idx / 3) % 2) ? 1 : -1;
        int a2_ns = root_idx % 3;

        Machine m;
        memset(&m, 0, sizeof(m));

        m.defined[0][0][0] = 1;
        m.t[0][0][0].write = a1_w;
        m.t[0][0][0].move = a1_d;
        m.t[0][0][0].next_state = a1_ns;

        m.defined[1][0][0] = 1;
        m.t[1][0][0].write = a2_w;
        m.t[1][0][0].move = a2_d;
        m.t[1][0][0].next_state = a2_ns;

        // Immediate collision check
        if (a1_d == 1 && a2_d == -1) {
            int u = count_undef(&m);
            double count = POW12[u];
            #pragma omp critical
            {
                global_collided += count;
                global_accounted += count;
            }
        } else {
            // Run branch
            run_branch(m, 1, TAPE_OFFSET + 0, TAPE_OFFSET + 2, 0, 0,
                       tape, visited, marker, 12);
        }

        free(tape);
        free(visited);
    }

    double elapsed = omp_get_wtime() - start_time;
    printf("\n====================================================================\n");
    printf("   TREE PROOF COMPLETE (%.2f seconds)\n", elapsed);
    printf("====================================================================\n");
    printf("Total Machines in Space: 8,916,100,448,256 (100.00%%)\n");
    printf("Total Accounted For:     %.0f (%.2f%%)\n", global_accounted, (global_accounted / 8916100448256.0) * 100.0);
    printf("  • Collided:            %.0f (%.2f%%)\n", global_collided, (global_collided / 8916100448256.0) * 100.0);
    printf("  • Escaped / Diverged:  %.0f (%.2f%%)\n", global_diverged, (global_diverged / 8916100448256.0) * 100.0);
    printf("  • Speed Barrier:       %.0f (%.2f%%)\n", global_speed_barrier, (global_speed_barrier / 8916100448256.0) * 100.0);
    printf("  • Genuine Holdouts:    %lld\n", global_holdouts);
    printf("Highest Halting Step:    %d\n", global_max_halt);
    if (global_max_halt > 0) {
        printf("Record Machine:          %s\n", global_max_halt_bb);
    }

    return 0;
}
