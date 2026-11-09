// verify_all_champions.c
// Complete, exact, ground-truth verifier for all major normal-halting Catch-Em-Turing champions:
// 1. CET(1)        : 1 step
// 2. CET(2)        : 97 steps
// 3. CET(3) 26.12M : 26,121,565 steps
// 4. MCET(3)       : 211,190,346 steps
// 5. CET(2, 3 sym) : 1,528,952,999 steps
// 6. CET(3) 3.092B : 3,092,745,703 steps
// 7. CET(4) 4.622B : 4,622,083,548 steps

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define TAPE_SIZE 33554432
#define TAPE_OFFSET 16777216

typedef struct {
    uint8_t w;
    int8_t m;
    uint8_t n;
} Trans;

typedef struct {
    Trans t[2][4][3]; // up to 2 agents, 4 states, 3 symbols
    int n_agents;
    int n_states;
    int n_symbols;
} TM2;

static int parse_tm2(const char* spec, int n_agents, int n_states, int n_symbols, TM2* tm) {
    memset(tm, 0, sizeof(*tm));
    tm->n_agents = n_agents;
    tm->n_states = n_states;
    tm->n_symbols = n_symbols;

    const char* p = spec;
    for (int a = 0; a < n_agents; a++) {
        for (int q = 0; q < n_states; q++) {
            for (int s = 0; s < n_symbols; s++) {
                while (*p == '_' || *p == '|' || *p == ' ') p++;
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

// 2-Agent Simulation
static void verify_2agent(const char* name, const char* spec, int n_states, int n_symbols, uint64_t max_steps) {
    printf("=================================================================\n");
    printf("Verifying %s\n", name);
    printf("Spec: %s\n", spec);
    fflush(stdout);

    TM2 tm;
    if (parse_tm2(spec, 2, n_states, n_symbols, &tm) < 0) {
        printf("ERROR: Failed to parse specification!\n");
        return;
    }

    uint8_t* tape = (uint8_t*)calloc(TAPE_SIZE, 1);
    if (!tape) {
        printf("ERROR: Failed to allocate tape!\n");
        return;
    }

    int p0 = 0, p1 = 2;
    int q0 = 0, q1 = 0;
    int min_p = 0, max_p = 2;
    int max_dist = 2;

    clock_t t0 = clock();
    uint64_t step = 0;
    int halted = 0;

    for (step = 1; step <= max_steps; step++) {
        int idx0 = p0 + TAPE_OFFSET;
        int idx1 = p1 + TAPE_OFFSET;

        int b0 = tape[idx0];
        int b1 = tape[idx1];

        Trans tr0 = tm.t[0][q0][b0];
        Trans tr1 = tm.t[1][q1][b1];

        if (p0 == p1) {
            tape[idx0] = tr0.w;
        } else {
            tape[idx0] = tr0.w;
            tape[idx1] = tr1.w;
        }

        p0 += tr0.m; q0 = tr0.n;
        p1 += tr1.m; q1 = tr1.n;

        if (p0 < min_p) min_p = p0;
        if (p0 > max_p) max_p = p0;
        if (p1 < min_p) min_p = p1;
        if (p1 > max_p) max_p = p1;
        int dist = (p0 > p1) ? (p0 - p1) : (p1 - p0);
        if (dist > max_dist) max_dist = dist;

        if (p0 == p1) {
            halted = 1;
            break;
        }

        if ((step % 500000000ULL) == 0) {
            double cur_el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            printf("  ... reached %llu Msteps (p0=%d, p1=%d, time=%.1fs)\n",
                   (unsigned long long)(step / 1000000ULL), p0, p1, cur_el);
            fflush(stdout);
        }
    }

    double elapsed = (double)(clock() - t0) / CLOCKS_PER_SEC;

    if (halted) {
        int nonzeros = 0;
        for (int x = min_p; x <= max_p; x++) {
            if (tape[x + TAPE_OFFSET] != 0) nonzeros++;
        }
        printf("✔ NORMAL HALT (Collision Confirmed!)\n");
        printf("  Collision Step: %llu\n", (unsigned long long)step);
        printf("  Collision Cell: x = %d\n", p0);
        printf("  Tape Bounds:    [%d, %d] (span = %d cells)\n", min_p, max_p, max_p - min_p + 1);
        printf("  Non-zero Cells: %d\n", nonzeros);
        printf("  Max Separation: %d cells\n", max_dist);
        printf("  Execution Time: %.3f s (%.1f Msteps/sec)\n", elapsed, (step / 1000000.0) / (elapsed > 0 ? elapsed : 0.001));
    } else {
        printf("✘ NO COLLISION within %llu steps (p0=%d, p1=%d)\n", (unsigned long long)max_steps, p0, p1);
    }
    printf("=================================================================\n\n");
    fflush(stdout);
    free(tape);
}

// 3-Agent MCET Simulation
static void verify_mcet3(const char* name, const char* spec, uint64_t max_steps) {
    printf("=================================================================\n");
    printf("Verifying %s\n", name);
    printf("Spec: %s\n", spec);
    fflush(stdout);

    Trans t[3][3][2];
    memset(t, 0, sizeof(t));
    const char* p = spec;
    for (int a = 0; a < 3; a++) {
        for (int q = 0; q < 3; q++) {
            for (int s = 0; s < 2; s++) {
                while (*p == '_' || *p == '|' || *p == ' ') p++;
                if (!*p) { printf("ERROR: Bad spec\n"); return; }
                t[a][q][s].w = p[0] - '0';
                t[a][q][s].m = (p[1] == 'R') ? 1 : -1;
                t[a][q][s].n = p[2] - 'A';
                p += 3;
            }
        }
    }

    uint8_t* tape = (uint8_t*)calloc(TAPE_SIZE, 1);
    int pos[3] = {0, 2, 4};
    int st[3] = {0, 0, 0};
    int min_p = 0, max_p = 4;
    int max_dist = 4;

    clock_t t0 = clock();
    uint64_t step = 0;
    int halted = 0;

    for (step = 1; step <= max_steps; step++) {
        int idx0 = pos[0] + TAPE_OFFSET;
        int idx1 = pos[1] + TAPE_OFFSET;
        int idx2 = pos[2] + TAPE_OFFSET;

        int b0 = tape[idx0], b1 = tape[idx1], b2 = tape[idx2];
        Trans tr0 = t[0][st[0]][b0];
        Trans tr1 = t[1][st[1]][b1];
        Trans tr2 = t[2][st[2]][b2];

        tape[idx2] = tr2.w;
        tape[idx1] = tr1.w;
        tape[idx0] = tr0.w;

        pos[0] += tr0.m; st[0] = tr0.n;
        pos[1] += tr1.m; st[1] = tr1.n;
        pos[2] += tr2.m; st[2] = tr2.n;

        for (int a = 0; a < 3; a++) {
            if (pos[a] < min_p) min_p = pos[a];
            if (pos[a] > max_p) max_p = pos[a];
        }

        if (pos[0] == pos[1] && pos[1] == pos[2]) {
            halted = 1;
            break;
        }

        if ((step % 50000000ULL) == 0) {
            double cur_el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            printf("  ... reached %llu Msteps (time=%.1fs)\n", (unsigned long long)(step / 1000000ULL), cur_el);
            fflush(stdout);
        }
    }

    double elapsed = (double)(clock() - t0) / CLOCKS_PER_SEC;

    if (halted) {
        int nonzeros = 0;
        for (int x = min_p; x <= max_p; x++) {
            if (tape[x + TAPE_OFFSET] != 0) nonzeros++;
        }
        printf("✔ NORMAL HALT (All 3 Agents Collided!)\n");
        printf("  Collision Step: %llu\n", (unsigned long long)step);
        printf("  Collision Cell: x = %d\n", pos[0]);
        printf("  Tape Bounds:    [%d, %d] (span = %d cells)\n", min_p, max_p, max_p - min_p + 1);
        printf("  Non-zero Cells: %d\n", nonzeros);
        printf("  Execution Time: %.3f s (%.1f Msteps/sec)\n", elapsed, (step / 1000000.0) / (elapsed > 0 ? elapsed : 0.001));
    } else {
        printf("✘ NO COLLISION within %llu steps\n", (unsigned long long)max_steps);
    }
    printf("=================================================================\n\n");
    fflush(stdout);
    free(tape);
}

int main(int argc, char** argv) {
    setvbuf(stdout, NULL, _IONBF, 0);

    printf("=================================================================\n");
    printf("CATCH-EM-TURING NORMAL HALTING (COLLISION) VERIFICATION SUITE\n");
    printf("=================================================================\n\n");

    // 1. CET(1)
    verify_2agent("CET(1) Champion", "0RA0RA|0LA0LA", 1, 2, 100ULL);

    // 2. CET(2)
    verify_2agent("CET(2) Champion (Nath76 / 97 steps)",
                  "1LB0LB_1RB0LA|1RB1LA_1LA1RB", 2, 2, 1000ULL);

    // 3. CET(3) 986k New TNF Record
    verify_2agent("CET(3) 986k TNF Discovery",
                  "0LB0LC_1RB0LA_0RB0LA|1RB1LA_1LC0RC_0LA1RC", 3, 2, 2000000ULL);

    // 4. CET(3) 26.12M Record
    verify_2agent("CET(3) 26.12M Record",
                  "0RB0LC_1LC1RB_1RC1LA|1RB1LB_0RC0RA_1LC0RB", 3, 2, 50000000ULL);

    // 5. MCET(3) 211.19M Champion
    verify_mcet3("MCET(3) Champion (3 agents, 211.19M steps)",
                 "1LC1LA_1RA1RB_0RB0RA|1LC1LB_1RC1RB_0LC0RA|0LA1RB_0RC1RB_0RA1RC",
                 300000000ULL);

    // 6. CET(2, 3-symbol) 1.528B Champion
    verify_2agent("CET(2, 3 sym) Champion (1.528B steps)",
                  "1RB0RA2LB_2LA2RB1LB|2RB0RA2RB_2LB1RA0RB", 2, 3, 2000000000ULL);

    // 7. CET(3) 3.092B Champion
    verify_2agent("CET(3) Champion (3.092B steps)",
                  "0LB0LC_1RB1LA_1RC0LA|1LB0RC_1RA1LB_0LB1RC", 3, 2, 4000000000ULL);

    // 8. CET(4) 4.622B Champion
    verify_2agent("CET(4) Champion (4.622B steps)",
                  "1LC0LC_1LA1RB_0RB1LC_0RA0RA|1RC0RA_1RA1RB_1LC0RD_0RA0RC", 4, 2, 5000000000ULL);

    return 0;
}
