#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

typedef struct {
    uint8_t w;
    int8_t d;
    uint8_t ns;
} Trans;

typedef struct {
    Trans t[2][2];
} AgentTable;

static AgentTable g_tables[4096];

void init_tables() {
    for (int code = 0; code < 4096; code++) {
        for (int i = 0; i < 4; i++) {
            int bits = (code >> (i * 3)) & 7;
            int s = i / 2;
            int sym = i % 2;
            g_tables[code].t[s][sym].w = bits & 1;
            g_tables[code].t[s][sym].d = (bits & 2) ? 1 : -1;
            g_tables[code].t[s][sym].ns = (bits >> 2) & 1;
        }
    }
}

#define TAPE_SIZE 65536
#define TAPE_OFFSET 32768
static uint8_t tape[TAPE_SIZE];
static int visited[TAPE_SIZE];
static int visit_marker = 0;

int simulate_pruned(int code1, int code2, int max_steps) {
    visit_marker++;
    int pos1 = 0 + TAPE_OFFSET;
    int pos2 = 2 + TAPE_OFFSET;
    uint8_t state1 = 0;
    uint8_t state2 = 0;

    const AgentTable* a1 = &g_tables[code1];
    const AgentTable* a2 = &g_tables[code2];

    int min_mod = TAPE_OFFSET;
    int max_mod = TAPE_OFFSET + 2;

    for (int step = 0; step < max_steps; step++) {
        if (pos1 == pos2) {
            return step;
        }

        // Triangle inequality prune: agents move at most 1 cell per step.
        // Max approach speed is 2 cells/step.
        int dist = abs(pos1 - pos2);
        int rem = max_steps - step;
        if (dist > 2 * rem) {
            return -1;
        }

        // Infinite escape prune:
        // If pos1 is left of all modified cells (and pos2) and moving left on 0, and state transition on 0 doesn't reverse
        // Similarly for pos2 to the right.
        if (pos1 < min_mod && pos1 < pos2) {
            Trans tr0 = a1->t[state1][0];
            if (tr0.d == -1 && tr0.ns == state1 && tr0.w == 0) {
                // Agent 1 is trapped moving left forever on blank tape!
                // Can pos2 catch pos1? Pos2 can only move left at speed 1, Pos1 is moving left at speed 1, distance won't decrease!
                return -1;
            }
        }
        if (pos2 > max_mod && pos2 > pos1) {
            Trans tr0 = a2->t[state2][0];
            if (tr0.d == 1 && tr0.ns == state2 && tr0.w == 0) {
                // Agent 2 moving right forever on blank tape!
                return -1;
            }
        }

        if (pos1 < 100 || pos1 >= TAPE_SIZE - 100 || pos2 < 100 || pos2 >= TAPE_SIZE - 100) {
            return -1;
        }

        uint8_t sym1 = (visited[pos1] == visit_marker) ? tape[pos1] : 0;
        uint8_t sym2 = (visited[pos2] == visit_marker) ? tape[pos2] : 0;

        Trans tr1 = a1->t[state1][sym1];
        Trans tr2 = a2->t[state2][sym2];

        visited[pos1] = visit_marker;
        tape[pos1] = tr1.w;
        if (tr1.w != 0) {
            if (pos1 < min_mod) min_mod = pos1;
            if (pos1 > max_mod) max_mod = pos1;
        }

        visited[pos2] = visit_marker;
        tape[pos2] = tr2.w;
        if (tr2.w != 0) {
            if (pos2 < min_mod) min_mod = pos2;
            if (pos2 > max_mod) max_mod = pos2;
        }

        pos1 += tr1.d;
        state1 = tr1.ns;

        pos2 += tr2.d;
        state2 = tr2.ns;
    }
    return (pos1 == pos2) ? max_steps : -1;
}

int main() {
    init_tables();
    printf("Starting pruned search up to 10,000 steps across all 16.7M CET(2) machines...\n");
    clock_t start = clock();
    int max_s = 0;
    int best_c1 = -1, best_c2 = -1;

    for (int c1 = 0; c1 < 4096; c1++) {
        for (int c2 = 0; c2 < 4096; c2++) {
            int s = simulate_pruned(c1, c2, 10000);
            if (s > max_s) {
                max_s = s;
                best_c1 = c1;
                best_c2 = c2;
                printf("Record: %d steps (c1=%d, c2=%d)\n", max_s, best_c1, best_c2);
                fflush(stdout);
            }
        }
        if (c1 % 512 == 0) {
            printf("Progress: %d / 4096 (Current best: %d)\n", c1, max_s);
            fflush(stdout);
        }
    }
    clock_t end = clock();
    printf("Exhaustive search complete in %.2f s! Absolute maximum steps: %d (c1=%d, c2=%d)\n",
           (double)(end - start) / CLOCKS_PER_SEC, max_s, best_c1, best_c2);
    return 0;
}
