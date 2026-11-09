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
    Trans t[2][2]; // [state][sym]
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

// Tape size for checking collision up to 10000 steps
#define TAPE_SIZE 32768
#define TAPE_OFFSET 16384
static uint8_t tape[TAPE_SIZE];
static int visited[TAPE_SIZE];
static int visit_marker = 0;

int simulate(int code1, int code2, int max_steps) {
    visit_marker++;
    int pos1 = 0 + TAPE_OFFSET;
    int pos2 = 2 + TAPE_OFFSET;
    uint8_t state1 = 0;
    uint8_t state2 = 0;

    const AgentTable* a1 = &g_tables[code1];
    const AgentTable* a2 = &g_tables[code2];

    for (int step = 0; step < max_steps; step++) {
        if (pos1 == pos2) {
            return step;
        }
        if (pos1 < 100 || pos1 >= TAPE_SIZE - 100 || pos2 < 100 || pos2 >= TAPE_SIZE - 100) {
            return -1; // Drifted off
        }

        uint8_t sym1 = (visited[pos1] == visit_marker) ? tape[pos1] : 0;
        uint8_t sym2 = (visited[pos2] == visit_marker) ? tape[pos2] : 0;

        Trans tr1 = a1->t[state1][sym1];
        Trans tr2 = a2->t[state2][sym2];

        visited[pos1] = visit_marker;
        tape[pos1] = tr1.w;

        visited[pos2] = visit_marker;
        tape[pos2] = tr2.w;

        pos1 += tr1.d;
        state1 = tr1.ns;

        pos2 += tr2.d;
        state2 = tr2.ns;
    }
    return (pos1 == pos2) ? max_steps : -1;
}

int main() {
    init_tables();
    printf("Testing user 97-step machine (485, 3663)...\n");
    int s = simulate(485, 3663, 10000);
    printf("Result: %d steps\n", s);

    printf("Running fast search across all 16.7 million CET(2) machines...\n");
    clock_t start = clock();
    int max_steps = 0;
    int best_c1 = -1, best_c2 = -1;

    // To be fast, let's search with step limit 2000
    long long checked = 0;
    for (int c1 = 0; c1 < 4096; c1++) {
        for (int c2 = 0; c2 < 4096; c2++) {
            int res = simulate(c1, c2, 1000);
            checked++;
            if (res > max_steps) {
                max_steps = res;
                best_c1 = c1;
                best_c2 = c2;
                printf("New record: %d steps at c1=%d, c2=%d\n", max_steps, best_c1, best_c2);
            }
        }
    }
    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;
    printf("Finished %lld machines in %.2f seconds (%.0f machines/sec)!\n", checked, elapsed, checked / elapsed);
    printf("Maximum steps found: %d (c1=%d, c2=%d)\n", max_steps, best_c1, best_c2);
    return 0;
}
