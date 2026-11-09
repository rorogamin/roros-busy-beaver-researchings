#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

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

int simulate_deep(int code1, int code2, int max_steps) {
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
            return -1;
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
    // Sample machines that didn't collide before 1000 steps:
    // Let's test a higher limit, say 10000 steps on machines where min distance between agents is small.
    printf("Checking if ANY machine halts between 98 and 10000 steps...\n");
    int count_between = 0;
    int max_s = 97;
    int best_c1 = 485, best_c2 = 3663;

    for (int c1 = 0; c1 < 4096; c1++) {
        for (int c2 = 0; c2 < 4096; c2++) {
            // First quick check: if it halts in <= 97 steps, we know it's <= 97
            // We only simulate up to 5000 steps
            int s = simulate_deep(c1, c2, 5000);
            if (s > 97) {
                count_between++;
                if (s > max_s) {
                    max_s = s;
                    best_c1 = c1;
                    best_c2 = c2;
                    printf("FOUND > 97! Steps: %d (c1=%d, c2=%d)\n", max_s, best_c1, best_c2);
                }
            }
        }
        if (c1 % 512 == 0) {
            printf("Progress: %d / 4096\n", c1);
            fflush(stdout);
        }
    }
    printf("Total found > 97: %d. Max: %d\n", count_between, max_s);
    return 0;
}
