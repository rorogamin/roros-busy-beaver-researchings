#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define TAPE_SIZE 20000000
#define ORIGIN    10000000

static uint8_t tape[TAPE_SIZE];

typedef struct { int w, mv, ns; } Tr;

// Agent 1: 1RB1LA_0LA0RB
// State A: 0->1RB, 1->1LA
// State B: 0->0LA, 1->0RB
static Tr ag1[2][2] = {
    { {1, 1, 1}, {1, -1, 0} },
    { {0, -1, 0}, {0, 1, 1} }
};

// Agent 2: 0LB1RA_1RA1LB
// State A: 0->0LB, 1->1RA
// State B: 0->1RA, 1->1LB
static Tr ag2[2][2] = {
    { {0, -1, 1}, {1, 1, 0} },
    { {1, 1, 0}, {1, -1, 1} }
};

int main() {
    int p1 = 0, p2 = 2;
    int s1 = 0, s2 = 0;
    long long cols = 0;
    long long last_col = 0;

    printf("Simulating Candidate 8540 up to 10,000,000 steps...\n");

    for (long long step = 1; step <= 10000000LL; step++) {
        int idx1 = ORIGIN + p1;
        int idx2 = ORIGIN + p2;

        int r1 = tape[idx1];
        int r2 = tape[idx2];

        Tr t1 = ag1[s1][r1];
        Tr t2 = ag2[s2][r2];

        tape[idx2] = t2.w;
        tape[idx1] = t1.w;

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        if (p1 == p2) {
            cols++;
            last_col = step;
            if (cols > 16) {
                printf("💥 Collision #%lld at step %lld on cell %d!\n", cols, step, p1);
                fflush(stdout);
            }
        }

        if (step % 2000000LL == 0) {
            printf("Step %lld: p1=%d, p2=%d, dist=%d, cols=%lld, last_col=%lld\n",
                   step, p1, p2, p2 - p1, cols, last_col);
            fflush(stdout);
        }
    }

    printf("Done 10M steps! Total cols = %lld, last_col = %lld\n", cols, last_col);
    return 0;
}
