#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define TAPE_SIZE 30000000
#define CENTER    15000000
#define MAX_STEPS 25000000LL

typedef struct { int8_t w, d, ns; } Tr;

// Nath76's 9,448,838 steps machine:
// agent 0: 0RB_0LC_0LC_1RA_1LA_0LB -> 0RB0LC_0LC1RA_1LA0LB
// agent 1: 1RB_1LC_0LC_0RC_1RA_1LA -> 1RB1LC_0LC0RC_1RA1LA

static const Tr ag0[3][2] = {
    { {0,  1, 1}, {0, -1, 2} }, // A0: 0RB, A1: 0LC
    { {0, -1, 2}, {1,  1, 0} }, // B0: 0LC, B1: 1RA
    { {1, -1, 0}, {0, -1, 1} }  // C0: 1LA, C1: 0LB
};

static const Tr ag1[3][2] = {
    { {1,  1, 1}, {1, -1, 2} }, // A0: 1RB, A1: 1LC
    { {0, -1, 2}, {0,  1, 2} }, // B0: 0LC, B1: 0RC
    { {1,  1, 0}, {1, -1, 0} }  // C0: 1RA, C1: 1LA
};

int main() {
    uint8_t *tape = (uint8_t *)calloc(TAPE_SIZE, 1);
    int p0 = CENTER;
    int p1 = CENTER + 2;
    int s0 = 0, s1 = 0;
    int min_p = p0, max_p = p1;

    printf("Verifying Nath76's 9,448,838-step CET(3) champion...\n");
    for (long long step = 1; step <= MAX_STEPS; step++) {
        uint8_t r0 = tape[p0];
        uint8_t r1 = tape[p1];

        Tr t0 = ag0[s0][r0];
        Tr t1 = ag1[s1][r1];

        tape[p1] = t1.w;
        tape[p0] = t0.w; // Agent 0 priority on same cell

        p0 += t0.d; s0 = t0.ns;
        p1 += t1.d; s1 = t1.ns;

        if (p0 < min_p) min_p = p0; if (p0 > max_p) max_p = p0;
        if (p1 < min_p) min_p = p1; if (p1 > max_p) max_p = p1;

        if (p0 == p1) {
            long long ones = 0;
            for (int i = min_p; i <= max_p; i++) ones += tape[i];
            printf("CONFIRMED COLLISION at step %lld on cell x = %d!\n", step, p0 - CENTER);
            printf("Tape span: [%d, %d] (%d cells), Ones on tape: %lld\n",
                   min_p - CENTER, max_p - CENTER, max_p - min_p + 1, ones);
            free(tape);
            return 0;
        }
    }
    printf("Did not collide within %lld steps!\n", MAX_STEPS);
    free(tape);
    return 1;
}
