#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define TAPE_SIZE 100000000
#define ORIGIN     50000000

static uint8_t tape[TAPE_SIZE];

typedef struct {
    int w;
    int mv;
    int ns;
} Trans;

// Agent 1: 1RA1RB_1LA0LB
// State A: 0->1RA, 1->1RB
// State B: 0->1LA, 1->0LB
static Trans ag1[2][2] = {
    { {1, 1, 0}, {1, 1, 1} },
    { {1, -1, 0}, {0, -1, 1} }
};

// Agent 2: 1LA0RB_0LA1RB
// State A: 0->1LA, 1->0RB
// State B: 0->0LA, 1->1RB
static Trans ag2[2][2] = {
    { {1, -1, 0}, {0, 1, 1} },
    { {0, -1, 0}, {1, 1, 1} }
};

int main() {
    int p1 = 0;
    int p2 = 2;
    int s1 = 0;
    int s2 = 0;
    
    long long cols = 0;
    long long lastCol = 0;
    int min_p2 = 0;
    int max_p2 = 2;

    printf("Starting ultra-deep simulation of 1399 machine...\n");
    fflush(stdout);

    for (long long step = 1; step <= 500000000LL; step++) {
        int idx1 = ORIGIN + p1;
        int idx2 = ORIGIN + p2;
        
        int r1 = tape[idx1];
        int r2 = tape[idx2];
        
        Trans t1 = ag1[s1][r1];
        Trans t2 = ag2[s2][r2];
        
        // Write order: p2 then p1 (if p1==p2, p1 wins)
        tape[idx2] = t2.w;
        tape[idx1] = t1.w;
        
        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;
        
        if (p2 < min_p2) {
            min_p2 = p2;
            if (min_p2 <= -11) {
                printf("Step %lld: NEW MIN P2 = %d (p1=%d, dist=%d)\n", step, min_p2, p1, p2 - p1);
                fflush(stdout);
            }
        }
        if (p2 > max_p2) {
            max_p2 = p2;
            if (max_p2 % 50 == 0) {
                printf("Step %lld: NEW MAX P2 = %d\n", step, max_p2);
                fflush(stdout);
            }
        }
        
        if (p1 == p2) {
            cols++;
            lastCol = step;
            printf("*** COLLISION #%lld at step %lld on cell %d! ***\n", cols, step, p1);
            fflush(stdout);
        }
        
        if (step % 50000000LL == 0) {
            printf("Progress: step = %lld | p1 = %d, p2 = %d | min_p2 = %d, max_p2 = %d | collisions = %lld\n", 
                   step, p1, p2, min_p2, max_p2, cols);
            fflush(stdout);
        }
    }
    printf("Finished 500M steps! Total collisions: %lld, Last collision: %lld\n", cols, lastCol);
    return 0;
}
