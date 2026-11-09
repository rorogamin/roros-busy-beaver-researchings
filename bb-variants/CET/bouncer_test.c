#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define TAPE_SIZE 1048576
#define TAPE_OFFSET 524288

typedef struct {
    uint8_t write;
    int8_t move;
    uint8_t next_state;
} Transition;

typedef struct {
    Transition t[2][3][2];
} Machine2;

void format_bb(const Machine2 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s > 0) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                Transition tr = m->t[a][s][r];
                *p++ = '0' + tr.write;
                *p++ = tr.move > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.next_state;
            }
        }
    }
    *p = '\0';
}

int main() {
    // Let's create an artificial bouncer / holdout candidate:
    // Agent 1: sweeps between 0 and 4 forever (a bouncer)
    // Agent 2: sweeps between 10 and 14 forever (a bouncer)
    // They are both bounded, never escape to infinity, yet NEVER collide!
    // That is a genuine bouncer holdout!
    
    // In BB(3), can an agent be a bouncer on blank tape?
    // Let's test if 3-state TMs can bounce between boundaries:
    printf("Investigating 3-state bouncer capabilities...\n");
    return 0;
}
