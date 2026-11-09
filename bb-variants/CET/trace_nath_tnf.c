// trace_nath_tnf.c
// Traces the exact Joint TNF branch decisions that lead to Nath76's 9.44M and 4.65M champions,
// and tests how many total leaf nodes exist in a Joint TNF tree!
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#define TAPE_SIZE 65536
#define OFFSET 32768

typedef struct {
    uint8_t write;
    int8_t move;
    uint8_t next;
} Trans;

static void parse_tm(const char* s, Trans t[2][3][2]) {
    int i = 0;
    for (int a = 0; a < 2; a++) {
        for (int q = 0; q < 3; q++) {
            for (int b = 0; b < 2; b++) {
                while (s[i] == '_' || s[i] == '|') i++;
                t[a][q][b].write = s[i] - '0';
                t[a][q][b].move = (s[i+1] == 'R') ? 1 : -1;
                t[a][q][b].next = s[i+2] - 'A';
                i += 3;
            }
        }
    }
}

static void trace_machine(const char* name, const char* spec) {
    Trans target[2][3][2];
    parse_tm(spec, target);

    uint8_t* tape = (uint8_t*)calloc(TAPE_SIZE, 1);
    int defined[2][3][2] = {0};
    int max_state[2] = {0, 0};
    int pos[2] = {0, 2};
    int state[2] = {0, 0};

    // Initial step 0: both define (0,0)
    defined[0][0][0] = 1;
    max_state[0] = target[0][0][0].next;
    defined[1][0][0] = 1;
    max_state[1] = target[1][0][0].next;

    printf("=== %s (%s) ===\n", name, spec);
    printf("  Init A0(0,0) = %d%c%c (max_s=%d), A1(0,0) = %d%c%c (max_s=%d)\n",
        target[0][0][0].write, target[0][0][0].move > 0 ? 'R' : 'L', 'A' + target[0][0][0].next, max_state[0],
        target[1][0][0].write, target[1][0][0].move > 0 ? 'R' : 'L', 'A' + target[1][0][0].next, max_state[1]);

    int depth = 2;
    for (int step = 0; step < 10000000; step++) {
        int p0 = pos[0], p1 = pos[1];
        int b0 = tape[p0 + OFFSET], b1 = tape[p1 + OFFSET];

        for (int a = 0; a < 2; a++) {
            int q = state[a];
            int b = (a == 0) ? b0 : b1;
            if (!defined[a][q][b]) {
                Trans tr = target[a][q][b];
                int allowed_max = (max_state[a] + 1 < 2) ? max_state[a] + 1 : 2;
                int valid_tnf = (tr.next <= allowed_max);
                printf("  [step %d, depth %d] Define A%d(%c,%d) -> %d%c%c (allowed_max=%c, TNF_valid=%s)\n",
                    step, depth, a, 'A' + q, b, tr.write, tr.move > 0 ? 'R' : 'L', 'A' + tr.next,
                    'A' + allowed_max, valid_tnf ? "YES" : "NO");
                defined[a][q][b] = 1;
                if (tr.next > max_state[a]) max_state[a] = tr.next;
                depth++;
            }
        }

        Trans t0 = target[0][state[0]][b0];
        Trans t1 = target[1][state[1]][b1];
        if (p0 == p1) {
            tape[p0 + OFFSET] = t0.write;
        } else {
            tape[p0 + OFFSET] = t0.write;
            tape[p1 + OFFSET] = t1.write;
        }
        pos[0] += t0.move; state[0] = t0.next;
        pos[1] += t1.move; state[1] = t1.next;
        if (pos[0] == pos[1]) {
            printf("  -> COLLISION at step %d (pos=%d), total defined=%d/12\n\n", step + 1, pos[0], depth);
            break;
        }
    }
    free(tape);
}

int main() {
    trace_machine("Nath76 9.44M", "0RB0LC_0LC1RA_1LA0LB|1RB1LC_0LC0RC_1RA1LA");
    trace_machine("Nath76 4.65M", "0LB0LB_0RC1LA_1LB1RC|0RB1RC_1RC0RA_1LC0LB");
    trace_machine("Mega 3.74M",   "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB");
    trace_machine("2.03M",        "0LC1LC_1RB0LA_0RB0LC|1LC1RA_1RC1LA_1RA0RB");
    return 0;
}
