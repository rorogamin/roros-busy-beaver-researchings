// profile_champions.c
// Profiles the exact trajectory metrics of the top CET(3) champions at steps
// 100, 500, 2000, 10000, 50000, 100000, 500000, 1000000, etc.:
// - Agent distance |p0 - p1|
// - Tape span (max_written - min_written + 1)
// - Number of 1s on tape
// - Number of direction reversals
// - Ratio of distance to span
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#define TAPE_SIZE 131072
#define OFFSET 65536

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

static void profile_machine(const char* name, const char* spec) {
    Trans t[2][3][2];
    parse_tm(spec, t);

    uint8_t* tape = (uint8_t*)calloc(TAPE_SIZE, 1);
    int pos[2] = {0, 2};
    int state[2] = {0, 0};
    int min_p = 0, max_p = 2;
    int max_dist_seen = 2;

    printf("=== %s (%s) ===\n", name, spec);
    int checkpoints[] = {50, 200, 500, 2000, 10000, 50000, 200000, 1000000, 4000000, 9000000};
    int cp_idx = 0;

    for (int step = 1; step <= 10000000; step++) {
        int p0 = pos[0], p1 = pos[1];
        int b0 = tape[p0 + OFFSET], b1 = tape[p1 + OFFSET];
        Trans t0 = t[0][state[0]][b0];
        Trans t1 = t[1][state[1]][b1];
        if (p0 == p1) {
            tape[p0 + OFFSET] = t0.write;
        } else {
            tape[p0 + OFFSET] = t0.write;
            tape[p1 + OFFSET] = t1.write;
        }
        pos[0] += t0.move; state[0] = t0.next;
        pos[1] += t1.move; state[1] = t1.next;

        if (pos[0] < min_p) min_p = pos[0];
        if (pos[0] > max_p) max_p = pos[0];
        if (pos[1] < min_p) min_p = pos[1];
        if (pos[1] > max_p) max_p = pos[1];
        int d = pos[0] > pos[1] ? (pos[0] - pos[1]) : (pos[1] - pos[0]);
        if (d > max_dist_seen) max_dist_seen = d;

        if (cp_idx < 10 && step == checkpoints[cp_idx]) {
            printf("  step %7d: p0=%5d, p1=%5d, dist=%4d (max_d=%4d), span=[%5d, %5d] (%4d)\n",
                step, pos[0], pos[1], d, max_dist_seen, min_p, max_p, max_p - min_p + 1);
            cp_idx++;
        }
        if (pos[0] == pos[1]) {
            printf("  COLLISION at step %d: pos=%d, max_dist=%d, final_span=[%d, %d] (%d)\n\n",
                step, pos[0], max_dist_seen, min_p, max_p, max_p - min_p + 1);
            break;
        }
    }
    free(tape);
}

int main() {
    profile_machine("Nath76 9.44M", "0RB0LC_0LC1RA_1LA0LB|1RB1LC_0LC0RC_1RA1LA");
    profile_machine("Nath76 4.65M", "0LB0LB_0RC1LA_1LB1RC|0RB1RC_1RC0RA_1LC0LB");
    profile_machine("Mega 3.74M",   "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB");
    profile_machine("2.03M",        "0LC1LC_1RB0LA_0RB0LC|1LC1RA_1RC1LA_1RA0RB");
    profile_machine("717k",         "0LB1LA_0LC0LB_1RB1RC|1LC0RC_1RA1LB_0LB1RC");
    profile_machine("265k",         "0LC1LA_0LC0LB_1RB1RC|1RC0RC_1RA1LB_0LB1RC");
    return 0;
}
