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
} MachineCET3;

void format_bb(const MachineCET3 *m, char *buf) {
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

int simulate(const MachineCET3 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos, int *max_d) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;
    int max_dist = 2;

    for (int step = 1; step <= max_steps; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Transition tr1 = m->t[0][s1][r1];
        Transition tr2 = m->t[1][s2][r2];

        visited[p2] = marker; tape[p2] = tr2.write;
        visited[p1] = marker; tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;

        s1 = tr1.next_state;
        s2 = tr2.next_state;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            *max_d = max_dist;
            return step;
        }

        int d = (p1 > p2) ? (p1 - p2) : (p2 - p1);
        if (d > max_dist) max_dist = d;
        int rem = max_steps - step;
        if (d > 2 * rem) return -1; // escaped
    }
    *max_d = max_dist;
    return -2; // alive at cutoff!
}

int main() {
    printf("Exploring tree of interactive CET(3) machines...\n");
    // Test machines where Agent 1 starts moving R towards Agent 2 (t[0][0][0].move = +1)
    // and Agent 2 starts moving L towards Agent 1 (t[1][0][0].move = -1)
    uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
    uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
    uint32_t marker = 1;

    long long count = 0;
    long long holdouts = 0;
    int max_halt = 0;

    // Search specifically around machines that make contact and don't immediately escape
    // We sample 2,000,000 interacting seeds
    for (int seed = 0; seed < 2000000; seed++) {
        MachineCET3 m;
        uint64_t rng = (uint64_t)seed * 0x9e3779b97f4a7c15ULL + 1;
        for (int a = 0; a < 2; a++) {
            for (int s = 0; s < 3; s++) {
                for (int r = 0; r < 2; r++) {
                    rng = (rng ^ (rng >> 30)) * 0xbf58476d1ce4e5b9ULL;
                    m.t[a][s][r].write = rng & 1;
                    m.t[a][s][r].move = ((rng >> 1) & 1) ? 1 : -1;
                    m.t[a][s][r].next_state = (rng >> 2) % 3;
                }
            }
        }
        // Force inward start
        m.t[0][0][0].move = 1; // Agent 1 moves right towards Agent 2
        m.t[1][0][0].move = -1; // Agent 2 moves left towards Agent 1
        
        marker++;
        int out_pos = 0, max_d = 0;
        int s = simulate(&m, 10000, tape, visited, marker, &out_pos, &max_d);
        if (s == -2) {
            // Test up to 100,000 steps!
            marker++;
            int s2 = simulate(&m, 100000, tape, visited, marker, &out_pos, &max_d);
            if (s2 == -2) {
                holdouts++;
                char bb[256];
                format_bb(&m, bb);
                printf("FOUND HOLDOUT: %s (max_d=%d)\n", bb, max_d);
            } else if (s2 > max_halt) {
                max_halt = s2;
                char bb[256];
                format_bb(&m, bb);
                printf("High halting machine: %d steps: %s\n", s2, bb);
            }
        } else if (s > max_halt) {
            max_halt = s;
        }
    }

    printf("Done. Total holdouts surviving 100k steps: %lld. Max halt seen: %d\n", holdouts, max_halt);
    return 0;
}
