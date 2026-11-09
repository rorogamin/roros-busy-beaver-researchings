#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define CUTOFF_SHORT 100000
#define CUTOFF_LONG  10000000

typedef struct {
    uint8_t write; // 0, 1, 2
    int8_t move;   // -1 or +1
    uint8_t next_state; // 0 or 1
} Transition;

typedef struct {
    Transition t[2][2][3]; // [agent][state][symbol]
} Machine2_3;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void random_machine(Machine2_3 *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
        for (int s = 0; s < 2; s++) {
            for (int sym = 0; sym < 3; sym++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][sym].write = v % 3;
                m->t[a][s][sym].move = ((v >> 4) & 1) ? 1 : -1;
                m->t[a][s][sym].next_state = (v >> 5) % 2;
            }
        }
    }
}

int simulate_cet_fast(const Machine2_3 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

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
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        // Early bailout: if distance exceeds 2*(max_steps - step) or diverges significantly
        int rem = max_steps - step;
        if (dist > 2 * rem) return -1;
    }
    return -2; // Timed out (holdout candidate!)
}

void format_bb_3sym(const Machine2_3 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 2; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 3; sym++) {
                Transition tr = m->t[a][s][sym];
                *p++ = '0' + tr.write;
                *p++ = tr.move > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.next_state;
            }
        }
    }
    *p = '\0';
}
