#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define CUTOFF_FAST 100000
#define CUTOFF_DEEP 20000000

typedef struct {
    uint8_t w;
    int8_t d;
    uint8_t ns;
} Trans3;

typedef struct {
    Trans3 t[2][3][2]; // [agent][state 0..2][symbol 0..1]
} Machine3_2;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void random_machine3_2(Machine3_2 *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
        for (int s = 0; s < 3; s++) {
            for (int sym = 0; sym < 2; sym++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][sym].w = v & 1;
                m->t[a][s][sym].d = ((v >> 2) & 1) ? 1 : -1;
                m->t[a][s][sym].ns = (v >> 4) % 3;
            }
        }
    }
}

int simulate_cet3_quick(const Machine3_2 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= max_steps; step++) {
        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Trans3 tr1 = m->t[0][s1][r1];
        Trans3 tr2 = m->t[1][s2][r2];

        visited[p2] = marker; tape[p2] = tr2.w;
        visited[p1] = marker; tape[p1] = tr1.w;

        p1 += tr1.d;
        p2 += tr2.d;

        s1 = tr1.ns;
        s2 = tr2.ns;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        int rem = max_steps - step;
        if (dist > 2 * rem || dist > 250) return -1;
    }
    return -2; // Holdout candidate
}

int simulate_cet3_deep(const Machine3_2 *m, int max_steps, uint8_t *tape, uint32_t *visited, uint32_t marker, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= max_steps; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) {
            return -1;
        }

        uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
        uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

        Trans3 tr1 = m->t[0][s1][r1];
        Trans3 tr2 = m->t[1][s2][r2];

        visited[p2] = marker; tape[p2] = tr2.w;
        visited[p1] = marker; tape[p1] = tr1.w;

        p1 += tr1.d;
        p2 += tr2.d;

        s1 = tr1.ns;
        s2 = tr2.ns;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        if (dist > 600) return -1;
    }
    return -2;
}

void format_bb3(const Machine3_2 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 2; sym++) {
                Trans3 tr = m->t[a][s][sym];
                *p++ = '0' + tr.w;
                *p++ = tr.d > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.ns;
            }
        }
    }
    *p = '\0';
}
