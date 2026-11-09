#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 67108864
#define TAPE_OFFSET 33554432
#define CUTOFF_FAST 1000000
#define CUTOFF_BILLION 1200000000ULL

typedef struct {
    uint8_t w;      // 0 or 1
    int8_t d;       // -1 or +1
    uint8_t ns;     // 0..3
} Trans4;

typedef struct {
    Trans4 t[2][4][2]; // [agent][state][symbol]
} Machine4_2;

static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void random_machine4_2(Machine4_2 *m, uint64_t *rng) {
    for (int a = 0; a < 2; a++) {
        for (int s = 0; s < 4; s++) {
            for (int sym = 0; sym < 2; sym++) {
                uint64_t v = splitmix64(rng);
                m->t[a][s][sym].w = v & 1;
                m->t[a][s][sym].d = ((v >> 2) & 1) ? 1 : -1;
                m->t[a][s][sym].ns = (v >> 4) & 3;
            }
        }
    }
}

void format_bb4(const Machine4_2 *m, char *buf) {
    char *p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int s = 0; s < 4; s++) {
            if (s > 0) *p++ = '_';
            for (int sym = 0; sym < 2; sym++) {
                Trans4 tr = m->t[a][s][sym];
                *p++ = '0' + tr.w;
                *p++ = tr.d > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.ns;
            }
        }
    }
    *p = '\0';
}
