#include <stdio.h>
#include <stdint.h>
#include <string.h>

typedef struct { uint8_t w; int8_t d; uint8_t ns; } Trans;
static const Trans AG1[4][2] = {
    {{1, 1, 1}, {0, 1, 1}},   /* A: 1RB 0RB */
    {{1,-1, 2}, {1, 1, 0}},   /* B: 1LC 1RA */
    {{1,-1, 3}, {0,-1, 2}},   /* C: 1LD 0LC */
    {{0, 1, 0}, {0,-1, 3}}    /* D: 0RA 0LD */
};

int main(void) {
    static uint8_t tape[4096];
    memset(tape, 0, sizeof(tape));
    int off = 2048;
    int p = off, s = 0, mn = off, mx = off;
    uint64_t next_m = 10;
    for (uint64_t t = 1; t <= 1000000000ULL; t++) {
        uint8_t v = tape[p];
        Trans tr = AG1[s][v];
        tape[p] = tr.w;
        p += tr.d; s = tr.ns;
        if (p < mn) mn = p;
        if (p > mx) mx = p;
        if (t == next_m) {
            int ones = 0;
            for (int x = mn; x <= mx; x++) if (tape[x]) ones++;
            printf("t=10^%d (%llu): span=[%d..%d] len=%d ones=%d\n",
                   (int)(next_m == 10 ? 1 : next_m == 100 ? 2 : next_m == 1000 ? 3 :
                         next_m == 10000 ? 4 : next_m == 100000 ? 5 : next_m == 1000000 ? 6 :
                         next_m == 10000000 ? 7 : next_m == 100000000 ? 8 : 9),
                   (unsigned long long)t, mn - off, mx - off, mx - mn + 1, ones);
            fflush(stdout);
            next_m *= 10;
        }
    }
    return 0;
}
