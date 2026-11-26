#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct {
    uint8_t w;
    int8_t d;
    uint8_t ns;
} Trans;

static uint64_t rng_state = 0x123456789abcdef0ULL;
static inline uint64_t xorshift64(void) {
    uint64_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rng_state = x;
    return x;
}

static int run_test(const Trans T[4][2], int L, int max_steps) {
    uint8_t tape[256];
    memset(tape, 0, sizeof(tape));
    int off = 128;
    for (int i = 1; i <= L; i++) tape[off + i] = 1;
    int p = off + L;
    int s = 0;
    for (int step = 1; step <= max_steps; step++) {
        if (p < 0 || p >= 256) return -1;
        uint8_t v = tape[p];
        Trans tr = T[s][v];
        tape[p] = tr.w;
        p += tr.d;
        s = tr.ns;
        if (p > off + L + 3) return step;
    }
    return -1;
}

int main(void) {
    Trans T[4][2];
    int found = 0;
    for (uint64_t trial = 0; trial < 2000000; trial++) {
        for (int s = 0; s < 4; s++) {
            for (int sym = 0; sym < 2; sym++) {
                uint64_t r = xorshift64();
                T[s][sym].w = r & 1;
                T[s][sym].d = ((r >> 1) & 1) ? 1 : -1;
                T[s][sym].ns = (r >> 2) & 3;
            }
        }
        int s2 = run_test(T, 2, 5000);
        if (s2 <= 10) continue;
        int s3 = run_test(T, 3, 20000);
        if (s3 <= 3 * s2) continue;
        int s4 = run_test(T, 4, 200000);
        if (s4 > 4 * s3) {
            printf("CANDIDATE: s2=%d s3=%d s4=%d | ", s2, s3, s4);
            for (int s = 0; s < 4; s++) {
                if (s > 0) printf("_");
                for (int sym = 0; sym < 2; sym++) {
                    printf("%d%c%c", T[s][sym].w, T[s][sym].d == 1 ? 'R' : 'L', 'A' + T[s][sym].ns);
                }
            }
            printf("\n");
            fflush(stdout);
            found++;
            if (found >= 20) break;
        }
    }
    printf("Done. Found %d candidates.\n", found);
    return 0;
}
