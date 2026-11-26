#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

typedef struct { uint8_t w; int8_t d; uint8_t ns; } Trans;
static const Trans AG1[4][2] = {
    {{1, 1, 1}, {0, 1, 1}},
    {{1,-1, 2}, {1, 1, 0}},
    {{1,-1, 3}, {0,-1, 2}},
    {{0, 1, 0}, {0,-1, 3}}
};
static const Trans AG2[4][2] = {
    {{1, 1, 2}, {0, 1, 2}},
    {{1,-1, 0}, {0, 1, 2}},
    {{1,-1, 0}, {1, 1, 3}},
    {{1,-1, 3}, {1,-1, 1}}
};

int main(void) {
    static uint8_t tape[2097152];
    int off = 10000;
    for (int p2_init = 2; p2_init <= 100; p2_init += 2) {
        memset(tape, 0, sizeof(tape));
        int p1 = 0, p2 = p2_init, s1 = 0, s2 = 0, max_p1 = 0;
        int bounces = 0, last_b = -100;
        int b_list[10];
        int halted = 0;
        for (int t = 1; t <= 5000000; t++) {
            uint8_t v1 = tape[off + p1], v2 = tape[off + p2];
            Trans tr1 = AG1[s1][v1], tr2 = AG2[s2][v2];
            tape[off + p2] = tr2.w; tape[off + p1] = tr1.w;
            p1 += tr1.d; s1 = tr1.ns; p2 += tr2.d; s2 = tr2.ns;
            if (p1 > max_p1) max_p1 = p1;
            if (p2 - p1 <= 4 && p1 != p2 && t - last_b > 50) {
                last_b = t;
                if (bounces < 10) b_list[bounces] = t;
                bounces++;
            }
            if (p1 == p2) {
                printf("p2_init=%3d: HALT t=%7d pos=%6d (bounces=%d", p2_init, t, p1, bounces);
                for (int i = 0; i < bounces && i < 10; i++) printf(" b@%d", b_list[i]);
                printf(")\n");
                halted = 1;
                break;
            }
        }
        if (!halted) {
            printf("p2_init=%3d: SURV 5M (max_p1=%d, bounces=%d", p2_init, max_p1, bounces);
            for (int i = 0; i < bounces && i < 10; i++) printf(" b@%d", b_list[i]);
            printf(")\n");
        }
    }
    return 0;
}
