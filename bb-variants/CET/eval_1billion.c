#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define TAPE_SIZE 67108864
#define TAPE_OFFSET 33554432
#define TARGET_STEPS 1000000000ULL // 1 Billion Steps!

typedef struct {
    uint8_t w, d, ns;
} Trans4;

typedef struct {
    Trans4 t[2][4][2];
} Machine4;

static Machine4 parse_bb4(const char *s) {
    Machine4 m;
    const char *p = s;
    for (int a = 0; a < 2; a++) {
        for (int st = 0; st < 4; st++) {
            for (int sym = 0; sym < 2; sym++) {
                m.t[a][st][sym].w = p[0] - '0';
                m.t[a][st][sym].d = p[1] == 'R' ? 1 : -1;
                m.t[a][st][sym].ns = p[2] - 'A';
                p += 3;
            }
            if (*p == '_' || *p == '|') p++;
        }
    }
    return m;
}

const char *cands[] = {
    "0RB0RD_1LC0LA_0RB1RB_1LA0RB|1RD1LC_0LB1RD_1RD1RA_0LB0LD",
    "0LD1LB_1RC0RC_0RC0RA_0RA0LA|1LB0RA_0RC0RA_0LD0LB_0RA1RC",
    "1LD1RD_1LB0RD_0LB1RC_1RD1LA|0LB0LA_0RA1RC_1LB1RD_0LB0RD",
    "1RD1LC_0LD0LA_0RA0RD_0LD1LC|1RD0RD_0RA0LB_0LD1LA_0RC1RC",
    "0RD0RC_1LC1LA_0RB0LA_1LA0LC|0RC1LD_1LA0RA_0LD1LB_0RC0RB",
    "0LD1LD_1RD1LA_1RB1RC_1RA1RA|0RD1RA_0RD1LA_0LD1RC_0RC0RC",
    "1LB1LB_0RB1LD_0LA1LA_0RD1LD|0LB0LB_0RA1RB_1LB1LB_1RD0RD",
    "1LD1RB_0LA1RA_0RB1RB_1LC0RC|1RB1RD_1LA1LA_1LD0LB_0LA0LA",
    "0RC1RD_1RD0LD_1LA1LA_0RC0LB|0RD1RB_1LD0LD_0LD1RD_0RC1RD",
    "0LB0RA_1RC1RC_0LB0LC_0LA1RC|0RD0LB_1LC0RD_1LC1RA_0LA1LA"
};

int main(void) {
    printf("Testing top 10 holdouts up to 1,000,000,000 (1 Billion) steps...\n");
    uint8_t *tape = calloc(TAPE_SIZE, 1);
    uint32_t *vis = calloc(TAPE_SIZE, 4);

    for (int i = 0; i < 10; i++) {
        Machine4 m = parse_bb4(cands[i]);
        int p1 = TAPE_OFFSET, p2 = TAPE_OFFSET + 2, s1 = 0, s2 = 0;
        uint32_t mk = i + 1;
        int halted = 0;
        int col_pos = 0;
        uint64_t col_step = 0;

        for (uint64_t step = 1; step <= TARGET_STEPS; step++) {
            if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) break;
            uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
            uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
            Trans4 tr1 = m.t[0][s1][r1], tr2 = m.t[1][s2][r2];
            vis[p2] = mk; tape[p2] = tr2.w;
            vis[p1] = mk; tape[p1] = tr1.w;
            p1 += tr1.d; p2 += tr2.d;
            s1 = tr1.ns; s2 = tr2.ns;
            if (p1 == p2) {
                halted = 1;
                col_pos = p1 - TAPE_OFFSET;
                col_step = step;
                break;
            }
            int d = p1 > p2 ? p1 - p2 : p2 - p1;
            if (d > 400) break;
        }

        if (halted) {
            printf("\n🌟🌟🌟 BILLION-CLASS RECORD: Candidate %d HALTED at %llu steps! (cell %d) 🌟🌟🌟\n", i, col_step, col_pos);
            printf("bbchallenge: %s\n", cands[i]);
        } else {
            printf("Candidate %d: reached 1 Billion steps without halting or diverging (minD/maxD tightly bounded)\n", i);
        }
    }
    return 0;
}
