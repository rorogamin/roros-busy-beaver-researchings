#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

#define TAPE_SIZE 16777216
#define TAPE_OFFSET 8388608
#define DEEP_LIMIT 100000000 // 100 million steps

typedef struct {
    uint8_t w;
    int8_t d;
    uint8_t ns;
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

int simulate_deep(const Machine4 *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *out_pos) {
    int p1 = TAPE_OFFSET + 0;
    int p2 = TAPE_OFFSET + 2;
    int s1 = 0, s2 = 0;

    for (int step = 1; step <= DEEP_LIMIT; step++) {
        if (p1 <= 200 || p1 >= TAPE_SIZE - 200 || p2 <= 200 || p2 >= TAPE_SIZE - 200) return -1;

        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;

        Trans4 tr1 = m->t[0][s1][r1];
        Trans4 tr2 = m->t[1][s2][r2];

        vis[p2] = mk; tape[p2] = tr2.w;
        vis[p1] = mk; tape[p1] = tr1.w;

        p1 += tr1.d;
        p2 += tr2.d;

        s1 = tr1.ns;
        s2 = tr2.ns;

        if (p1 == p2) {
            *out_pos = p1 - TAPE_OFFSET;
            return step;
        }

        int dist = p1 > p2 ? p1 - p2 : p2 - p1;
        if (dist > 500) return -1;
    }
    return -2;
}

const char *holdouts[] = {
    "1RA0LD_0LA0RA_0RD0RB_1LD0LB|0RD1LB_0RD1LA_1LB1RB_0RD1RC",
    "1RB1RB_1RB0RB_0LC1RC_1RC1LD|0RA0LA_1LC0RC_1RB0RC_1RB1LB",
    "0LD0RA_0RD1RD_1RC0LD_0LC0RA|0RA0LA_0LA1RC_1RC0LD_0RC0LD",
    "1RC0LD_1LA0RD_1LA1LB_1RD0RA|1RC0LB_0LB1RC_0RC1LC_1LD1RC",
    "0RC0RC_1LA1LD_1RD1LB_1LA1RD|1RB1RC_1RB1RC_0RD0LD_0LD1RD",
    "0RC0LA_1RC0LD_0LC1RC_1RD0RB|0RC1RD_0RB0LA_1LC0LC_1RB0LC",
    "0LD1LC_1RD1RB_1LB1RB_0RB0RD|1RB1RA_0RB1RA_0RB0RB_0LC0LB",
    "0LA0LB_0LA1LB_0RB0LA_1LA1LA|0RC1LA_0LC0LD_0LB0RD_0LB0LC",
    "1RC0LC_1LD1LB_1LC1LA_0RC1LA|1RC1RC_1LA0LA_0LD1LC_0LC0RC",
    "1LB0LB_0LC1LD_1RB1RC_1LB0RD|1RA0RD_1LC1LB_0LC0LC_0LB1RA",
    "0LD0LD_0RA1LD_1RB1LC_0LA1RB|0LB0RA_0LA0RB_0LB0RD_1RD0RA",
    "1LC0RD_1RD1LB_1LD0LD_1LC1LA|1LC0RB_0RD1LC_0LC0RB_0LD0LD",
    "0LC0LA_1LA1RC_1RD1RC_0RD1RB|0LB0LB_0RD1LC_0LB1RB_1RD0RB",
    "0RD0RC_0LB1LD_0RA0LC_0RC1RD|0RC1LA_1RD0RA_1RC1RC_1RB0LB",
    "0RA1RC_0RA0LC_1LC1LD_1LA0RC|0RD0RA_1RB1LB_0RC1RD_0RD0RD",
    "1RB1RB_0RB1LB_1RA0RA_0LB0LC|0RB1LA_0RB0RC_1RB0LD_0LB1LD",
    "1LA0LB_0LB1RB_0LD0LB_1RB0LC|1LA0LA_1RD0RB_0LC1RA_1LA1LD",
    "0LD1RB_1LC0RA_1LB1LD_1RA1LB|1RC1LD_0RB1RB_0LC0LA_1RC0LC",
    "0LD0RC_1RD0LA_1LD1RA_1LA1RB|1LC1LA_0LD0LC_0LB0RD_1RB1RC",
    "0RB1RC_0RA1RB_1LD0RA_0LB0LD|0RA0LD_1LB1RB_0RC1LA_1LD0LC",
    "1RD0RA_0LB0LD_0LA0RC_0RD1RB|0RD0RC_0LC0RA_0RB0LD_0RA0LA",
    "1LC0RA_1RC1RD_1LC0RA_0LC0RA|1LA1LA_0RB0RC_0RC1LB_1RA1RD",
    "1RA0RC_0RA0LC_0LB0RC_0LB1RC|0RA1RC_1RC0LD_0LC1RB_0RA1RD",
    "1LD1LB_0RC1LA_1LB1RC_0RB0RC|0RC1RD_0LC0RB_1LB0LB_0LD1LD",
    "1LA1RC_0RA1LD_1LC1LB_1RB0LC|1LB0LD_1RD1LD_0RB1RB_1LA1LB",
    "0RC1LA_1RC0LB_0RB0RD_1RB1LD|0RA0LA_1RB1RA_0LD1LB_1RC1RD",
    "1LD1LB_0RB0RA_0RA0RD_1RD0LD|0LB0RC_0RB0RD_1RD1RA_1LA0RA",
    "1RC1LB_0RB1RC_0RC1RB_0RD0RC|1RB1RC_1RC0LC_0RA1RB_1RA1RB",
    "1RC0RC_0LD1RD_1RC1LB_0RC0LA|1RD0LA_0LD0LA_0RD0LC_0RD1RB",
    "0LD1LB_0LD1LB_1LD0RD_0LB1RD|0RB1RA_0LB0RC_0LB1RB_0RD1LB",
    "0LC0LD_0LC1RB_0RA1RB_1LC1RB|0RD0RC_1RB0LA_1LB1LB_0LC0LB",
    "0LC0LD_0LB0LC_1RC1LC_1RB1LD|0RC0RC_1RB1RB_0RC0LB_1LD0LD",
    "0LA0LC_0RC1RC_1RA1LB_1LC1LC|1RD1LD_1LD1LA_0RD1RC_0LD1RB",
    "1LB0RD_1LB1LD_0RD1LD_0RC0LB|0RB0LD_1LB0LB_1RD1RA_0RA0RA",
    "0LC0LC_1LC0LC_0RB0RD_1RB0LA|0LC0RA_1LA0LB_1RA1RD_0LC0LD",
    "1RC1RD_0RB1RB_0RC1LA_0RC0LB|1RA0LD_0LC1LA_1LC0LD_1RC1RB",
    "0LC0LD_1RD1LA_0LC0RB_1RA1RA|0RB1LC_1LC0LD_1RD1LB_1LD0RC",
    "1LA1RB_0RA0RD_0RD0LA_0RA0RC|1RB1LB_1RD0RD_1LC1LD_0RC0LD",
    "0LA0LD_1LC0RA_0LC1LC_1LA1RA|1LD1LC_0LA1LA_1LC1RB_1RB1RB",
    "0LC1RD_0RB0RB_1RA1LD_0RD0RB|1RA1RC_0RA0RD_0LB1RB_1LD1LC"
};

int main(void) {
    int n = sizeof(holdouts) / sizeof(holdouts[0]);
    printf("Evaluating %d top CET(4) holdouts up to 100,000,000 steps...\n", n);

    #pragma omp parallel for schedule(dynamic)
    for (int i = 0; i < n; i++) {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        uint32_t *vis = calloc(TAPE_SIZE, 4);
        Machine4 m = parse_bb4(holdouts[i]);
        int pos = 0;
        int s = simulate_deep(&m, tape, vis, 1, &pos);
        if (s > 0) {
            printf("\n>>> CANDIDATE %d HALTED at %d steps! cell %d <<<\n bb: %s\n", i, s, pos, holdouts[i]);
        } else if (s == -2) {
            printf("[Still running >100M steps]: candidate %d (%s)\n", i, holdouts[i]);
        }
        free(tape);
        free(vis);
    }
    return 0;
}
