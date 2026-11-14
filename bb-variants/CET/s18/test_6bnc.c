#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

typedef struct { int write, dir, next; } Trans;
typedef struct { Trans t[3][2]; } Agent;
static void parse_agent(const char *s, Agent *ag) {
    for (int st = 0; st < 3; st++) {
        const char *row = s + st * 7;
        for (int sym = 0; sym < 2; sym++) {
            const char *e = row + sym * 3;
            if (e[0] == '-') { ag->t[st][sym].write = -1; }
            else { ag->t[st][sym].write = e[0]-'0'; ag->t[st][sym].dir = (e[1]=='L')?-1:1; ag->t[st][sym].next = e[2]-'A'; }
        }
    }
}
#define TAPE_SIZE 1048576
#define TAPE_MID (TAPE_SIZE / 2)
static uint8_t tape[TAPE_SIZE];

int main() {
    const char *cases[] = {
        "11776 1RA1LB_0LA0LC_1LB0LB|1RB---_1RC1LB_0LB0RC",
        "11827 1RA1LB_0LA0LC_1RB0LB|1RB---_1RC1LB_0LB0RC",
        "12366 1RB---_1LC1RB_0RB0LC|0RB0RC_1LB1RA_1LA0RA",
        "12367 1RB---_1LC1RB_0RB0LC|0RB0RC_1LB1RA_1RA0RA",
        "18340 1RB1RA_1LC0LA_0RA0LC|0RB0RC_1LB1RA_1LA0RA",
        "18341 1RB1RA_1LC0LA_0RA0LC|0RB0RC_1LB1RA_1RA0RA"
    };
    for (int c = 0; c < 6; c++) {
        int id; char s1[64], s2[64];
        sscanf(cases[c], "%d %63[^|]|%63s", &id, s1, s2);
        Agent a1, a2; parse_agent(s1, &a1); parse_agent(s2, &a2);
        memset(tape, 0, TAPE_SIZE);
        int p1=0, p2=2, st1=0, st2=0, mn=0, mx=2;
        long long t;
        int res = 0;
        for (t = 1; t <= 100000000LL; t++) {
            int i1 = p1 + TAPE_MID, i2 = p2 + TAPE_MID;
            if (i1 < 0 || i1 >= TAPE_SIZE || i2 < 0 || i2 >= TAPE_SIZE) { res = 3; break; }
            Trans tr1 = a1.t[st1][tape[i1]], tr2 = a2.t[st2][tape[i2]];
            if (tr1.write < 0 || tr2.write < 0) { res = 2; break; }
            tape[i2] = tr2.write; tape[i1] = tr1.write;
            if (p1 < mn) mn = p1; if (p1 > mx) mx = p1;
            if (p2 < mn) mn = p2; if (p2 > mx) mx = p2;
            p1 += tr1.dir; p2 += tr2.dir; st1 = tr1.next; st2 = tr2.next;
            if (p1 == p2) { res = 1; break; }
        }
        printf("#%d: res=%d t=%lld p1=%d p2=%d [%d,%d]\n", id, res, t, p1, p2, mn, mx);
    }
    return 0;
}
