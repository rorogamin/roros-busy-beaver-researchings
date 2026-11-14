#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { int write, dir, next; } Trans;
typedef struct { Trans t[3][2]; } Agent;

static int parse_agent(const char *s, Agent *ag) {
    if (strlen(s) < 20) return 0;
    for (int st = 0; st < 3; st++) {
        const char *row = s + st * 7;
        for (int sym = 0; sym < 2; sym++) {
            const char *e = row + sym * 3;
            if (e[0] == '-' && e[1] == '-' && e[2] == '-') {
                ag->t[st][sym].write = -1; ag->t[st][sym].dir = 0; ag->t[st][sym].next = 0;
            } else {
                ag->t[st][sym].write = e[0] - '0';
                ag->t[st][sym].dir = (e[1] == 'L') ? -1 : 1;
                ag->t[st][sym].next = e[2] - 'A';
            }
        }
    }
    return 1;
}

#define TAPE_SIZE 1048576
#define TAPE_MID (TAPE_SIZE / 2)
#define MAX_STEPS 10000000

static uint8_t tape[TAPE_SIZE];

int main() {
    FILE *f = fopen("cg_toward.txt", "r");
    if (!f) { perror("fopen"); return 1; }
    FILE *f_halt = fopen("cg_halted.txt", "w");
    FILE *f_bnc = fopen("cg_bouncers.txt", "w");

    char line[256];
    int total = 0, halted = 0, undef = 0, oob = 0, bouncers = 0;

    while (fgets(line, sizeof(line), f)) {
        int idx;
        char s1[64], s2[64];
        if (sscanf(line, "%d\t%63s %63s", &idx, s1, s2) != 3) continue;
        total++;
        Agent a1, a2;
        parse_agent(s1, &a1); parse_agent(s2, &a2);

        memset(tape, 0, TAPE_SIZE);
        int p1 = 0, p2 = 2, st1 = 0, st2 = 0;
        int mn = 0, mx = 2;
        int far = 0, bounces = 0;
        int res = 0, t = 0;

        for (t = 1; t <= MAX_STEPS; t++) {
            int i1 = p1 + TAPE_MID, i2 = p2 + TAPE_MID;
            if (i1 < 0 || i1 >= TAPE_SIZE || i2 < 0 || i2 >= TAPE_SIZE) { res = 3; break; }
            Trans tr1 = a1.t[st1][tape[i1]];
            Trans tr2 = a2.t[st2][tape[i2]];
            if (tr1.write < 0 || tr2.write < 0) { res = 2; break; }
            tape[i2] = (uint8_t)tr2.write;
            tape[i1] = (uint8_t)tr1.write;
            if (p1 < mn) mn = p1; if (p1 > mx) mx = p1;
            if (p2 < mn) mn = p2; if (p2 > mx) mx = p2;
            p1 += tr1.dir; p2 += tr2.dir;
            st1 = tr1.next; st2 = tr2.next;
            if (p1 == p2) { res = 1; break; }
            int dist = abs(p2 - p1);
            if (!far && dist > 100) far = 1;
            else if (far && dist < 20) { far = 0; bounces++; }
        }
        if (res == 1) {
            halted++;
            fprintf(f_halt, "%d\t%d\t%s|%s\n", idx, t, s1, s2);
        } else if (res == 2) undef++;
        else if (res == 3) oob++;
        else if (bounces > 0) {
            bouncers++;
            fprintf(f_bnc, "%d\tbounces=%d\t[%d,%d]\t%s|%s\n", idx, bounces, mn, mx, s1, s2);
        }
        if (total % 200 == 0) {
            fprintf(stderr, "CG %d/1384: halt=%d undef=%d oob=%d bouncers=%d\n", total, halted, undef, oob, bouncers);
            fflush(stderr);
        }
    }
    printf("DONE CG Total=%d Halt=%d Undef=%d OOB=%d Bouncers=%d\n", total, halted, undef, oob, bouncers);
    fclose(f); fclose(f_halt); fclose(f_bnc);
    return 0;
}
