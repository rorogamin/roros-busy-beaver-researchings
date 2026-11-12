#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int w, d, n; } Tr;
static Tr A1[4][2], A2[4][2];
static unsigned char tape[4000000];
#define OFF 1000000
#define CAP 4000
#define R 2
static char full_line[512];

static int parse_agent(const char *s, Tr a[4][2]) {
    for (int st = 0; st < 4; st++) {
        for (int sy = 0; sy < 2; sy++) {
            if (*s == '-') {
                a[st][sy] = (Tr){0, 1, -1};
                s += 3;
            } else {
                a[st][sy] = (Tr){s[0] - '0', s[1] == 'R' ? 1 : -1,
                                 s[2] - 'A'};
                s += 3;
            }
            if (*s == '_') s++;
        }
    }
    return 0;
}

static int parse_line(char *line) {
    snprintf(full_line, sizeof full_line, "%s", line);
    char *bar = strchr(line, '|');
    if (!bar) return -1;
    *bar = 0;
    parse_agent(line, A1);
    parse_agent(bar + 1, A2);
    return 0;
}

static int win(long p, int out[2 * R + 1]) {
    for (int z = -R; z <= R; z++) {
        long x = p + z + OFF;
        out[z + R] = (x >= 0 && x < (long)sizeof(tape)) ? tape[x] : 0;
    }
    return 0;
}

/* Clean one-step test: run and compare state/window before and after. */
static int one_step(const char *line, int *kout, int *dout, long *p1out,
                    long *p2out) {
    memset(tape, 0, sizeof(tape));
    long p1 = OFF, p2 = OFF + 2;
    int s1 = 0, s2 = 0;
    int w1[2 * R + 1], w2[2 * R + 1], v1[2 * R + 1], v2[2 * R + 1];
    for (int k = 0; k < CAP; k++) {
        win(p1, w1); win(p2, w2);
        int ps1 = s1, ps2 = s2;
        long pp1 = p1, pp2 = p2;
        Tr x = A1[s1][tape[p1 + OFF]];
        Tr y = A2[s2][tape[p2 + OFF]];
        tape[p1 + OFF] = x.w;
        tape[p2 + OFF] = y.w;
        p1 += x.d; s1 = x.n;
        p2 += y.d; s2 = y.n;
        if (p1 == p2) return 0;
        if (s1 != ps1 || s2 != ps2 || p2 - p1 != pp2 - pp1) continue;
        if (p1 - pp1 != p2 - pp2 || p1 == pp1) continue;
        win(p1, v1); win(p2, v2);
        int ok = 1;
        for (int z = 0; z <= 2 * R; z++) {
            if (w1[z] != v1[z] || w2[z] != v2[z]) { ok = 0; break; }
        }
        if (ok) {
            long lo = p1 < p2 ? p1 : p2;
            long hi = p1 > p2 ? p1 : p2;
            if (p1 - pp1 > 0) {
                for (long x = hi + 3; x <= hi + 30; x++) {
                    long y = x + OFF;
                    if (y >= 0 && y < (long)sizeof(tape) && tape[y]) {
                        ok = 0; break;
                    }
                }
            } else {
                for (long x = lo - 30; x <= lo - 3; x++) {
                    long y = x + OFF;
                    if (y >= 0 && y < (long)sizeof(tape) && tape[y]) {
                        ok = 0; break;
                    }
                }
            }
        }
        if (ok) {
            *kout = k;
            *dout = (int)(p1 - pp1);
            *p1out = p1;
            *p2out = p2;
            return 1;
        }
    }
    return 0;
}

int main(void) {
    FILE *f = fopen("all_holdouts_cet4.txt", "r");
    if (!f) { perror("all_holdouts_cet4.txt"); return 1; }
    char line[512];
    int idx = 0, count = 0;
    FILE *out = fopen("solved_holdouts_period1_all.txt", "w");
    while (fgets(line, sizeof line, f)) {
        char *nl = strpbrk(line, "\r\n");
        if (nl) *nl = 0;
        if (!line[0] || line[0] == '#') continue;
        if (parse_line(line) < 0) continue;
        int k, d; long p1, p2;
        if (one_step(line, &k, &d, &p1, &p2)) {
            count++;
            if (out) fprintf(out, "%d\t%d\t%d\t%ld\t%ld\t%s\n",
                             idx, k, d, p1 - OFF, p2 - OFF, full_line);
        }
        idx++;
    }
    if (out) fclose(out);
    printf("period-1 cycles: %d / %d\n", count, idx);
    return 0;
}
