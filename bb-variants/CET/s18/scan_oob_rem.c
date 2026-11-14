#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAX_TAPE 2000000
#define OFFSET (MAX_TAPE / 2)

typedef struct {
    int write;
    int dir;
    int next;
} Trans;

static int parse_agent(const char *s, Trans tbl[3][2]) {
    for (int st = 0; st < 3; st++) {
        for (int sym = 0; sym < 2; sym++) {
            int idx = st * 7 + sym * 3;
            if (st > 0 && s[st * 7 - 1] != '_') return 0;
            if (s[idx] == '-') {
                tbl[st][sym].write = 0;
                tbl[st][sym].dir = 0;
                tbl[st][sym].next = -1;
            } else {
                tbl[st][sym].write = s[idx] - '0';
                tbl[st][sym].dir = (s[idx + 1] == 'L') ? -1 : 1;
                tbl[st][sym].next = s[idx + 2] - 'A';
            }
        }
    }
    return 1;
}

int main(void) {
    FILE *f = fopen("oob_rem.txt", "r");
    if (!f) { perror("oob_rem.txt"); return 1; }
    static uint8_t tape[MAX_TAPE];
    char line[256];
    int total = 0, halts = 0, undefs = 0, oobs = 0;
    while (fgets(line, sizeof(line), f)) {
        int id;
        char s1[64], s2[64];
        if (sscanf(line, "%d %63s %63s", &id, s1, s2) != 3) continue;
        total++;
        Trans a1[3][2], a2[3][2];
        if (!parse_agent(s1, a1) || !parse_agent(s2, a2)) continue;
        memset(tape, 0, MAX_TAPE);
        int p1 = OFFSET, p2 = OFFSET;
        int st1 = 0, st2 = 0;
        int status = 0;
        long long t = 0;
        long long LIMIT = 50000000LL;
        for (t = 1; t <= LIMIT; t++) {
            if (p1 < 2 || p1 >= MAX_TAPE - 2 || p2 < 2 || p2 >= MAX_TAPE - 2) {
                status = 3;
                break;
            }
            if (p1 == p2) {
                int sym = tape[p1];
                Trans t1 = a1[st1][sym];
                Trans t2 = a2[st2][sym];
                if (t1.next == -1 || t2.next == -1) { status = 1; break; }
                if (t1.write != t2.write) { status = 2; break; }
                tape[p1] = t1.write;
                p1 += t1.dir;
                p2 += t2.dir;
                st1 = t1.next;
                st2 = t2.next;
            } else {
                int sym1 = tape[p1];
                int sym2 = tape[p2];
                Trans t1 = a1[st1][sym1];
                Trans t2 = a2[st2][sym2];
                if (t1.next == -1 || t2.next == -1) { status = 1; break; }
                tape[p1] = t1.write;
                tape[p2] = t2.write;
                p1 += t1.dir;
                p2 += t2.dir;
                st1 = t1.next;
                st2 = t2.next;
            }
        }
        if (status == 1) { halts++; printf("HALT #%d at t=%lld (%s|%s)\n", id, t, s1, s2); }
        else if (status == 2) { undefs++; }
        else if (status == 3) { oobs++; }
    }
    fclose(f);
    printf("DONE Total=%d Halt=%d Undef=%d OOB=%d\n", total, halts, undefs, oobs);
    return 0;
}
