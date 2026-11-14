#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct {
    int write;   // 0 or 1, -1 if undefined
    int dir;     // -1 (L) or +1 (R)
    int next;    // 0 (A), 1 (B), 2 (C)
} Trans;

typedef struct {
    Trans t[3][2];
} Agent;

static int parse_agent(const char *s, Agent *ag) {
    // Format: 0LB---_0LC---_1RC0LC (20 chars)
    if (strlen(s) < 20) return 0;
    for (int st = 0; st < 3; st++) {
        const char *row = s + st * 7;
        for (int sym = 0; sym < 2; sym++) {
            const char *e = row + sym * 3;
            if (e[0] == '-' && e[1] == '-' && e[2] == '-') {
                ag->t[st][sym].write = -1;
                ag->t[st][sym].dir = 0;
                ag->t[st][sym].next = 0;
            } else {
                ag->t[st][sym].write = e[0] - '0';
                ag->t[st][sym].dir = (e[1] == 'L') ? -1 : 1;
                ag->t[st][sym].next = e[2] - 'A';
            }
        }
    }
    return 1;
}

#define TAPE_SIZE 65536
#define TAPE_MID (TAPE_SIZE / 2)

typedef struct {
    int p1, p2;
    int s1, s2;
    int min_w, max_w;
    uint8_t tape[TAPE_SIZE];
} SimState;

static inline void init_sim(SimState *st) {
    st->p1 = 0;
    st->p2 = 2;
    st->s1 = 0;
    st->s2 = 0;
    st->min_w = 0;
    st->max_w = 2;
    memset(st->tape, 0, TAPE_SIZE);
}

// Returns: 0 = ok, 1 = collision, 2 = undef, 3 = oob
static inline int step_sim(const Agent *a1, const Agent *a2, SimState *st) {
    int idx1 = st->p1 + TAPE_MID;
    int idx2 = st->p2 + TAPE_MID;
    if (idx1 < 0 || idx1 >= TAPE_SIZE || idx2 < 0 || idx2 >= TAPE_SIZE) return 3;
    int r1 = st->tape[idx1];
    int r2 = st->tape[idx2];
    Trans tr1 = a1->t[st->s1][r1];
    Trans tr2 = a2->t[st->s2][r2];
    if (tr1.write < 0 || tr2.write < 0) return 2;
    st->tape[idx2] = (uint8_t)tr2.write;
    st->tape[idx1] = (uint8_t)tr1.write; // Agent 1 priority
    if (st->p1 < st->min_w) st->min_w = st->p1;
    if (st->p1 > st->max_w) st->max_w = st->p1;
    if (st->p2 < st->min_w) st->min_w = st->p2;
    if (st->p2 > st->max_w) st->max_w = st->p2;
    st->p1 += tr1.dir;
    st->p2 += tr2.dir;
    st->s1 = tr1.next;
    st->s2 = tr2.next;
    if (st->p1 == st->p2) return 1;
    return 0;
}

int main(int argc, char **argv) {
    const char *path = (argc > 1) ? argv[1] : "residue_s18.txt";
    int max_steps = (argc > 2) ? atoi(argv[2]) : 200000;
    FILE *f = fopen(path, "r");
    if (!f) { perror("fopen"); return 1; }

    FILE *f_halt = fopen("halted.txt", "w");
    FILE *f_undef = fopen("undef.txt", "w");
    FILE *f_rem = fopen("rem_after_sim.txt", "w");

    char line[256];
    int total = 0, halted = 0, undef = 0, oob = 0, rem = 0;
    int max_halt_steps = 0;
    char max_halt_line[256] = "";
    SimState st;

    while (fgets(line, sizeof(line), f)) {
        size_t len = strlen(line);
        while (len > 0 && (line[len-1] == '\n' || line[len-1] == '\r' || line[len-1] == ' ')) {
            line[--len] = '\0';
        }
        if (len == 0) continue;
        total++;

        // Split by whitespace
        char *sp = strchr(line, ' ');
        if (!sp) continue;
        char s1[64], s2[64];
        size_t l1 = sp - line;
        if (l1 >= 64) continue;
        memcpy(s1, line, l1); s1[l1] = '\0';
        while (*sp == ' ') sp++;
        strncpy(s2, sp, 63); s2[63] = '\0';

        Agent a1, a2;
        if (!parse_agent(s1, &a1) || !parse_agent(s2, &a2)) continue;

        init_sim(&st);
        int res = 0;
        int t = 0;
        for (t = 1; t <= max_steps; t++) {
            res = step_sim(&a1, &a2, &st);
            if (res != 0) break;
        }
        if (res == 1) {
            halted++;
            fprintf(f_halt, "%d\t%d\t%s\n", total, t, line);
            if (t > max_halt_steps) {
                max_halt_steps = t;
                strcpy(max_halt_line, line);
            }
        } else if (res == 2) {
            undef++;
            fprintf(f_undef, "%d\t%d\t%s\n", total, t, line);
        } else if (res == 3) {
            oob++;
            fprintf(f_rem, "%d\tOOB\t%s\n", total, line);
        } else {
            rem++;
            fprintf(f_rem, "%d\t%s\n", total, line);
        }
    }

    printf("Total: %d\n", total);
    printf("Halted (<=%d): %d (max=%d: %s)\n", max_steps, halted, max_halt_steps, max_halt_line);
    printf("Undef (<=%d): %d\n", max_steps, undef);
    printf("OOB: %d\n", oob);
    printf("Remaining: %d\n", rem);

    fclose(f); fclose(f_halt); fclose(f_undef); fclose(f_rem);
    return 0;
}
