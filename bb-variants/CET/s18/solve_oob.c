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

#define TAPE_SIZE 262144
#define TAPE_MID (TAPE_SIZE / 2)

typedef struct {
    int p1, p2, s1, s2, min_w, max_w;
    uint8_t tape[TAPE_SIZE];
} SimState;

static void init_sim(SimState *st) {
    st->p1 = 0; st->p2 = 2; st->s1 = 0; st->s2 = 0;
    st->min_w = 0; st->max_w = 2;
    memset(st->tape, 0, TAPE_SIZE);
}

static inline int step_sim(const Agent *a1, const Agent *a2, SimState *st) {
    int i1 = st->p1 + TAPE_MID, i2 = st->p2 + TAPE_MID;
    if (i1 < 0 || i1 >= TAPE_SIZE || i2 < 0 || i2 >= TAPE_SIZE) return 3;
    Trans tr1 = a1->t[st->s1][st->tape[i1]];
    Trans tr2 = a2->t[st->s2][st->tape[i2]];
    if (tr1.write < 0 || tr2.write < 0) return 2;
    st->tape[i2] = (uint8_t)tr2.write;
    st->tape[i1] = (uint8_t)tr1.write;
    if (st->p1 < st->min_w) st->min_w = st->p1;
    if (st->p1 > st->max_w) st->max_w = st->p1;
    if (st->p2 < st->min_w) st->min_w = st->p2;
    if (st->p2 > st->max_w) st->max_w = st->p2;
    st->p1 += tr1.dir; st->p2 += tr2.dir;
    st->s1 = tr1.next; st->s2 = tr2.next;
    if (st->p1 == st->p2) return 1;
    return 0;
}

#define HT_SIZE (1 << 16)
#define HT_MASK (HT_SIZE - 1)
typedef struct { uint64_t hash; int step, p1, p2; uint8_t s1, s2; } HTEntry;
static HTEntry ht1[HT_SIZE], ht2[HT_SIZE];

int main() {
    FILE *f = fopen("p1_oob.txt", "r");
    if (!f) { perror("fopen"); return 1; }
    FILE *f_sep = fopen("oob_separated_cand.txt", "w");
    FILE *f_rem = fopen("oob_rem.txt", "w");

    char line[512];
    int total = 0, sep = 0, rem = 0;
    static SimState st;

    while (fgets(line, sizeof(line), f)) {
        // Format: idx \t t \t p1 \t p2 \t s1  s2
        int idx, t_oob, p1_oob, p2_oob;
        char s1[64], s2[64];
        if (sscanf(line, "%d\t%d\t%d\t%d\t%63s %63s", &idx, &t_oob, &p1_oob, &p2_oob, s1, s2) != 6) continue;
        total++;
        Agent a1, a2;
        parse_agent(s1, &a1); parse_agent(s2, &a2);

        init_sim(&st);
        memset(ht1, 0, sizeof(ht1));
        memset(ht2, 0, sizeof(ht2));

        int a1_p = 0, a1_dx = 0, a2_p = 0, a2_dx = 0;
        int max_p1 = 0, min_p2 = 2;
        int min_p1_after = 1e9, max_p1_after = -1e9;
        int min_p2_after = 1e9, max_p2_after = -1e9;

        int t;
        for (t = 1; t <= 50000; t++) {
            int res = step_sim(&a1, &a2, &st);
            if (res != 0) break;
            if (t >= 10000) {
                if (st.p1 < min_p1_after) min_p1_after = st.p1;
                if (st.p1 > max_p1_after) max_p1_after = st.p1;
                if (st.p2 < min_p2_after) min_p2_after = st.p2;
                if (st.p2 > max_p2_after) max_p2_after = st.p2;
            }
        }
        if (max_p1_after < min_p2_after) {
            sep++;
            fprintf(f_sep, "%d\t[%d,%d]\t[%d,%d]\t%s  %s\n", idx, min_p1_after, max_p1_after, min_p2_after, max_p2_after, s1, s2);
        } else {
            rem++;
            fprintf(f_rem, "%d\t%d\t%d\t%d\t%s  %s\n", idx, t_oob, p1_oob, p2_oob, s1, s2);
        }
    }
    printf("OOB Total=%d DisjointAfter10k=%d Rem=%d\n", total, sep, rem);
    fclose(f); fclose(f_sep); fclose(f_rem);
    return 0;
}
