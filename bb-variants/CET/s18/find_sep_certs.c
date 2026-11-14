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
typedef struct { uint64_t hash; int step, pos; uint8_t st; } HTEntry;
static HTEntry ht1[HT_SIZE], ht2[HT_SIZE];

static inline uint64_t hash_win(const uint8_t *tape, int pos, int st) {
    uint64_t h = (uint64_t)st * 0x9e3779b97f4a7c15ULL;
    uint64_t w = 0;
    for (int d = -20; d <= 20; d++) {
        int idx = pos + d + TAPE_MID;
        uint8_t b = (idx >= 0 && idx < TAPE_SIZE) ? tape[idx] : 0;
        w = (w * 31) ^ b;
    }
    return h ^ (w * 0xbf58476d1ce4e5b9ULL);
}

int main() {
    FILE *f = fopen("oob_separated_cand.txt", "r");
    if (!f) { perror("fopen"); return 1; }
    FILE *f_ok = fopen("oob_sep_certs.txt", "w");
    FILE *f_rem = fopen("oob_sep_rem.txt", "w");

    char line[512];
    int total = 0, ok = 0, rem = 0;
    static SimState st, s_base, s_test;

    while (fgets(line, sizeof(line), f)) {
        int idx;
        char b1[64], b2[64], s1[64], s2[64];
        if (sscanf(line, "%d\t%63s\t%63s\t%63s %63s", &idx, b1, b2, s1, s2) != 5) continue;
        total++;
        Agent a1, a2;
        parse_agent(s1, &a1); parse_agent(s2, &a2);

        init_sim(&st);
        memset(ht1, 0, sizeof(ht1));
        memset(ht2, 0, sizeof(ht2));

        int t0 = 10000;
        int sim_ok = 1;
        for (int t = 0; t < t0; t++) {
            if (step_sim(&a1, &a2, &st) != 0) { sim_ok = 0; break; }
        }
        if (!sim_ok) { rem++; fprintf(f_rem, "%s", line); continue; }

        int f1 = 0, t1_0 = 0, p1 = 0, dx1 = 0, bud1 = 30;
        int f2 = 0, t2_0 = 0, p2 = 0, dx2 = 0, bud2 = 30;

        for (int t = 0; t < 40000; t++) {
            if (!f1 && bud1 > 0) {
                uint64_t h1 = hash_win(st.tape, st.p1, st.s1);
                uint32_t sl = (uint32_t)(h1 & HT_MASK);
                if (ht1[sl].step > 0 && ht1[sl].hash == h1 && ht1[sl].st == st.s1) {
                    int cand_dx = st.p1 - ht1[sl].pos;
                    int cand_p = (t + 1) - ht1[sl].step;
                    if (cand_dx <= 0 && cand_p > 0) {
                        bud1--;
                        f1 = 1; t1_0 = t0 + ht1[sl].step - 1; p1 = cand_p; dx1 = cand_dx;
                    }
                }
                ht1[sl].hash = h1; ht1[sl].step = t + 1; ht1[sl].pos = st.p1; ht1[sl].st = (uint8_t)st.s1;
            }
            if (!f2 && bud2 > 0) {
                uint64_t h2 = hash_win(st.tape, st.p2, st.s2);
                uint32_t sl = (uint32_t)(h2 & HT_MASK);
                if (ht2[sl].step > 0 && ht2[sl].hash == h2 && ht2[sl].st == st.s2) {
                    int cand_dx = st.p2 - ht2[sl].pos;
                    int cand_p = (t + 1) - ht2[sl].step;
                    if (cand_dx >= 0 && cand_p > 0) {
                        bud2--;
                        f2 = 1; t2_0 = t0 + ht2[sl].step - 1; p2 = cand_p; dx2 = cand_dx;
                    }
                }
                ht2[sl].hash = h2; ht2[sl].step = t + 1; ht2[sl].pos = st.p2; ht2[sl].st = (uint8_t)st.s2;
            }
            if (f1 && f2) break;
            if (step_sim(&a1, &a2, &st) != 0) { sim_ok = 0; break; }
        }

        if (!sim_ok || !f1 || !f2) { rem++; fprintf(f_rem, "%s", line); continue; }

        int check_t0 = (t1_0 > t2_0) ? t1_0 : t2_0;
        init_sim(&s_base);
        for (int t = 0; t < check_t0; t++) {
            if (step_sim(&a1, &a2, &s_base) != 0) { sim_ok = 0; break; }
        }
        if (!sim_ok) { rem++; fprintf(f_rem, "%s", line); continue; }

        int max_p = (p1 > p2) ? p1 : p2;
        s_test = s_base;
        int r1_min = s_test.p1, r1_max = s_test.p1;
        int r2_min = s_test.p2, r2_max = s_test.p2;
        int p1_end = 0, s1_end = 0, p2_end = 0, s2_end = 0;
        static uint8_t tp1[TAPE_SIZE], tp2[TAPE_SIZE];

        for (int t = 1; t <= max_p; t++) {
            if (step_sim(&a1, &a2, &s_test) != 0) { sim_ok = 0; break; }
            if (t < p1) {
                if (s_test.p1 < r1_min) r1_min = s_test.p1;
                if (s_test.p1 > r1_max) r1_max = s_test.p1;
            }
            if (t < p2) {
                if (s_test.p2 < r2_min) r2_min = s_test.p2;
                if (s_test.p2 > r2_max) r2_max = s_test.p2;
            }
            if (t == p1) {
                p1_end = s_test.p1; s1_end = s_test.s1;
                memcpy(tp1 + r1_min + dx1 + TAPE_MID, s_test.tape + r1_min + dx1 + TAPE_MID, r1_max - r1_min + 1);
            }
            if (t == p2) {
                p2_end = s_test.p2; s2_end = s_test.s2;
                memcpy(tp2 + r2_min + dx2 + TAPE_MID, s_test.tape + r2_min + dx2 + TAPE_MID, r2_max - r2_min + 1);
            }
        }
        if (!sim_ok || r1_max >= r2_min || p1_end - s_base.p1 != dx1 || s1_end != s_base.s1 ||
            p2_end - s_base.p2 != dx2 || s2_end != s_base.s2) {
            rem++; fprintf(f_rem, "%s", line); continue;
        }
        int valid = 1;
        if (dx1 < 0) {
            for (int z = s_base.min_w; z < r1_min; z++) if (s_base.tape[z + TAPE_MID] != 0) { valid = 0; break; }
        }
        for (int z = r1_min; z <= r1_max && valid; z++) {
            if (tp1[z + dx1 + TAPE_MID] != s_base.tape[z + TAPE_MID]) valid = 0;
        }
        if (dx2 > 0 && valid) {
            for (int z = r2_max + 1; z <= s_base.max_w; z++) if (s_base.tape[z + TAPE_MID] != 0) { valid = 0; break; }
        }
        for (int z = r2_min; z <= r2_max && valid; z++) {
            if (tp2[z + dx2 + TAPE_MID] != s_base.tape[z + TAPE_MID]) valid = 0;
        }
        if (valid) {
            ok++;
            fprintf(f_ok, "%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%s  %s\n",
                    idx, check_t0, p1, dx1, r1_min, r1_max, p2, dx2, r2_min, r2_max, s1, s2);
        } else {
            rem++; fprintf(f_rem, "%s", line);
        }
    }
    printf("SepCand Total=%d Verified=%d Rem=%d\n", total, ok, rem);
    fclose(f); fclose(f_ok); fclose(f_rem);
    return 0;
}
