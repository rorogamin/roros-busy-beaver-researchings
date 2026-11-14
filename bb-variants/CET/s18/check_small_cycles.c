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

#define TAPE_SIZE 4096
#define TAPE_MID 2048

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

#define HT_SIZE (1 << 18)
#define HT_MASK (HT_SIZE - 1)
typedef struct { uint64_t hash; int step, p1, p2; uint8_t s1, s2; } HTEntry;
static HTEntry ht[HT_SIZE];

static inline uint64_t hash_full(const SimState *st) {
    uint64_t h = ((uint64_t)st->p1 << 32) ^ (uint32_t)st->p2 ^ ((uint64_t)(st->s1 * 3 + st->s2) << 48);
    for (int z = st->min_w; z <= st->max_w; z++) {
        h = h * 1315423911ULL + st->tape[z + TAPE_MID] + 1;
    }
    return h;
}

int main() {
    FILE *f = fopen("p1_rem.txt", "r");
    if (!f) { perror("fopen"); return 1; }
    FILE *f_cyc = fopen("small_fixed_cycles.txt", "w");
    FILE *f_ctr = fopen("small_counters.txt", "w");

    char line[512];
    int tested = 0, cyc = 0, ctr = 0;
    static SimState st, s0, s1;

    while (fgets(line, sizeof(line), f)) {
        int idx, p1, p2, mn, mx;
        char ag1_s[64], ag2_s[64];
        if (sscanf(line, "%d\t%d\t%d\t%d\t%d\t%63s %63s", &idx, &p1, &p2, &mn, &mx, ag1_s, ag2_s) != 7) continue;
        if (mx - mn >= 100) continue;
        tested++;

        Agent a1, a2;
        parse_agent(ag1_s, &a1); parse_agent(ag2_s, &a2);

        init_sim(&st);
        memset(ht, 0, sizeof(ht));
        int found = 0, f_t0 = 0, f_p = 0, f_wmin = 0, f_wmax = 0;
        int budget = 5;

        for (int t = 1; t <= 2000000; t++) {
            if (step_sim(&a1, &a2, &st) != 0) break;
            if (t >= 1000) {
                uint64_t h = hash_full(&st);
                uint32_t sl = (uint32_t)(h & HT_MASK);
                if (budget > 0 && ht[sl].step > 0 && ht[sl].hash == h &&
                    ht[sl].p1 == st.p1 && ht[sl].p2 == st.p2 &&
                    ht[sl].s1 == st.s1 && ht[sl].s2 == st.s2) {
                    budget--;
                    int t0 = ht[sl].step;
                    int p = t - t0;
                    // Exact verify
                    init_sim(&s0);
                    for (int k = 0; k < t0; k++) step_sim(&a1, &a2, &s0);
                    s1 = s0;
                    int rmin = s1.p1 < s1.p2 ? s1.p1 : s1.p2;
                    int rmax = s1.p1 > s1.p2 ? s1.p1 : s1.p2;
                    int ok = 1;
                    for (int k = 0; k < p; k++) {
                        if (s1.p1 < rmin) rmin = s1.p1;
                        if (s1.p1 > rmax) rmax = s1.p1;
                        if (s1.p2 < rmin) rmin = s1.p2;
                        if (s1.p2 > rmax) rmax = s1.p2;
                        if (step_sim(&a1, &a2, &s1) != 0) { ok = 0; break; }
                    }
                    if (ok && s1.p1 == s0.p1 && s1.p2 == s0.p2 && s1.s1 == s0.s1 && s1.s2 == s0.s2) {
                        for (int z = rmin; z <= rmax; z++) {
                            if (s1.tape[z + TAPE_MID] != s0.tape[z + TAPE_MID]) { ok = 0; break; }
                        }
                        if (ok) {
                            found = 1; f_t0 = t0; f_p = p; f_wmin = rmin; f_wmax = rmax;
                            break;
                        }
                    }
                }
                ht[sl].hash = h; ht[sl].step = t;
                ht[sl].p1 = st.p1; ht[sl].p2 = st.p2;
                ht[sl].s1 = (uint8_t)st.s1; ht[sl].s2 = (uint8_t)st.s2;
            }
        }
        if (found) {
            cyc++;
            fprintf(f_cyc, "%d\t%d\t%d\t0\t%d\t%d\t%s  %s\n", idx, f_t0, f_p, f_wmin, f_wmax, ag1_s, ag2_s);
        } else {
            ctr++;
            fprintf(f_ctr, "%d\t%d\t%d\t%d\t%d\t%s  %s\n", idx, st.p1, st.p2, st.min_w, st.max_w, ag1_s, ag2_s);
        }
    }
    printf("Small (<100) Tested=%d FixedCycles=%d Counters/Other=%d\n", tested, cyc, ctr);
    fclose(f); fclose(f_cyc); fclose(f_ctr);
    return 0;
}
