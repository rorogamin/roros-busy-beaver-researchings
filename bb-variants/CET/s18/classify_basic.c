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

#define TAPE_SIZE 262144
#define TAPE_MID (TAPE_SIZE / 2)
#define MAX_STEPS 50000

typedef struct {
    int p1, p2;
    int s1, s2;
    int min_w, max_w; // min and max cell ever written (or 0..2 initially)
    uint8_t tape[TAPE_SIZE];
} SimState;

static void init_sim(SimState *st) {
    st->p1 = 0;
    st->p2 = 2;
    st->s1 = 0;
    st->s2 = 0;
    st->min_w = 0;
    st->max_w = 2;
    memset(st->tape, 0, TAPE_SIZE);
}

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
    st->tape[idx1] = (uint8_t)tr1.write;
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

// Snapshots for cycle detection: store at checkpoints or hash
#define HT_SIZE (1 << 16)
#define HT_MASK (HT_SIZE - 1)

typedef struct {
    uint64_t hash;
    int step;
    int p1, p2;
    uint8_t s1, s2;
} HTEntry;

static HTEntry ht[HT_SIZE];

static inline uint64_t hash_config(const SimState *st) {
    uint64_t h = (uint64_t)(st->s1 * 3 + st->s2) * 0x9e3779b97f4a7c15ULL;
    int diff = st->p2 - st->p1;
    h ^= (uint64_t)(uint32_t)diff * 0xbf58476d1ce4e5b9ULL;
    // Hash 16 cells around p1 and 16 cells around p2
    uint64_t w1 = 0, w2 = 0;
    for (int d = -8; d < 8; d++) {
        int i1 = st->p1 + d + TAPE_MID;
        int i2 = st->p2 + d + TAPE_MID;
        uint8_t b1 = (i1 >= 0 && i1 < TAPE_SIZE) ? st->tape[i1] : 0;
        uint8_t b2 = (i2 >= 0 && i2 < TAPE_SIZE) ? st->tape[i2] : 0;
        w1 = (w1 << 1) | b1;
        w2 = (w2 << 1) | b2;
    }
    h ^= w1 * 0x94d049bb133111ebULL;
    h ^= (w2 << 17) ^ (w2 >> 13);
    h ^= (h >> 30);
    h *= 0xbf58476d1ce4e5b9ULL;
    h ^= (h >> 27);
    return h;
}

// Verify exact cycle from t0 with period p, dx = p1(t0+p) - p1(t0)
// Returns 1 if verified, 0 otherwise
static int verify_joint_cycle(const Agent *a1, const Agent *a2, int t0, int p, int *out_dx, int *out_wmin, int *out_wmax) {
    static SimState s0, s1;
    init_sim(&s0);
    for (int t = 0; t < t0; t++) {
        if (step_sim(a1, a2, &s0) != 0) return 0;
    }
    int init_min_w = s0.min_w;
    int init_max_w = s0.max_w;

    s1 = s0;
    int rmin = s1.p1 < s1.p2 ? s1.p1 : s1.p2;
    int rmax = s1.p1 > s1.p2 ? s1.p1 : s1.p2;
    for (int t = 0; t < p; t++) {
        if (s1.p1 < rmin) rmin = s1.p1;
        if (s1.p1 > rmax) rmax = s1.p1;
        if (s1.p2 < rmin) rmin = s1.p2;
        if (s1.p2 > rmax) rmax = s1.p2;
        if (step_sim(a1, a2, &s1) != 0) return 0;
    }
    int dx1 = s1.p1 - s0.p1;
    int dx2 = s1.p2 - s0.p2;
    if (dx1 != dx2 || s1.s1 != s0.s1 || s1.s2 != s0.s2) return 0;
    int dx = dx1;

    if (dx == 0) {
        // Fixed cycle: tape on [rmin, rmax] must be identical
        for (int z = rmin; z <= rmax; z++) {
            if (s1.tape[z + TAPE_MID] != s0.tape[z + TAPE_MID]) return 0;
        }
        *out_dx = 0;
        *out_wmin = rmin;
        *out_wmax = rmax;
        return 1;
    } else if (dx > 0) {
        // Translated right:
        // 1. All cells > rmax at t0 must be 0 (i.e. init_max_w <= rmax, or check tape[z]==0 for rmax < z <= init_max_w)
        for (int z = rmax + 1; z <= init_max_w; z++) {
            if (s0.tape[z + TAPE_MID] != 0) return 0;
        }
        // 2. Tape on [rmin + dx, rmax + dx] at t0+p must equal tape on [rmin, rmax] at t0
        for (int z = rmin; z <= rmax; z++) {
            if (s1.tape[z + dx + TAPE_MID] != s0.tape[z + TAPE_MID]) return 0;
        }
        *out_dx = dx;
        *out_wmin = rmin;
        *out_wmax = rmax;
        return 1;
    } else {
        // Translated left (dx < 0):
        // 1. All cells < rmin at t0 must be 0
        for (int z = init_min_w; z < rmin; z++) {
            if (s0.tape[z + TAPE_MID] != 0) return 0;
        }
        // 2. Tape on [rmin + dx, rmax + dx] at t0+p must equal tape on [rmin, rmax] at t0
        for (int z = rmin; z <= rmax; z++) {
            if (s1.tape[z + dx + TAPE_MID] != s0.tape[z + TAPE_MID]) return 0;
        }
        *out_dx = dx;
        *out_wmin = rmin;
        *out_wmax = rmax;
        return 1;
    }
}

// Verify separated agents:
// Run to t0 = 50000 (or check at t0), then run 50000 more steps to find independent periods p1, p2!
// Actually, let's check if at some t0, a1 and a2 are in disjoint halves and each loops independently.
static int verify_separated(const Agent *a1, const Agent *a2, int *out_t0, int *out_p1, int *out_dx1, int *out_p2, int *out_dx2) {
    static SimState st;
    init_sim(&st);
    // Run to t0 = 15000
    int t0 = 15000;
    for (int t = 0; t < t0; t++) {
        if (step_sim(a1, a2, &st) != 0) return 0;
    }
    if (st.p1 >= st.p2) return 0;

    static HTEntry ht1[HT_SIZE], ht2[HT_SIZE];
    memset(ht1, 0, sizeof(ht1));
    memset(ht2, 0, sizeof(ht2));

    int a1_found = 0, a1_t0 = 0, a1_p = 0, a1_dx = 0;
    int a2_found = 0, a2_t0 = 0, a2_p = 0, a2_dx = 0;

    int min_p2 = st.p2, max_p1 = st.p1;
    for (int t = 0; t < 20000; t++) {
        if (st.p1 > max_p1) max_p1 = st.p1;
        if (st.p2 < min_p2) min_p2 = st.p2;
        if (max_p1 >= min_p2) return 0; // Not separated!

        if (!a1_found) {
            uint64_t h1 = (uint64_t)st.s1 * 0x9e3779b97f4a7c15ULL;
            uint64_t w1 = 0;
            for (int d = -8; d < 8; d++) {
                int idx = st.p1 + d + TAPE_MID;
                w1 = (w1 << 1) | ((idx >= 0 && idx < TAPE_SIZE) ? st.tape[idx] : 0);
            }
            h1 ^= w1 * 0x94d049bb133111ebULL;
            uint32_t slot = (uint32_t)(h1 & HT_MASK);
            if (ht1[slot].step > 0 && ht1[slot].hash == h1) {
                int cand_t0 = t0 + ht1[slot].step - 1;
                int cand_p = (t0 + t) - cand_t0;
                int cand_dx = st.p1 - ht1[slot].p1;
                if (cand_dx <= 0 && cand_p > 0) {
                    a1_found = 1; a1_t0 = cand_t0; a1_p = cand_p; a1_dx = cand_dx;
                }
            }
            ht1[slot].hash = h1;
            ht1[slot].step = t + 1;
            ht1[slot].p1 = st.p1;
        }
        if (!a2_found) {
            uint64_t h2 = (uint64_t)st.s2 * 0x9e3779b97f4a7c15ULL;
            uint64_t w2 = 0;
            for (int d = -8; d < 8; d++) {
                int idx = st.p2 + d + TAPE_MID;
                w2 = (w2 << 1) | ((idx >= 0 && idx < TAPE_SIZE) ? st.tape[idx] : 0);
            }
            h2 ^= w2 * 0x94d049bb133111ebULL;
            uint32_t slot = (uint32_t)(h2 & HT_MASK);
            if (ht2[slot].step > 0 && ht2[slot].hash == h2) {
                int cand_t0 = t0 + ht2[slot].step - 1;
                int cand_p = (t0 + t) - cand_t0;
                int cand_dx = st.p2 - ht2[slot].p2;
                if (cand_dx >= 0 && cand_p > 0) {
                    a2_found = 1; a2_t0 = cand_t0; a2_p = cand_p; a2_dx = cand_dx;
                }
            }
            ht2[slot].hash = h2;
            ht2[slot].step = t + 1;
            ht2[slot].p2 = st.p2;
        }
        if (a1_found && a2_found) break;
        if (step_sim(a1, a2, &st) != 0) return 0;
    }
    if (!a1_found || !a2_found) return 0;

    // Exact verification of separated cycles!
    int check_t0 = (a1_t0 > a2_t0) ? a1_t0 : a2_t0;
    static SimState s_base, s_test;
    init_sim(&s_base);
    for (int t = 0; t < check_t0; t++) {
        if (step_sim(a1, a2, &s_base) != 0) return 0;
    }
    int init_min_w = s_base.min_w;
    int init_max_w = s_base.max_w;

    // Verify Agent 1 over a1_p steps from check_t0 (using dummy/actual Agent 2, but checking max_r1 < min_r2)
    int max_steps_need = (a1_p > a2_p) ? a1_p : a2_p;
    s_test = s_base;
    int r1_min = s_test.p1, r1_max = s_test.p1;
    int r2_min = s_test.p2, r2_max = s_test.p2;

    int p1_end_pos = 0, p1_end_st = 0;
    int p2_end_pos = 0, p2_end_st = 0;
    static uint8_t tape_p1[TAPE_SIZE], tape_p2[TAPE_SIZE];

    for (int t = 1; t <= max_steps_need; t++) {
        if (step_sim(a1, a2, &s_test) != 0) return 0;
        if (t <= a1_p) {
            if (s_test.p1 < r1_min) r1_min = s_test.p1;
            if (s_test.p1 > r1_max) r1_max = s_test.p1;
        }
        if (t <= a2_p) {
            if (s_test.p2 < r2_min) r2_min = s_test.p2;
            if (s_test.p2 > r2_max) r2_max = s_test.p2;
        }
        if (t == a1_p) {
            p1_end_pos = s_test.p1;
            p1_end_st = s_test.s1;
            memcpy(tape_p1 + r1_min + a1_dx + TAPE_MID, s_test.tape + r1_min + a1_dx + TAPE_MID, (r1_max - r1_min + 1));
        }
        if (t == a2_p) {
            p2_end_pos = s_test.p2;
            p2_end_st = s_test.s2;
            memcpy(tape_p2 + r2_min + a2_dx + TAPE_MID, s_test.tape + r2_min + a2_dx + TAPE_MID, (r2_max - r2_min + 1));
        }
    }
    // Include start positions in r1, r2
    if (s_base.p1 < r1_min) r1_min = s_base.p1;
    if (s_base.p1 > r1_max) r1_max = s_base.p1;
    if (s_base.p2 < r2_min) r2_min = s_base.p2;
    if (s_base.p2 > r2_max) r2_max = s_base.p2;

    if (r1_max >= r2_min) return 0; // Regions must be strictly disjoint!
    if (p1_end_pos - s_base.p1 != a1_dx || p1_end_st != s_base.s1) return 0;
    if (p2_end_pos - s_base.p2 != a2_dx || p2_end_st != s_base.s2) return 0;
    if (a1_dx > 0 || a2_dx < 0) return 0;

    if (a1_dx < 0) {
        for (int z = init_min_w; z < r1_min; z++) {
            if (s_base.tape[z + TAPE_MID] != 0) return 0;
        }
    }
    for (int z = r1_min; z <= r1_max; z++) {
        if (tape_p1[z + a1_dx + TAPE_MID] != s_base.tape[z + TAPE_MID]) return 0;
    }
    if (a2_dx > 0) {
        for (int z = r2_max + 1; z <= init_max_w; z++) {
            if (s_base.tape[z + TAPE_MID] != 0) return 0;
        }
    }
    for (int z = r2_min; z <= r2_max; z++) {
        if (tape_p2[z + a2_dx + TAPE_MID] != s_base.tape[z + TAPE_MID]) return 0;
    }

    *out_t0 = check_t0;
    *out_p1 = a1_p; *out_dx1 = a1_dx;
    *out_p2 = a2_p; *out_dx2 = a2_dx;
    return 1;
}

int main(int argc, char **argv) {
    const char *path = (argc > 1) ? argv[1] : "residue_s18.txt";
    FILE *f = fopen(path, "r");
    if (!f) { perror("fopen"); return 1; }

    FILE *f_halt = fopen("s18_halted.txt", "w");
    FILE *f_undef = fopen("s18_undef.txt", "w");
    FILE *f_cyc = fopen("s18_cycles.txt", "w");
    FILE *f_sep = fopen("s18_separated.txt", "w");
    FILE *f_rem = fopen("s18_rem.txt", "w");

    char line[256];
    int total = 0, halted = 0, undef = 0, cyc = 0, sep = 0, rem = 0;
    static SimState st;

    while (fgets(line, sizeof(line), f)) {
        size_t len = strlen(line);
        while (len > 0 && (line[len-1] == '\n' || line[len-1] == '\r' || line[len-1] == ' ')) {
            line[--len] = '\0';
        }
        if (len == 0) continue;
        total++;

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
        memset(ht, 0, sizeof(ht));
        int res = 0, t = 0;
        int cyc_found = 0, c_t0 = 0, c_p = 0, c_dx = 0, c_wmin = 0, c_wmax = 0;
        int verify_budget = 20;

        for (t = 1; t <= MAX_STEPS; t++) {
            res = step_sim(&a1, &a2, &st);
            if (res != 0) break;
            if (t >= 10) {
                uint64_t h = hash_config(&st);
                uint32_t slot = (uint32_t)(h & HT_MASK);
                if (verify_budget > 0 && ht[slot].step > 0 && ht[slot].hash == h &&
                    ht[slot].s1 == st.s1 && ht[slot].s2 == st.s2 &&
                    (st.p1 - ht[slot].p1) == (st.p2 - ht[slot].p2)) {
                    int cand_t0 = ht[slot].step;
                    int cand_p = t - cand_t0;
                    if (cand_p > 0 && cand_p <= 50000) {
                        verify_budget--;
                        if (verify_joint_cycle(&a1, &a2, cand_t0, cand_p, &c_dx, &c_wmin, &c_wmax)) {
                            cyc_found = 1;
                            c_t0 = cand_t0;
                            c_p = cand_p;
                            break;
                        }
                    }
                }
                ht[slot].hash = h;
                ht[slot].step = t;
                ht[slot].p1 = st.p1;
                ht[slot].p2 = st.p2;
                ht[slot].s1 = (uint8_t)st.s1;
                ht[slot].s2 = (uint8_t)st.s2;
            }
        }

        if (res == 1) {
            halted++;
            fprintf(f_halt, "%d\t%d\t%s\n", total, t, line);
        } else if (res == 2) {
            undef++;
            fprintf(f_undef, "%d\t%d\t%s\n", total, t, line);
        } else if (cyc_found) {
            cyc++;
            fprintf(f_cyc, "%d\t%d\t%d\t%d\t%d\t%d\t%s\n", total, c_t0, c_p, c_dx, c_wmin, c_wmax, line);
        } else {
            int st0, sp1, sdx1, sp2, sdx2;
            if (verify_separated(&a1, &a2, &st0, &sp1, &sdx1, &sp2, &sdx2)) {
                sep++;
                fprintf(f_sep, "%d\t%d\t%d\t%d\t%d\t%d\t%s\n", total, st0, sp1, sdx1, sp2, sdx2, line);
            } else {
                rem++;
                fprintf(f_rem, "%d\t%s\n", total, line);
            }
        }

        if (total % 2000 == 0) {
            fprintf(stderr, "Processed %d/19000: halt=%d undef=%d cyc=%d sep=%d rem=%d\n",
                    total, halted, undef, cyc, sep, rem);
            fflush(stderr);
        }
    }

    printf("DONE Total=%d Halt=%d Undef=%d JointCycle=%d Separated=%d Rem=%d\n",
           total, halted, undef, cyc, sep, rem);

    fclose(f); fclose(f_halt); fclose(f_undef); fclose(f_cyc); fclose(f_sep); fclose(f_rem);
    return 0;
}
