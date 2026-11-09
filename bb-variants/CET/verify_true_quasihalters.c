#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { int8_t w, mv, ns; } Tr;
typedef struct { Tr t[2][2]; } Agent;

static inline void decode_agent(uint16_t code, Agent *ag) {
    for (int s = 0; s < 2; s++) {
        for (int r = 0; r < 2; r++) {
            int shift = (s * 2 + r) * 3;
            int tr = (code >> shift) & 7;
            ag->t[s][r].w = tr & 1;
            ag->t[s][r].mv = (tr & 2) ? 1 : -1;
            ag->t[s][r].ns = (tr & 4) ? 1 : 0;
        }
    }
}

static inline void fmt_agent_bb(uint16_t code, char *buf) {
    Agent ag;
    decode_agent(code, &ag);
    char *p = buf;
    for (int s = 0; s < 2; s++) {
        if (s > 0) *p++ = '_';
        for (int r = 0; r < 2; r++) {
            *p++ = '0' + ag.t[s][r].w;
            *p++ = ag.t[s][r].mv > 0 ? 'R' : 'L';
            *p++ = 'A' + ag.t[s][r].ns;
        }
    }
    *p = 0;
}

#define TAPE_SIZE 131072
#define TAPE_OFF   65536
#define MAX_STEPS  100000

static uint8_t tape[TAPE_SIZE];
static uint16_t vis[TAPE_SIZE];
static uint16_t mk = 0;

typedef struct {
    int16_t rel_p;
    int16_t p1;
    uint8_t s1, s2;
    int step;
    int cols;
    uint64_t hash;
} Hist;

static Hist hist[4096];

static uint64_t Z_REL[64];
static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void init_z() {
    uint64_t seed = 0x8849204820491024ULL;
    for (int i = 0; i < 64; i++) Z_REL[i] = splitmix64(&seed);
}

static inline uint64_t get_tape_hash(int base_p) {
    uint64_t h = 0;
    for (int d = -16; d <= 32; d++) {
        int pos = TAPE_OFF + base_p + d;
        if (pos >= 0 && pos < TAPE_SIZE && vis[pos] == mk && tape[pos]) {
            h ^= Z_REL[d + 16];
        }
    }
    return h;
}

// Return 1 if certified quasi-halt, with details
int test_machine(uint16_t c1, uint16_t c2, int *out_last_col, int *out_cols, int *out_period, int *out_drift, char *out_type) {
    Agent ag1, ag2;
    decode_agent(c1, &ag1);
    decode_agent(c2, &ag2);

    mk++;
    if (mk == 0) {
        memset(vis, 0, sizeof(vis));
        mk = 1;
    }

    int p1 = 0, p2 = 2;
    int s1 = 0, s2 = 0;
    int cols = 0;
    int last_col = 0;

    int hist_cnt = 0;

    for (int step = 1; step <= MAX_STEPS; step++) {
        int idx1 = TAPE_OFF + p1;
        int idx2 = TAPE_OFF + p2;
        if (idx1 < 20 || idx1 >= TAPE_SIZE - 20 || idx2 < 20 || idx2 >= TAPE_SIZE - 20) {
            // Tape bound reached
            break;
        }

        int r1 = (vis[idx1] == mk) ? tape[idx1] : 0;
        int r2 = (vis[idx2] == mk) ? tape[idx2] : 0;

        Tr t1 = ag1.t[s1][r1];
        Tr t2 = ag2.t[s2][r2];

        tape[idx2] = t2.w; vis[idx2] = mk;
        tape[idx1] = t1.w; vis[idx1] = mk;

        p1 += t1.mv; s1 = t1.ns;
        p2 += t2.mv; s2 = t2.ns;

        if (p1 == p2) {
            cols++;
            last_col = step;
            hist_cnt = 0; // reset history on collision
            continue;
        }

        // Only search for cycles if we haven't collided for at least 15 steps
        if (step - last_col > 15) {
            uint64_t th = get_tape_hash(p1);
            int16_t rel = (int16_t)(p2 - p1);

            // Check history
            for (int h = hist_cnt - 1; h >= 0 && h >= hist_cnt - 2000; h--) {
                if (hist[h].rel_p == rel && hist[h].s1 == s1 && hist[h].s2 == s2 && hist[h].hash == th) {
                    int period = step - hist[h].step;
                    int drift1 = p1 - hist[h].p1;
                    int drift2 = p2 - (hist[h].p1 + hist[h].rel_p);

                    if (drift1 == drift2 && hist[h].cols == cols) {
                        // Certified cycle with 0 collisions in period!
                        *out_last_col = last_col;
                        *out_cols = cols;
                        *out_period = period;
                        *out_drift = drift1;
                        if (drift1 == 0) strcpy(out_type, "Stationary");
                        else strcpy(out_type, "Translated");
                        return 1;
                    }
                }
            }

            int hidx = hist_cnt % 4096;
            hist[hidx].rel_p = rel;
            hist[hidx].p1 = p1;
            hist[hidx].s1 = s1;
            hist[hidx].s2 = s2;
            hist[hidx].step = step;
            hist[hidx].cols = cols;
            hist[hidx].hash = th;
            hist_cnt++;
        }
    }
    return 0;
}

int main() {
    init_z();
    printf("Reading cet1_candidates.txt...\n");
    FILE *f = fopen("cet1_candidates.txt", "r");
    if (!f) { printf("Failed to open cet1_candidates.txt\n"); return 1; }

    char line[256];
    int tested = 0;
    int champions_found = 0;
    int max_recorded = 110;

    while (fgets(line, sizeof(line), f)) {
        int last_col, cols, max_step;
        char m1[32], m2[32];
        if (sscanf(line, "%d | %d | %d | %15[^|]|%15s", &last_col, &cols, &max_step, m1, m2) != 5) continue;
        if (last_col < 110) continue;

        // Parse codes
        // We can re-simulate directly by decoding strings or looping
        // Let's decode strings back to codes
        // For simplicity, let's parse m1 and m2
        uint16_t c1 = 0, c2 = 0;
        // Parse m1
        for (int s = 0; s < 2; s++) {
            for (int r = 0; r < 2; r++) {
                int off = (s == 0) ? (r * 3) : (7 + r * 3);
                int w = m1[off] - '0';
                int mv = (m1[off+1] == 'R') ? 1 : 0;
                int ns = (m1[off+2] == 'B') ? 1 : 0;
                int tr = w | (mv << 1) | (ns << 2);
                c1 |= (tr << ((s * 2 + r) * 3));
            }
        }
        // Parse m2
        for (int s = 0; s < 2; s++) {
            for (int r = 0; r < 2; r++) {
                int off = (s == 0) ? (r * 3) : (7 + r * 3);
                int w = m2[off] - '0';
                int mv = (m2[off+1] == 'R') ? 1 : 0;
                int ns = (m2[off+2] == 'B') ? 1 : 0;
                int tr = w | (mv << 1) | (ns << 2);
                c2 |= (tr << ((s * 2 + r) * 3));
            }
        }

        int true_last, true_cols, period, drift;
        char type[32];
        if (test_machine(c1, c2, &true_last, &true_cols, &period, &drift, type)) {
            if (true_last > max_recorded) {
                max_recorded = true_last;
                champions_found++;
                printf("🏆 NEW RECORD: %d steps (%d cols, %s Period %d, Drift %+d) | %s|%s\n",
                       true_last, true_cols, type, period, drift, m1, m2);
                fflush(stdout);
            }
        }
        tested++;
    }
    fclose(f);
    printf("Finished testing %d candidates! Found %d new high-step champions.\n", tested, champions_found);
    return 0;
}
