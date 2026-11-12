#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define TAPE_SIZE (1 << 20)
#define OFF (1 << 19)

typedef struct { int w, d, ns; } Tr;
typedef struct { Tr t[2][4][3]; int n, k; } M;

static int parse_agent(const char *s, Tr *t, int n, int k) {
    int count = 0;
    const char *p = s;
    for (int st = 0; st < n; st++) {
        for (int sym = 0; sym < k; sym++) {
            if (*p == 0) return 0;
            if (p[0] == '-' && p[1] == '-' && p[2] == '-') {
                /* Unused transition: choose a harmless filler. */
                t[st * k + sym].w = 0;
                t[st * k + sym].d = 1;
                t[st * k + sym].ns = 0;
                p += 3;
            } else {
                t[st * k + sym].w = p[0] - '0';
                t[st * k + sym].d = p[1] == 'R' ? 1 : -1;
                t[st * k + sym].ns = p[2] - 'A';
                p += 3;
            }
            count++;
        }
        if (*p == '_') p++;
    }
    return count == n * k;
}

static void fmt_agent(const Tr *t, int n, int k, char *out) {
    char *p = out;
    for (int st = 0; st < n; st++) {
        if (st) *p++ = '_';
        for (int sym = 0; sym < k; sym++) {
            *p++ = '0' + t[st * k + sym].w;
            *p++ = t[st * k + sym].d > 0 ? 'R' : 'L';
            *p++ = 'A' + t[st * k + sym].ns;
        }
    }
    *p = 0;
}

static inline uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

typedef struct {
    int collision;
    int steps;
    int p1, p2, s1, s2;
    int lo, hi;
    int same_dir;
    int d1, d2;
    int ones_growth;
    int trail_ones;
} Result;

static Result run(const Tr *a1, const Tr *a2, int n, int k, int limit) {
    static uint8_t tape[TAPE_SIZE];
    memset(tape, 0, sizeof(tape));
    int p1 = OFF, p2 = OFF + 2;
    int s1 = 0, s2 = 0;
    int lo = p1, hi = p2;
    int oldp1 = p1, oldp2 = p2;
    int oldones = 0, curones = 0;
    Result r;
    memset(&r, 0, sizeof(r));

    for (int t = 1; t <= limit; t++) {
        int r1 = tape[p1], r2 = tape[p2];
        Tr x = a1[s1 * k + r1];
        Tr y = a2[s2 * k + r2];
        tape[p1] = x.w;
        tape[p2] = y.w;
        p1 += x.d;
        p2 += y.d;
        s1 = x.ns;
        s2 = y.ns;

        if (p1 < 0 || p1 >= TAPE_SIZE || p2 < 0 || p2 >= TAPE_SIZE) {
            r.collision = -1;
            r.steps = t;
            r.p1 = p1 - OFF; r.p2 = p2 - OFF;
            r.s1 = s1; r.s2 = s2;
            return r;
        }
        if (p1 == p2) {
            r.collision = 1;
            r.steps = t;
            r.p1 = p1 - OFF; r.p2 = p2 - OFF;
            r.s1 = s1; r.s2 = s2;
            return r;
        }
        if (p1 < lo) lo = p1;
        if (p1 > hi) hi = p1;
        if (p2 < lo) lo = p2;
        if (p2 > hi) hi = p2;
        if (t == limit - 10000) {
            oldp1 = p1; oldp2 = p2;
            oldones = 0;
            for (int z = 0; z < TAPE_SIZE; z++) oldones += tape[z];
        }
    }
    r.collision = 0;
    r.steps = limit;
    r.p1 = p1 - OFF; r.p2 = p2 - OFF;
    r.s1 = s1; r.s2 = s2;
    r.lo = lo - OFF; r.hi = hi - OFF;
    r.d1 = p1 - oldp1;
    r.d2 = p2 - oldp2;
    r.same_dir = (r.d1 > 0 && r.d2 > 0) || (r.d1 < 0 && r.d2 < 0);
    for (int z = 0; z < TAPE_SIZE; z++) curones += tape[z];
    r.ones_growth = curones - oldones;

    /* The translated cycler must leave only 1s behind it. */
    r.trail_ones = 1;
    if (r.d2 > 0) {
        for (int z = p2 - 64; z < p2; z++) {
            if (z < 0 || tape[z] != 1) { r.trail_ones = 0; break; }
        }
    } else if (r.d2 < 0) {
        for (int z = p2 + 1; z <= p2 + 64; z++) {
            if (z >= TAPE_SIZE || tape[z] != 1) { r.trail_ones = 0; break; }
        }
    } else {
        r.trail_ones = 0;
    }
    return r;
}

static void search(const char *name, const char *a1s, int n, int k,
                   int trials, int limit) {
    Tr a1[8] = {{0}};
    if (!parse_agent(a1s, a1, n, k)) {
        printf("%s: bad agent1 parse\n", name);
        return;
    }
    uint64_t rng = 0x9e3779b97f4a7c15ULL ^ (uint64_t)n * 0x100000001b3ULL ^ (uint64_t)k;
    long long alive = 0, slow_same = 0, collision = 0, period1_like = 0;
    int shown = 0;
    printf("\n=== %s | trials=%d limit=%d ===\n", name, trials, limit);
    printf("Classification: 'slow_same' means the OTHER agent moves in the same direction but at <0.9 cells/step; period-1 locks are rejected.\n");

    for (int trial = 0; trial < trials; trial++) {
        Tr a2[8] = {{0}};
        for (int st = 0; st < n; st++) for (int sym = 0; sym < k; sym++) {
            uint64_t v = splitmix64(&rng);
            a2[st * k + sym].w = v % k;
            a2[st * k + sym].d = ((v >> 8) & 1) ? 1 : -1;
            a2[st * k + sym].ns = (v >> 12) % n;
        }
        Result r = run(a1, a2, n, k, limit);
        if (r.collision == 1) { collision++; continue; }
        if (r.collision < 0) continue;
        alive++;
        int ad1 = r.d1 < 0 ? -r.d1 : r.d1;
        int ad2 = r.d2 < 0 ? -r.d2 : r.d2;
        int period1_lock = (ad1 >= 9000 && ad2 >= 9000 && r.same_dir) ||
                           (ad1 <= 2 && r.ones_growth <= 0);
        if (period1_lock) { period1_like++; continue; }
        int same_sign = (r.d1 > 0 && r.d2 > 0) || (r.d1 < 0 && r.d2 < 0);
        /* The other agent must be slower than 1 cell/step, and the binary
           counter must still be doing work (ones count growing). */
        int other_slow = same_sign && ad2 > 0 && ad2 < 9000 &&
                         r.ones_growth > 100 && r.trail_ones;
        if (other_slow) slow_same++;
        if (shown < 12 && other_slow) {
            char b2[64];
            fmt_agent(a2, n, k, b2);
            printf("PAIR slow t=%d p=(%d,%d) span=[%d,%d] d=(%d,%d) speed2=%.3f ones_growth=%d trail_ones=%d agent2=%s\n",
                   r.steps, r.p1, r.p2, r.lo, r.hi, r.d1, r.d2,
                   (double)ad2 / 10000.0, r.ones_growth, r.trail_ones, b2);
            shown++;
        }
    }
    printf("SUMMARY %s: collision=%lld survivors=%lld slow_same=%lld period1_like=%lld\n",
           name, collision, alive, slow_same, period1_like);
}

int main(int argc, char **argv) {
    int trials = argc > 1 ? atoi(argv[1]) : 5000;
    int limit = argc > 2 ? atoi(argv[2]) : 100000;
    /* Current CET(3) binary counter. */
    search("CET(3) binary", "1LB---_1LC1RB_0RB0LC", 3, 2, trials, limit);
    /* Current CET(2,3) ternary counter/record agent. */
    search("CET(2,3) ternary", "1RB0RA2LB_2LA2RB1LB", 2, 3, trials, limit);
    /* Current CET(4) four-state binary record agent. */
    search("CET(4) four-state", "1LC0LC_1LA1RB_0RB1LC_0RA0RA", 4, 2, trials, limit);
    return 0;
}
