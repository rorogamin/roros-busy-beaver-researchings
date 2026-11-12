#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { int w, d, n; } Tr;
static Tr A1[4][2], A2[4][2];
static unsigned char tape[400000];
#define OFF 100000
#define CAP 3000
#define R 12
#define W 25
#define HSIZE 16384

typedef struct {
    int used;
    int s1, s2, dist;
    unsigned char w1[W], w2[W];
    int k, p1, p2;
} Slot;
static Slot slots[HSIZE];
static char full_line[512];

static int parse_agent(const char *s, Tr a[4][2]) {
    for (int st = 0; st < 4; st++)
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

static uint64_t hash_slot(const Slot *q) {
    uint64_t h = 1469598103934665603ULL;
    h ^= (uint64_t)(q->s1 + 10); h *= 1099511628211ULL;
    h ^= (uint64_t)(q->s2 + 10); h *= 1099511628211ULL;
    h ^= (uint64_t)(q->dist + 1000); h *= 1099511628211ULL;
    for (int i = 0; i < W; i++) {
        h ^= q->w1[i]; h *= 1099511628211ULL;
        h ^= q->w2[i]; h *= 1099511628211ULL;
    }
    return h;
}

static int same_key(const Slot *a, const Slot *b) {
    return a->s1 == b->s1 && a->s2 == b->s2 && a->dist == b->dist &&
           !memcmp(a->w1, b->w1, W) && !memcmp(a->w2, b->w2, W);
}

static int find_cycle(const char *line, int *kout, int *pout, int *dout) {
    memset(tape, 0, sizeof tape);
    memset(slots, 0, sizeof slots);
    long p1 = OFF, p2 = OFF + 2;
    int s1 = 0, s2 = 0;
    for (int k = 0; k < CAP; k++) {
        Slot q;
        q.used = 1; q.s1 = s1; q.s2 = s2; q.dist = (int)(p2 - p1);
        q.k = k; q.p1 = (int)p1; q.p2 = (int)p2;
        for (int z = -R; z <= R; z++) {
            q.w1[z + R] = tape[p1 + z];
            q.w2[z + R] = tape[p2 + z];
        }
        uint64_t h = hash_slot(&q) % HSIZE;
        for (int probe = 0; probe < HSIZE; probe++) {
            Slot *o = &slots[(h + probe) % HSIZE];
            if (!o->used) { *o = q; break; }
            if (same_key(o, &q)) {
                int P = k - o->k;
                int d = (int)p1 - o->p1;
                int d2 = (int)p2 - o->p2;
                if (P <= 9 && d == d2 && d == 0) {
                    long lo = p1 < p2 ? p1 : p2;
                    long hi = p1 > p2 ? p1 : p2;
                    int ok = 1;
                    if (d > 0) {
                        for (long x = hi + R + 1; x <= hi + R + 100; x++)
                            if (tape[x]) { ok = 0; break; }
                    } else {
                        for (long x = lo - R - 100; x < lo - R; x++)
                            if (tape[x]) { ok = 0; break; }
                    }
                    if (ok) {
                        *kout = o->k; *pout = P; *dout = d;
                        return 1;
                    }
                }
                break;
            }
        }
        Tr x = A1[s1][tape[p1]], y = A2[s2][tape[p2]];
        tape[p1] = x.w; tape[p2] = y.w;
        p1 += x.d; s1 = x.n;
        p2 += y.d; s2 = y.n;
        if (p1 == p2) return 0;
    }
    return 0;
}

int main(void) {
    FILE *f = fopen("all_holdouts_cet4.txt", "r");
    if (!f) { perror("all_holdouts_cet4.txt"); return 1; }
    FILE *out = fopen("solved_holdouts_small_all.txt", "w");
    char line[512];
    int idx = 0, count = 0;
    while (fgets(line, sizeof line, f)) {
        char *nl = strpbrk(line, "\r\n");
        if (nl) *nl = 0;
        if (!line[0] || line[0] == '#') continue;
        if (parse_line(line) < 0) continue;
        int k, P, d;
        if (find_cycle(line, &k, &P, &d)) {
            count++;
            if (out) fprintf(out, "%d\t%d\t%d\t%d\t%s\n", idx, k, P, d, full_line);
        }
        idx++;
    }
    if (out) fclose(out);
    printf("fixed cycles: %d / %d\n", count, idx);
    return 0;
}
