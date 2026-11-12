#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

typedef struct { int w, d, n; } Tr;
static Tr A1[4][2], A2[4][2];
static unsigned char tape[2000000];
static const int OFF = 500000;
#define MAXSTEPS 20000000LL
#define R 16
#define HSIZE (1u << 22)
static uint64_t *keys;
static int *times;

static void parse(const char *s, Tr a[4][2]) {
    for (int i = 0; i < 4; i++)
        for (int j = 0; j < 2; j++) {
            if (*s == '-') { a[i][j] = (Tr){0, 1, -1}; s += 3; }
            else { a[i][j] = (Tr){s[0]-'0', s[1]=='R'?1:-1, s[2]-'A'}; s += 3; }
            if (*s == '_') s++;
        }
}

static uint64_t mix(uint64_t h, uint64_t x) {
    h ^= x; h *= 1099511628211ULL; return h;
}
static uint64_t statehash(long p1, long p2, int s1, int s2) {
    uint64_t h = 1469598103934665603ULL;
    h = mix(h, (uint64_t)(p1 - OFF));
    h = mix(h, (uint64_t)(p2 - OFF));
    h = mix(h, (uint64_t)s1);
    h = mix(h, (uint64_t)s2);
    for (int i = -R; i <= R; i++) h = mix(h, tape[p1 + i]);
    for (int i = -R; i <= R; i++) h = mix(h, tape[p2 + i]);
    return h ? h : 1;
}

static void run(const char *line, int idx) {
    char a[64], b[64];
    const char *bar = strchr(line, '|');
    if (!bar) return;
    int n = (int)(bar - line); if (n > 63) n = 63;
    memcpy(a, line, n); a[n] = 0;
    snprintf(b, sizeof b, "%s", bar + 1);
    char *nl = strpbrk(b, "\r\n"); if (nl) *nl = 0;
    parse(a, A1); parse(b, A2);
    memset(tape, 0, sizeof tape);
    memset(keys, 0, HSIZE * sizeof *keys);
    long p1 = OFF, p2 = OFF + 2;
    int s1 = 0, s2 = 0;
    for (long long k = 1; k <= MAXSTEPS; k++) {
        Tr x = A1[s1][tape[p1]], y = A2[s2][tape[p2]];
        tape[p1] = x.w; tape[p2] = y.w;
        p1 += x.d; s1 = x.n;
        p2 += y.d; s2 = y.n;
        if (p1 == p2) { printf("%d collision %lld\n", idx, k); return; }
        if (p1 < R || p1 >= (long)sizeof tape - R || p2 < R || p2 >= (long)sizeof tape - R) {
            printf("%d edge %lld\n", idx, k); return;
        }
        uint64_t h = statehash(p1, p2, s1, s2);
        uint32_t pos = (uint32_t)(h & (HSIZE - 1));
        for (;;) {
            if (!keys[pos]) { keys[pos] = h; times[pos] = (int)k; break; }
            if (keys[pos] == h) {
                printf("%d repeat k=%lld prev=%d period=%lld p1=%ld p2=%ld s1=%d s2=%d\n",
                       idx, k, times[pos], k - times[pos], p1-OFF, p2-OFF, s1, s2);
                return;
            }
            pos = (pos + 1) & (HSIZE - 1);
        }
    }
    printf("%d nomatch %lld p1=%ld p2=%ld s1=%d s2=%d\n", idx, MAXSTEPS, p1-OFF, p2-OFF, s1, s2);
}

int main(void) {
    keys = calloc(HSIZE, sizeof *keys);
    times = calloc(HSIZE, sizeof *times);
    if (!keys || !times) { perror("calloc"); return 1; }
    FILE *f = fopen("remaining_holdouts4.txt", "r");
    if (!f) { perror("remaining_holdouts4.txt"); return 1; }
    char line[512]; int idx = 0;
    while (fgets(line, sizeof line, f)) {
        if (!line[0] || line[0] == '#') continue;
        run(line, idx++);
        fflush(stdout);
    }
    return 0;
}
