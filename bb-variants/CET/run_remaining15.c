#include <stdio.h>
#include <string.h>
#include <stdlib.h>

typedef struct { int w, d, n; } Tr;
static Tr A1[4][2], A2[4][2];
static unsigned char tape[16000000];
static const int OFF = 6000000;
#define CAP 10000000000LL

static void parse(const char *s, Tr a[4][2]) {
    for (int i = 0; i < 4; i++)
        for (int j = 0; j < 2; j++) {
            if (*s == '-') { a[i][j] = (Tr){0, 1, -1}; s += 3; }
            else { a[i][j] = (Tr){s[0]-'0', s[1]=='R'?1:-1, s[2]-'A'}; s += 3; }
            if (*s == '_') s++;
        }
}

static void run(const char *line, int idx) {
    char a[64], b[64];
    const char *bar = strchr(line, '|');
    if (!bar) return;
    int n = (int)(bar - line);
    if (n > 63) n = 63;
    memcpy(a, line, n); a[n] = 0;
    snprintf(b, sizeof b, "%s", bar + 1);
    char *nl = strpbrk(b, "\r\n"); if (nl) *nl = 0;
    parse(a, A1); parse(b, A2);
    memset(tape, 0, sizeof tape);
    long p1 = OFF, p2 = OFF + 2;
    int s1 = 0, s2 = 0;
    for (long long k = 1; k <= CAP; k++) {
        Tr x = A1[s1][tape[p1]], y = A2[s2][tape[p2]];
        tape[p1] = x.w; tape[p2] = y.w;
        p1 += x.d; s1 = x.n;
        p2 += y.d; s2 = y.n;
        if (p1 == p2) { printf("%d collision %lld p=%ld\n", idx, k, p1-OFF); return; }
        if (p1 < 0 || p1 >= (long)sizeof tape || p2 < 0 || p2 >= (long)sizeof tape) {
            printf("%d edge %lld\n", idx, k); return;
        }
    }
    printf("%d nohalt %lld p1=%ld p2=%ld\n", idx, CAP, p1-OFF, p2-OFF);
}

int main(void) {
    FILE *f = fopen("remaining_holdouts4.txt", "r");
    if (!f) { perror("remaining_holdouts4.txt"); return 1; }
    char line[512];
    int idx = 0;
    while (fgets(line, sizeof line, f)) {
        if (!line[0] || line[0] == '#') continue;
        run(line, idx++);
        fflush(stdout);
    }
    return 0;
}
