// Exhaustive one-entry mutation sweep around a CET champion.
// Usage: mutate_champ <states> <symbols> <base-spec> <base-steps>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdatomic.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define TAPE_SIZE 100000000
#define TAPE_OFF 50000000

typedef struct { int w, m, n; } Tr;
static Tr A[2][4][3];
static int NS, NSYM;
static uint64_t BASE;

static int parse(const char *s) {
    const char *p = s;
    for (int a = 0; a < 2; a++)
        for (int q = 0; q < NS; q++)
            for (int b = 0; b < NSYM; b++) {
                while (*p == '_' || *p == '|' || *p == ' ') p++;
                if (!*p) return 0;
                A[a][q][b].w = p[0] - '0';
                A[a][q][b].m = p[1] == 'R' ? 1 : -1;
                A[a][q][b].n = p[2] - 'A';
                p += 3;
            }
    return 1;
}

static void fmtT(char *out, Tr T[2][4][3]) {
    char *p = out;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int q = 0; q < NS; q++) {
            if (q) *p++ = '_';
            for (int b = 0; b < NSYM; b++) {
                p += sprintf(p, "%d%c%c", T[a][q][b].w, T[a][q][b].m > 0 ? 'R' : 'L', 'A' + T[a][q][b].n);
            }
        }
    }
    *p = 0;
}

typedef struct { uint64_t steps; int halt; int pos; char spec[256]; } Result;
static Result best;
static atomic_int have_new;

static Result run_one(void) {
    Result r = {0, 0, 0, {0}};
    uint8_t *tape = calloc(TAPE_SIZE, 1);
    if (!tape) return r;
    long p1 = TAPE_OFF, p2 = TAPE_OFF + 2;
    int s1 = 0, s2 = 0;
    for (uint64_t k = 1; k <= 5000000000ULL; k++) {
        int b1 = tape[p1], b2 = tape[p2];
        Tr x = A[0][s1][b1], y = A[1][s2][b2];
        if (p1 == p2) tape[p1] = x.w;
        else { tape[p1] = x.w; tape[p2] = y.w; }
        p1 += x.m; s1 = x.n;
        p2 += y.m; s2 = y.n;
        if (p1 == p2) { r.halt = 1; r.steps = k; r.pos = (int)(p1 - TAPE_OFF); break; }
        if (p1 < 0 || p1 >= TAPE_SIZE || p2 < 0 || p2 >= TAPE_SIZE) break;
    }
    free(tape);
    fmtT(r.spec, A);
    return r;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: %s states symbols base base-steps\n", argv[0]); return 2; }
    NS = atoi(argv[1]); NSYM = atoi(argv[2]); BASE = strtoull(argv[4], 0, 10);
    if (!parse(argv[3])) { fprintf(stderr, "parse failed\n"); return 2; }
    Tr orig[2][4][3]; memcpy(orig, A, sizeof A);
    int total = 2 * NS * NSYM;
    printf("sweep %d entries, base=%llu\n", total, (unsigned long long)BASE);
    fflush(stdout);
    #pragma omp parallel
    {
        uint8_t *tape = calloc(TAPE_SIZE, 1);
        #pragma omp for schedule(dynamic)
        for (int e = 0; e < total; e++) {
            int a = e / (NS * NSYM), rem = e % (NS * NSYM), q = rem / NSYM, b = rem % NSYM;
            for (int alt = 0; alt < 16; alt++) {
                int w = alt & 1, m = (alt >> 1) & 1 ? 1 : -1, n = (alt >> 2) & 3;
                if (n >= NS) continue;
                Tr T[2][4][3];
                memcpy(T, orig, sizeof T);
                Tr old = T[a][q][b];
                if (w == old.w && m == old.m && n == old.n) continue;
                T[a][q][b] = (Tr){w, m, n};
                // run
                Result r = {0, 0, 0, {0}};
                long p1 = TAPE_OFF, p2 = TAPE_OFF + 2;
                int s1 = 0, s2 = 0;
                memset(tape, 0, TAPE_SIZE);
                for (uint64_t k = 1; k <= 5000000000ULL; k++) {
                    int b1 = tape[p1], b2 = tape[p2];
                    Tr x = T[0][s1][b1], y = T[1][s2][b2];
                    if (p1 == p2) tape[p1] = x.w;
                    else { tape[p1] = x.w; tape[p2] = y.w; }
                    p1 += x.m; s1 = x.n; p2 += y.m; s2 = y.n;
                    if (p1 == p2) { r.halt = 1; r.steps = k; r.pos = (int)(p1 - TAPE_OFF); break; }
                    if (p1 < 0 || p1 >= TAPE_SIZE || p2 < 0 || p2 >= TAPE_SIZE) break;
                }
                if (r.halt) {
                    fmtT(r.spec, T);
                    #pragma omp critical
                    {
                        if (r.steps > BASE && r.steps > best.steps) {
                            best = r; atomic_store(&have_new, 1);
                            printf("NEW %llu pos=%d %s\n", (unsigned long long)r.steps, r.pos, r.spec);
                            fflush(stdout);
                        } else if (r.steps > 1000000000ULL) {
                            printf("halt %llu pos=%d %s\n", (unsigned long long)r.steps, r.pos, r.spec);
                            fflush(stdout);
                        }
                    }
                }
            }
        }
        free(tape);
    }
    if (best.halt) printf("BEST %llu pos=%d %s\n", (unsigned long long)best.steps, best.pos, best.spec);
    else printf("NO NEW CHAMPION\n");
    return 0;
}
