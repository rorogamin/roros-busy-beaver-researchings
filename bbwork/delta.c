/* delta.c -- scan the documented A(a,c) chain map of BB(3,3) holdout 758.
 *
 * A(a,c) = 0^inf 1 2^a <C (20)^c 0^inf   (wiki: 1RB2LC1RC_2LC---2RB_2LA0LB0RA)
 * Rules (a)-(j) from the wiki, in order; a "chain" starts at A(1,c) and ends
 * at the next A(1,c') or at a halt.  We record the increment c'-c, the max
 * over a range of c, and every halting c found.
 *
 * usage: delta N [--list]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef unsigned long long u64;

static int step(u64 *a, u64 *c, int *halt) {
    u64 A = *a, C = *c;
    *halt = 0;
    if (C + 1 <= A && (C & 1) == 0) {          /* (a) */
        *a = A - C - 1; *c = 3 * (C / 2) + 2; return 'a';
    }
    if (C + 2 <= A && (C & 3) == 1) {          /* (b) */
        *a = A - C - 2; *c = 3 * ((C - 1) / 2) + 5; return 'b';
    }
    if (C + 4 <= A && (C & 3) == 3) {          /* (c) */
        *a = A - C - 4; *c = 3 * ((C - 1) / 2) + 8; return 'c';
    }
    if (C + 3 == A && (C & 3) == 3) {          /* (d) */
        *halt = 1; return 'd';
    }
    if (C + 2 == A && (C & 3) == 3) {          /* (e) */
        *a = 3 * C + 8; *c = 1; return 'e';
    }
    if (C + 1 == A && (C & 1) == 1) {          /* (f) */
        *halt = 1; return 'f';
    }
    if (C >= A && (A & 1) == 0 && (C & 1) == 0) { /* (g) */
        *halt = 1; return 'g';
    }
    if (C >= A && (A & 1) == 0 && (C & 1) == 1) { /* (h) */
        *a = 1; *c = A / 2 + C + 2; return 'h';
    }
    if (C >= A && (A & 1) == 1 && (C & 1) == 0) { /* (i) */
        *a = 3 * A; *c = C - A + 4; return 'i';
    }
    if (C >= A && (A & 1) == 1 && (C & 1) == 1) { /* (j) */
        *a = 3 * A + 2; *c = C - A + 1; return 'j';
    }
    return 0;
}

int main(int argc, char **argv) {
    u64 N = 1ULL << 27;
    int list = 0, trace = 0;
    if (argc > 1) N = strtoull(argv[1], NULL, 0);
    if (argc > 2 && strcmp(argv[2], "--list") == 0) list = 1;
    if (argc > 2 && strcmp(argv[2], "--trace") == 0) trace = 1;

    if (trace) {
        u64 a = 1, c = N;
        int halt = 0, r;
        printf("start A(1,%llu)\n", c);
        do {
            r = step(&a, &c, &halt);
            printf("%c A(%llu,%llu)%s\n", r, a, c, halt ? " HALT" : "");
        } while (!halt && a != 1 && r);
        return 0;
    }

    u64 max_delta = 0, max_c = 0, max_c2 = 0;
    u64 max_a = 0;
    unsigned long long max_len = 0, max_len_c = 0;
    unsigned long long halts = 0;
    for (u64 c0 = 1; c0 <= N; c0++) {
        u64 a = 1, c = c0;
        int halt = 0;
        unsigned long long guard = 0;
        do {
            int r = step(&a, &c, &halt);
            if (r == 0) {
                fprintf(stderr, "no rule at a=%llu c=%llu (start %llu)\n",
                        a, c, c0);
                return 1;
            }
            if (a > max_a) max_a = a;
            if (++guard > 10000000ULL) {
                fprintf(stderr, "chain guard at start %llu\n", c0);
                return 1;
            }
        } while (!halt && a != 1);

        if (guard > max_len) { max_len = guard; max_len_c = c0; }
        if (halt) {
            halts++;
            if (list) printf("HALT %llu\n", c0);
        } else if (c > c0) {
            u64 d = c - c0;
            if (d > max_delta) { max_delta = d; max_c = c0; max_c2 = c; }
        }
    }
    printf("N=%llu halts=%llu max_delta=%llu at c=%llu -> %llu max_len=%llu at c=%llu max_a=%llu\n",
           N, halts, max_delta, max_c, max_c2, max_len, max_len_c, max_a);
    return 0;
}
