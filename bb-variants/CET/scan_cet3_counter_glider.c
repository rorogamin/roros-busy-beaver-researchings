#include <stdio.h>
#include <stdint.h>
#include <string.h>

#define OFF 256
#define TAPE 1024

/* Agent 1 of the current CET(3) champion.
   index = state*2 + read, state A=0 B=1 C=2.
   tuple = write, direction, next state. */
static const int A1[6][3] = {
    {1, -1, 1}, {0, 0, 0}, /* A0, A1(unused) */
    {1, -1, 2}, {1,  1, 1}, /* B0, B1 */
    {0,  1, 1}, {0, -1, 2}  /* C0, C1 */
};

typedef struct {
    int w, d, ns;
} Tr;

static void decode(int v, Tr *t) {
    /* 12 choices per transition: write 0/1, direction L/R, next A/B/C */
    t->w = v % 2; v /= 2;
    t->d = (v % 2) ? 1 : -1; v /= 2;
    t->ns = v % 3;
}

static void fmt(const Tr *t, char *b) {
    char *p = b;
    for (int i = 0; i < 6; i++) {
        *p++ = '0' + t[i].w;
        *p++ = t[i].d > 0 ? 'R' : 'L';
        *p++ = 'A' + t[i].ns;
        if (i == 1 || i == 3) *p++ = '_';
    }
    *p = 0;
}

/* Local final-round configuration:
   p1=0 B, p2=8 B; tape <0 = 1, [0..7]=1, [8..10]=0,1,1, >=11=0. */
static int local_bounce(const Tr *t, int *out_p1, int *out_p2,
                        int *out_min_diff, int *out_max_p2, int *halt_step) {
    int tape[TAPE];
    for (int i = 0; i < TAPE; i++) tape[i] = 1;
    for (int i = OFF + 8; i < TAPE; i++) tape[i] = 0;
    tape[OFF + 9] = 1;
    tape[OFF + 10] = 1;

    int p1 = OFF, p2 = OFF + 8;
    int s1 = 1, s2 = 1;
    int min_diff = 1000000, max_p2 = p2, min_p1 = p1;

    for (int step = 1; step <= 200; step++) {
        int r1 = tape[p1], r2 = tape[p2];
        int w1 = A1[s1 * 2 + r1][0];
        int d1 = A1[s1 * 2 + r1][1];
        int n1 = A1[s1 * 2 + r1][2];
        Tr x = t[s2 * 2 + r2];

        tape[p1] = w1;
        tape[p2] = x.w;
        p1 += d1;
        p2 += x.d;
        s1 = n1;
        s2 = x.ns;

        if (p1 == p2) {
            *halt_step = step;
            *out_p1 = p1 - OFF;
            *out_p2 = p2 - OFF;
            return 0;
        }
        int diff = p2 - p1;
        if (diff < min_diff) min_diff = diff;
        if (p2 > max_p2) max_p2 = p2;
        if (p1 < min_p1) min_p1 = p1;
    }
    *out_p1 = p1 - OFF;
    *out_p2 = p2 - OFF;
    *out_min_diff = min_diff;
    *out_max_p2 = max_p2 - OFF;
    *halt_step = 0;
    (void)min_p1;
    return 1;
}

/* Run the full bootstrap from blank tape, enough to see whether the candidate
   gets past the initial 7-bit counter and enters the long regime. */
static int full_run(const Tr *t, int limit, int *where, int *span_out,
                    int *p1_out, int *p2_out) {
    int tape[TAPE];
    memset(tape, 0, sizeof(tape));
    int p1 = OFF, p2 = OFF + 2;
    int s1 = 0, s2 = 0;
    int lo = p1, hi = p2;
    for (int step = 1; step <= limit; step++) {
        if (p1 < 0 || p1 >= TAPE || p2 < 0 || p2 >= TAPE) return -1;
        int r1 = tape[p1], r2 = tape[p2];
        int w1 = A1[s1 * 2 + r1][0];
        int d1 = A1[s1 * 2 + r1][1];
        int n1 = A1[s1 * 2 + r1][2];
        Tr x = t[s2 * 2 + r2];

        tape[p1] = w1;
        tape[p2] = x.w;
        p1 += d1;
        p2 += x.d;
        s1 = n1;
        s2 = x.ns;

        if (p1 < lo) lo = p1;
        if (p1 > hi) hi = p1;
        if (p2 < lo) lo = p2;
        if (p2 > hi) hi = p2;

        if (p1 == p2) {
            *where = p1 - OFF;
            *span_out = hi - lo;
            *p1_out = p1 - OFF;
            *p2_out = p2 - OFF;
            return step;
        }
    }
    *where = p2 - p1;
    *span_out = hi - lo;
    *p1_out = p1 - OFF;
    *p2_out = p2 - OFF;
    return 0;
}

int main(void) {
    printf("Scanning 12^6 = 2,985,984 agent-2 tables against current CET(3) counter\n");
    printf("Bounce filter: local gap-8 no collision, p1 resets left, p2 bounded right.\n");

    long long nohalt = 0, bounces = 0, full_alive = 0;
    int printed = 0;

    for (int a = 0; a < 12; a++) for (int b = 0; b < 12; b++)
    for (int c = 0; c < 12; c++) for (int d = 0; d < 12; d++)
    for (int e = 0; e < 12; e++) for (int f = 0; f < 12; f++) {
        int code[6] = {a,b,c,d,e,f};
        Tr t[6];
        for (int i = 0; i < 6; i++) decode(code[i], &t[i]);

        int p1, p2, md, mp2, hs;
        int alive = local_bounce(t, &p1, &p2, &md, &mp2, &hs);
        if (!alive) continue;
        nohalt++;

        /* A bounce needs the counter to reset left and the glider not to run away. */
        if (p1 <= -2 && p2 > p1 && p2 < 40 && mp2 < 60) {
            bounces++;
            char bb[64]; fmt(t, bb);
            int where = 0, span = 0, fp1 = 0, fp2 = 0;
            int fr = full_run(t, 1000000, &where, &span, &fp1, &fp2);
            if (fr == 0) full_alive++;
            if (fr == 0 && printed < 200) {
                printf("SURV table=%s local p1=%d p2=%d mindiff=%d maxp2=%d full p1=%d p2=%d span=%d\n",
                       bb, p1, p2, md, mp2, fp1, fp2, span);
                printed++;
            }
        }
    }
    printf("local no-collision=%lld bounce-family=%lld full-alive-200k=%lld\n",
           nohalt, bounces, full_alive);
    return 0;
}
