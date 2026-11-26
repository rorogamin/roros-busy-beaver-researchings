/* Longest halting n-state, m-symbol machine on a semi-infinite tape.
 *
 * Cells 0,1,2,... only; the head starts on cell 0; a left move from cell 0 is
 * ignored.  Machines are enumerated up to renaming of states and of the
 * non-blank symbols, so every machine is tested once.
 *
 *   gcc -O2 -o semibb semibb.c
 *   ./semibb 4 2 1200      n states, m symbols, step cap
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define MAXST 5
#define MAXSYM 9
#define TAPE (1 << 16)

static int NST, NSYM, CELLS, HALT, CAP;
static uint8_t tape[TAPE];
static uint64_t rnd[TAPE];
static int32_t vstep[TAPE];
static uint8_t vstate[TAPE];
static uint64_t vsig[TAPE];

static unsigned char ops[MAXST * MAXSYM], best[MAXST * MAXSYM];
static long long best_steps = -1, best_ones = -1;
static long long machines, unresolved;
static int shard, nshards = 1;          /* split the first state across processes */
static int cleared;      /* leading cells zeroed for this machine */
static int seen_gen[MAXST];   /* blank-frontier runaway detector */
static int cur_gen;
static int dirty;        /* highest cell the last machine touched */

static long long run(void) {
    int h = 0, q = 0, step = 0, maxh = 0;
    uint64_t sig = 0;
    memset(tape, 0, (size_t)(dirty + 2));
    memset(vstep, 0, sizeof(int32_t) * (size_t)(dirty + 2));
    cleared = dirty + 2;
    dirty = 0;
    cur_gen++;
    for (;;) {
        int op = ops[q * NSYM + tape[h]];
        int code = op >> 5;
        if (code == HALT) {
            long long ones = 0;
            for (int i = 0; i <= maxh; i++) ones += tape[i];
            if (step + 1 > best_steps ||
                (step + 1 == best_steps && ones > best_ones)) {
                best_steps = step + 1;
                best_ones = ones;
                memcpy(best, ops, (size_t)CELLS);
            }
            return step + 1;
        }
        /* Beyond every touched cell the tape is all blank, so the future depends
           on the state alone: if a state repeats out there the machine loops. */
        if (h > maxh) {
            if (seen_gen[q] == cur_gen) return -1;
            seen_gen[q] = cur_gen;
        } else {
            cur_gen++;
        }
        if (h >= cleared) {                      /* virgin cells may hold junk */
            int n = h + 2;
            memset(tape + cleared, 0, (size_t)(n - cleared));
            memset(vstep + cleared, 0, sizeof(int32_t) * (size_t)(n - cleared));
            cleared = n;
        }
        if (vstep[h] && vstate[h] == q && vsig[h] == sig) {   /* cycle */
            return -1;
        }
        vstep[h] = step + 1;
        vstate[h] = (uint8_t)q;
        vsig[h] = sig;

        if (h > dirty) dirty = h;
        int w = op & 15;
        if (tape[h] != w) { tape[h] = (uint8_t)w; sig ^= rnd[h]; }
        h += ((op >> 4) & 1) ? 1 : -1;
        if (h < 0) h = 0;                       /* the wall */
        if (h > maxh) maxh = h;
        q = code;
        if (++step >= CAP) {
            unresolved++;
            return -1;
        }
    }
}

static void gen(int cell, int nused, int used_sym) {
    if (cell == CELLS) {
        machines++;
        run();
        if ((machines & 0xFFFFF) == 0)
            fprintf(stderr, "%lld machines, best %lld\n", machines, best_steps);
        return;
    }
    int q = cell / NSYM;
    if (q >= nused) return;                     /* state never created */
    int is_new_state = nused < NST;
    int opt = 0;                        /* option counter, sharded at cell 0 */
    for (int w = 0; w < NSYM; w++) {
        if (w > used_sym) continue;             /* new symbol: next one only */
        int nused2 = used_sym > w ? used_sym : w + 1;
        for (int d = 0; d < 2; d++) {
            for (int code = 0; code < nused; code++, opt++) {
                if (cell == 1 && opt % nshards != shard) continue;
                ops[cell] = (unsigned char)(w | (d << 4) | (code << 5));
                gen(cell + 1, nused, nused2);
            }
            if (is_new_state) {
                if (!(cell == 1 && opt % nshards != shard)) {
                    ops[cell] = (unsigned char)(w | (d << 4) | (nused << 5));
                    gen(cell + 1, nused + 1, nused2);
                }
                opt++;
            }
            if (!(cell == 1 && opt % nshards != shard)) {
                ops[cell] = (unsigned char)(w | (d << 4) | (HALT << 5));
                gen(cell + 1, nused, nused2);
            }
            opt++;
        }
    }
}

int main(int argc, char **argv) {
    NST = argc > 1 ? atoi(argv[1]) : 4;
    NSYM = argc > 2 ? atoi(argv[2]) : 2;
    CAP = argc > 3 ? atoi(argv[3]) : 1200;
    CELLS = NST * NSYM;
    HALT = NST;

    uint64_t x = 88172645463325252ULL;
    for (int i = 0; i < TAPE; i++) {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        rnd[i] = x;
    }
    shard = argc > 4 ? atoi(argv[4]) : 0;
    nshards = argc > 5 ? atoi(argv[5]) : 1;
    gen(0, 1, 1);
    printf("%d states, %d symbols, cap %d\n", NST, NSYM, CAP);
    printf("machines %lld, unresolved %lld\n", machines, unresolved);
    printf("best %lld steps, %lld ones\n", best_steps, best_ones);
    for (int q = 0; q < NST; q++)
        for (int s = 0; s < NSYM; s++) {
            int op = best[q * NSYM + s];
            int code = op >> 5;
            char sym[8], wr[8];
            if (s == 0) snprintf(sym, sizeof sym, "_");
            else snprintf(sym, sizeof sym, "%d", s);
            if ((op & 15) == 0) snprintf(wr, sizeof wr, "_");
            else snprintf(wr, sizeof wr, "%d", op & 15);
            printf("%d %s %s %s ", q, sym, wr, ((op >> 4) & 1) ? "r" : "l");
            if (code == HALT) printf("halt\n");
            else printf("%d\n", code);
        }
    return 0;
}
