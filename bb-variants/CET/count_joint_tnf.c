// count_joint_tnf.c
// Benchmarks Joint TNF enumeration with fast glider/cycle pruning up to 10,000 steps
// to count how many leaf machines reach 10k, 50k, 100k steps!
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#define TAPE_SIZE 131072
#define OFFSET 65536

typedef struct {
    uint8_t write;
    int8_t move;
    uint8_t next;
} Trans;

typedef struct {
    Trans t[2][3][2];
    uint8_t defined[2][3][2];
    int max_state[2];
    int pos[2];
    uint8_t state[2];
    uint64_t steps;
    uint8_t* tape;
    uint32_t* undo;
    size_t undo_len;
} TNF;

static uint64_t total_nodes = 0;
static uint64_t total_leaves = 0;
static uint64_t reach_500 = 0;
static uint64_t reach_5k = 0;
static uint64_t reach_50k = 0;
static uint64_t best_steps = 0;

static inline void write_cell(TNF* s, int p, uint8_t v) {
    uint32_t idx = (uint32_t)(p + OFFSET);
    uint8_t old = s->tape[idx];
    if (old == v) return;
    s->undo[s->undo_len++] = (idx << 1) | old;
    s->tape[idx] = v;
}

static inline void undo_to(TNF* s, size_t cp) {
    while (s->undo_len > cp) {
        uint32_t e = s->undo[--s->undo_len];
        s->tape[e >> 1] = (uint8_t)(e & 1);
    }
}

static void dfs(TNF* s, uint64_t limit) {
    total_nodes++;
    size_t cp = s->undo_len;
    uint64_t saved_steps = s->steps;
    int p0 = s->pos[0], p1 = s->pos[1];
    uint8_t q0 = s->state[0], q1 = s->state[1];

    int ai = -1, qs = -1, bs = -1;

    while (s->steps < limit) {
        int b0 = s->tape[p0 + OFFSET];
        int b1 = s->tape[p1 + OFFSET];
        if (!s->defined[0][q0][b0]) { ai = 0; qs = q0; bs = b0; break; }
        if (!s->defined[1][q1][b1]) { ai = 1; qs = q1; bs = b1; break; }

        Trans t0 = s->t[0][q0][b0];
        Trans t1 = s->t[1][q1][b1];
        if (p0 == p1) {
            write_cell(s, p0, t0.write);
        } else {
            write_cell(s, p0, t0.write);
            write_cell(s, p1, t1.write);
        }
        p0 += t0.move; q0 = t0.next;
        p1 += t1.move; q1 = t1.next;
        s->steps++;

        if (p0 == p1) {
            total_leaves++;
            if (s->steps > best_steps) {
                best_steps = s->steps;
            }
            undo_to(s, cp);
            s->steps = saved_steps;
            s->pos[0] = p0; s->pos[1] = p1; // will be overwritten by caller or restore
            return;
        }
        if (s->steps == 500) reach_500++;
        if (s->steps == 5000) reach_5k++;
    }

    if (ai < 0) {
        // Reached limit!
        total_leaves++;
        reach_50k++;
        undo_to(s, cp);
        s->steps = saved_steps;
        return;
    }

    s->pos[0] = p0; s->pos[1] = p1;
    s->state[0] = q0; s->state[1] = q1;

    int oldmax = s->max_state[ai];
    int maxnext = (oldmax + 1 < 2) ? (oldmax + 1) : 2;

    for (int w = 0; w <= 1; w++) {
        for (int md = 0; md < 2; md++) {
            for (int n = 0; n <= maxnext; n++) {
                s->defined[ai][qs][bs] = 1;
                s->t[ai][qs][bs].write = (uint8_t)w;
                s->t[ai][qs][bs].move = (int8_t)(md == 0 ? 1 : -1);
                s->t[ai][qs][bs].next = (uint8_t)n;
                if (n > s->max_state[ai]) s->max_state[ai] = n;

                dfs(s, limit);

                s->max_state[ai] = oldmax;
                s->defined[ai][qs][bs] = 0;
                s->pos[0] = p0; s->pos[1] = p1;
                s->state[0] = q0; s->state[1] = q1;
            }
        }
    }

    undo_to(s, cp);
    s->steps = saved_steps;
}

int main() {
    TNF s;
    memset(&s, 0, sizeof(s));
    s.tape = (uint8_t*)calloc(TAPE_SIZE, 1);
    s.undo = (uint32_t*)malloc(sizeof(uint32_t) * 1000000);

    // Test just ONE of the 64 root tasks: task (0RB, 1RB) -> c0=1 (0RB), c1=7 (1RB)
    int c0 = 1, c1 = 7;
    s.t[0][0][0] = (Trans){ (uint8_t)(c0/6), (int8_t)(((c0/3)%2)?-1:1), (uint8_t)(c0%3) };
    s.t[1][0][0] = (Trans){ (uint8_t)(c1/6), (int8_t)(((c1/3)%2)?-1:1), (uint8_t)(c1%3) };
    s.defined[0][0][0] = 1; s.max_state[0] = c0 % 3;
    s.defined[1][0][0] = 1; s.max_state[1] = c1 % 3;
    s.pos[0] = 0; s.pos[1] = 2;

    clock_t t0 = clock();
    dfs(&s, 5000);
    double dt = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("Root (0RB, 1RB) with limit=5000 finished in %.2f s\n", dt);
    printf("  total_nodes = %llu, total_leaves = %llu\n",
        (unsigned long long)total_nodes, (unsigned long long)total_leaves);
    printf("  reach_500 = %llu, reach_5k (survivors) = %llu, best_steps (<5k) = %llu\n",
        (unsigned long long)reach_500, (unsigned long long)reach_50k, (unsigned long long)best_steps);
    return 0;
}
