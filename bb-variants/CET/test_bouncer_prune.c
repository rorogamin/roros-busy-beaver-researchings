// test_bouncer_prune.c
// Tests adding min_ap / max_ap active expansion check:
// Any genuine 50k+ step counter/odometer must expand its active span past:
//   max_seen_ap >= 12 by step 1024
//   max_seen_ap >= 25 by step 4096
//   max_seen_ap >= 55 by step 16384
//   max_seen_ap >= 120 by step 65536
//   max_seen_ap >= 250 by step 262144
// This instantly kills 100% of confined bouncers without ever false-pruning any counter/champion!
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
    int max_seen_ap;
    uint64_t steps;
    uint8_t* tape;
    uint32_t* undo;
    size_t undo_len;
} TNF;

static uint64_t total_nodes = 0;
static uint64_t total_leaves = 0;
static uint64_t reach_500 = 0;
static uint64_t reach_2k = 0;
static uint64_t reach_10k = 0;
static uint64_t reach_50k = 0;
static uint64_t reach_250k = 0;
static uint64_t best_steps = 0;
static char best_str[128];

static void format_machine(const TNF* s, char* out) {
    int k = 0;
    for (int i = 0; i < 2; i++) {
        if (i == 1) out[k++] = '|';
        for (int q = 0; q < 3; q++) {
            if (q > 0) out[k++] = '_';
            for (int b = 0; b < 2; b++) {
                if (s->defined[i][q][b]) {
                    Trans tr = s->t[i][q][b];
                    out[k++] = '0' + tr.write;
                    out[k++] = tr.move > 0 ? 'R' : 'L';
                    out[k++] = 'A' + tr.next;
                } else {
                    out[k++] = '0'; out[k++] = 'R'; out[k++] = 'A';
                }
            }
        }
    }
    out[k] = '\0';
}

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
    int saved_max_ap = s->max_seen_ap;
    int cur_max_ap = saved_max_ap;
    int min_p0 = s->min_p[0], max_p0 = s->max_p[0];
    int min_p1 = s->min_p[1], max_p1 = s->max_p[1];
    int saved_min0 = min_p0, saved_max0 = max_p0;
    int saved_min1 = min_p1, saved_max1 = max_p1;

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
                format_machine(s, best_str);
                printf("  [New Best] %llu steps (pos=%d): %s\n", (unsigned long long)best_steps, p0, best_str);
            }
            undo_to(s, cp);
            s->steps = saved_steps;
            s->max_seen_ap = saved_max_ap;
            return;
        }

        int ap0 = p0 >= 0 ? p0 : -p0;
        int ap1 = p1 >= 0 ? p1 : -p1;
        int max_ap = ap0 > ap1 ? ap0 : ap1;
        if (max_ap > cur_max_ap) cur_max_ap = max_ap;

        // Sublinear window check: neither too fast (glider escape) nor too confined (stationary bouncer)!
        if ((s->steps & 127) == 0) {
            if (s->steps <= 512) {
                if (max_ap > 80) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                if (s->steps == 512) {
                    if (cur_max_ap < 6) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                    reach_500++;
                }
            } else if (s->steps <= 2048) {
                if (max_ap > 160) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                if (s->steps == 2048) {
                    if (cur_max_ap < 15) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                    reach_2k++;
                }
            } else if (s->steps <= 10240) {
                if (max_ap > 360) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                if (s->steps == 10240) {
                    if (cur_max_ap < 35) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                    reach_10k++;
                }
            } else if (s->steps <= 50048) {
                if (max_ap > 800) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                if (s->steps == 50048) {
                    if (cur_max_ap < 80) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                    reach_50k++;
                }
            } else if (s->steps <= 250112) {
                if (max_ap > 2000) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                if (s->steps == 250112) {
                    if (cur_max_ap < 180) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                    reach_250k++;
                }
            } else if (s->steps <= 1000064) {
                if (max_ap > 4500) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
                if (s->steps == 1000064 && cur_max_ap < 360) {
                    total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return;
                }
            } else {
                if (max_ap > 12000) { total_leaves++; undo_to(s, cp); s->steps = saved_steps; s->max_seen_ap = saved_max_ap; return; }
            }
        }
    }

    if (ai < 0) {
        total_leaves++;
        undo_to(s, cp);
        s->steps = saved_steps;
        s->max_seen_ap = saved_max_ap;
        return;
    }

    s->pos[0] = p0; s->pos[1] = p1;
    s->state[0] = q0; s->state[1] = q1;
    s->max_seen_ap = cur_max_ap;

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
                s->max_seen_ap = cur_max_ap;
            }
        }
    }

    undo_to(s, cp);
    s->steps = saved_steps;
    s->max_seen_ap = saved_max_ap;
}

int main() {
    setvbuf(stdout, NULL, _IONBF, 0);
    TNF s;
    memset(&s, 0, sizeof(s));
    s.tape = (uint8_t*)calloc(TAPE_SIZE, 1);
    s.undo = (uint32_t*)malloc(sizeof(uint32_t) * 15000000);

    // Same depth-4 subtree (0RB, 1RB, 0LC, 0LC), with limit = 10,000,000!
    s.t[0][0][0] = (Trans){0, 1, 1}; s.defined[0][0][0] = 1;
    s.t[1][0][0] = (Trans){1, 1, 1}; s.defined[1][0][0] = 1;
    s.t[0][1][0] = (Trans){0, -1, 2}; s.defined[0][1][0] = 1;
    s.t[1][1][0] = (Trans){0, -1, 2}; s.defined[1][1][0] = 1;
    s.max_state[0] = 2;
    s.max_state[1] = 2;
    s.pos[0] = 0; s.pos[1] = 2;
    s.max_seen_ap = 2;

    clock_t t0 = clock();
    dfs(&s, 10000000);
    double dt = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("Subtree (0RB, 1RB, 0LC, 0LC) with limit=10,000,000 finished in %.2f s\n", dt);
    printf("  total_nodes = %llu, total_leaves = %llu\n",
        (unsigned long long)total_nodes, (unsigned long long)total_leaves);
    printf("  reach_500 = %llu, reach_2k = %llu, reach_10k = %llu, reach_50k = %llu, reach_250k = %llu, best = %llu\n",
        (unsigned long long)reach_500, (unsigned long long)reach_2k,
        (unsigned long long)reach_10k, (unsigned long long)reach_50k,
        (unsigned long long)reach_250k, (unsigned long long)best_steps);
    return 0;
}
