// test_overlap_prune.c
// Tests sublinear + bounding-box overlap pruning on subtree (0RB, 1RB, 0LC, 0LC):
// After step 512, if the intervals [min_p0, max_p0] and [min_p1, max_p1] are disjoint
// (max_p0 < min_p1 || max_p1 < min_p0), then the agents' active regions have permanently
// separated and they can never interact!
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
    int min_p[2], max_p[2];
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
    int min0 = s->min_p[0], max0 = s->max_p[0];
    int min1 = s->min_p[1], max1 = s->max_p[1];

    #define RESTORE() do { \
        undo_to(s, cp); \
        s->steps = saved_steps; \
        s->max_seen_ap = saved_max_ap; \
        s->min_p[0] = min0; s->max_p[0] = max0; \
        s->min_p[1] = min1; s->max_p[1] = max1; \
    } while(0)

    int c_min0 = min0, c_max0 = max0;
    int c_min1 = min1, c_max1 = max1;

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
            RESTORE();
            return;
        }

        if (p0 < c_min0) c_min0 = p0;
        if (p0 > c_max0) c_max0 = p0;
        if (p1 < c_min1) c_min1 = p1;
        if (p1 > c_max1) c_max1 = p1;

        int ap0 = p0 >= 0 ? p0 : -p0;
        int ap1 = p1 >= 0 ? p1 : -p1;
        int max_ap = ap0 > ap1 ? ap0 : ap1;
        if (max_ap > cur_max_ap) cur_max_ap = max_ap;

        if ((s->steps & 127) == 0) {
            // Disjoint bounding boxes after step 256 -> agents never touch each other's tape!
            if (c_max0 < c_min1 || c_max1 < c_min0) {
                total_leaves++; RESTORE(); return;
            }
            if (s->steps <= 512) {
                if (max_ap > 80) { total_leaves++; RESTORE(); return; }
                if (s->steps == 512) {
                    if (cur_max_ap < 6) { total_leaves++; RESTORE(); return; }
                    reach_500++;
                }
            } else if (s->steps <= 2048) {
                if (max_ap > 160) { total_leaves++; RESTORE(); return; }
                if (s->steps == 2048) {
                    if (cur_max_ap < 15 || (c_max0 - c_min0) < 4 || (c_max1 - c_min1) < 4) { total_leaves++; RESTORE(); return; }
                    reach_2k++;
                }
            } else if (s->steps <= 10240) {
                if (max_ap > 360) { total_leaves++; RESTORE(); return; }
                if (s->steps == 10240) {
                    if (cur_max_ap < 35) { total_leaves++; RESTORE(); return; }
                    reach_10k++;
                }
            } else if (s->steps <= 50048) {
                if (max_ap > 800) { total_leaves++; RESTORE(); return; }
                if (s->steps == 50048) {
                    if (cur_max_ap < 80) { total_leaves++; RESTORE(); return; }
                    reach_50k++;
                }
            } else if (s->steps <= 250112) {
                if (max_ap > 2000) { total_leaves++; RESTORE(); return; }
                if (s->steps == 250112) {
                    if (cur_max_ap < 180) { total_leaves++; RESTORE(); return; }
                    reach_250k++;
                }
            } else if (s->steps <= 1000064) {
                if (max_ap > 4500) { total_leaves++; RESTORE(); return; }
                if (s->steps == 1000064 && cur_max_ap < 360) {
                    total_leaves++; RESTORE(); return;
                }
            } else {
                if (max_ap > 12000) { total_leaves++; RESTORE(); return; }
            }
        }
    }

    if (ai < 0) {
        total_leaves++;
        RESTORE();
        return;
    }

    s->pos[0] = p0; s->pos[1] = p1;
    s->state[0] = q0; s->state[1] = q1;
    s->max_seen_ap = cur_max_ap;
    s->min_p[0] = c_min0; s->max_p[0] = c_max0;
    s->min_p[1] = c_min1; s->max_p[1] = c_max1;

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
                s->min_p[0] = c_min0; s->max_p[0] = c_max0;
                s->min_p[1] = c_min1; s->max_p[1] = c_max1;
            }
        }
    }

    RESTORE();
}

int main() {
    setvbuf(stdout, NULL, _IONBF, 0);
    TNF s;
    memset(&s, 0, sizeof(s));
    s.tape = (uint8_t*)calloc(TAPE_SIZE, 1);
    s.undo = (uint32_t*)malloc(sizeof(uint32_t) * 15000000);

    // Subtree (0RB, 1RB, 0LC, 0LC), with limit = 10,000,000!
    s.t[0][0][0] = (Trans){0, 1, 1}; s.defined[0][0][0] = 1;
    s.t[1][0][0] = (Trans){1, 1, 1}; s.defined[1][0][0] = 1;
    s.t[0][1][0] = (Trans){0, -1, 2}; s.defined[0][1][0] = 1;
    s.t[1][1][0] = (Trans){0, -1, 2}; s.defined[1][1][0] = 1;
    s.max_state[0] = 2; s.max_state[1] = 2;
    s.pos[0] = 0; s.pos[1] = 2;
    s.min_p[0] = 0; s.max_p[0] = 0;
    s.min_p[1] = 2; s.max_p[1] = 2;
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
