#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int8_t w, mv, ns; } Tr;
typedef struct { Tr t[2][2]; } Agent;

static inline void decode_agent(uint16_t code, Agent *ag) {
    for (int s = 0; s < 2; s++) {
        for (int r = 0; r < 2; r++) {
            int shift = (s * 2 + r) * 3;
            int tr = (code >> shift) & 7;
            ag->t[s][r].w = tr & 1;
            ag->t[s][r].mv = (tr & 2) ? 1 : -1;
            ag->t[s][r].ns = (tr & 4) ? 1 : 0;
        }
    }
}

static inline void fmt_agent_bb(uint16_t code, char *buf) {
    Agent ag;
    decode_agent(code, &ag);
    char *p = buf;
    for (int s = 0; s < 2; s++) {
        if (s > 0) *p++ = '_';
        for (int r = 0; r < 2; r++) {
            *p++ = '0' + ag.t[s][r].w;
            *p++ = ag.t[s][r].mv > 0 ? 'R' : 'L';
            *p++ = 'A' + ag.t[s][r].ns;
        }
    }
    *p = 0;
}

#define TAPE_SIZE 65536
#define TAPE_OFF  32768

typedef struct {
    uint8_t tape[TAPE_SIZE];
    uint16_t vis[TAPE_SIZE];
    uint16_t mk;
} SimCtx;

int main() {
    printf("Starting complete scan of all 16,777,216 CET_1(2) machines...\n");
    fflush(stdout);

    int max_threads = omp_get_max_threads();
    SimCtx *ctxs = (SimCtx *)calloc(max_threads, sizeof(SimCtx));

    FILE *out = fopen("cet1_candidates.txt", "w");

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        SimCtx *ctx = &ctxs[tid];
        ctx->mk = 1;

        #pragma omp for schedule(dynamic, 1024)
        for (int code1 = 0; code1 < 4096; code1++) {
            Agent ag1;
            decode_agent(code1, &ag1);

            for (int code2 = 0; code2 < 4096; code2++) {
                Agent ag2;
                decode_agent(code2, &ag2);

                ctx->mk++;
                if (ctx->mk == 0) {
                    memset(ctx->vis, 0, sizeof(ctx->vis));
                    ctx->mk = 1;
                }
                uint16_t cur_mk = ctx->mk;
                uint8_t *tape = ctx->tape;
                uint16_t *vis = ctx->vis;

                int p1 = 0, p2 = 2;
                int s1 = 0, s2 = 0;
                int cols = 0;
                int last_col = 0;
                int max_step = 2500;

                for (int step = 1; step <= max_step; step++) {
                    int idx1 = TAPE_OFF + p1;
                    int idx2 = TAPE_OFF + p2;
                    if (idx1 < 0 || idx1 >= TAPE_SIZE || idx2 < 0 || idx2 >= TAPE_SIZE) break;

                    int r1 = (vis[idx1] == cur_mk) ? tape[idx1] : 0;
                    int r2 = (vis[idx2] == cur_mk) ? tape[idx2] : 0;

                    Tr t1 = ag1.t[s1][r1];
                    Tr t2 = ag2.t[s2][r2];

                    tape[idx2] = t2.w; vis[idx2] = cur_mk;
                    tape[idx1] = t1.w; vis[idx1] = cur_mk;

                    p1 += t1.mv; s1 = t1.ns;
                    p2 += t2.mv; s2 = t2.ns;

                    if (p1 == p2) {
                        cols++;
                        last_col = step;
                        if (step > max_step - 500 && max_step < 20000) {
                            max_step += 2500;
                        }
                    } else if (step > 500 && last_col < 100) {
                        break; // early prune
                    }
                }

                if (last_col >= 110) {
                    char str1[32], str2[32];
                    fmt_agent_bb(code1, str1);
                    fmt_agent_bb(code2, str2);

                    #pragma omp critical
                    {
                        fprintf(out, "%d | %d | %d | %s|%s\n", last_col, cols, max_step, str1, str2);
                        fflush(out);
                    }
                }
            }
        }
    }

    fclose(out);
    free(ctxs);
    printf("Scan complete! Results written to cet1_candidates.txt\n");
    return 0;
}
