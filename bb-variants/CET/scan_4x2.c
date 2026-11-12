#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns, def; } Tr;

/* Test resettable exponential counter on L=8 vs L=11 (tsym=1) */
static int test_engine_4x2(const Tr *T, int chase_mask, char *sr_out, char *ex_out, long long *l8_out, long long *l11_out) {
    for (int sr = 0; sr < 4; sr++) {
        long long steps[2] = {0, 0};
        int est[2] = {-1, -1};
        int used_all_mask = 0;
        int valid = 1;
        for (int li = 0; li < 2; li++) {
            int L = li == 0 ? 8 : 11;
            uint8_t tp[512]; int TOFF = 256;
            memset(tp, 0, sizeof(tp));
            for (int z = 0; z < 200; z++) tp[TOFF + z] = 1;
            int pp = TOFF + L - 1, ss = sr;
            long long step = 0;
            for (step = 1; step <= 1500000; step++) {
                Tr x = T[ss * 2 + tp[pp]];
                if (!x.def) { valid = 0; break; }
                used_all_mask |= (1 << ss);
                tp[pp] = x.w; pp += x.d; ss = x.ns;
                if (pp < TOFF - 50) { valid = 0; break; }
                if (pp >= TOFF + L) { est[li] = ss; break; }
            }
            if (!valid || step > 1500000) { valid = 0; break; }
            steps[li] = step;
        }
        if (valid && steps[0] >= 80 && steps[1] >= 2 * steps[0] &&
            (chase_mask & (1 << est[0])) && (chase_mask & (1 << est[1])) &&
            used_all_mask == 0xF) {
            *sr_out = 'A' + sr;
            *ex_out = 'A' + est[1];
            *l8_out = steps[0];
            *l11_out = steps[1];
            return 1;
        }
    }
    return 0;
}

static void fmt_table(const Tr *T, char *out) {
    char *p = out;
    for (int q = 0; q < 4; q++) {
        if (q) *p++ = '_';
        for (int b = 0; b < 2; b++) {
            Tr x = T[q * 2 + b];
            if (!x.def) { memcpy(p, "---", 3); p += 3; }
            else { p += sprintf(p, "%d%c%c", x.w, x.d > 0 ? 'R' : 'L', 'A' + x.ns); }
        }
    }
    *p = 0;
}

/* Classify a fully/partially built (4,2) TM during TNF DFS.
   Returns: -1 if aborted on undefined transition (sets out_need_state, out_need_sym),
   otherwise 0 (finished classification). */
static int eval_tm(const Tr *T, int n_def, int *out_need_q, int *out_need_b,
                   int is_glider_check, FILE *f_gl, FILE *f_eng,
                   long long *cnt_gl, long long *cnt_eng) {
    uint8_t tape[256];
    const int OFF = 128;
    memset(tape, 0, sizeof(tape));
    int p = OFF, s = 0, lo = p, hi = p;
    int st_mask = 1;
    int last_exp = 0, nexp = 0;

    /* For fast glider detection up to 2400 steps */
    int ph[2400], ps[2400];
    int max_steps = is_glider_check ? 2400 : 25000;

    for (int step = 0; step < max_steps; step++) {
        if (step < 2400) { ph[step] = p; ps[step] = s; }
        int r = tape[p];
        Tr x = T[s * 2 + r];
        if (!x.def) {
            /* Before branching, prune if we already looped or ran too far without reaching new states */
            *out_need_q = s; *out_need_b = r;
            return -1;
        }
        tape[p] = x.w; p += x.d; s = x.ns;
        st_mask |= (1 << s);
        if (p < lo) { lo = p; last_exp = step + 1; nexp++; if (lo < 8) break; }
        else if (p > hi) { hi = p; last_exp = step + 1; nexp++; if (hi > 248) break; }

        /* Early prune if stuck in <=2 states by step 600, or not all 4 states by step 2000 */
        if (step == 600 && (st_mask == 1 || st_mask == 2 || st_mask == 3)) return 0;
        if (step == 1800 && st_mask != 0xF && is_glider_check) return 0;

        /* Early glider detection check at step=1800 and step=2399 */
        if (step == 1800 || step == 2399) {
            if (st_mask == 0xF && p > lo + 12 && hi - p < 40) {
                /* Check if drifting slowly right on blank tape */
                for (int P = 10; P <= 180; P++) {
                    if (step - 2 * P < 100) break;
                    int D = ph[step] - ph[step - P];
                    if (D <= 0 || D >= P) continue;
                    int ok = 1;
                    for (int k = step - 2 * P + 1; k <= step; k++) {
                        if (ph[k] - ph[k - P] != D || ps[k] != ps[k - P]) { ok = 0; break; }
                    }
                    if (!ok) continue;
                    int min_h = ph[step];
                    for (int k = step - P + 1; k <= step; k++) if (ph[k] < min_h) min_h = ph[k];
                    int unif1 = 1;
                    for (int z = min_h - 15; z < min_h; z++) {
                        if (z < 8 || tape[z] != 1) { unif1 = 0; break; }
                    }
                    if (unif1) {
                        char spec[64]; fmt_table(T, spec);
                        #pragma omp critical (glwrite)
                        {
                            (*cnt_gl)++;
                            fprintf(f_gl, "%s\tP=%d\tD=%d\tunif=1\ttsym=1\n", spec, P, D);
                            if (*cnt_gl <= 25) printf("  [4x2 GLIDER #%lld] %s P=%d D=%d\n", *cnt_gl, spec, P, D);
                        }
                        return 0;
                    }
                }
            }
            if (step == 2399 && is_glider_check) return 0;
        }
    }

    if (st_mask != 0xF) return 0;
    int span = hi - lo + 1;
    if (lo >= 8 && hi <= 248 && span >= 6 && span <= 56 && last_exp >= 4000 && nexp <= 75) {
        int chase_mask = 0;
        for (int st = 0; st < 4; st++) {
            if (!T[st * 2 + 1].def) continue;
            if (T[st * 2 + 1].w == 1 && T[st * 2 + 1].d == 1 && T[st * 2 + 1].ns == st) chase_mask |= (1 << st);
        }
        if (chase_mask) {
            char sr_c, ex_c; long long l8, l11;
            if (test_engine_4x2(T, chase_mask, &sr_c, &ex_c, &l8, &l11)) {
                char spec[64]; fmt_table(T, spec);
                #pragma omp critical (engwrite)
                {
                    (*cnt_eng)++;
                    fprintf(f_eng, "%s\ttsym=1\tsr=%c\texit=%c\tanchor=0\tL8=%lld\tL11=%lld\tratio=%.2f\n",
                            spec, sr_c, ex_c, l8, l11, (double)l11 / l8);
                    if (*cnt_eng <= 25) {
                        printf("  [4x2 ENGINE #%lld] %s sr=%c exit=%c L8=%lld L11=%lld ratio=%.2f\n",
                               *cnt_eng, spec, sr_c, ex_c, l8, l11, (double)l11 / l8);
                    }
                }
            }
        }
    }
    return 0;
}

typedef struct { Tr T[8]; int next_state_allowed, n_def; } Task4;

static void dfs_4x2(Tr *T, int next_st, int n_def, int depth_budget,
                    FILE *f_gl, FILE *f_eng, long long *cnt_gl, long long *cnt_eng, long long *nodes) {
    if ((*nodes)++ > 4000000LL) return; /* ~64M total DFS nodes across 16 threads */
    int nq = -1, nb = -1;
    int res = eval_tm(T, n_def, &nq, &nb, (n_def < 7), f_gl, f_eng, cnt_gl, cnt_eng);
    if (res != -1) return;
    if (n_def >= 8) return;

    int max_st = next_st < 3 ? next_st + 1 : 3;
    for (int ns = 0; ns <= max_st; ns++) {
        for (int d = -1; d <= 1; d += 2) {
            for (int w = 0; w <= 1; w++) {
                T[nq * 2 + nb] = (Tr){w, d, ns, 1};
                int nns = (ns > next_st) ? ns : next_st;
                dfs_4x2(T, nns, n_def + 1, depth_budget, f_gl, f_eng, cnt_gl, cnt_eng, nodes);
            }
        }
    }
    T[nq * 2 + nb] = (Tr){0, 0, 0, 0};
}

static uint64_t xorshift64(uint64_t *st) {
    uint64_t x = *st;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return (*st = x);
}

int main(void) {
    FILE *f_gl = fopen("bbwork/bb-variants/CET/gliders_4x2_tnf.txt", "w");
    FILE *f_eng = fopen("bbwork/bb-variants/CET/engines_4x2_tnf.txt", "w");
    long long cnt_gl = 0, cnt_eng = 0;

    /* Build root tasks of depth 3 (A0 fixed in {0,1}x{L,R}xB -> 4 choices, then 2 TNF steps) */
    Task4 *tasks = malloc(sizeof(Task4) * 5000);
    int nt = 0;
    for (int fw = 0; fw <= 1; fw++) {
        for (int fd = -1; fd <= 1; fd += 2) {
            Tr T0[8]; memset(T0, 0, sizeof(T0));
            T0[0] = (Tr){fw, fd, 1, 1}; /* A0 -> fw, fd, B */
            /* Step 1: read at p + fd is cell 0 -> (B, 0) = index 2 */
            for (int w1 = 0; w1 <= 1; w1++) {
                for (int d1 = -1; d1 <= 1; d1 += 2) {
                    for (int ns1 = 0; ns1 <= 2; ns1++) {
                        Tr T1[8]; memcpy(T1, T0, sizeof(T1));
                        T1[2] = (Tr){w1, d1, ns1, 1};
                        int mx1 = ns1 > 1 ? ns1 : 1;
                        /* Find next undefined transition cleanly via 1-step sim */
                        int q2 = ns1, r2 = (d1 == -fd) ? fw : 0;
                        int idx2 = q2 * 2 + r2;
                        if (T1[idx2].def) {
                            /* simulate until undef or skip (handled cleanly by pushing Task4) */
                            Task4 t; memcpy(t.T, T1, sizeof(T1)); t.next_state_allowed = mx1; t.n_def = 2;
                            tasks[nt++] = t;
                        } else {
                            for (int w2 = 0; w2 <= 1; w2++) {
                                for (int d2 = -1; d2 <= 1; d2 += 2) {
                                    for (int ns2 = 0; ns2 <= (mx1 < 3 ? mx1 + 1 : 3); ns2++) {
                                        Task4 t; memcpy(t.T, T1, sizeof(T1));
                                        t.T[idx2] = (Tr){w2, d2, ns2, 1};
                                        t.next_state_allowed = ns2 > mx1 ? ns2 : mx1;
                                        t.n_def = 3;
                                        tasks[nt++] = t;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    printf("Generated %d TNF depth-2/3 root tasks for (4,2)...\n", nt);
    fflush(stdout);

    #pragma omp parallel
    {
        long long local_nodes = 0;
        #pragma omp for schedule(dynamic, 1)
        for (int ti = 0; ti < nt; ti++) {
            Tr T[8]; memcpy(T, tasks[ti].T, sizeof(T));
            dfs_4x2(T, tasks[ti].next_state_allowed, tasks[ti].n_def, 8, f_gl, f_eng, &cnt_gl, &cnt_eng, &local_nodes);
        }
    }
    printf("Phase 1 (TNF) done: 4x2 gliders=%lld, 4x2 engines=%lld. Running Phase 2 (20M random 4x2)...\n", cnt_gl, cnt_eng);
    fflush(stdout);

    /* Phase 2: 20M random (4,2) with A0=(B, L/R), D reached, + chase entry for half of samples */
    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        uint64_t rng = 0x9e3779b97f4a7c15ULL ^ (uint64_t)(tid + 1) * 0xbf58476d1ce4e5b9ULL;
        long long per_th = 1250000; /* 16 * 1.25M = 20M */
        for (long long it = 0; it < per_th; it++) {
            Tr T[8];
            for (int e = 0; e < 8; e++) {
                uint64_t r = xorshift64(&rng);
                T[e] = (Tr){(int)(r & 1), ((r >> 1) & 1) ? 1 : -1, (int)((r >> 2) & 3), 1};
            }
            /* Canonicalize A0 -> B and for first half force a speed-1 chase on symbol 1 in state B or C or D */
            T[0].ns = 1;
            if ((it & 1) == 0) {
                int ch_st = 1 + (int)(xorshift64(&rng) % 3);
                T[ch_st * 2 + 1] = (Tr){1, 1, ch_st, 1};
            }
            int dummy_q, dummy_b;
            eval_tm(T, 8, &dummy_q, &dummy_b, 0, f_gl, f_eng, &cnt_gl, &cnt_eng);
        }
    }

    fclose(f_gl); fclose(f_eng); free(tasks);
    printf("Done ALL 4x2 scans: 4x2 gliders=%lld, 4x2 engines=%lld\n", cnt_gl, cnt_eng);
    return 0;
}
