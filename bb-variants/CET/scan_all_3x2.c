/* Exhaustive (3,2) glider & exponential counter enumerator (tsym=0 and tsym=1, ANY chase speed) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef struct { int w, d, ns; } Tr;

static void decode_3x2(long long code, Tr T[6]) {
    for (int i = 0; i < 6; i++) {
        int c = (int)(code % 12); code /= 12;
        int w = c % 2; c /= 2;
        int d = (c % 2) ? 1 : -1; c /= 2;
        int ns = c;
        T[i] = (Tr){w, d, ns};
    }
}

static void canon_bc(const Tr T[6], char *out) {
    /* First appearance of B or C in row-major order A0,A1,B0,B1,C0,C1? Standard BFS from A! */
    int order[3] = {0, -1, -1}, seen[3] = {1, 0, 0}, q[3] = {0}, qh = 0, qt = 1, oi = 1;
    while (qh < qt) {
        int s = q[qh++];
        for (int b = 0; b < 2; b++) {
            int ns = T[s * 2 + b].ns;
            if (!seen[ns]) { seen[ns] = 1; order[oi++] = ns; q[qt++] = ns; }
        }
    }
    for (int s = 0; s < 3; s++) if (!seen[s]) order[oi++] = s;
    int inv[3]; for (int i = 0; i < 3; i++) inv[order[i]] = i;
    char *p = out;
    for (int ns = 0; ns < 3; ns++) {
        int os = order[ns];
        if (ns) *p++ = '_';
        for (int b = 0; b < 2; b++) {
            Tr x = T[os * 2 + b];
            p += sprintf(p, "%d%c%c", x.w, x.d > 0 ? 'R' : 'L', 'A' + inv[x.ns]);
        }
    }
    *p = 0;
}

static void fmt_3x2(const Tr T[6], char *out) {
    char *p = out;
    for (int q = 0; q < 3; q++) {
        if (q) *p++ = '_';
        for (int b = 0; b < 2; b++) {
            Tr x = T[q * 2 + b];
            p += sprintf(p, "%d%c%c", x.w, x.d > 0 ? 'R' : 'L', 'A' + x.ns);
        }
    }
    *p = 0;
}

static int detect_glider_3x2(const Tr *T, const uint8_t *orig_tape, int orig_sz,
                             int p_cur, int s_cur, int tsym, int *out_P, int *out_D, int *out_sl) {
    uint8_t tp[1024];
    int base = p_cur - 64;
    if (base < 0 || p_cur >= orig_sz) return 0;
    int avail = orig_sz - base; if (avail > 1024) avail = 1024;
    memset(tp, 0, 1024); memcpy(tp, orig_tape + base, avail);
    int p = p_cur - base, s = s_cur;
    int ph[300], ps[300];
    for (int t = 0; t < 300; t++) {
        ph[t] = p; ps[t] = s;
        if (p < 12 || p >= 1012) return 0;
        Tr x = T[s * 2 + tp[p]];
        tp[p] = x.w; p += x.d; s = x.ns;
    }
    for (int P = 3; P <= 80; P++) {
        int D = ph[299] - ph[299 - P];
        if (D <= 0 || D >= P) continue;
        int ok = 1;
        for (int t = 300 - 2 * P; t < 300; t++) {
            if (ph[t] - ph[t - P] != D || ps[t] != ps[t - P]) { ok = 0; break; }
        }
        if (!ok) continue;
        int min_h = ph[299];
        for (int t = 300 - P; t < 300; t++) if (ph[t] < min_h) min_h = ph[t];
        int trail_ok = 1;
        for (int z = min_h - 10; z < min_h; z++) if (z < 0 || tp[z] != tsym) { trail_ok = 0; break; }
        if (!trail_ok) continue;
        *out_P = P; *out_D = D; *out_sl = ph[299] - min_h;
        return 1;
    }
    return 0;
}

int main(void) {
    long long TOTAL = 12LL * 12 * 12 * 12 * 12 * 12; /* 2,985,984 */
    FILE *fg = fopen("bbwork/bb-variants/CET/gliders_3x2_all.txt", "w");
    FILE *fe = fopen("bbwork/bb-variants/CET/engines_3x2_all.txt", "w");
    long long ng = 0, ne = 0;

    #pragma omp parallel for schedule(dynamic, 4096) reduction(+:ng,ne)
    for (long long code = 0; code < TOTAL; code++) {
        Tr T[6]; decode_3x2(code, T);
        /* Symmetry break: first state visited from A != C if we enforce B <= C on first non-A,
           Wait simpler: require A0.ns != 2 (B before C unless A0=A & A1=C? No just check T[0].ns != 2 && !(T[0].ns==0 && T[1].ns==2)) -> saves 33%, wait let's keep all 2.98M if deduplicating? Actually skip T[0].ns == 2 cuts 33% AND canon_bc is lossless except swap B<->C doesn't change start A! Wait yes swapping B<->C keeps start state A unchanged! */
        if (T[0].ns == 2) continue;

        /* 1. Glider check (on blank 0 tape from (256, A)) */
        {
            uint8_t tp[2048]; memset(tp, 0, sizeof(tp));
            int p = 512, s = 0, mask = 0, ok = 1;
            for (int t = 0; t < 1200; t++) {
                Tr x = T[s * 2 + tp[p]];
                mask |= (1 << s);
                tp[p] = x.w; p += x.d; s = x.ns;
                if (p < 20 || p >= 1980) { ok = 0; break; }
            }
            if (ok && mask == 7) {
                for (int tsym = 0; tsym <= 1; tsym++) {
                    int P = 0, D = 0, sl = 0;
                    if (detect_glider_3x2(T, tp, 2048, p, s, tsym, &P, &D, &sl) && (P - D) >= 2) {
                        /* Only emit canonical B<->C? Actually keep B,C distinct since B<->C was only broken on A0! Keep canon_bc dedup in pair_hunter OR print raw! Print raw takes 10k lines max, or check canon! */
                        char sp[32], csp[32]; fmt_3x2(T, sp); canon_bc(T, csp);
                        if (strcmp(sp, csp) == 0) {
                            ng++;
                            #pragma omp critical(glw)
                            fprintf(fg, "%s\tP=%d\tD=%d\tM=%d\ttsym=%d\tsl=%d\n", sp, P, D, P - D, tsym, sl);
                        }
                    }
                }
            }
        }

        /* 2. Resettable exponential engine check (tsym in {0, 1}, sr in {0, 1, 2}) */
        /* Note: keep raw spec (only A is special as CET start state! Swapping B<->C in engine CAN'T break A, so keep canon_bc == raw!). */
        char sp[32], csp[32]; fmt_3x2(T, sp); canon_bc(T, csp);
        if (strcmp(sp, csp) != 0) continue;

        for (int tsym = 0; tsym <= 1; tsym++) {
            int clean = 1 - tsym;
            for (int sr = 0; sr < 3; sr++) {
                /* Test both left_anchor=clean (pos=OFF-1 on clean) AND left_anchor=tsym (pos=OFF-1 on tsym)! */
                int best_found = 0;
                for (int la = 0; la <= 1 && !best_found; la++) {
                    long long ts[4] = {0};
                    int exs[4] = {-1, -1, -1, -1};
                    int ok = 1, mask = 0;
                    uint8_t fin_tp[512]; int fin_pos = 0;
                    for (int li = 0; li < 4; li++) {
                        int L = 8 + li;
                        uint8_t tp[512];
                        int OFF = 256;
                        for (int z = 0; z < 512; z++) tp[z] = clean;
                        if (la == 1) { tp[OFF - 2] = tsym; tp[OFF - 1] = tsym; }
                        for (int z = OFF + L; z < 512; z++) tp[z] = tsym;
                        int pos = OFF - 1, st = sr;
                        long long stp = 0;
                        for (stp = 1; stp <= 150000; stp++) {
                            Tr x = T[st * 2 + tp[pos]];
                            if (li >= 1) mask |= (1 << st);
                            tp[pos] = x.w; pos += x.d; st = x.ns;
                            if (pos < OFF - 60) { ok = 0; break; }
                            if (pos >= OFF + L) { exs[li] = st; break; }
                        }
                        if (!ok || stp > 150000) { ok = 0; break; }
                        ts[li] = stp;
                        if (li == 3) { memcpy(fin_tp, tp, 512); fin_pos = pos; }
                    }
                    if (!ok || mask != 7 || ts[3] < 3 * ts[0]) continue;
                    if (exs[0] != exs[1] || exs[1] != exs[2] || exs[2] != exs[3]) continue;
                    int ex = exs[3], pos = fin_pos, st = ex;
                    int ph[150], ps[150], cok = 1;
                    for (int t = 0; t < 150; t++) {
                        ph[t] = pos; ps[t] = st;
                        if (pos < 250 || pos >= 500) { cok = 0; break; }
                        Tr x = T[st * 2 + fin_tp[pos]];
                        fin_tp[pos] = x.w; pos += x.d; st = x.ns;
                    }
                    if (!cok) continue;
                    int Pc = 0, Dc = 0;
                    for (int P = 1; P <= 20; P++) {
                        int D = ph[149] - ph[149 - P];
                        if (D <= 0) continue;
                        int m = 1;
                        for (int t = 150 - 2 * P; t < 150; t++) {
                            if (ph[t] - ph[t - P] != D || ps[t] != ps[t - P]) { m = 0; break; }
                        }
                        if (m) { Pc = P; Dc = D; break; }
                    }
                    if (!Pc) continue;
                    best_found = 1;
                    ne++;
                    #pragma omp critical(enw)
                    fprintf(fe, "%s\ttsym=%d\tsr=%c\texit=%c\tPc=%d\tDc=%d\tL8=%lld\tL11=%lld\trat=%.2f\n",
                            sp, tsym, 'A'+sr, 'A'+ex, Pc, Dc, ts[0], ts[3], (double)ts[3]/ts[0]);
                }
            }
        }
    }
    fclose(fg); fclose(fe);
    printf("Exhaustive 3x2: gliders=%lld engines=%lld\n", ng, ne);
    return 0;
}
