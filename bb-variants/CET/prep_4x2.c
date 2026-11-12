#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int w, d, ns; } Tr;

void canon_bcd(const char *spec, char *out, int *inv_out) {
    Tr tbl[4][2];
    char buf[64]; strncpy(buf, spec, 63); buf[63] = 0;
    char *p = buf;
    for (int st = 0; st < 4; st++) {
        char *nx = strchr(p, '_');
        if (nx) *nx = 0;
        for (int sym = 0; sym < 2; sym++) {
            const char *q = p + sym * 3;
            if (q[0] == '-') tbl[st][sym] = (Tr){-1, 0, 0};
            else tbl[st][sym] = (Tr){q[0]-'0', q[1]=='L'?-1:1, q[2]-'A'};
        }
        if (nx) p = nx + 1;
    }
    int order[4] = {0}, seen[4] = {1,0,0,0}, q[4] = {0}, qh = 0, qt = 1, oi = 1;
    while (qh < qt) {
        int s = q[qh++];
        for (int sym = 0; sym < 2; sym++) {
            if (tbl[s][sym].w >= 0) {
                int ns = tbl[s][sym].ns;
                if (!seen[ns]) { seen[ns] = 1; order[oi++] = ns; q[qt++] = ns; }
            }
        }
    }
    for (int s = 0; s < 4; s++) if (!seen[s]) order[oi++] = s;
    int inv[4];
    for (int i = 0; i < 4; i++) inv[order[i]] = i;
    if (inv_out) memcpy(inv_out, inv, sizeof(inv));
    int pos = 0;
    for (int ns = 0; ns < 4; ns++) {
        int os = order[ns];
        if (ns > 0) out[pos++] = '_';
        for (int sym = 0; sym < 2; sym++) {
            Tr t = tbl[os][sym];
            if (t.w < 0) { strcpy(out+pos, "---"); pos += 3; }
            else {
                out[pos++] = '0' + t.w;
                out[pos++] = t.d < 0 ? 'L' : 'R';
                out[pos++] = 'A' + inv[t.ns];
            }
        }
    }
    out[pos] = 0;
}

void parse_tbl(const char *spec, Tr tbl[4][2]) {
    char buf[64]; strncpy(buf, spec, 63); buf[63] = 0;
    char *p = buf;
    for (int st = 0; st < 4; st++) {
        char *nx = strchr(p, '_');
        if (nx) *nx = 0;
        for (int sym = 0; sym < 2; sym++) {
            const char *q = p + sym * 3;
            if (q[0] == '-') tbl[st][sym] = (Tr){-1, 0, 0};
            else tbl[st][sym] = (Tr){q[0]-'0', q[1]=='L'?-1:1, q[2]-'A'};
        }
        if (nx) p = nx + 1;
    }
}

typedef struct { char spec[32]; int P, D, M; } Glider;
static Glider gliders[100000];
static int n_gliders = 0;

int cmp_glider(const void *a, const void *b) {
    const Glider *x = a, *y = b;
    int sx = (x->M >= 10 && x->M <= 26) ? 0 : 1;
    int sy = (y->M >= 10 && y->M <= 26) ? 0 : 1;
    if (sx != sy) return sx - sy;
    if (x->M != y->M) return y->M - x->M;
    return strcmp(x->spec, y->spec);
}

// Fast open-addressing hash set for canonical 32-char specs
#define HTSZ 262144
static char ht[HTSZ][32];
static int ht_used[HTSZ];

unsigned hash_str(const char *s) {
    unsigned h = 2166136261u;
    while (*s) { h ^= (unsigned char)*s++; h *= 16777619u; }
    return h;
}

int ht_insert(const char *s) {
    unsigned idx = hash_str(s) & (HTSZ - 1);
    while (ht_used[idx]) {
        if (strcmp(ht[idx], s) == 0) return 0;
        idx = (idx + 1) & (HTSZ - 1);
    }
    ht_used[idx] = 1;
    strcpy(ht[idx], s);
    return 1;
}

int all4(const char *s) {
    int m = 0;
    for (; *s; s++) if (*s >= 'A' && *s <= 'D') m |= (1 << (*s - 'A'));
    return m == 15;
}

int main() {
    // 1. Engines
    FILE *fe = fopen("bbwork/bb-variants/CET/engines_4x2_tnf.txt", "r");
    FILE *feo = fopen("bbwork/bb-variants/CET/engines_4x2_clean.txt", "w");
    char line[256];
    int e_cnt = 0;
    memset(ht_used, 0, sizeof(ht_used));
    while (fgets(line, sizeof(line), fe)) {
        line[strcspn(line, "\r\n")] = 0;
        char *tab = strchr(line, '\t');
        if (!tab) continue;
        *tab = 0;
        if (!all4(line)) continue;
        char *sr_p = strstr(tab + 1, "sr=");
        if (!sr_p) continue;
        int sr_old = sr_p[3] - 'A';
        char cspec[32]; int inv[4];
        canon_bcd(line, cspec, inv);
        int sr = inv[sr_old];
        // Build combined key cspec+sr so different sr on same canon are kept if distinct!
        char key[36]; sprintf(key, "%s:%c", cspec, 'A'+sr);
        if (!ht_insert(key)) continue;

        Tr tbl[4][2]; parse_tbl(cspec, tbl);
        long long ts[6];
        int ok = 1, mask = 0;
        for (int L = 7; L <= 12; L++) {
            unsigned char tp[512]; memset(tp, 0, sizeof(tp));
            int OFF = 256;
            for (int i = L; i < 250; i++) tp[OFF+i] = 1;
            int pos = OFF - 1, st = sr;
            long long t = 0;
            while (t < 150000) {
                Tr tr = tbl[st][tp[pos]];
                if (tr.w < 0) { ok = 0; break; }
                if (L >= 9) mask |= (1 << st);
                tp[pos] = tr.w; pos += tr.d; st = tr.ns; t++;
                if (pos >= OFF + L) { ts[L-7] = t; break; }
                if (pos < OFF - 60) { ok = 0; break; }
            }
            if (t >= 150000 || !ok) { ok = 0; break; }
        }
        if (ok && mask == 15 && ts[5] >= 4 * ts[2]) {
            fprintf(feo, "%s\tsr=%c\tL12=%lld\trat=%.2f\n", cspec, 'A'+sr, ts[5], (double)ts[5]/ts[2]);
            e_cnt++;
        }
    }
    fclose(fe); fclose(feo);

    // 2. Gliders
    FILE *fg = fopen("bbwork/bb-variants/CET/gliders_4x2_tnf.txt", "r");
    FILE *fgo = fopen("bbwork/bb-variants/CET/gliders_4x2_clean.txt", "w");
    memset(ht_used, 0, sizeof(ht_used));
    while (fgets(line, sizeof(line), fg)) {
        line[strcspn(line, "\r\n")] = 0;
        char *tab = strchr(line, '\t');
        if (!tab) continue;
        *tab = 0;
        if (!all4(line)) continue;
        char *pp = strstr(tab+1, "P="), *dp = strstr(tab+1, "D=");
        if (!pp || !dp) continue;
        int P = atoi(pp+2), D = atoi(dp+2), M = P - D;
        if (P < 4 || M < 8) continue;
        char cspec[32]; canon_bcd(line, cspec, NULL);
        if (!ht_insert(cspec)) continue;
        Tr tbl[4][2]; parse_tbl(cspec, tbl);
        unsigned char tp[2048]; memset(tp, 0, sizeof(tp));
        int pos = 512, st = 0, mask = 0, ok = 1;
        for (int t = 0; t < 1000; t++) {
            Tr tr = tbl[st][tp[pos]];
            if (tr.w < 0) { ok = 0; break; }
            mask |= (1 << st); tp[pos] = tr.w; pos += tr.d; st = tr.ns;
            if (pos < 10 || pos >= 2030) { ok = 0; break; }
        }
        if (ok && mask == 15) {
            strcpy(gliders[n_gliders].spec, cspec);
            gliders[n_gliders].P = P; gliders[n_gliders].D = D; gliders[n_gliders].M = M;
            n_gliders++;
        }
    }
    qsort(gliders, n_gliders, sizeof(Glider), cmp_glider);
    for (int i = 0; i < n_gliders; i++) {
        fprintf(fgo, "%s\tP=%d\tD=%d\tM=%d\n", gliders[i].spec, gliders[i].P, gliders[i].D, gliders[i].M);
    }
    fclose(fg); fclose(fgo);
    printf("Clean all4 canonical engines=%d, gliders(M>=8)=%d\n", e_cnt, n_gliders);
    return 0;
}
