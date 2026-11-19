#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <string>

// Fast DFS for fw4_8 (4 states, 8 symbols) maximizing count of 7s in 0^inf 3^N D> w 0^inf (w in {4,5,6,7}^*, N>=2)
// Fixed fw4_8 core:
// A: 0:5LC 1:3LB 2:7LA 3:2RA 4:4LB 5:--- 6:4LB 7:6LA
// B: 0:1RZ 1:3RB 2:1LC 3:2RA 4:3RD 5:3RA 6:4LC 7:---
// C: 0:3RB 1:1LB 2:3LC 3:2RC 4:4LC 5:--- 6:5LD 7:---
// D: 0:3RB 1:--- 2:6LC 3:4LD 4:4LC 5:4LD 6:6LC 7:7LA

struct Tr { int8_t w, d, nx; }; // nx = -2 unassigned, -1 halt
static Tr tab[4][8];
static uint8_t tape[4096];
static const int MID = 2048;
static int CAP = 600;
static long long BUDGET = 80000000LL;
static long long totalSteps = 0;
static int bestSevens = 0;
static int bestTotal = 0;
static int bestStep = 0;
static int bestN = 0;
static std::string bestWord;
static Tr bestTab[4][8];

static void setCell(int s, int sym, const char* c) {
    if (c[0] == '-') { tab[s][sym] = {-1, 0, -2}; return; }
    tab[s][sym].w = c[0] - '0';
    tab[s][sym].d = (c[1] == 'L') ? -1 : 1;
    tab[s][sym].nx = (c[2] == 'Z') ? -1 : (c[2] - 'A');
}

static void initCore() {
    const char* rows[4] = {
        "5LC3LB7LA2RA4LB---4LB6LA",
        "1RZ3RB1LC2RA3RD3RA4LC---",
        "3RB1LB3LC2RC4LC---5LD---",
        "3RB---6LC4LD4LC4LD6LC7LA"
    };
    for (int s = 0; s < 4; s++)
        for (int sym = 0; sym < 8; sym++)
            setCell(s, sym, rows[s] + 3*sym);
}

static std::string fmtTab(const Tr t[4][8]) {
    std::string out;
    for (int s = 0; s < 4; s++) {
        if (s) out += '_';
        for (int sym = 0; sym < 8; sym++) {
            if (t[s][sym].nx == -2) out += "---";
            else {
                out += char('0' + t[s][sym].w);
                out += (t[s][sym].d == -1 ? 'L' : 'R');
                out += (t[s][sym].nx == -1 ? 'Z' : char('A' + t[s][sym].nx));
            }
        }
    }
    return out;
}

static void checkLandmark(int pos, int st, int step, int lo, int hi) {
    if (st != 3) return; // must be in state D
    // Left of pos must be 0^inf 3^N with N >= 2
    int n3 = 0;
    int p = pos - 1;
    while (p >= lo && tape[p] == 3) { n3++; p--; }
    if (n3 < 2) return;
    while (p >= lo) { if (tape[p] != 0) return; p--; }
    // Right from pos must be {4,5,6,7}^* followed by 0^inf
    int sevens = 0, tot = 0;
    int q = pos;
    while (q <= hi && tape[q] >= 4 && tape[q] <= 7) {
        if (tape[q] == 7) sevens++;
        tot++;
        q++;
    }
    if (sevens <= 0) return;
    int r = q;
    while (r <= hi) { if (tape[r] != 0) return; r++; }
    if (sevens > bestSevens || (sevens == bestSevens && tot > bestTotal)) {
        bestSevens = sevens;
        bestTotal = tot;
        bestStep = step;
        bestN = n3;
        bestWord.clear();
        for (int i = pos; i < q; i++) bestWord += char('0' + tape[i]);
        memcpy(bestTab, tab, sizeof(tab));
        printf("NEW BEST: 3^%d D> %s (sevens=%d, len=%d, step=%d)\n  TM: %s\n",
               n3, bestWord.c_str(), sevens, tot, step, fmtTab(tab).c_str());
        fflush(stdout);
    }
}

struct Undo { int pos; uint8_t old; };

static void dfs(int pos, int st, int step, int lo, int hi, int filled) {
    if (totalSteps >= BUDGET) return;
    std::vector<Undo> undos;
    undos.reserve(CAP - step + 1);
    while (step < CAP) {
        if (totalSteps >= BUDGET) break;
        totalSteps++;
        checkLandmark(pos, st, step, lo, hi);
        uint8_t sym = tape[pos];
        Tr tr = tab[st][sym];
        if (tr.nx == -2) {
            if (filled < 5) {
                for (int w = 7; w >= 0; w--) {
                    for (int d = -1; d <= 1; d += 2) {
                        for (int nx = 0; nx < 4; nx++) {
                            if (totalSteps >= BUDGET) break;
                            tab[st][sym] = {(int8_t)w, (int8_t)d, (int8_t)nx};
                            uint8_t old = tape[pos];
                            tape[pos] = w;
                            int nlo = lo, nhi = hi;
                            if (pos < nlo) nlo = pos;
                            if (pos > nhi) nhi = pos;
                            dfs(pos + d, nx, step + 1, nlo, nhi, filled + 1);
                            tape[pos] = old;
                        }
                    }
                }
                tab[st][sym] = {-1, 0, -2};
            }
            break;
        }
        if (tr.nx == -1) break;
        undos.push_back({pos, sym});
        tape[pos] = tr.w;
        if (pos < lo) lo = pos;
        if (pos > hi) hi = pos;
        pos += tr.d;
        st = tr.nx;
        step++;
        if (pos <= 10 || pos >= 4085) break;
    }
    for (int i = (int)undos.size() - 1; i >= 0; i--)
        tape[undos[i].pos] = undos[i].old;
}

int main(int argc, char** argv) {
    if (argc > 1) CAP = atoi(argv[1]);
    if (argc > 2) BUDGET = atoll(argv[2]);
    initCore();
    memset(tape, 0, sizeof(tape));
    dfs(MID, 0, 0, MID, MID, 0);
    printf("DONE: totalSteps=%lld bestSevens=%d bestStep=%d\n", totalSteps, bestSevens, bestStep);
    return 0;
}
