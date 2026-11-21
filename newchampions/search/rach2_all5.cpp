#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <tuple>

struct Tr { uint8_t w; int8_t d; int8_t ns; };
static const int CELLS = 4096;
static const int MID = 2048;

static uint64_t rng = 0x1122334455667789ULL;
static inline uint64_t nextRng() {
    uint64_t x = rng; x ^= x << 13; x ^= x >> 7; x ^= x << 17; return rng = x;
}

static const char *CORE17 =
    "0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_"
    "1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ";

static void parseCore(const std::string &s, Tr tab[25][2]) {
    for (int i = 0; i < 25; ++i)
        for (int c = 0; c < 2; ++c) tab[i][c] = {0, 0, -2};
    int r = 0, pos = 0;
    while (pos < (int)s.size()) {
        for (int c = 0; c < 2; ++c) {
            std::string cell = s.substr(pos, 3); pos += 3;
            if (cell != "---")
                tab[r][c] = {(uint8_t)(cell[0]-'0'), (int8_t)(cell[1]=='L' ? -1 : 1), (int8_t)(cell[2]-'A')};
        }
        if (pos < (int)s.size() && s[pos] == '_') ++pos;
        ++r;
    }
}

static std::string fmtTab(Tr tab[25][2], int nst) {
    std::string out;
    for (int r = 0; r < nst; ++r) {
        if (r) out.push_back('_');
        for (int c = 0; c < 2; ++c) {
            if (tab[r][c].ns == -2) out += "---";
            else { out.push_back('0'+tab[r][c].w); out.push_back(tab[r][c].d<0?'L':'R'); out.push_back('A'+tab[r][c].ns); }
        }
    }
    return out;
}

// Match ONLY pure stack entered directly in H:
// 0^inf 1^3 H> 0 1^{b_1} 0 ... 0 1^{b_k} 00 1^c 0^inf  (k >= 4, b_k >= 2, c >= 3)
// Notice: once in this pure stack in state H, ONLY A..Q and (T0, R0) [for BB(21..24)] or (X0, V0, T0, R0) [for BB(25)] are EVER visited!
// S0, U0 (and W0, Y0 in BB(25)) are NEVER visited again!
struct Score {
    int c = 0, k = 0, last_b = 0;
    bool operator>(const Score &o) const {
        return std::tie(c, k, last_b) > std::tie(o.c, o.k, o.last_b);
    }
};

static Score matchH(const uint8_t *tape, int p, int lo, int hi, int st, std::string *desc = nullptr) {
    Score z;
    if (st != 7 || tape[p] != 0) return z;
    if (p < 3 || tape[p-1] != 1 || tape[p-2] != 1 || tape[p-3] != 1) return z;
    for (int i = lo; i < p - 3; ++i) if (tape[i] != 0) return z;
    int t = p + 1, k = 0, last_b = 0;
    std::string sd;
    while (t <= hi && tape[t] == 1) {
        int b = 0;
        while (t <= hi && tape[t] == 1) { ++b; ++t; }
        ++k; last_b = b;
        if (desc) { if (!sd.empty()) sd += ","; sd += std::to_string(b); }
        if (t <= hi && tape[t] == 0) {
            ++t;
            if (t <= hi && tape[t] == 0) {
                ++t;
                int c = 0;
                while (t <= hi && tape[t] == 1) { ++c; ++t; }
                if (c < 3 || k < 4 || last_b < 2) return z;
                for (int i = t; i <= hi; ++i) if (tape[i] != 0) return z;
                if (desc) *desc = "111 H> 0 [" + sd + "] 00 1^" + std::to_string(c);
                return {c, k, last_b};
            }
        } else return z;
    }
    return z;
}

static int gNst;
static Tr gBase[25][2], gTab[25][2], gBestTab[25][2];
static Score gBest;
static int gBestStep = 0;
static std::string gBestDesc;
static uint8_t gTape[CELLS];
static long long gSteps = 0, gBudget = 0;
static std::vector<Tr> gChoices;

static void dfs(int pos, int st, int lo, int hi, int steps, int cap, int depth, long long &bs, long long blim) {
    if (gSteps >= gBudget || bs >= blim) return;
    struct Undo { int idx; uint8_t oldv; };
    std::vector<Undo> undos;
    undos.reserve(64);
    while (steps < cap) {
        if (pos < 16 || pos >= CELLS - 16) break;
        Score sc = matchH(gTape, pos, lo, hi, st);
        if (sc > gBest) {
            std::string desc;
            matchH(gTape, pos, lo, hi, st, &desc);
            gBest = sc; gBestStep = steps; gBestDesc = desc;
            memcpy(gBestTab, gTab, sizeof(gTab));
            printf("  NEW BEST BB(%d,2): c=%d k=%d last_b=%d step=%d (%s) | %s\n",
                   gNst, sc.c, sc.k, sc.last_b, steps, desc.c_str(), fmtTab(gTab, gNst).c_str());
            fflush(stdout);
        }
        uint8_t sym = gTape[pos];
        Tr &tr = gTab[st][sym];
        if (tr.ns == -2) {
            int nch = (int)gChoices.size();
            int start = (int)(nextRng() % nch);
            int stride = 1 + (int)(nextRng() % (nch - 1));
            long long subLim = (depth == 0) ? 25000 : (depth == 1 ? 8000 : 2500);
            for (int kk = 0; kk < nch; ++kk) {
                if (gSteps >= gBudget || bs >= blim) break;
                int ci = (start + (int)((1LL * kk * stride) % nch)) % nch;
                tr = gChoices[ci];
                long long sub = 0;
                dfs(pos, st, lo, hi, steps, cap, depth + 1, sub, subLim);
                bs += sub;
            }
            tr = {0, 0, -2};
            break;
        }
        if (tr.ns == 25) break;
        if (gTape[pos] != tr.w) { undos.push_back({pos, gTape[pos]}); gTape[pos] = tr.w; }
        if (pos < lo) lo = pos;
        if (pos > hi) hi = pos;
        pos += tr.d; st = tr.ns;
        ++steps; ++gSteps; ++bs;
    }
    for (int i = (int)undos.size() - 1; i >= 0; --i) gTape[undos[i].idx] = undos[i].oldv;
}

static void run(int nst, const std::string &ring, long long budget, uint64_t seed) {
    gNst = nst; gBudget = budget; gSteps = 0; rng = seed | 1ULL;
    parseCore(std::string(CORE17) + "_" + ring, gBase);
    gBest = Score(); gBestStep = 0; gBestDesc = "";
    gChoices.clear();
    for (int w = 0; w < 2; ++w)
        for (int d = -1; d <= 1; d += 2)
            for (int ns = 0; ns < nst; ++ns)
                gChoices.push_back({(uint8_t)w, (int8_t)d, (int8_t)ns});
    std::vector<std::pair<int,int>> fcs;
    for (int s = 0; s < nst; ++s)
        for (int c = 0; c < 2; ++c)
            if (gBase[s][c].ns == -2) fcs.push_back({s, c});
    printf("=== Search BB(%d,2) (%d free cells) ===\n", nst, (int)fcs.size());
    int pass = 0;
    int caps[4] = { 250, 500, 1200, 3000 };
    while (gSteps < gBudget) {
        int cap = caps[pass % 4];
        memset(gTape, 0, sizeof(gTape));
        if (gBest.c > 0 && (pass & 1) && fcs.size() > 2) {
            memcpy(gTab, gBestTab, sizeof(gTab));
            int nun = 1 + (int)(nextRng() % 3);
            for (int u = 0; u < nun; ++u) {
                auto fc = fcs[nextRng() % fcs.size()];
                gTab[fc.first][fc.second] = {0, 0, -2};
            }
        } else memcpy(gTab, gBase, sizeof(gBase));
        long long bs = 0;
        dfs(MID, 0, MID, MID, 0, cap, 0, bs, 250000);
        ++pass;
    }
    printf("FINAL BB(%d,2): c=%d k=%d last_b=%d step=%d (%s)\n  %s\n\n",
           nst, gBest.c, gBest.k, gBest.last_b, gBestStep, gBestDesc.c_str(), fmtTab(gBestTab, nst).c_str());
}

int main() {
    // BB(21,2): BOTH S0 and U0 are free!
    run(21, "1RZ0LS_---0LT_1LH1LU_---1LR", 60000000LL, 21001);
    // BB(22,2): S0, U0, V0, V1 are ALL free (4 free cells)!
    run(22, "1RZ0LS_---0LT_1LH1LU_---1LR_------", 100000000LL, 22001);
    // BB(25,2): S0, U0, W0, Y0 are ALL free (4 free cells)!
    run(25, "1RZ0LS_---0LT_1LH1LU_---1LV_0LH0LW_---0LX_1LH1LY_---1LR", 100000000LL, 25001);
    return 0;
}
