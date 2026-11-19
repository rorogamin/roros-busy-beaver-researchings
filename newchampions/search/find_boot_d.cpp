#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <string>
#include <sstream>

// Fast Monte-Carlo + Hill-Climbing bootstrap finder for Dcfg Kropitz cores.
// Target landmark:
//   0^inf 3^N <targetSt>> w 0^inf   with N >= 2, w in allowW, topCnt >= 1
// Args:
//   <core> <targetStChar> <allowW> <topSym> <cap> <budget> [targetTop] [seed]

struct Tr { int8_t w, d, nx; };
static int NS = 0, MS = 0;
static Tr coreTab[20][12], tab[20][12], bestTab[20][12];
static uint8_t tape[2048];
static const int MID = 1024;
static int TARGET_ST = 3;
static bool allowW[12];
static int TOP_SYM = 1;
static int CAP = 300;
static long long BUDGET = 80000000LL;
static long long totalSteps = 0;
static int TARGET_TOP = 10;
static int MAX_FILL = 16;

static int bestTopScore = -1;
static int bestExtra = 999999;
static int bestTopRaw = -1;
static int bestStep = 999999;
static bool hasBest = false;
static std::string bestDesc, bestTM;
static std::vector<std::pair<int,int>> freeCells;

static std::string fmtTab(const Tr t[20][12]) {
    std::string out;
    for (int s = 0; s < NS; s++) {
        if (s) out += '_';
        for (int sym = 0; sym < MS; sym++) {
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

static bool checkLandmark(int pos, int st, int step, int lo, int hi) {
    if (st != TARGET_ST) return false;
    int p = pos - 1;
    int n3 = 0;
    while (p >= lo && tape[p] == 3) { n3++; p--; }
    if (n3 < 2 || n3 > 20) return false;
    while (p >= lo) { if (tape[p] != 0) return false; p--; }

    int q = pos;
    int topCnt = 0, wLen = 0;
    while (q <= hi && allowW[tape[q]]) {
        if (tape[q] == TOP_SYM) topCnt++;
        wLen++;
        q++;
    }
    if (topCnt <= 0) return false;
    for (int u = q; u <= hi; u++) if (tape[u] != 0) return false;

    int topScore = (topCnt > TARGET_TOP) ? TARGET_TOP : topCnt;
    int extra = wLen - topCnt;
    bool better = false;
    if (topScore > bestTopScore) better = true;
    else if (topScore == bestTopScore) {
        if (extra < bestExtra) better = true;
        else if (extra == bestExtra) {
            if (step < bestStep) better = true;
            else if (step == bestStep && topCnt > bestTopRaw) better = true;
        }
    }
    if (better) {
        bestTopScore = topScore;
        bestExtra = extra;
        bestTopRaw = topCnt;
        bestStep = step;
        hasBest = true;
        memcpy(bestTab, tab, sizeof(tab));
        std::string wStr;
        for (int i = pos; i < q; i++) wStr += char('0' + tape[i]);
        char buf[512];
        snprintf(buf, sizeof(buf), "3^%d %c> %s 0^inf [top=%d extra=%d step=%d]",
                 n3, char('A' + TARGET_ST), wStr.c_str(), topCnt, extra, step);
        bestDesc = buf;
        bestTM = fmtTab(tab);
        printf("NEW BEST: %s\n  TM: %s\n", bestDesc.c_str(), bestTM.c_str());
        fflush(stdout);
        return true;
    }
    return false;
}

struct Undo { int pos; uint8_t old; };
static uint64_t rngState = 0xabcdef1234567891ULL;
static uint64_t xorshift() {
    uint64_t x = rngState;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return rngState = x;
}

static Tr randTr() {
    uint64_t rv = xorshift();
    int w = ((rv & 3) == 0) ? TOP_SYM : (int)((rv >> 8) % MS);
    int d = ((rv >> 20) & 1) ? 1 : -1;
    int nx = (int)((rv >> 24) % NS);
    return {(int8_t)w, (int8_t)d, (int8_t)nx};
}

static void runTrial(bool mutateFromBest) {
    if (mutateFromBest && hasBest) {
        memcpy(tab, bestTab, sizeof(tab));
        int nmut = 1 + (int)(xorshift() & 1);
        for (int i = 0; i < nmut; i++) {
            auto c = freeCells[xorshift() % freeCells.size()];
            if ((xorshift() & 3) == 0) tab[c.first][c.second] = {-1, 0, -2};
            else tab[c.first][c.second] = randTr();
        }
    } else {
        memcpy(tab, coreTab, sizeof(tab));
    }
    std::vector<Undo> undos;
    undos.reserve(CAP + 1);
    int pos = MID, st = 0, lo = MID, hi = MID, filled = 0;
    for (int step = 0; step < CAP; step++) {
        totalSteps++;
        checkLandmark(pos, st, step, lo, hi);
        uint8_t sym = tape[pos];
        Tr tr = tab[st][sym];
        if (tr.nx == -2) {
            if (filled >= MAX_FILL) break;
            tab[st][sym] = randTr();
            filled++;
            tr = tab[st][sym];
        }
        if (tr.nx == -1) break;
        undos.push_back({pos, sym});
        tape[pos] = tr.w;
        if (pos < lo) lo = pos;
        if (pos > hi) hi = pos;
        pos += tr.d;
        st = tr.nx;
        if (pos <= 10 || pos >= 2035) break;
    }
    for (int i = (int)undos.size() - 1; i >= 0; i--)
        tape[undos[i].pos] = undos[i].old;
}

int main(int argc, char** argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: find_boot_d <core> <targetSt> <allowW> <topSym> <cap> <budget> [targetTop] [seed]\n");
        return 1;
    }
    std::string core = argv[1];
    TARGET_ST = argv[2][0] - 'A';
    memset(allowW, 0, sizeof(allowW));
    for (const char* p = argv[3]; *p; p++) allowW[*p - '0'] = true;
    TOP_SYM = atoi(argv[4]);
    CAP = atoi(argv[5]);
    BUDGET = atoll(argv[6]);
    if (argc > 7) TARGET_TOP = atoi(argv[7]);
    if (argc > 8) rngState = strtoull(argv[8], nullptr, 10) | 1ULL;

    std::vector<std::string> rows;
    std::stringstream ss(core);
    std::string item;
    while (std::getline(ss, item, '_')) rows.push_back(item);
    NS = (int)rows.size();
    MS = (int)rows[0].size() / 3;
    for (int s = 0; s < NS; s++) {
        for (int sym = 0; sym < MS; sym++) {
            const char* c = rows[s].c_str() + 3 * sym;
            if (c[0] == '-') {
                coreTab[s][sym] = {-1, 0, -2};
                freeCells.push_back({s, sym});
            } else {
                coreTab[s][sym].w = c[0] - '0';
                coreTab[s][sym].d = (c[1] == 'L') ? -1 : 1;
                coreTab[s][sym].nx = (c[2] == 'Z') ? -1 : (c[2] - 'A');
            }
        }
    }
    memset(tape, 0, sizeof(tape));
    long long trials = 0;
    while (totalSteps < BUDGET) {
        runTrial(hasBest && ((trials & 3) != 0));
        trials++;
    }
    printf("DONE: trials=%lld steps=%lld bestTop=%d extra=%d step=%d\n",
           trials, totalSteps, bestTopRaw, bestExtra, bestStep);
    return 0;
}
