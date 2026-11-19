#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <string>
#include <sstream>
#include <algorithm>

// Fast Monte-Carlo + Hill-Climbing bootstrap finder for cursor-5 Fwp2_H cores.
// Target landmark:
//   0^inf 5^r 3^(2m+1) 2^1 A> w_low 5 w_high 0^inf
// Args:
//   <core_str> <min_r> <max_r> <allowLow> <allowHigh> <topSym> <cap> <budget> [targetTop] [seed]
// Note:
//   - If w_low is empty, requires n3 >= 3 (i.e. m >= 1).
//   - If w_low is nonempty, requires n3 >= 3 OR w_low[0] == 1 OR w_low[0] == 2.
//   - Requires exact 0^inf after w_high (so 5 0 halts cleanly!).
//   - Maximizes min(topCnt, targetTop), then minimizes (wLowLen + nonTopHigh), then minimizes step.

struct Tr { int8_t w, d, nx; }; // nx=-2 unassigned, -1 halt
static int NS = 0, MS = 0;
static Tr coreTab[20][12];
static Tr tab[20][12];
static Tr bestTab[20][12];
static uint8_t tape[2048];
static const int MID = 1024;
static int CAP = 350;
static long long BUDGET = 50000000LL;
static long long totalSteps = 0;
static int MIN_R = 1, MAX_R = 8;
static bool allowLow[12];
static bool allowHigh[12];
static int TOP_SYM = 1;
static int TARGET_TOP = 8;
static int MAX_FILL = 18;

static int bestTopScore = -1;
static int bestExtra = 999999;
static int bestTopRaw = -1;
static int bestStep = 999999;
static bool hasBest = false;
static std::string bestDesc;
static std::string bestTM;

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
    if (st != 0) return false; // A>
    int p = pos - 1;
    int k = 0;
    while (p >= lo && tape[p] == 2) { k++; p--; }
    if (k != 1) return false;
    int n3 = 0;
    while (p >= lo && tape[p] == 3) { n3++; p--; }
    if (n3 < 1 || (n3 % 2) == 0) return false;
    int r = 0;
    while (p >= lo && tape[p] == 5) { r++; p--; }
    if (r < MIN_R || r > MAX_R) return false;
    while (p >= lo) { if (tape[p] != 0) return false; p--; }

    // Right side: w_low 5 w_high 0^inf
    int q = pos;
    int lowLen = 0;
    while (q <= hi && tape[q] != 5 && allowLow[tape[q]]) {
        lowLen++;
        q++;
    }
    if (q > hi || tape[q] != 5) return false;
    if (lowLen > 4) return false;
    // Safety for m=0: require n3 >= 3 OR (lowLen > 0 && (tape[pos] == 1 || tape[pos] == 2))
    if (n3 < 3) {
        if (lowLen == 0) return false;
        if (tape[pos] != 1 && tape[pos] != 2) return false;
    }
    int pos5 = q;
    q++; // skip cursor 5

    int topCnt = 0, highLen = 0;
    while (q <= hi && allowHigh[tape[q]]) {
        if (tape[q] == TOP_SYM) topCnt++;
        highLen++;
        q++;
    }
    if (topCnt <= 0) return false;
    // Must be 0^inf after w_high!
    for (int u = q; u <= hi; u++) {
        if (tape[u] != 0) return false;
    }

    int topScore = (topCnt > TARGET_TOP) ? TARGET_TOP : topCnt;
    int extra = lowLen + (highLen - topCnt);

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
        std::string wLow, wHigh;
        for (int i = pos; i < pos5; i++) wLow += char('0' + tape[i]);
        for (int i = pos5 + 1; i < q; i++) wHigh += char('0' + tape[i]);
        char buf[512];
        snprintf(buf, sizeof(buf), "5^%d 3^%d 2 A> %s 5 %s 0^inf [top=%d extra=%d step=%d]",
                 r, n3, wLow.c_str(), wHigh.c_str(), topCnt, extra, step);
        bestDesc = buf;
        bestTM = fmtTab(tab);
        printf("NEW BEST: %s\n  TM: %s\n", bestDesc.c_str(), bestTM.c_str());
        fflush(stdout);
        return true;
    }
    return false;
}

struct Undo { int pos; uint8_t old; };
static uint64_t rngState = 0x987654321abcdef1ULL;
static uint64_t xorshift() {
    uint64_t x = rngState;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return rngState = x;
}

static Tr randTr() {
    uint64_t rv = xorshift();
    int w;
    uint64_t rmod = rv & 7;
    if (rmod == 0 || rmod == 1) w = TOP_SYM;
    else if (rmod == 2) w = 5;
    else w = (int)((rv >> 8) % MS);
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
    if (argc < 9) {
        fprintf(stderr, "usage: find_boot_cursor <core> <min_r> <max_r> <allowLow> <allowHigh> <topSym> <cap> <budget> [targetTop] [seed]\n");
        return 1;
    }
    std::string core = argv[1];
    MIN_R = atoi(argv[2]);
    MAX_R = atoi(argv[3]);
    memset(allowLow, 0, sizeof(allowLow));
    for (const char* p = argv[4]; *p; p++) if (*p >= '0' && *p <= '9') allowLow[*p - '0'] = true;
    memset(allowHigh, 0, sizeof(allowHigh));
    for (const char* p = argv[5]; *p; p++) if (*p >= '0' && *p <= '9') allowHigh[*p - '0'] = true;
    TOP_SYM = atoi(argv[6]);
    CAP = atoi(argv[7]);
    BUDGET = atoll(argv[8]);
    if (argc > 9) TARGET_TOP = atoi(argv[9]);
    if (argc > 10) rngState = strtoull(argv[10], nullptr, 10) | 1ULL;

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
        bool mut = hasBest && ((trials & 3) != 0);
        runTrial(mut);
        trials++;
    }
    printf("DONE: trials=%lld steps=%lld bestTop=%d extra=%d step=%d\n",
           trials, totalSteps, bestTopRaw, bestExtra, bestStep);
    return 0;
}
