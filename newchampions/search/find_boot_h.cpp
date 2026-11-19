#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <string>
#include <sstream>
#include <algorithm>

// Generic fast Monte-Carlo + Hill-Climbing bootstrap finder
// Target: 0^inf 5^r 3^(2m+1) 2^k A> w HALT_SYM ...
// Args: <core_str> <start_st> <min_r> <max_r> <allowed_w_digits> <top_digit> <halt_digit> <cap> <budget> [blankAfterHalt] [seed]

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
static int MIN_R = 1, MAX_R = 1;
static bool allowW[12];
static int TOP_SYM = 2;
static int HALT_SYM = 5;
static bool REQUIRE_BLANK_AFTER_HALT = false;
static int START_ST = 0;
static int MAX_FILL = 14;

static int bestTop = -1;
static int bestLen = -1;
static int bestStep = 0;
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
    if (n3 < 3 && tape[pos] != 1 && tape[pos] != 2) return false;
    int r = 0;
    while (p >= lo && tape[p] == 5) { r++; p--; }
    if (r < MIN_R || r > MAX_R) return false;
    while (p >= lo) { if (tape[p] != 0) return false; p--; }

    int q = pos;
    int topCnt = 0, wLen = 0;
    while (q <= hi && allowW[tape[q]]) {
        if (tape[q] == TOP_SYM) topCnt++;
        wLen++;
        q++;
    }
    if (topCnt <= 0) return false;
    if (HALT_SYM >= 0) {
        if (q > hi || tape[q] != HALT_SYM) return false;
        if (REQUIRE_BLANK_AFTER_HALT) {
            for (int u = q + 1; u <= hi; u++) if (tape[u] != 0) return false;
        }
    } else {
        for (int u = q; u <= hi; u++) if (tape[u] != 0) return false;
    }

    if (topCnt > bestTop || (topCnt == bestTop && wLen > bestLen) ||
        (topCnt == bestTop && wLen == bestLen && step < bestStep)) {
        bestTop = topCnt;
        bestLen = wLen;
        bestStep = step;
        hasBest = true;
        memcpy(bestTab, tab, sizeof(tab));
        std::string wStr;
        for (int i = pos; i < q; i++) wStr += char('0' + tape[i]);
        char buf[512];
        snprintf(buf, sizeof(buf), "5^%d 3^%d 2^%d A> %s (halt=%d) [top=%d len=%d step=%d]",
                 r, n3, k, wStr.c_str(), HALT_SYM, topCnt, wLen, step);
        bestDesc = buf;
        bestTM = fmtTab(tab);
        printf("NEW BEST: %s\n  TM: %s\n", bestDesc.c_str(), bestTM.c_str());
        fflush(stdout);
        return true;
    }
    return false;
}

struct Undo { int pos; uint8_t old; };
static uint64_t rngState = 0x123456789abcdef1ULL;
static uint64_t xorshift() {
    uint64_t x = rngState;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return rngState = x;
}

static Tr randTr() {
    uint64_t rv = xorshift();
    int w;
    if ((rv & 3) == 0) w = TOP_SYM;
    else if ((rv & 7) == 1 && HALT_SYM >= 0) w = HALT_SYM;
    else w = (int)((rv >> 8) % MS);
    int d = ((rv >> 20) & 1) ? 1 : -1;
    int nx = (int)((rv >> 24) % NS);
    return {(int8_t)w, (int8_t)d, (int8_t)nx};
}

static void runTrial(bool mutateFromBest) {
    if (mutateFromBest && hasBest) {
        memcpy(tab, bestTab, sizeof(tab));
        // Mutate 1 or 2 free cells (either randomize or clear to unassigned)
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
    int pos = MID, st = START_ST, lo = MID, hi = MID, filled = 0;
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
    if (argc < 10) {
        fprintf(stderr, "usage: find_boot <core> <start_st> <min_r> <max_r> <allowW> <top> <halt> <cap> <budget> [blankAfterHalt] [seed]\n");
        return 1;
    }
    std::string core = argv[1];
    START_ST = argv[2][0] - 'A';
    MIN_R = atoi(argv[3]);
    MAX_R = atoi(argv[4]);
    memset(allowW, 0, sizeof(allowW));
    for (const char* p = argv[5]; *p; p++) allowW[*p - '0'] = true;
    TOP_SYM = atoi(argv[6]);
    HALT_SYM = atoi(argv[7]);
    CAP = atoi(argv[8]);
    BUDGET = atoll(argv[9]);
    if (argc > 10) REQUIRE_BLANK_AFTER_HALT = (atoi(argv[10]) != 0);
    if (argc > 11) rngState = strtoull(argv[11], nullptr, 10) | 1ULL;

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
        bool mut = hasBest && ((trials & 3) != 0); // 75% hill-climb, 25% fresh restart
        runTrial(mut);
        trials++;
    }
    printf("DONE: trials=%lld steps=%lld bestTop=%d\n", trials, totalSteps, bestTop);
    return 0;
}
