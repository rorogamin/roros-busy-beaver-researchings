// find_hydra_boot.cpp — Ultra-fast Monte-Carlo + Graduated Shaping + LNS bootstrapper
// specifically engineered for Busy Beaver Hydra cores (fe0, fe1, fe2, fe3) up to 40 states, 10 symbols.
//
// Supports:
//   1) 0^inf 1^m <head> X^n 0^inf           (KIND_ONES, standard fe0/fe1/fe2/fe3)
//   2) 0^inf 1^k 0 1^m <head> X^n 0^inf     (fe01_5 / --left-sep)
//
// Key speedup over generic bbsearch:
//   - Weighted random fill heavily favoring {X, 1, 0} + head states (B).
//   - 3-tier graduated shaping reward:
//       Tier 3: Exact clean landmark (m>=1, n>=1, no dirty tape) -> scored by (n, m, irreducibility_bonus, -step)
//       Tier 2: Reached head state B scanning X with clean-left 1^m (or partial) -> guides LNS straight to Tier 3!
//       Tier 1: Boot trajectory wrote >=1 X and >=1 1 and used multiple states -> guides cold starts!
//   - Post-landmark simulation check (5,000 steps) + state/symbol irreducibility scoring.
//   - Multi-startstate probing (with automatic A <-> startstate relabeling on output!).
//
// Build: g++ -O3 -march=native -std=c++17 -o find_hydra_boot.exe find_hydra_boot.cpp

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <string>
#include <vector>

static const int MAXST = 40;
static const int MAXSYM = 10;
static const int TAPE_SZ = 131072;
static const int MID = 65536;

struct Tr { int8_t w, mv, nst; }; // nst: -2 UNASSIGNED, -1 HALT_Z, -3 HALT_UNDEF
static const int8_t UNASSIGNED = -2;
static const int8_t HALT_Z = -1;
static const int8_t HALT_UNDEF = -3;

static inline char stChar(int s) {
    return (s < 25) ? (char)('A' + s) : (char)('a' + (s - 25));
}
static inline int parseStChar(char c) {
    if (c >= 'A' && c <= 'Y') return c - 'A';
    if (c >= 'a' && c <= 'o') return 25 + (c - 'a');
    return -1;
}

struct CoreDef {
    std::string name, cfg, slot, core;
    int nfixed = 0, nsym = 0;
    int headState = 1; // B
    int targetSym = 2;
    bool leftSep = false; // 1^k 0 1^m B> X^n
    Tr tab[MAXST][MAXSYM];
};

static std::string trim(const std::string &s) {
    size_t b = 0, e = s.size();
    while (b < e && isspace((unsigned char)s[b])) ++b;
    while (e > b && isspace((unsigned char)s[e - 1])) --e;
    return s.substr(b, e - b);
}

static bool parseCore(const std::string &path, const std::string &wantName, CoreDef &out) {
    FILE *f = fopen(path.c_str(), "r");
    if (!f) return false;
    char buf[8192];
    std::string nm, cfg, slot, core;
    bool found = false;
    auto flush = [&]() {
        if (nm == wantName && !core.empty()) {
            out.name = nm; out.cfg = cfg; out.slot = slot; out.core = core;
            found = true;
        }
    };
    while (fgets(buf, sizeof buf, f)) {
        std::string l = trim(buf);
        if (l.empty() || l[0] == '#' || l[0] == '*') continue;
        if (l.rfind("name ", 0) == 0) { flush(); if (found) break; nm = trim(l.substr(5)); cfg = slot = core = ""; }
        else if (l.rfind("cfg ", 0) == 0) cfg = trim(l.substr(4));
        else if (l.rfind("slot ", 0) == 0) slot = trim(l.substr(5));
        else if (l.rfind("core ", 0) == 0) core = trim(l.substr(5));
    }
    if (!found) flush();
    fclose(f);
    if (!found) return false;

    for (int s = 0; s < MAXST; ++s)
        for (int y = 0; y < MAXSYM; ++y)
            out.tab[s][y] = {0, 0, UNASSIGNED};

    std::vector<std::string> rows;
    size_t p = 0;
    while (true) {
        size_t u = out.core.find('_', p);
        rows.push_back(out.core.substr(p, (u == std::string::npos ? out.core.size() : u) - p));
        if (u == std::string::npos) break;
        p = u + 1;
    }
    out.nfixed = (int)rows.size();
    out.nsym = (int)(rows[0].size() / 3);
    for (int s = 0; s < out.nfixed; ++s) {
        for (int y = 0; y < out.nsym; ++y) {
            const char *t = rows[s].c_str() + 3 * y;
            if (t[0] == '-') continue;
            int w = t[0] - '0';
            int mv = (t[1] == 'L') ? -1 : 1;
            int8_t ns = (t[2] == 'Z') ? HALT_Z : (int8_t)parseStChar(t[2]);
            out.tab[s][y] = {(int8_t)w, (int8_t)mv, ns};
        }
    }

    // Parse cfg: e.g. "1^m B> 5^n BLANK" or "1^k 0^1 1^m B> 2^n BLANK"
    out.leftSep = (out.cfg.find("0^1") != std::string::npos);
    size_t gt = out.cfg.find('>');
    if (gt != std::string::npos && gt >= 1) {
        out.headState = parseStChar(out.cfg[gt - 1]);
        std::string rightPart = trim(out.cfg.substr(gt + 1));
        for (char ch : rightPart) {
            if (isdigit((unsigned char)ch)) { out.targetSym = ch - '0'; break; }
        }
    }
    return true;
}

static uint64_t gRng = 0x9e3779b97f4a7c15ULL;
static inline uint64_t rng() {
    uint64_t x = gRng;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return gRng = x;
}

struct BestHit {
    int tier = 0;
    long long score1 = -1; // n (or k for leftSep)
    long long score2 = -1; // m
    long long score3 = -1; // extra sym/state count or -step
    int step = 0;
    int m = 0, n = 0, k = 0;
    Tr tab[MAXST][MAXSYM];
};

static int nstates = 24, nsyms = 9;
static CoreDef gCore;
static Tr curTab[MAXST][MAXSYM];
static Tr seedTab[MAXST][MAXSYM];
static bool hasSeedTab = false;
static uint8_t tape[TAPE_SZ];
static int CAP = 1200;
static long long BUDGET = 200000000LL;
static int gStartState = 0;

static std::vector<std::pair<int, int>> freeCells;

static std::string fmtTab(const Tr t[MAXST][MAXSYM], int startSt) {
    // If startSt != 0, relabel state 0 <-> startSt so output starts at A!
    auto mapSt = [&](int s) {
        if (startSt == 0) return s;
        if (s == 0) return startSt;
        if (s == startSt) return 0;
        return s;
    };
    std::string out;
    for (int os = 0; os < nstates; ++os) {
        if (os) out += '_';
        int s = mapSt(os);
        for (int y = 0; y < nsyms; ++y) {
            Tr tr = t[s][y];
            if (tr.nst == UNASSIGNED || tr.nst == HALT_UNDEF) {
                out += "---";
            } else if (tr.nst == HALT_Z) {
                out += char('0' + tr.w);
                out += (tr.mv < 0 ? 'L' : 'R');
                out += 'Z';
            } else {
                out += char('0' + tr.w);
                out += (tr.mv < 0 ? 'L' : 'R');
                out += stChar(mapSt(tr.nst));
            }
        }
    }
    return out;
}

// Check 5000 steps post-landmark to reject instant UNDEF/halting dead ends
static bool survivePost(const Tr t[MAXST][MAXSYM], int pos, int st, int lo, int hi, int &usedStCnt, int &usedSymCnt,
                        uint64_t initStMask, uint32_t initSymMask) {
    static uint8_t ptape[TAPE_SZ];
    memcpy(ptape, tape, TAPE_SZ);
    uint64_t stMask = initStMask;
    uint32_t symMask = initSymMask;
    int p = pos, s = st;
    for (int step = 0; step < 5000; ++step) {
        if (p < 2 || p >= TAPE_SZ - 2) return false;
        uint8_t c = ptape[p];
        stMask |= (1ULL << s);
        symMask |= (1u << c);
        Tr tr = t[s][c];
        if (tr.nst == UNASSIGNED || tr.nst == HALT_UNDEF || tr.nst == HALT_Z) return false;
        ptape[p] = (uint8_t)tr.w;
        p += tr.mv;
        s = tr.nst;
    }
    usedStCnt = __builtin_popcountll(stMask);
    usedSymCnt = __builtin_popcount(symMask);
    return true;
}

static inline Tr pickWeightedTr(int curSt, int curSym, int targetSym) {
    uint64_t r = rng();
    int w;
    uint64_t wr = r % 100;
    if (wr < 32) w = targetSym;
    else if (wr < 58) w = 1;
    else if (wr < 72) w = 0;
    else w = (int)((r >> 8) % nsyms);

    int mv = ((r >> 16) & 1) ? 1 : -1;

    int nst;
    uint64_t sr = (r >> 17) % 100;
    if (sr < 18 && w == targetSym) {
        nst = gCore.headState; // jump into B!
    } else if (sr < 45 && nstates > gCore.nfixed) {
        // favor extra boot states when available
        nst = gCore.nfixed + (int)((r >> 24) % (nstates - gCore.nfixed));
    } else if (sr < 65) {
        // favor states that appear in boot paths: A, L..R, nfixed..
        nst = (int)((r >> 24) % nstates);
    } else {
        nst = (int)((r >> 24) % nstates);
    }
    return {(int8_t)w, (int8_t)mv, (int8_t)nst};
}

static BestHit best;
static BestHit bestIrred;

static void checkTapeLandmark(int pos, int st, int step, int lo, int hi,
                              uint64_t stMask, uint32_t symMask, BestHit &unusedBest) {
    (void)unusedBest;
    if (st != gCore.headState) return;
    int X = gCore.targetSym;
    if (tape[pos] != X) return;

    // Check right: X^n 0^inf
    int r = pos, n = 0;
    while (r <= hi && tape[r] == X) { ++n; ++r; }
    if (n < 1) return;
    bool rightClean = true;
    for (int u = r; u <= hi; ++u) {
        if (tape[u] != 0) { rightClean = false; break; }
    }

    // Check left: 0^inf [1^k 0] 1^m
    int l = pos - 1, m = 0;
    while (l >= lo && tape[l] == 1) { ++m; --l; }
    if (m < 1) return;
    int k = 0;
    if (gCore.leftSep) {
        if (l < lo || tape[l] != 0) return;
        --l;
        while (l >= lo && tape[l] == 1) { ++k; --l; }
        if (k < 2) return;
    }
    bool leftClean = true;
    for (int u = lo; u <= l; ++u) {
        if (tape[u] != 0) { leftClean = false; break; }
    }

    if (leftClean && rightClean) {
        // Check survival 5000 steps post-landmark!
        int ust = 0, usy = 0;
        if (!survivePost(curTab, pos, st, lo, hi, ust, usy, stMask, symMask)) return;

        int irred = (ust == nstates && usy == nsyms) ? 1 : 0;
        long long s1 = gCore.leftSep ? k : n;
        long long s2 = gCore.leftSep ? n : m;
        // LNS score NEVER regresses on (s1, s2) for an extra state; prefer higher (s1, s2), then irred/coverage
        long long p1 = s1 * 100000LL + s2;
        long long s3 = (irred * 1000000LL) + (ust * 1000LL) + (usy * 10LL) - (step / 100000LL);
        bool betterLNS = (best.tier < 3) || (p1 > best.score1) || (p1 == best.score1 && s3 > best.score3);
        if (betterLNS) {
            best.tier = 3;
            best.score1 = p1;
            best.score2 = s2;
            best.score3 = s3;
            best.step = step;
            best.m = m; best.n = n; best.k = k;
            memcpy(best.tab, curTab, sizeof(curTab));
        }
        bool betterIrred = (irred == 1) && (bestIrred.tier < 3 || p1 > bestIrred.score1 || (p1 == bestIrred.score1 && s3 > bestIrred.score3));
        if (betterIrred) {
            bestIrred.tier = 3;
            bestIrred.score1 = p1;
            bestIrred.score2 = s2;
            bestIrred.score3 = s3;
            bestIrred.step = step;
            bestIrred.m = m; bestIrred.n = n; bestIrred.k = k;
            memcpy(bestIrred.tab, curTab, sizeof(curTab));
        }
        if ((betterLNS && irred == 1) || betterIrred) {
            std::string tmStr = fmtTab(curTab, gStartState);
            if (gCore.leftSep) {
                printf("HIT tier=3 irred=%d k=%d n=%d m=%d step=%d st=%d/%d sym=%d/%d | %s\n",
                       irred, k, n, m, step, ust, nstates, usy, nsyms, tmStr.c_str());
            } else {
                printf("HIT tier=3 irred=%d n=%d m=%d step=%d st=%d/%d sym=%d/%d | %s\n",
                       irred, n, m, step, ust, nstates, usy, nsyms, tmStr.c_str());
            }
            fflush(stdout);
        }
    } else if (best.tier < 3) {
        // Tier 2 shaping reward: reached B> X^n with 1^m left (partial dirty tape)
        long long p1 = (long long)n * 1000 + m - (leftClean ? 0 : 500) - (rightClean ? 0 : 500);
        if (best.tier < 2 || p1 > best.score1) {
            best.tier = 2;
            best.score1 = p1;
            best.score2 = m;
            best.score3 = -step;
            best.step = step;
            best.m = m; best.n = n; best.k = k;
            memcpy(best.tab, curTab, sizeof(curTab));
        }
    }
}

static bool loadSeedTM(const std::string &tnf, const CoreDef &core) {
    std::vector<std::string> rows;
    size_t p = 0;
    while (true) {
        size_t u = tnf.find('_', p);
        rows.push_back(tnf.substr(p, (u == std::string::npos ? tnf.size() : u) - p));
        if (u == std::string::npos) break;
        p = u + 1;
    }
    if ((int)rows.size() > nstates) return false;
    int ssym = (int)(rows[0].size() / 3);
    memcpy(seedTab, core.tab, sizeof(seedTab));
    for (int s = 0; s < (int)rows.size(); ++s) {
        for (int y = 0; y < std::min(ssym, nsyms); ++y) {
            if (core.tab[s][y].nst != UNASSIGNED) continue;
            const char *t = rows[s].c_str() + 3 * y;
            if (t[0] == '-') continue;
            int w = t[0] - '0';
            if (w < 0 || w >= nsyms) continue;
            int mv = (t[1] == 'L') ? -1 : 1;
            int8_t ns = (t[2] == 'Z') ? HALT_Z : (int8_t)parseStChar(t[2]);
            if (ns >= nstates) continue;
            seedTab[s][y] = {(int8_t)w, (int8_t)mv, ns};
        }
    }
    hasSeedTab = true;
    return true;
}

int main(int argc, char **argv) {
    std::string coreName = "fe2_9", coreFile = "bbcores_ultimate.txt", seedTM;
    for (int i = 1; i < argc; ++i) {
        std::string k = argv[i];
        auto nxt = [&](const char *d) { return (i + 1 < argc) ? argv[++i] : d; };
        if      (k == "--core") coreName = nxt("fe2_9");
        else if (k == "--cores-file") coreFile = nxt("bbcores_ultimate.txt");
        else if (k == "--states") nstates = atoi(nxt("24"));
        else if (k == "--symbols") nsyms = atoi(nxt("9"));
        else if (k == "--cap") { CAP = atoi(nxt("1200")); if (CAP > MID - 16) CAP = MID - 16; }
        else if (k == "--budget") BUDGET = (long long)strtod(nxt("2e8"), nullptr);
        else if (k == "--seed") gRng = strtoull(nxt("42"), nullptr, 10) | 1ULL;
        else if (k == "--startstate") gStartState = parseStChar(nxt("A")[0]);
        else if (k == "--seed-tm") seedTM = nxt("");
    }

    if (!parseCore(coreFile, coreName, gCore)) {
        fprintf(stderr, "Cannot load core '%s' from '%s'\n", coreName.c_str(), coreFile.c_str());
        return 1;
    }
    if (nstates < gCore.nfixed) nstates = gCore.nfixed;
    if (nsyms < gCore.nsym) nsyms = gCore.nsym;

    for (int s = 0; s < nstates; ++s)
        for (int y = 0; y < nsyms; ++y)
            if (gCore.tab[s][y].nst == UNASSIGNED)
                freeCells.push_back({s, y});

    if (!seedTM.empty()) loadSeedTM(seedTM, gCore);

    long long totalSteps = 0;
    long long ep = 0;
    int caps[4] = { 120, 300, 700, CAP };

    // Optional: evaluate seedTM first
    std::vector<std::pair<int, int>> usedFree;
    std::vector<std::pair<int, int>> assignedFree;
    int prevLo = MID, prevHi = MID;
    while (totalSteps < BUDGET) {
        ++ep;
        int curCap = caps[ep & 3];
        if (curCap > CAP) curCap = CAP;
        bool lns = false;
        if (ep == 1 && hasSeedTab) {
            memcpy(curTab, seedTab, sizeof(curTab));
            curCap = CAP;
        } else if ((best.tier >= 2 || (best.tier == 1 && (ep % 5 != 0)) || hasSeedTab) && (ep % 4 != 0) && !freeCells.empty()) {
            lns = true;
            const Tr (&src)[MAXST][MAXSYM] = (best.tier >= 2 || (best.tier == 1 && !hasSeedTab)) ? best.tab : seedTab;
            memcpy(curTab, src, sizeof(curTab));
            assignedFree.clear();
            for (auto &fc : freeCells) {
                if (curTab[fc.first][fc.second].nst != UNASSIGNED) assignedFree.push_back(fc);
            }
            if (!assignedFree.empty()) {
                int nun = 1 + (int)(rng() % std::min<size_t>(3, assignedFree.size()));
                for (int u = 0; u < nun; ++u) {
                    auto fc = assignedFree[rng() % assignedFree.size()];
                    curTab[fc.first][fc.second] = {0, 0, UNASSIGNED};
                }
            }
            curCap = CAP;
        } else {
            memcpy(curTab, gCore.tab, sizeof(curTab));
        }

        // Fast roll-out with inline tape clear over exact previous [prevLo..prevHi]
        if (prevHi >= prevLo) memset(tape + prevLo, 0, prevHi - prevLo + 1);
        int pos = MID, st = gStartState;
        int lo = MID, hi = MID;
        uint64_t stMask = 0;
        uint32_t symMask = 0;
        usedFree.clear();
        int cnt1 = 0, cntX = 0;

        for (int t = 1; t <= curCap; ++t) {
            if (pos < 4 || pos >= TAPE_SZ - 4) break;
            uint8_t c = tape[pos];
            stMask |= (1ULL << st);
            symMask |= (1u << c);
            Tr tr = curTab[st][c];
            if (tr.nst == UNASSIGNED) {
                tr = pickWeightedTr(st, c, gCore.targetSym);
                curTab[st][c] = tr;
                usedFree.push_back({st, c});
            }
            if (tr.nst == HALT_Z || tr.nst == HALT_UNDEF) break;
            if (tr.w == 1 && c != 1) ++cnt1;
            if (tr.w == gCore.targetSym && c != gCore.targetSym) ++cntX;
            tape[pos] = (uint8_t)tr.w;
            if (pos < lo) lo = pos;
            if (pos > hi) hi = pos;
            pos += tr.mv;
            if (pos < lo) lo = pos;
            if (pos > hi) hi = pos;
            st = tr.nst;
            ++totalSteps;

            if (st == gCore.headState && tape[pos] == gCore.targetSym) {
                checkTapeLandmark(pos, st, t, lo, hi, stMask, symMask, best);
            }
        }
        prevLo = lo; prevHi = hi;
        // Tier 1 shaping reward if still tier <= 1
        if (best.tier <= 1 && cntX > 0 && cnt1 > 0) {
            long long sc = (long long)__builtin_popcountll(stMask) * 100 + std::min(cntX, 20) * 10 + std::min(cnt1, 10);
            if (best.tier == 0 || sc > best.score1) {
                best.tier = 1;
                best.score1 = sc;
                memcpy(best.tab, curTab, sizeof(curTab));
            }
        }
    }

    const BestHit &outHit = (bestIrred.tier == 3) ? bestIrred : best;
    if (outHit.tier == 3) {
        std::string tmStr = fmtTab(outHit.tab, gStartState);
        if (gCore.leftSep) {
            printf("BEST tier=3 k=%d n=%d m=%d step=%d cfg=0^inf 1^%d 0 1^%d %c> %d^%d 0^inf\nTM=%s\n",
                   outHit.k, outHit.n, outHit.m, outHit.step, outHit.k, outHit.m,
                   stChar(gCore.headState), gCore.targetSym, outHit.n, tmStr.c_str());
        } else {
            printf("BEST tier=3 n=%d m=%d step=%d cfg=0^inf 1^%d %c> %d^%d 0^inf\nTM=%s\n",
                   outHit.n, outHit.m, outHit.step, outHit.m,
                   stChar(gCore.headState), gCore.targetSym, outHit.n, tmStr.c_str());
        }
    } else {
        printf("NONE best_tier=%d steps=%lld\n", best.tier, totalSteps);
    }
    return 0;
}
