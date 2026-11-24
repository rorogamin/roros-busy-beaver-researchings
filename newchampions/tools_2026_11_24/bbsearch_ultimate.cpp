// bbsearch.cpp -- maximum-configuration landmark search over every TM core
// listed in bbcores_new.txt.
//
// Generalises the original 6-symbol-only searcher in three ways:
//
//   1. the cores are not all 6-symbol: bbcores_new.txt has cores with 3, 4, 5,
//      6 and 7 symbols and with 3 .. 17 states.  Each core therefore carries
//      its own symbol count and its own number of fixed states.
//
//   2. the landmark is not always "0^inf 3^(2m+1) 2^k A> 1^n <right>" and
//      is read from bbcores_new.txt.
//
//   3. the importance order (which counter dominates which) is per core and
//      is read from bbcores_new.txt.
//
// Everything else (the DFS over free cells, the cycle hash table, the
// landmark matching, the ranking) is the same idea as the original searcher: a core
// row is 3 characters per symbol (write, move, next state), '---' is a FREE
// cell that the DFS fills in on demand, and the best configuration is the one
// that is largest in the core's importance order (lexicographic).
//
// The core table itself is read at run time from bbcores_new.txt (see
// --cores-file).  A core block in that file consists of four lines:
//
//   name <core-name>
//   cfg  <landmark description>
//   slot <counter slots in importance order>
//   core <transition rows, separated by '_'>
//
// The file is the only source of core definitions: every core the program
// knows is read from it.
//
// This is a SIMULATION search, not a proof.
//
// Build: g++ -O3 -march=native -std=c++11 -o bbsearch bbsearch.cpp
// Run  : ./bbsearch --core fw1_6 --states 3 --cap 50000 --budget 3e9
//        ./bbsearch --all --cap 200000 --budget 3e9 --log all.log
//        ./bbsearch --core dfw_4 --startstate B --cap 5000 --budget 3e9
//        ./bbsearch --cores
//
// --startstate X picks the state the machine starts in.  dfw_4 and tfw_5 halt
// within a few steps when started in state A (their A row leads straight into
// the halt); from another state they keep running, so the blank-tape search
// can explore them at all.
//
// NOTE on --budget: the landmark is often only reached deep in the DFS tree.
// A truncated budget can stop the search long before the landmark region is
// visited, which looks exactly like "the core never produces this shape".

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cstdarg>
#include <cctype>
#include <string>
#include <vector>
#include <map>
#include <algorithm>
#include <ctime>

// ---------------------------------------------------------------- constants
static const int MAXSYM = 10;      // symbols 0..MAXSYM-1 (single-digit encoding)
static const int MAXST  = 40;      // A..Y ('Z' is the halt marker, not a state)
static const int CELLS  = 1 << 16; // one blank-tape run, centred

// The core table is read from this file (see --cores-file).
static const char *DEFAULT_CORE_FILE = "bbcores_new.txt";

// The active alphabet size, set by --symbols (default: the core's own count).
// The core rows describe symbols 0..coreSym-1 only; with a larger alphabet
// the extra columns stay FREE and are filled by the DFS, so the search runs
// over N-symbol machines that contain the core.  With a smaller alphabet the
// extra core columns are dropped (their transitions can never fire).
static int gNSym = 6;

static const int8_t UNASSIGNED = -2;   // free slot: the DFS must branch here
static const int8_t HALT_UNDEF = -1;   // '---' : halt before write/move
static const int8_t HALT_Z     = -3;   // 'wRZ' : write, move, then halt


static inline char stChar(int s) { return (s < 25) ? (char)('A' + s) : (char)('a' + (s - 25)); }
static inline int parseStChar(char c) {
    if (c >= 'A' && c <= 'Y') return c - 'A';
    if (c >= 'a' && c <= 'o') return 25 + (c - 'a');
    return -1;
}
static int gBiasSym = -1;
static std::string gSeedTM;
static bool gHasSeedTab = false;

struct Tr  { int8_t w, mv, nst; };
static Tr gSeedTab[MAXST][MAXSYM];
struct Choice { int8_t w, mv, nst; };

// ---------------------------------------------------------------- core table
// The core table lives in bbcores_new.txt and is read at run time -- there is
// no built-in copy of it (see the "core file" section below).

// ---------------------------------------------------------------- landmark spec
// Counter slots.  K = length of the 2^k run left of the head, N = length of
// the 1^n run, M = (|3-run|-1)/2, P/Q/R/S = right-side run lengths,
// R5 = length of the 5-run on the left of the 3-run.
enum { SLOT_K = 0, SLOT_N = 1, SLOT_M = 2, SLOT_P = 3, SLOT_Q = 4,
       SLOT_R = 5, SLOT_R5 = 6, SLOT_S = 7, SLOT_T = 8, SLOT_NUM = 9 };

static const char *SLOT_NAME[SLOT_NUM] = { "k", "n", "m", "p", "q", "r", "r5", "s", "t" };

// A right-side segment: a maximal run of one symbol.
//   minCnt  : the run must have at least this many cells (a counter level must
//             be nonempty, otherwise the landmark is degenerate)
//   maxCnt  : -1 = unbounded
//   slot    : which counter slot the length feeds, -1 = not a counter
struct Seg { uint8_t sym; int minCnt; int maxCnt; int slot; };

// Left-side 5-run modes.
enum { L5_NONE = 0,   // no 5 may sit between the 3-run and the blank region
       L5_ONE  = 1,   // exactly one 5
       L5_MANY = 2 }; // 5^r, r >= 1

// Landmark kinds.
enum { KIND_BCFG  = 0,  // 0^inf [5^r] 3^(2m+1) 2^k <head> 1^n <right>
       KIND_THREE = 1,  // 0^inf <head> 3^n 0^inf        (the 3-run is a counter)
       KIND_ONES  = 2 }; // 0^inf 1^m <head> [right config] [0^inf] (the 1^m count goes into leftSlot, the 0^inf is checked only when termBlank is true).

struct CoreSpec {
    int      kind;
    int      left5;        // L5_*
    uint64_t headMask;     // allowed head states (bit s = state s)
    Seg      right[10];
    int      nright;
    bool     termBlank;    // require a blank cell right after the last segment
    int      slot[10];      // counter slots in importance order (largest first)
    int      nslot;
    int      leftSlot;     // KIND_ONES: slot of the 1^m count
};

// ---------------------------------------------------------------- core file
static std::string trimStr(const std::string &s);   // defined with --fix below

// The core table can be read from a file (bbcores_new.txt by default).  A core
// block consists of four lines:
//
//   name <core-name>
//   cfg  <landmark description>
//   slot <counter slots in importance order>
//   core <transition rows, separated by '_'>
//
// The file is the authority: it holds every core the program knows.
//
// The cfg line describes the landmark:
//
//   [5^1|5^r] BCFG(<states>) <segments>   KIND_BCFG, the head is in one of
//                                         <states> on the first 1 of the 1^n
//                                         run, the segments follow that run
//   <states>> <segments>                  KIND_THREE, the head sits on the
//                                         first cell of the first segment
//   1^<counter> <states>> <segments>      KIND_ONES, the head sits on the
//                                         first cell of the first segment and
//                                         <counter> ones are left of it
//
// A segment is  <sym>^<count>  (a run of exactly <count> cells),
// <sym>^<counter>  (a run whose length is the counter) or  BLANK  (the rest
// of the tape is blank).  The slot line lists the counters in importance
// order and may carry a minimum:  k n m   p>=1 k n m
//
// Without a trailing BLANK the last fixed segment is not pinned down to a
// single cell:  "1^n 2" only says that the cell behind the run holds a 2, so
// the run itself may be longer (see buildSpec()).
struct CoreEntry {
    std::string name;
    int  nfixed;                     // number of fixed states (A..)
    int  nsym;                       // symbols covered by the core rows
    std::vector<std::string> rows;   // rows[s], 3*nsym characters each
    CoreSpec spec;
};

// The core table is the core file; there is no built-in copy of it.
static std::vector<CoreEntry> gCores;

// A right-side segment as written in the cfg line.
struct CfgSeg {
    int         sym;      // the symbol of the run
    bool        counter;  // true: the length is a counter, false: a fixed length
    int         count;    // fixed length
    std::string name;     // the name of the counter
};

// The cfg line in parsed form.
struct CfgDesc {
    int         kind;
    int         left5;          // L5_*
    std::string left5Name;      // the counter of the 5-run (L5_MANY)
    uint64_t    headMask;
    std::vector<CfgSeg> segs;
    bool        termBlank;
    std::string leftSlotName;   // KIND_ONES: the counter of the 1^m run
};

// split a string at whitespace
static std::vector<std::string> splitWs(const std::string &s) {
    std::vector<std::string> out;
    size_t i = 0;
    while (i < s.size()) {
        while (i < s.size() && isspace((unsigned char)s[i])) ++i;
        size_t b = i;
        while (i < s.size() && !isspace((unsigned char)s[i])) ++i;
        if (i > b) out.push_back(s.substr(b, i - b));
    }
    return out;
}

// "A" or "AC" -> the mask of the allowed head states
static bool parseHeadStates(const std::string &s, uint64_t &mask, std::string &err) {
    mask = 0;
    if (s.empty()) { err = "no head state"; return false; }
    for (size_t i = 0; i < s.size(); ++i) {
        char c = s[i];
        if (c < 'A' || c > (char)('A' + MAXST - 1)) {
            err = std::string("bad head state '") + c + "'";
            return false;
        }
        mask |= 1ULL << (c - 'A');
    }
    return true;
}

// Parse one cfg line.
static bool parseCfg(const std::string &line, CfgDesc &cd, std::string &err) {
    std::vector<std::string> tok = splitWs(line);
    if (tok.empty()) { err = "empty cfg line"; return false; }

    cd.kind = KIND_BCFG;
    cd.left5 = L5_NONE;
    cd.headMask = 0;
    cd.termBlank = false;
    cd.left5Name.clear();
    cd.leftSlotName.clear();
    cd.segs.clear();

    size_t i = 0;
    // the optional 5-run left of the 3-run: "5^1" (exactly one) or "5^r"
    if (tok[i].size() > 2 && tok[i][0] == '5' && tok[i][1] == '^') {
        std::string cnt = tok[i].substr(2);
        if (isdigit((unsigned char)cnt[0])) {
            if (cnt != "1") { err = "the 5-run must be '5^1' or '5^r'"; return false; }
            cd.left5 = L5_ONE;
        } else {
            cd.left5 = L5_MANY;
            cd.left5Name = cnt;
        }
        ++i;
    }
    if (i >= tok.size()) { err = "the cfg line has no landmark"; return false; }

    std::string head = tok[i];
    std::vector<std::string> segTok;

    if (head.compare(0, 5, "BCFG(") == 0) {
        // KIND_BCFG:  BCFG(A) <segments>
        size_t close = head.find(')');
        if (close == std::string::npos) { err = "BCFG(...) without ')'"; return false; }
        if (!parseHeadStates(head.substr(5, close - 5), cd.headMask, err)) return false;
        cd.kind = KIND_BCFG;
        ++i;
        for (; i < tok.size(); ++i) segTok.push_back(tok[i]);
    } else {
        // KIND_THREE: <states>> <segments>      KIND_ONES: 1^<counter> <states>> ...
        std::string leftCounter;
        if (head.compare(0, 2, "1^") == 0) {
            leftCounter = head.substr(2);
            ++i;
            if (i >= tok.size()) { err = "the cfg line has no head state"; return false; }
            head = tok[i];
        }
        if (head.empty() || head[head.size() - 1] != '>') {
            err = "expected a head state like 'A>' or 'ACG>'";
            return false;
        }
        if (!parseHeadStates(head.substr(0, head.size() - 1), cd.headMask, err)) return false;
        if (leftCounter.empty()) {
            // the head sits on the counter run, so the rest of the tape is blank
            cd.kind = KIND_THREE;
            cd.termBlank = true;
        } else {
            cd.kind = KIND_ONES;
            cd.leftSlotName = leftCounter;
        }
        ++i;
        for (; i < tok.size(); ++i) segTok.push_back(tok[i]);
    }

    for (size_t j = 0; j < segTok.size(); ++j) {
        const std::string &t = segTok[j];
        if (t == "BLANK") { cd.termBlank = true; continue; }
        CfgSeg sg;
        sg.sym = -1;
        sg.counter = false;
        sg.count = 1;
        sg.name.clear();
        size_t caret = t.find('^');
        std::string symPart = (caret == std::string::npos) ? t : t.substr(0, caret);
        if (symPart.size() != 1 || !isdigit((unsigned char)symPart[0])) {
            err = "bad segment '" + t + "'";
            return false;
        }
        sg.sym = symPart[0] - '0';
        if (caret != std::string::npos) {
            std::string cnt = t.substr(caret + 1);
            if (cnt.empty()) { err = "bad segment '" + t + "'"; return false; }
            if (isdigit((unsigned char)cnt[0])) {
                sg.count = atoi(cnt.c_str());
                if (sg.count < 1) { err = "bad segment '" + t + "'"; return false; }
            } else {
                sg.counter = true;
                sg.name = cnt;
            }
        }
        if (cd.segs.size() >= 10) { err = "too many segments in the cfg line"; return false; }
        cd.segs.push_back(sg);
    }
    return true;
}

// Parse one slot line: the counters in importance order, each of them
// optionally followed by ">=<minimum>".
static bool parseSlotLine(const std::string &line,
                           std::vector<std::pair<std::string, int> > &out,
                           std::string &err) {
    std::vector<std::string> tok = splitWs(line);
    out.clear();
    for (size_t i = 0; i < tok.size(); ++i) {
        std::string name = tok[i];
        int mn = 1;
        size_t ge = name.find(">=");
        if (ge != std::string::npos) {
            std::string v = name.substr(ge + 2);
            name = name.substr(0, ge);
            if (v.empty() || !isdigit((unsigned char)v[0])) {
                err = "bad slot constraint '" + tok[i] + "'";
                return false;
            }
            mn = atoi(v.c_str());
        }
        if (name.empty()) { err = "bad slot '" + tok[i] + "'"; return false; }
        out.push_back(std::make_pair(name, mn));
    }
    if (out.empty()) { err = "empty slot line"; return false; }
    return true;
}

// The slot a counter name refers to.  "r" is ambiguous: it is the length of
// the right-hand 1^r run, but in the slot line of a core with a 5^r run it is
// the length of that 5-run (r5).  The cfg line decides which one is meant.
static int slotIndexFor(const std::string &name, const CfgDesc &cd) {
    if (name == "r" && cd.left5 == L5_MANY && cd.left5Name == "r") return SLOT_R5;
    for (int s = 0; s < SLOT_NUM; ++s)
        if (name == SLOT_NAME[s]) return s;
    return -1;
}

// Turn the parsed cfg and slot lines into a core spec.
static bool buildSpec(const CfgDesc &cd,
                      const std::vector<std::pair<std::string, int> > &slots,
                      CoreSpec &sp, std::string &err) {
    sp = CoreSpec();
    sp.kind = cd.kind;
    sp.left5 = cd.left5;
    sp.headMask = cd.headMask;
    sp.termBlank = cd.termBlank;

    std::map<std::string, int> byName;
    for (size_t i = 0; i < slots.size(); ++i) {
        int idx = slotIndexFor(slots[i].first, cd);
        if (idx < 0) { err = "unknown counter '" + slots[i].first + "'"; return false; }
        if (sp.nslot < SLOT_NUM) sp.slot[sp.nslot++] = idx;
        byName[slots[i].first] = idx;
    }

    for (size_t i = 0; i < cd.segs.size(); ++i) {
        const CfgSeg &sg = cd.segs[i];
        Seg &out = sp.right[sp.nright];
        out.sym = (uint8_t)sg.sym;
        if (sg.counter) {
            std::map<std::string, int>::const_iterator it = byName.find(sg.name);
            int idx = (it != byName.end()) ? it->second : slotIndexFor(sg.name, cd);
            if (idx < 0) { err = "unknown counter '" + sg.name + "'"; return false; }
            out.slot = idx;
            out.minCnt = 1;
            out.maxCnt = -1;
            for (size_t j = 0; j < slots.size(); ++j)
                if (slots[j].first == sg.name)
                    out.minCnt = slots[j].second;
        } else {
            out.slot = -1;
            out.minCnt = sg.count;
            out.maxCnt = sg.count;
        }
        ++sp.nright;
    }

    // A trailing fixed run without the BLANK marker is not pinned down to a
    // single cell: the notation "1^n 2" only says that the cell behind the
    // run holds a 2, so the run may be longer.  BLANK (and KIND_THREE, whose
    // tail is blank by definition) turns this off.
    if (!cd.termBlank && sp.nright > 0) {
        Seg &last = sp.right[sp.nright - 1];
        if (last.slot < 0 && last.sym != 0) last.maxCnt = -1;
    }

    if (cd.kind == KIND_ONES) {
        std::map<std::string, int>::const_iterator it = byName.find(cd.leftSlotName);
        int idx = (it != byName.end()) ? it->second : slotIndexFor(cd.leftSlotName, cd);
        if (idx < 0) { err = "unknown counter '" + cd.leftSlotName + "'"; return false; }
        sp.leftSlot = idx;
    }
    return true;
}

// Parse the core line: the transition rows, separated by '_'.
static bool parseCoreRows(const std::string &line, CoreEntry &e, std::string &err) {
    std::vector<std::string> rows;
    size_t start = 0;
    for (;;) {
        size_t u = line.find('_', start);
        rows.push_back(line.substr(start,
            (u == std::string::npos ? line.size() : u) - start));
        if (u == std::string::npos) break;
        start = u + 1;
    }
    if (rows.empty()) { err = "empty core line"; return false; }
    if (rows[0].size() % 3 != 0) {
        err = "the core rows must be 3 characters per symbol";
        return false;
    }
    int nsym = (int)(rows[0].size() / 3);
    if (nsym < 1) { err = "the core needs at least one symbol"; return false; }
    if (nsym > MAXSYM) { err = "too many symbols"; return false; }
    if ((int)rows.size() > MAXST) { err = "too many states"; return false; }
    for (size_t i = 0; i < rows.size(); ++i) {
        if (rows[i].size() != rows[0].size()) {
            err = "row " + std::to_string((int)i) + " has a different length";
            return false;
        }
    }
    e.nsym = nsym;
    e.nfixed = (int)rows.size();
    e.rows = rows;
    return true;
}

// Build one core from its four lines.
static bool makeCoreEntry(const std::string &name, const std::string &cfgLine,
                          const std::string &slotLine, const std::string &coreLine,
                          CoreEntry &e, std::string &err) {
    if (name.empty())     { err = "empty name"; return false; }
    if (cfgLine.empty())  { err = "missing cfg line"; return false; }
    if (slotLine.empty()) { err = "missing slot line"; return false; }
    if (coreLine.empty()) { err = "missing core line"; return false; }

    CfgDesc cd;
    if (!parseCfg(cfgLine, cd, err)) return false;
    std::vector<std::pair<std::string, int> > slots;
    if (!parseSlotLine(slotLine, slots, err)) return false;

    e.name = name;
    if (!buildSpec(cd, slots, e.spec, err)) return false;
    if (!parseCoreRows(coreLine, e, err)) return false;
    return true;
}

// Read the core file.  Blocks in the old format (a bare core row without a
// name) are ignored -- such a core has no definition at all.
static bool loadCoreFile(const std::string &path, std::vector<CoreEntry> &out,
                         std::string &err) {
    FILE *f = fopen(path.c_str(), "r");
    if (!f) { err = "cannot open '" + path + "'"; return false; }

    out.clear();
    std::string name, cfg, slot, core;
    int lineNo = 0, nameLine = 0;
    bool haveBlock = false;

    struct Flush {
        static void run(const std::string &path, int lineNo, const std::string &name,
                        const std::string &cfg, const std::string &slot,
                        const std::string &core, std::vector<CoreEntry> &out) {
            CoreEntry e;
            std::string e2;
            if (!makeCoreEntry(name, cfg, slot, core, e, e2)) {
                fprintf(stderr, "%s:%d: core '%s' ignored: %s\n",
                        path.c_str(), lineNo, name.c_str(), e2.c_str());
                return;
            }
            out.push_back(e);
        }
    };

    char buf[4096];
    while (fgets(buf, sizeof buf, f)) {
        ++lineNo;
        std::string line = trimStr(buf);
        if (line.empty()) continue;
        if (line[0] == '#' || line[0] == '*') continue;
        if (line.compare(0, 5, "name ") == 0) {
            if (haveBlock)
                Flush::run(path, nameLine, name, cfg, slot, core, out);
            name = trimStr(line.substr(5));
            cfg.clear(); slot.clear(); core.clear();
            haveBlock = true;
            nameLine = lineNo;
        } else if (line.compare(0, 4, "cfg ") == 0) {
            cfg = trimStr(line.substr(4));
        } else if (line.compare(0, 5, "slot ") == 0) {
            slot = trimStr(line.substr(5));
        } else if (line.compare(0, 5, "core ") == 0) {
            core = trimStr(line.substr(5));
        }
    }
    if (haveBlock)
        Flush::run(path, nameLine, name, cfg, slot, core, out);
    fclose(f);
    return true;
}

// Read the core file: it is the only source of core definitions.  A core
// whose name appears twice keeps the last definition.
static bool loadCoresFromFile(const std::string &path) {
    std::vector<CoreEntry> parsed;
    std::string err;
    if (!loadCoreFile(path, parsed, err)) {
        fprintf(stderr, "error: %s\n", err.c_str());
        return false;
    }
    for (size_t i = 0; i < parsed.size(); ++i) {
        bool replaced = false;
        for (size_t j = 0; j < gCores.size(); ++j) {
            if (gCores[j].name == parsed[i].name) {
                gCores[j] = parsed[i];
                replaced = true;
                break;
            }
        }
        if (!replaced) gCores.push_back(parsed[i]);
    }
    return true;
}

// The active spec: a copy of the chosen core's spec that the command line
// may override.
static CoreSpec gSpec;

// LOOSE mode: the right side of the landmark is not checked, only the left
// half (0^inf [5^r] 3^(2m+1) 2^k <head> 1^n).  This is what --start cfg
// needs: a core whose input configuration is given to the machine (the
// "B(k,n,m) ..." family) transforms it into a bigger configuration whose right
// side is different from the input's, and that transformed configuration is
// the interesting one.
static bool gLoose = false;

// counter values of the configuration the machine is started at (--start cfg)
static int gCfgVal[SLOT_NUM] = { 16, 3, 0, 1, 1, 1, 1, 1, 1 };

// which counter slots are known in the current mode (the others are unknown
// and therefore skipped when ranking two configurations)
static bool gSlotKnown[SLOT_NUM] = { true, true, true, true, true, true, true, true, true };

// ---------------------------------------------------------------- globals
static Tr      trans_[MAXST][MAXSYM];
static int     nstates  = 4;
static int     gCore    = 0;
static long long CAP    = 50000;
static long long BUDGET = 0;          // 0 = unlimited (in TM steps)
static int     FILLMAX  = 0;          // max #free cells that may be assigned
static int     gFilled  = 0;          // free cells assigned on the current path
static long long gSteps = 0;
static bool    gAbort   = false;
static bool    gCensus  = false;      // report observed shapes instead of matching
static bool    gCensusL = false;      // census restricted to the landmark's left half

// --startstate X : the state the machine starts in (A..Y).
// -1 = the default: state A on the blank tape, or the core's lowest head
// state when the machine is started on the documented input configuration.
// Some cores (dfw_4, tfw_5) halt within a few steps when they are started in
// state A; starting them in another state avoids that.
static int     gStartState = -1;

static uint8_t  tape_[CELLS];
static uint64_t zob_[MAXSYM * CELLS];
static uint64_t zpos_[CELLS];
static uint64_t zst_[MAXST];

static std::vector<int>     tpos_;
static std::vector<uint8_t> tval_;

static const int HB = 22;                 // 4M slots
static const int HS = 1 << HB;
static uint64_t hkey_[HS];
static uint8_t  hocc_[HS];
static std::vector<int> htrail_;

static std::vector<Choice> choices_;

// best landmark
struct CfgBest {
    int c[SLOT_NUM] = { -1, -1, -1, -1, -1, -1, -1, -1, -1 };
    int st = 0;                                    // landmark head state
    long long step = -1;
    int used = 0;
    Tr tab[MAXST][MAXSYM];
    std::string shape;      // right-hand shape of the configuration
};
static CfgBest bestCfg;
static CfgBest bestIrredCfg;

static long long gNodes = 0;
static time_t gLastPrint = 0;

static FILE *gLog = nullptr;       // optional log file (--log), NULL = stdout only

// census: observed right-hand shapes -> how often
static std::map<std::string, long long> gCensusMap;
static long long gCensusTotal = 0;

// print to stdout and, when --log is active, to the log file as well
static void emit(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
    if (gLog) {
        va_start(ap, fmt);
        vfprintf(gLog, fmt, ap);
        va_end(ap);
        fflush(gLog);
    }
}

// ---------------------------------------------------------------- helpers
static inline uint64_t splitmix64(uint64_t &x) {
    x += 0x9E3779B97F4A7C15ull;
    uint64_t z = x;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}

static void initZobrist() {
    uint64_t s = 0x123456789abcdefull;
    for (int i = 0; i < MAXSYM * CELLS; ++i) zob_[i] = splitmix64(s);
    for (int i = 0; i < CELLS; ++i)          zpos_[i] = splitmix64(s);
    for (int i = 0; i < MAXST; ++i)          zst_[i]  = splitmix64(s);
}

static inline void twrite(int p, uint8_t v) {
    tpos_.push_back(p); tval_.push_back(tape_[p]); tape_[p] = v;
}
static inline void tundo(size_t m) {
    while (tpos_.size() > m) {
        tape_[tpos_.back()] = tval_.back();
        tpos_.pop_back(); tval_.pop_back();
    }
}
static inline bool htTry(uint64_t k) {
    int i = (int)(k & (uint64_t)(HS - 1));
    int probes = 0;
    while (hocc_[i]) {
        if (hkey_[i] == k) return false;          // seen before -> cycle
        i = (i + 1) & (HS - 1);
        if (++probes > 4096) return true;         // table saturated: skip (never hang)
    }
    hocc_[i] = 1; hkey_[i] = k; htrail_.push_back(i);
    return true;
}
static inline void htUndo(size_t m) {
    while (htrail_.size() > m) { hocc_[htrail_.back()] = 0; htrail_.pop_back(); }
}

static inline bool stateUsed(int s) {
    for (int y = 0; y < gNSym; ++y) if (trans_[s][y].nst != UNASSIGNED) return true;
    return false;
}
static inline bool allowNst(int s) {           // canonical state-introduction order
    if (s < 3) return true;
    for (int j = 3; j < s; ++j) if (!stateUsed(j)) return false;
    return true;
}

static int countUsedStates() {
    int n = 0;
    for (int s = 0; s < nstates; ++s) if (stateUsed(s)) ++n;
    return n;
}

// blk = 3*nsym transitions, 3 chars each.  '---' = free cell (UNASSIGNED).
// With gNSym > the core's symbol count the extra columns stay UNASSIGNED
// (free); with gNSym < it the extra columns are dropped, since the machine can
// never see those symbols.
static void setRow(int s, const char *blk, int nsym) {
    for (int y = 0; y < nsym; ++y) {
        if (y >= gNSym) break;
        const char *t = blk + 3 * y;
        if (t[0] == '-') { trans_[s][y] = {0, 0, UNASSIGNED}; continue; }
        int w = t[0] - '0';
        int mv = (t[1] == 'L') ? -1 : 1;
        int8_t ns;
        if (t[2] == 'Z') ns = HALT_Z;
        else ns = (int8_t)(t[2] - 'A');
        trans_[s][y] = {(int8_t)w, (int8_t)mv, ns};
    }
}

// Install the fixed part of the chosen core.  Free cells stay UNASSIGNED.
static void setupCore() {
    for (int s = 0; s < MAXST; ++s)
        for (int y = 0; y < MAXSYM; ++y) trans_[s][y] = {0, 0, UNASSIGNED};
    const CoreEntry &cd = gCores[gCore];
    for (size_t s = 0; s < cd.rows.size(); ++s)
        setRow((int)s, cd.rows[s].c_str(), cd.nsym);
}

// The landmark spec names symbols explicitly (the 5-run, the right-side
// segments).  They must exist in the chosen alphabet, otherwise the landmark
// can never be matched and the run is pointless.
static bool checkSpecSymbols(std::string &err) {
    if (gSpec.kind == KIND_BCFG) {
        if (gNSym < 4) {
            err = "the landmark needs symbols 1, 2 and 3 but --symbols "
                + std::to_string(gNSym) + " has only symbols 0.."
                + std::to_string(gNSym - 1);
            return false;
        }
        if (gSpec.left5 != L5_NONE && gNSym <= 5) {
            err = "the landmark needs symbol 5 (the 5-run left of the 3-run) but --symbols "
                + std::to_string(gNSym) + " has only symbols 0.." + std::to_string(gNSym - 1);
            return false;
        }
    }
    for (int i = 0; i < gSpec.nright; ++i) {
        int sym = gSpec.right[i].sym;
        if (sym >= gNSym) {
            err = "the landmark's right side needs symbol " + std::to_string(sym) +
                  " but --symbols " + std::to_string(gNSym) + " has only symbols 0.." +
                  std::to_string(gNSym - 1);
            return false;
        }
    }
    if (gSpec.kind == KIND_THREE && gNSym < 4) {
        err = "the landmark needs symbol 3 but --symbols " + std::to_string(gNSym) +
              " has only symbols 0.." + std::to_string(gNSym - 1);
        return false;
    }
    if (gSpec.kind == KIND_ONES && gNSym < 2) {
        err = "the landmark needs symbol 1 (the run of ones left of the head) but --symbols " +
              std::to_string(gNSym) + " has only symbols 0.." + std::to_string(gNSym - 1);
        return false;
    }
    return true;
}

// A core transition may only write a symbol that exists in the alphabet.
// With --symbols below the core's count this can fail; report which cell is
// at fault.
static bool checkCoreWrites(std::string &err) {
    const CoreEntry &cd = gCores[gCore];
    for (size_t s = 0; s < cd.rows.size(); ++s) {
        const std::string &row = cd.rows[s];
        for (int y = 0; y < cd.nsym && y < gNSym; ++y) {
            const char *t = row.c_str() + 3 * y;
            if (t[0] == '-') continue;
            int w = t[0] - '0';
            if (w >= gNSym) {
                char b[64];
                snprintf(b, sizeof b, "%c%d writes symbol %d", 'A' + s, y, w);
                err = std::string(b) + " but --symbols " + std::to_string(gNSym) +
                      " has only symbols 0.." + std::to_string(gNSym - 1);
                return false;
            }
        }
    }
    return true;
}

// ---------------------------------------------------------------- --fix
// One item looks like  A0=4LC  (cell = write/move/next).  Several items may be
// separated by commas.  A fixed cell is removed from the DFS: it is never
// branched on.  Fixing a cell the core already defines is allowed only when
// the value is identical.
static std::string trimStr(const std::string &s) {
    size_t b = 0, e = s.size();
    while (b < e && isspace((unsigned char)s[b])) ++b;
    while (e > b && isspace((unsigned char)s[e - 1])) --e;
    return s.substr(b, e - b);
}

static bool applyFixSpec(const std::string &spec, std::string &err) {
    size_t start = 0;
    while (start <= spec.size()) {
        size_t comma = spec.find(',', start);
        std::string item = trimStr(spec.substr(start,
            (comma == std::string::npos ? spec.size() : comma) - start));
        if (!item.empty()) {
            size_t eq = item.find('=');
            if (eq == std::string::npos) {
                err = "expected CELL=WRITE-MOVE-NEXT, got '" + item + "'";
                return false;
            }
            std::string lhs = trimStr(item.substr(0, eq));
            std::string rhs = trimStr(item.substr(eq + 1));
            if (lhs.size() != 2 || rhs.size() != 3) { err = "bad fix '" + item + "'"; return false; }
            char sl = lhs[0], sd = lhs[1];
            if (sl < 'A' || sl > (char)('A' + MAXST - 1) || sd < '0' || sd > (char)('0' + gNSym - 1)) {
                err = "bad cell in '" + item + "'"; return false;
            }
            int st = sl - 'A', sy = sd - '0';
            if (st >= nstates) {
                err = "cell '" + item + "' uses a state outside --states";
                return false;
            }
            if (rhs == "---") {                       // pin the cell to halt
                Tr old = trans_[st][sy];
                if (old.nst != UNASSIGNED && old.nst != HALT_UNDEF) {
                    err = "fix '" + item + "' conflicts with the fixed core";
                    return false;
                }
                trans_[st][sy] = {0, 0, HALT_UNDEF};
            } else {
                char wch = rhs[0], mch = rhs[1], nch = rhs[2];
                if (wch < '0' || wch > (char)('0' + gNSym - 1)) { err = "bad write symbol in '" + item + "'"; return false; }
                if (mch != 'L' && mch != 'R') { err = "bad move in '" + item + "'"; return false; }
                int w = wch - '0', mv = (mch == 'L') ? -1 : 1;
                int8_t ns;
                if (nch == 'Z') ns = HALT_Z;
                else {
                    if (nch < 'A' || nch > (char)('A' + MAXST - 1)) {
                        err = "bad next state in '" + item + "'"; return false;
                    }
                    ns = (int8_t)(nch - 'A');
                }
                if (ns != HALT_Z && ns >= nstates) {
                    err = "next state in '" + item + "' is outside --states";
                    return false;
                }
                Tr old = trans_[st][sy];
                if (old.nst != UNASSIGNED &&
                    !(old.w == (int8_t)w && old.mv == (int8_t)mv && old.nst == ns)) {
                    err = "fix '" + item + "' conflicts with the fixed core";
                    return false;
                }
                trans_[st][sy] = {(int8_t)w, (int8_t)mv, ns};
            }
        }
        if (comma == std::string::npos) break;
        start = comma + 1;
    }
    return true;
}

static void buildChoices() {
    choices_.clear();
    for (int w = 0; w < gNSym; ++w)
        for (int mv = -1; mv <= 1; mv += 2) {
            for (int s = 0; s < nstates; ++s)
                choices_.push_back({(int8_t)w, (int8_t)mv, (int8_t)s});
            choices_.push_back({(int8_t)w, (int8_t)mv, HALT_Z});
        }
    choices_.push_back({0, 0, HALT_UNDEF});
}

static void printTabF(FILE *f, const Tr tab[MAXST][MAXSYM], int used) {
    for (int s = 0; s < nstates; ++s) {
        if (s >= used) fprintf(f, "[unused] ");
        for (int y = 0; y < gNSym; ++y) {
            Tr t = tab[s][y];
            if (t.nst == UNASSIGNED || t.nst == HALT_UNDEF) fprintf(f, "---");
            else if (t.nst == HALT_Z) fprintf(f, "%d%cZ", t.w, t.mv < 0 ? 'L' : 'R');
            else fprintf(f, "%d%c%c", t.w, t.mv < 0 ? 'L' : 'R', stChar(t.nst));
        }
        if (s + 1 < nstates) fprintf(f, "_");
    }
    fprintf(f, "\n");
}

static void copyTab(Tr dst[MAXST][MAXSYM], const Tr src[MAXST][MAXSYM]) {
    for (int s = 0; s < MAXST; ++s)
        for (int y = 0; y < MAXSYM; ++y) dst[s][y] = src[s][y];
}

// ---------------------------------------------------------------- landmark
// The head state(s) the landmark allows, e.g. "A" or "A|E".
static std::string fmtHead() {
    std::string out;
    for (int s = 0; s < MAXST; ++s) {
        if (!(gSpec.headMask & (1ULL << s))) continue;
        if (!out.empty()) out += "|";
        out += (char)('A' + s);
    }
    return out;
}

// Describe the right-hand structure of the landmark, e.g. "4 5^3 0".
static std::string fmtRight(const int *c) {
    char buf[128];
    const CoreSpec &sp = gSpec;
    std::string out;
    for (int i = 0; i < sp.nright; ++i) {
        const Seg &sg = sp.right[i];
        if (sg.slot < 0) { snprintf(buf, sizeof buf, "%d", sg.sym); }
        else              { snprintf(buf, sizeof buf, "%d^%d", sg.sym, c[sg.slot]); }
        if (!out.empty()) out += " ";
        out += buf;
    }
    if (sp.termBlank) { if (!out.empty()) out += " "; out += "0^inf"; }
    return out;
}

// The whole input configuration, e.g.
//   0^inf 3^(2m+1) 2^k A> 1^n 4 5^p 0
// In loose mode the right side is free-form and passed in as `shape`.
static std::string fmtLeft(const int *c, const std::string &shape = std::string()) {
    char buf[160];
    const CoreSpec &sp = gSpec;
    if (sp.kind == KIND_THREE) {
        // the counter is the run under the head; the rest of the tape is blank
        snprintf(buf, sizeof buf, "0^inf %s>", fmtHead().c_str());
        std::string out = buf;
        out += " ";
        out += fmtRight(c);
        return out;
    }
    if (sp.kind == KIND_ONES) {
        // the head scans the first cell of the right config; the ones on its
        // left are the counter
        snprintf(buf, sizeof buf, "1^%d %s>", c[sp.leftSlot], fmtHead().c_str());
        std::string out = buf;
        out += " ";
        out += shape.empty() ? fmtRight(c) : shape;
        return out;
    }
    std::string out;
    if (sp.left5 == L5_MANY)      snprintf(buf, sizeof buf, "0^inf 5^%d ", c[SLOT_R5]);
    else if (sp.left5 == L5_ONE)  snprintf(buf, sizeof buf, "0^inf 5 ");
    else                          snprintf(buf, sizeof buf, "0^inf ");
    out += buf;
    snprintf(buf, sizeof buf, "3^(%d) 2^%d %s> 1^%d %s",
             2 * c[SLOT_M] + 1, c[SLOT_K], fmtHead().c_str(), c[SLOT_N],
             shape.empty() ? fmtRight(c).c_str() : shape.c_str());
    out += buf;
    return out;
}

// The same pattern with symbolic counter names, for the header line.
static std::string fmtTemplate() {
    const CoreSpec &sp = gSpec;
    std::string out;
    if (sp.kind == KIND_THREE) {
        // 0^inf <head> 3^n 0^inf: the counter is the run under the head
        out = "0^inf ";
        out += fmtHead();
        out += ">";
        for (int i = 0; i < sp.nright; ++i) {
            const Seg &sg = sp.right[i];
            out += " ";
            if (sg.slot < 0) { char b[8]; snprintf(b, sizeof b, "%d", sg.sym); out += b; }
            else { char b[16]; snprintf(b, sizeof b, "%d^%s", sg.sym, SLOT_NAME[sg.slot]); out += b; }
        }
        if (sp.termBlank) out += " 0^inf";
        return out;
    }
    if (sp.kind == KIND_ONES) {
        // 0^inf 1^m <head> [right config] 0^inf (the 1^m count lives in leftSlot)
        out = "0^inf 1^";
        out += SLOT_NAME[sp.leftSlot];
        out += " ";
        out += fmtHead();
        out += ">";
        for (int i = 0; i < sp.nright; ++i) {
            const Seg &sg = sp.right[i];
            out += " ";
            if (sg.slot < 0) { char b[8]; snprintf(b, sizeof b, "%d", sg.sym); out += b; }
            else { char b[16]; snprintf(b, sizeof b, "%d^%s", sg.sym, SLOT_NAME[sg.slot]); out += b; }
        }
        if (sp.termBlank) out += " 0^inf";
        return out;
    }
    if (sp.left5 == L5_MANY)      out += "0^inf 5^r ";
    else if (sp.left5 == L5_ONE)  out += "0^inf 5 ";
    else                          out += "0^inf ";
    out += "3^(2m+1) 2^k ";
    out += fmtHead();
    out += "> 1^n";
    for (int i = 0; i < sp.nright; ++i) {
        const Seg &sg = sp.right[i];
        out += " ";
        if (sg.slot < 0) { char b[8]; snprintf(b, sizeof b, "%d", sg.sym); out += b; }
        else { char b[16]; snprintf(b, sizeof b, "%d^%s", sg.sym, SLOT_NAME[sg.slot]); out += b; }
    }
    if (sp.termBlank) out += " 0^inf";
    return out;
}

// ---------------------------------------------------------------- census
// Record the run-length shape of the cells right of the 1^n run, up to the
// first blank.  Only the first few segments are kept, otherwise the census
// output is unreadable.  Used by --census to check the table above against
// reality.
static std::string shapeRight(int pos, int hi) {
    char buf[64];
    std::string out;
    int t = pos, seg = 0;
    while (t < hi && tape_[t] != 0) {
        int sym = tape_[t], cnt = 0;
        while (t < hi && tape_[t] == sym) { ++cnt; ++t; }
        if (seg >= 4) { out += "..."; break; }
        snprintf(buf, sizeof buf, "%d", sym);
        out += buf;
        if (cnt > 1) { snprintf(buf, sizeof buf, "^%d", cnt); out += buf; }
        out += " ";
        ++seg;
    }
    return out;
}

// ---------------------------------------------------------------- noteCfg
// Rank the candidate configuration against the best one so far.  The first
// differing slot of the importance order decides.
static void considerCfg(const int *c, int st, long long step, const std::string &shape) {
    int curUsed = countUsedStates();
    uint32_t symM = 1u;
    for (int s = 0; s < nstates; ++s)
        for (int y = 0; y < gNSym; ++y)
            if (trans_[s][y].nst != UNASSIGNED && trans_[s][y].w >= 0 && trans_[s][y].w < gNSym)
                symM |= (1u << trans_[s][y].w);
    int curSyms = __builtin_popcount(symM);
    int curIrredScore = curUsed * 16 + curSyms;

    auto isBetter = [&](const CfgBest &ref, bool useIrredTie) {
        for (int si = 0; si < gSpec.nslot; ++si) {
            int slot = gSpec.slot[si];
            if (!gSlotKnown[slot]) continue;
            if (c[slot] != ref.c[slot]) return c[slot] > ref.c[slot];
        }
        if (useIrredTie) {
            int refSyms = 0;
            uint32_t rsm = 1u;
            for (int s = 0; s < nstates; ++s)
                for (int y = 0; y < gNSym; ++y)
                    if (ref.tab[s][y].nst != UNASSIGNED && ref.tab[s][y].w >= 0 && ref.tab[s][y].w < gNSym)
                        rsm |= (1u << ref.tab[s][y].w);
            refSyms = __builtin_popcount(rsm);
            return curIrredScore > (ref.used * 16 + refSyms);
        }
        return false;
    };

    bool better = isBetter(bestCfg, true);
    bool betterIrred = (curUsed == nstates && curSyms == gNSym) && isBetter(bestIrredCfg, false);
    if (!better && !betterIrred) return;

    if (better) {
        for (int i2 = 0; i2 < SLOT_NUM; ++i2) bestCfg.c[i2] = c[i2];
        bestCfg.st = st;
        bestCfg.step = step;
        bestCfg.used = curUsed;
        bestCfg.shape = shape;
        copyTab(bestCfg.tab, trans_);
        emit("\nNew Best Config Found:  %s\n", fmtLeft(c, shape).c_str());
        emit("          ");
        printTabF(stdout, trans_, bestCfg.used);
        if (gLog) printTabF(gLog, trans_, bestCfg.used);
        fflush(stdout);
    }
    if (betterIrred) {
        for (int i2 = 0; i2 < SLOT_NUM; ++i2) bestIrredCfg.c[i2] = c[i2];
        bestIrredCfg.st = st;
        bestIrredCfg.step = step;
        bestIrredCfg.used = curUsed;
        bestIrredCfg.shape = shape;
        copyTab(bestIrredCfg.tab, trans_);
        if (!better) {
            emit("\nNew Best Irred Config Found:  %s\n", fmtLeft(c, shape).c_str());
            emit("          ");
            printTabF(stdout, trans_, curUsed);
            if (gLog) printTabF(gLog, trans_, curUsed);
            fflush(stdout);
        }
    }
}

// Landmark of the KIND_THREE kind:  0^inf <head> 3^n 0^inf
// The head sits on the FIRST cell of the 3^n run; every other cell of the
// tape is blank.  The run under the head is the counter itself, so there is
// no left half to relax in loose mode: the whole shape is checked.
static void noteCfgThree(int st, int pos, int lo, int hi, long long step) {
    const CoreSpec &sp = gSpec;
    if (sp.nright < 1) return;
    if (tape_[pos] != sp.right[0].sym) return;      // the head is on the run

    int i = pos - 1;
    while (i >= lo && tape_[i] == 0) --i;           // everything left is blank
    if (i >= lo) return;

    int c[SLOT_NUM];
    for (int k = 0; k < SLOT_NUM; ++k) c[k] = 0;

    int t = pos;
    for (int si = 0; si < sp.nright; ++si) {
        const Seg &sg = sp.right[si];
        int cnt = 0;
        while (t < hi && tape_[t] == sg.sym) { ++cnt; ++t; }
        if (cnt < sg.minCnt) return;
        if (sg.maxCnt >= 0 && cnt > sg.maxCnt) return;
        if (sg.slot >= 0) c[sg.slot] = cnt;
    }
    if (sp.termBlank) {
        while (t < hi && tape_[t] == 0) ++t;        // everything right is blank
        if (t < hi) return;
    }

    considerCfg(c, st, step, fmtRight(c));
}

// Landmark of the KIND_ONES kind:  0^inf 1^m <head> <right[0]> <right[1]> ...
// The head sits on the FIRST cell of the right[0] run (which may be a counter
// run of its own, e.g. the 1^n of fw1_3 or the 2^n of fe0_5); m ones are
// directly to its left and nothing else, the remaining segments of the spec
// follow to the right.  termBlank demands that the rest of the tape is blank.
static void noteCfgOnes(int st, int pos, int lo, int hi, long long step) {
    const CoreSpec &sp = gSpec;
    if (sp.nright < 1) return;
    if (tape_[pos] != sp.right[0].sym) return;      // the head is on the first segment

    int i = pos - 1, m = 0;
    while (i >= lo && tape_[i] == 1) { ++m; --i; }
    if (m < 1) return;                               // m >= 1
    while (i >= lo && tape_[i] == 0) --i;            // everything further left is blank
    if (i >= lo) return;

    int c[SLOT_NUM];
    for (int k = 0; k < SLOT_NUM; ++k) c[k] = 0;
    c[sp.leftSlot] = m;

    if (gLoose) {
        // only the left half has to match; the right side is free-form
        considerCfg(c, st, step, shapeRight(pos + 1, hi));
        return;
    }

    int t = pos;
    for (int si = 0; si < sp.nright; ++si) {
        const Seg &sg = sp.right[si];
        if (si == sp.nright - 1 && sg.sym == 0 && sg.slot < 0) {
            // a trailing blank cell is a sentinel: the blank region behind it
            // may simply continue, so only the cell itself is checked
            if (t >= hi || tape_[t] != 0) return;
            ++t;
            continue;
        }
        int cnt = 0;
        while (t < hi && tape_[t] == sg.sym) { ++cnt; ++t; }
        if (cnt < sg.minCnt) return;
        if (sg.maxCnt >= 0 && cnt > sg.maxCnt) return;
        if (sg.slot >= 0) c[sg.slot] = cnt;
    }
    if (sp.termBlank) {
        while (t < hi && tape_[t] == 0) ++t;         // everything right is blank
        if (t < hi) return;
    }

    considerCfg(c, st, step, fmtRight(c));
}


// The head must sit on the FIRST 1 of the 1^n run, in one of the landmark's
// head states.  The cells left of it must be  0^inf [5^r] 3^(2m+1) 2^k,  the
// cells right of it the right-side segments of the core spec.
static void noteCfg(int st, int pos, int lo, int hi, long long step) {
    if (!(gSpec.headMask & (1ULL << st))) return;
    if (gSpec.kind == KIND_THREE) {
        noteCfgThree(st, pos, lo, hi, step);
        return;
    }
    if (gSpec.kind == KIND_ONES) {
        noteCfgOnes(st, pos, lo, hi, step);
        return;
    }

    if (tape_[pos] != 1) return;

    int left = (pos > lo) ? tape_[pos - 1] : 0;
    if (left == 1) return;                          // not the first 1 of the run

    int j = pos, n = 0;
    while (j < hi && tape_[j] == 1) { ++n; ++j; }
    if (n < 1) return;

    // Raw census: record the shape right of the 1^n run for EVERY config whose
    // head sits on the first 1, without any left-side constraint.
    // Used to find out what the core actually produces.
    if (gCensus && !gCensusL) {
        char key[200];
        snprintf(key, sizeof key, "%s", shapeRight(j, hi).c_str());
        gCensusMap[key]++;
        ++gCensusTotal;
        return;
    }

    // Left-constrained census: keep only the configs whose LEFT side already
    // has the landmark shape  0^inf [5^r] 3^(2m+1) 2^k,  and record the shape
    // of the right side together with r.
    if (gCensusL) {
        int i = pos - 1, k = 0, n3 = 0;
        while (i >= lo && tape_[i] == 2) { ++k; --i; }
        while (i >= lo && tape_[i] == 3) { ++n3; --i; }
        if (n3 < 1 || (n3 & 1) == 0) return;
        int r5 = 0;
        while (i >= lo && tape_[i] == 5) { ++r5; --i; }
        while (i >= lo && tape_[i] == 0) { --i; }
        if (i >= lo) return;
        char key[220];
        snprintf(key, sizeof key, "5^%d 3^%d 2^%d | %s", r5, n3, k,
                 shapeRight(j, hi).c_str());
        gCensusMap[key]++;
        ++gCensusTotal;
        return;
    }

    int i = pos - 1, k = 0, n3 = 0;
    while (i >= lo && tape_[i] == 2) { ++k; --i; }
    if (k < 1) return;
    while (i >= lo && tape_[i] == 3) { ++n3; --i; }
    if (n3 < 1 || (n3 & 1) == 0) return;
    int m = (n3 - 1) / 2;

    // the optional 5-run on the left of the 3-run
    int r5 = 0;
    while (i >= lo && tape_[i] == 5) { ++r5; --i; }
    if (gSpec.left5 == L5_NONE && r5 != 0) return;
    if (gSpec.left5 == L5_ONE  && r5 != 1) return;
    if (gSpec.left5 == L5_MANY && r5 < 1)  return;
    // everything further left must be blank
    while (i >= lo && tape_[i] == 0) { --i; }
    if (i >= lo) return;

    int c[SLOT_NUM];
    for (int k2 = 0; k2 < SLOT_NUM; ++k2) c[k2] = 0;
    c[SLOT_K] = k; c[SLOT_N] = n; c[SLOT_M] = m; c[SLOT_R5] = r5;

    // right side: the segments of the core spec
    const CoreSpec &sp = gSpec;
    int t = j;
    if (gLoose) {
        // only the left half has to match; the right side is free-form and
        // only its shape is recorded
        considerCfg(c, st, step, shapeRight(j, hi));
        return;
    }
    for (int si = 0; si < sp.nright; ++si) {
        const Seg &sg = sp.right[si];
        int cnt = 0;
        while (t < hi && tape_[t] == sg.sym) { ++cnt; ++t; }
        if (cnt < sg.minCnt) return;
        if (sg.maxCnt >= 0 && cnt > sg.maxCnt) return;
        if (sg.slot >= 0) c[sg.slot] = cnt;
    }
    if (sp.termBlank) {
        while (t < hi && tape_[t] == 0) ++t;        // everything right is blank
        if (t < hi) return;
    }

    considerCfg(c, st, step, fmtRight(c));
}


static void search(int pos, int st, long long steps, uint64_t h, int lo, int hi);
static bool gMC = false;
static bool gRDFS = false;
static uint64_t gRng = 0x9e3779b97f4a7c15ULL;
static inline uint64_t nextRng() {
    uint64_t x = gRng;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return gRng = x;
}
static Tr coreBase_[MAXST][MAXSYM];
static std::vector<std::pair<int,int>> freeCells_;


static bool applySeedTM(const std::string &tnf, std::string &err) {
    std::vector<std::string> rows;
    size_t st = 0;
    for (;;) {
        size_t u = tnf.find('_', st);
        rows.push_back(tnf.substr(st, (u == std::string::npos ? tnf.size() : u) - st));
        if (u == std::string::npos) break;
        st = u + 1;
    }
    if ((int)rows.size() > nstates) { err = "seed TM has too many rows"; return false; }
    int seedSym = (int)(rows[0].size() / 3);
    if (seedSym > gNSym) { err = "seed TM has too many symbols"; return false; }
    copyTab(gSeedTab, coreBase_);
    for (int s = 0; s < (int)rows.size(); ++s) {
        if ((int)rows[s].size() != 3 * seedSym) { err = "bad row len in seed TM"; return false; }
        for (int y = 0; y < seedSym; ++y) {
            if (coreBase_[s][y].nst != UNASSIGNED) continue; // keep core fixed
            const char *t = rows[s].c_str() + 3 * y;
            if (t[0] == '-') continue;
            int w = t[0] - '0';
            if (w < 0 || w >= gNSym) continue;
            int mv = (t[1] == 'L') ? -1 : 1;
            int8_t ns = (t[2] == 'Z') ? HALT_Z : (int8_t)parseStChar(t[2]);
            if (ns != HALT_Z && (ns < 0 || ns >= nstates)) continue;
            gSeedTab[s][y] = {(int8_t)w, (int8_t)mv, ns};
        }
    }
    gHasSeedTab = true;
    return true;
}

static long long gPassStepLimit = 0;

static void searchRDFS(int pos, int st, long long steps, uint64_t h, int lo, int hi, long long curCap, int maxFill) {
    for (;;) {
        if (gAbort || gSteps >= gPassStepLimit) return;
        if (steps >= curCap) return;
        if (pos < lo || pos >= hi) return;

        int sym = tape_[pos];
        noteCfg(st, pos, lo, hi, steps);

        uint64_t key = h ^ zst_[st] ^ zpos_[pos];
        if (!htTry(key)) return;

        Tr t = trans_[st][sym];
        if (t.nst == UNASSIGNED) {
            if (maxFill > 0 && gFilled >= maxFill) return;
            ++gNodes;
            const int nch = (int)choices_.size();
            // Create a shuffled index array or stride permutation of choices
            int startIdx = (int)(nextRng() % nch);
            if (gBiasSym >= 0 && (nextRng() % 4) == 0) {
                // Jump into a block of choices writing gBiasSym or 1
                int wantW = (nextRng() & 1) ? gBiasSym : 1;
                if (wantW >= gNSym) wantW = gBiasSym;
                int perW = nch / gNSym;
                if (perW > 0) startIdx = (wantW * perW + (int)(nextRng() % perW)) % nch;
            }
            int stride = 1 + (int)(nextRng() % (nch > 1 ? nch - 1 : 1));
            while (std::__gcd(stride, nch) != 1) stride = (stride + 1) % nch + (stride + 1 == nch ? 1 : 0);

            int depth = gFilled;
            // Limit how many steps a single child branch at shallow depth can consume
            long long childSlice = (depth == 0) ? 40000LL : (depth == 1) ? 15000LL : (depth == 2) ? 6000LL : gPassStepLimit;

            for (int k = 0; k < nch; ++k) {
                int ci = (startIdx + k * stride) % nch;
                Choice c = choices_[ci];
                if (c.nst == HALT_UNDEF || c.nst == HALT_Z) continue;
                if (c.nst >= 3 && !allowNst(c.nst)) continue;
                trans_[st][sym] = {c.w, c.mv, c.nst};
                ++gFilled;
                size_t tm = tpos_.size(), hm = htrail_.size();
                uint8_t old = tape_[pos];
                twrite(pos, (uint8_t)c.w);
                uint64_t nh = h ^ zob_[old * CELLS + pos] ^ zob_[(int)c.w * CELLS + pos];

                long long savedLimit = gPassStepLimit;
                if (gSteps + childSlice < gPassStepLimit) gPassStepLimit = gSteps + childSlice;
                searchRDFS(pos + c.mv, c.nst, steps + 1, nh, lo, hi, curCap, maxFill);
                gPassStepLimit = savedLimit;

                tundo(tm); htUndo(hm);
                trans_[st][sym] = {0, 0, UNASSIGNED};
                --gFilled;
                if (gAbort || gSteps >= gPassStepLimit) return;
            }
            return;
        }

        if (t.nst == HALT_UNDEF) return;

        uint8_t old = tape_[pos];
        twrite(pos, (uint8_t)t.w);
        h ^= zob_[old * CELLS + pos] ^ zob_[(int)t.w * CELLS + pos];
        pos += t.mv;
        ++steps;
        ++gSteps;
        if ((gSteps & 0xFFFFFF) == 0) {
            if (BUDGET && gSteps > BUDGET) { gAbort = true; return; }
        }
        if (t.nst == HALT_Z) return;
        st = t.nst;
    }
}

static void runRDFS(int head, int startSt) {
    copyTab(coreBase_, trans_);
    freeCells_.clear();
    for (int s = 0; s < nstates; ++s)
        for (int sym = 0; sym < gNSym; ++sym)
            if (coreBase_[s][sym].nst == UNASSIGNED)
                freeCells_.push_back({s, sym});
    if (!gSeedTM.empty()) {
        std::string err;
        if (!applySeedTM(gSeedTM, err)) {
            fprintf(stderr, "--seed-tm error: %s\n", err.c_str());
        } else {
            // Evaluate the seed first so bestCfg gets populated if it hits landmark
            copyTab(trans_, gSeedTab);
            size_t hm0 = htrail_.size();
            searchRDFS(head, startSt, 0, 0, 0, CELLS, CAP, (int)freeCells_.size());
            htUndo(hm0); tundo(0);
            copyTab(trans_, coreBase_);
        }
    }
    long long budget = BUDGET > 0 ? BUDGET : 100000000LL;
    int pass = 0;
    long long caps[5] = { 120, 300, 750, 1800, CAP };
    while (gSteps < budget && !gAbort) {
        long long curCap = caps[pass % 5];
        if (curCap > CAP) curCap = CAP;
        int maxFill = FILLMAX > 0 ? FILLMAX : (int)freeCells_.size();
        // ~66% LNS passes once bestCfg is seeded or found
        if ((bestCfg.step >= 0 || gHasSeedTab) && (pass % 3 != 0) && freeCells_.size() > 2) {
            copyTab(trans_, (bestCfg.step >= 0) ? bestCfg.tab : gSeedTab);
            int nun = 1 + (int)(nextRng() % 3);
            gFilled = 0;
            for (auto &fc : freeCells_) if (trans_[fc.first][fc.second].nst != UNASSIGNED) ++gFilled;
            for (int u = 0; u < nun; ++u) {
                auto fc = freeCells_[nextRng() % freeCells_.size()];
                if (trans_[fc.first][fc.second].nst != UNASSIGNED) {
                    trans_[fc.first][fc.second] = {0, 0, UNASSIGNED};
                    --gFilled;
                }
            }
            curCap = CAP;
            gPassStepLimit = std::min(budget, gSteps + 1500000LL);
        } else {
            copyTab(trans_, coreBase_);
            gFilled = 0;
            gPassStepLimit = std::min(budget, gSteps + 4000000LL);
        }
        size_t hm = htrail_.size();
        searchRDFS(head, startSt, 0, 0, 0, CELLS, curCap, maxFill);
        htUndo(hm);
        tundo(0);
        if (BUDGET && gSteps >= BUDGET) { gAbort = true; break; }
        ++pass;
    }
}

// ---------------------------------------------------------------- search
static void search(int pos, int st, long long steps, uint64_t h, int lo, int hi) {
    for (;;) {
        if (gAbort) return;
        if (steps >= CAP) return;
        if (pos < lo || pos >= hi) return;

        int sym = tape_[pos];
        noteCfg(st, pos, lo, hi, steps);

        uint64_t key = h ^ zst_[st] ^ zpos_[pos];
        if (!htTry(key)) return;                   // cycle

        Tr t = trans_[st][sym];
        if (t.nst == UNASSIGNED) {
            // With --fill K only K free cells may be filled; a run that needs
            // another one simply leaves it undefined, i.e. halts here.
            if (FILLMAX > 0 && gFilled >= FILLMAX) return;
            ++gNodes;
            const int nch = (int)choices_.size();
            for (int ci = 0; ci < nch; ++ci) {
                Choice c = choices_[ci];
                if (c.nst >= 3 && !allowNst(c.nst)) continue;
                trans_[st][sym] = {c.w, c.mv, c.nst};
                ++gFilled;
                size_t tm = tpos_.size(), hm = htrail_.size();
                if (c.nst != HALT_UNDEF) {
                    uint8_t old = tape_[pos];
                    twrite(pos, (uint8_t)c.w);
                    uint64_t nh = h ^ zob_[old * CELLS + pos] ^ zob_[(int)c.w * CELLS + pos];
                    if (c.nst != HALT_Z) search(pos + c.mv, c.nst, steps + 1, nh, lo, hi);
                }
                tundo(tm); htUndo(hm);
                trans_[st][sym] = {0, 0, UNASSIGNED};
                --gFilled;
                if (gAbort) return;
            }
            return;
        }

        if (t.nst == HALT_UNDEF) return;

        uint8_t old = tape_[pos];
        twrite(pos, (uint8_t)t.w);
        h ^= zob_[old * CELLS + pos] ^ zob_[(int)t.w * CELLS + pos];
        pos += t.mv;
        ++steps;
        ++gSteps;
        if ((gSteps & 0xFFFFFF) == 0) {
            if (BUDGET && gSteps > BUDGET) { gAbort = true; return; }
            time_t now = time(NULL);
            if (now != gLastPrint) {
                gLastPrint = now;
                fprintf(stderr, "  ... steps=%lld nodes=%lld\n", gSteps, gNodes);
            }
        }
        if (t.nst == HALT_Z) return;
        st = t.nst;
    }
}

// The state the machine starts in.  --startstate X overrides it; otherwise
// state A is used (blank tape) or the core's lowest head state (input config).
static int startStateOr(int dflt) {
    return (gStartState >= 0) ? gStartState : dflt;
}

// blank-tape start: 0^inf A> 0^inf (head centred, state A)
// With --startstate X the head starts in state X instead, on the same blank
// cell.  Some cores (dfw_4, tfw_5) halt after a couple of steps when started
// in state A; from another state they keep running.
static void startBlank() {
    gFilled = 0;
    int lo = 0, hi = CELLS;
    int head = CELLS / 2;
    size_t hm = htrail_.size();
    if (gRDFS || gMC) runRDFS(head, startStateOr(0)); else search(head, startStateOr(0), 0, 0, lo, hi);
    htUndo(hm);
    tundo(0);
}

// Build the documented INPUT configuration of the core on the tape and return
// the head position.  The head sits on the first 1 of the 1^n run (for the
// KIND_ONES cores on the first cell of the right-hand segment).
//
// This is needed for the cores that contain no construction phase: their
// champion is started on the input configuration itself, so the blank-tape
// start would just die (see dfw_4, which halts after 3 steps).
static int buildStartConfig(uint64_t &h) {
    memset(tape_, 0, sizeof(tape_));
    h = 0;
    int head = CELLS / 2;
    const CoreSpec &sp = gSpec;

    auto put = [&](int p, uint8_t sym) {
        tape_[p] = sym;
        h ^= zob_[sym * CELLS + p];
    };

    if (sp.kind == KIND_THREE) {
        // 0^inf <head> <segments> : the head sits on the first cell of the
        // first segment, the rest of the tape is blank.  The segment lengths
        // are the counters; a segment without a counter has a fixed length.
        int t = head;
        for (int si = 0; si < sp.nright; ++si) {
            const Seg &sg = sp.right[si];
            int cnt = 1;
            if (sg.slot >= 0)    cnt = gCfgVal[sg.slot];
            else if (sg.maxCnt >= 0) cnt = sg.maxCnt;
            if (cnt < sg.minCnt) cnt = sg.minCnt;   // the core needs at least this
            for (int i = 0; i < cnt; ++i) put(t++, (uint8_t)sg.sym);
        }
        return head;
    }

    if (sp.kind == KIND_ONES) {
        // 1^m <head> <right[0]> <right[1]> ... : the head scans the first
        // cell of the first segment, m ones are directly to its left.  A
        // segment with a counter takes its length from the command line, a
        // segment without one has a fixed length.
        int m = gCfgVal[sp.leftSlot];
        if (m < 1) m = 1;                             // the core needs at least one 1
        for (int i = 1; i <= m; ++i) put(head - i, 1);
        int t = head;
        for (int si = 0; si < sp.nright; ++si) {
            const Seg &sg = sp.right[si];
            int cnt = 1;
            if (sg.slot >= 0) cnt = gCfgVal[sg.slot];
            else if (sg.maxCnt >= 0) cnt = sg.maxCnt;
            if (cnt < sg.minCnt) cnt = sg.minCnt;    // the core needs at least this
            for (int i = 0; i < cnt; ++i) put(t++, (uint8_t)sg.sym);
        }
        return head;
    }

    int k = gCfgVal[SLOT_K], n = gCfgVal[SLOT_N], m = gCfgVal[SLOT_M];
    int r5 = gCfgVal[SLOT_R5];
    // The landmark is  0^inf [5^r] 3^(2m+1) 2^k <head> 1^n  : the 2-run sits
    // directly left of the head, the 3-run behind it and the optional 5-run
    // furthest left.  Every group is written towards smaller cell numbers, so
    // the groups have to be written from right to left.
    int left = head;
    for (int i = 0; i < k; ++i)          put(--left, 2);
    for (int i = 0; i < 2 * m + 1; ++i)   put(--left, 3);
    if (sp.left5 == L5_MANY) {
        int r = r5 < 1 ? 1 : r5;          // the core needs at least one 5
        for (int i = 0; i < r; ++i) put(--left, 5);
    }
    else if (sp.left5 == L5_ONE)  { put(--left, 5); }
    for (int i = 0; i < n; ++i)      put(head + i, 1);

    int t = head + (n > 0 ? n : 1);
    for (int si = 0; si < sp.nright; ++si) {
        const Seg &sg = sp.right[si];
        int cnt = 1;
        if (sg.slot >= 0) cnt = gCfgVal[sg.slot];
        else if (sg.maxCnt >= 0) cnt = sg.maxCnt;
        if (cnt < 1) cnt = 1;
        for (int i = 0; i < cnt; ++i) put(t++, sg.sym);
    }
    return head;
}

// The lowest head state the core's landmark allows (usually A; B for the
// fwm2_3 / fwm21_3 / fwm21_4 / fe0_5 cores, A for fwp2_4 whose head may also
// be C or G).
static int firstHeadState() {
    for (int s = 0; s < MAXST; ++s) if (gSpec.headMask & (1u << s)) return s;
    return 0;
}

// start at the documented input configuration instead of the blank tape
static void startAtConfig() {
    gFilled = 0;
    int lo = 0, hi = CELLS;
    uint64_t h;
    int head = buildStartConfig(h);
    size_t hm = htrail_.size();
    search(head, startStateOr(firstHeadState()), 0, h, lo, hi);
    htUndo(hm);
    tundo(0);
}

// ---------------------------------------------------------------- spec override
// --left5 none|one|many
static bool parseLeft5(const std::string &v, std::string &err) {
    if (v == "none") { gSpec.left5 = L5_NONE; return true; }
    if (v == "one")  { gSpec.left5 = L5_ONE;  return true; }
    if (v == "many") { gSpec.left5 = L5_MANY; return true; }
    err = "bad --left5 '" + v + "' (want none|one|many)";
    return false;
}

// --startstate X : the state the machine starts in.
// X is a letter A..Y (case insensitive) or a state index 0..24.
// Without it the machine starts in state A on the blank tape, resp. in the
// core's lowest landmark head state when --start cfg is used.
static bool parseStartState(const std::string &v, std::string &err) {
    if (v.empty()) { err = "bad --startstate '' (want A..Y)"; return false; }
    int s = -1;
    if (v.size() == 1 && isalpha((unsigned char)v[0])) {
        s = toupper((unsigned char)v[0]) - 'A';
    } else {
        char *end = nullptr;
        long n = strtol(v.c_str(), &end, 10);
        if (end && *end == 0 && n >= 0 && n < MAXST) s = (int)n;
    }
    if (s < 0 || s >= MAXST) {
        err = "bad --startstate '" + v + "' (want A..Y)";
        return false;
    }
    gStartState = s;
    return true;
}

// --right SYM:MIN:MAX,SYM:MIN:MAX,...   (MAX = -1 means unbounded)
// The slot of a segment is taken from the segment of the core's spec that
// uses the same symbol, otherwise the segment does not feed a counter.
static bool parseRight(const std::string &v, std::string &err) {
    Seg segs[8];
    int n = 0;
    size_t start = 0;
    while (start <= v.size() && n < 8) {
        size_t comma = v.find(',', start);
        std::string item = trimStr(v.substr(start,
            (comma == std::string::npos ? v.size() : comma) - start));
        if (!item.empty()) {
            int sym = -1, mn = 1, mx = -1;
            if (sscanf(item.c_str(), "%d:%d:%d", &sym, &mn, &mx) != 3) {
                err = "bad --right item '" + item + "' (want SYM:MIN:MAX)";
                return false;
            }
            if (sym < 0 || sym >= gNSym) { err = "bad symbol in '" + item + "'"; return false; }
            segs[n].sym = (uint8_t)sym;
            segs[n].minCnt = mn;
            segs[n].maxCnt = mx;
            segs[n].slot = -1;
            ++n;
        }
        if (comma == std::string::npos) break;
        start = comma + 1;
    }
    if (n == 0) { err = "empty --right"; return false; }
    for (int a = 0; a < n; ++a) {
        for (int b = 0; b < gSpec.nright; ++b) {
            if (gSpec.right[b].sym == segs[a].sym && gSpec.right[b].slot >= 0) {
                segs[a].slot = gSpec.right[b].slot;
                break;
            }
        }
    }
    for (int a = 0; a < n; ++a) gSpec.right[a] = segs[a];
    gSpec.nright = n;
    return true;
}

// --slots P,R5,K,N,M
static bool ieq(const std::string &a, const char *b) {
    size_t n = strlen(b);
    if (a.size() != n) return false;
    for (size_t i = 0; i < n; ++i)
        if (tolower((unsigned char)a[i]) != tolower((unsigned char)b[i])) return false;
    return true;
}

static bool parseSlots(const std::string &v, std::string &err) {
    int slots[10];
    int n = 0;
    size_t start = 0;
    while (start <= v.size() && n < 8) {
        size_t comma = v.find(',', start);
        std::string item = trimStr(v.substr(start,
            (comma == std::string::npos ? v.size() : comma) - start));
        if (!item.empty()) {
            int found = -1;
            for (int s = 0; s < SLOT_NUM; ++s) {
                if (ieq(item, SLOT_NAME[s])) { found = s; break; }
            }
            if (found < 0) { err = "bad slot name '" + item + "'"; return false; }
            slots[n++] = found;
        }
        if (comma == std::string::npos) break;
        start = comma + 1;
    }
    if (n == 0) { err = "empty --slots"; return false; }
    for (int a = 0; a < n; ++a) gSpec.slot[a] = slots[a];
    gSpec.nslot = n;
    return true;
}

// ---------------------------------------------------------------- listing
static void listCores() {
    printf("%-10s %6s %6s  %-52s %s\n", "core", "states", "syms", "landmark", "importance");
    for (size_t c = 0; c < gCores.size(); ++c) {
        CoreSpec sp = gCores[c].spec;
        gSpec = sp;
        std::string tmpl = fmtTemplate();
        std::string imp;
        for (int i = 0; i < sp.nslot; ++i) {
            if (i) imp += " > ";
            imp += SLOT_NAME[sp.slot[i]];
        }
        printf("%-10s %6d %6d  %-52s %s\n", gCores[c].name.c_str(), gCores[c].nfixed,
               gCores[c].nsym, tmpl.c_str(), imp.c_str());
    }
    if (gCore >= 0 && gCore < (int)gCores.size()) gSpec = gCores[gCore].spec;
}

// ---------------------------------------------------------------- main
static void usage() {
    printf("usage:\n");
    printf("  bbsearch --core CORE [--states N] [--cap N] [--budget N] [--fill K] [--log F] [--census] [--fix ...]\n");
    printf("  bbsearch --all [--cap N] [--budget N] [--log F]      run every core in turn\n");
    printf("  bbsearch --cores                                       list the cores\n");
    printf("  CORE one of:");
    // usage() also runs before the core file is loaded (no arguments, unknown
    // option), so fall back to the default file for the name list.
    std::vector<CoreEntry> listed = gCores;
    if (listed.empty()) {
        std::string err;
        loadCoreFile(DEFAULT_CORE_FILE, listed, err);
    }
    for (size_t c = 0; c < listed.size(); ++c) printf(" %s", listed[c].name.c_str());
    printf("\n");
    printf("  --states defaults to the core's own number of fixed states\n");
    printf("  --cores-file PATH         the core file to read (default: %s)\n", DEFAULT_CORE_FILE);
    printf("           every core block consists of the lines name/cfg/slot/core;\n");
    printf("           the file holds every core the program knows\n");
    printf("  add --fix A0=4LC,B0=1RZ to pin transitions (CELL=WRITE-MOVE-NEXT)\n");
    printf("  --census prints the observed right-hand shapes instead of matching a landmark\n");
    printf("  --censusL like --census but keeps only configs whose left half already\n");
    printf("           matches 0^inf 5^r 3^(2m+1) 2^k, and prints r with the shape\n");
    printf("  --symbols N               alphabet size, %d..%d (default: the core's own).\n",
           2, MAXSYM);
    printf("           The core rows describe symbols 0..coreSym-1 only; with a larger\n");
    printf("           alphabet the extra columns are free and get filled by the DFS, so\n");
    printf("           the search runs over N-symbol machines that contain the core.\n");
    printf("  --start blank|cfg          where the machine starts.  'blank' (default) is the\n");
    printf("           blank tape 0^inf A> 0^inf; 'cfg' is the documented INPUT\n");
    printf("           configuration of the core, built with the counters below.  Use\n");
    printf("           'cfg' for the cores that contain no construction phase (their\n");
    printf("           blank-tape run dies immediately, e.g. dfw_4 halts after 3 steps).\n");
    printf("           In 'cfg' mode only the LEFT half of the landmark is matched,\n");
    printf("           because the machine transforms the input into a bigger config.\n");
    printf("  --startstate A..Y          the state the machine starts in (default: A on the\n");
    printf("           blank tape, the core's lowest landmark head state in 'cfg' mode).\n");
    printf("           dfw_4 and tfw_5 halt within a few steps when started\n");
    printf("           in state A; from another state they keep running.\n");
    printf("  --k --n --m --p --q --r --r5   counter values of the start configuration\n");
    printf("           (defaults 16, 3, 0, 1, 1, 1, 1).\n");
    printf("landmark spec overrides (no recompile needed to try another guess):\n");
    printf("  --left5 none|one|many     the 5-run left of the 3-run\n");
    printf("  --right 2:1:-1,5:1:-1     right-side segments SYM:MIN:MAX (-1 = unbounded)\n");
    printf("  --slots P,R5,K,N,M        importance order of the counter slots\n");
    printf("  --noblank                 do not require a blank after the last segment\n");
    printf("starts from the blank tape 0^inf A> 0^inf and reports the largest landmark\n");
    printf("of the chosen core (importance order per bbcores_new.txt).\n");
}

// Run the search for one core; returns the best configuration in bestCfg.
static void runCore(int coreIdx, int states, int symOverride, bool startAtCfg,
                    const std::vector<std::string> &fixSpecs) {
    gCore = coreIdx;
    nstates = states;
    gSpec = gCores[coreIdx].spec;
    gNSym = symOverride ? symOverride : gCores[coreIdx].nsym;
    if (gStartState >= nstates) {
        fprintf(stderr, "--core %s: --startstate %c is outside the machine's %d states\n",
                gCores[coreIdx].name.c_str(), (char)('A' + gStartState), nstates);
        exit(1);
    }
    gFilled = 0;
    gSteps = 0;
    gNodes = 0;
    gAbort = false;
    gCensusMap.clear();
    gCensusTotal = 0;
    bestCfg = CfgBest();
    bestIrredCfg = CfgBest();
    memset(tape_, 0, sizeof(tape_));
    memset(hocc_, 0, sizeof(hocc_));
    htrail_.clear();
    tpos_.clear();
    tval_.clear();

    setupCore();
    {
        std::string err;
        if (!checkCoreWrites(err)) {
            fprintf(stderr, "--core %s: %s\n", gCores[coreIdx].name.c_str(), err.c_str());
            exit(1);
        }
        if (!checkSpecSymbols(err)) {
            fprintf(stderr, "--core %s: %s\n", gCores[coreIdx].name.c_str(), err.c_str());
            exit(1);
        }
    }
    for (size_t fi = 0; fi < fixSpecs.size(); ++fi) {
        std::string err;
        if (!applyFixSpec(fixSpecs[fi], err)) {
            fprintf(stderr, "--fix %s: %s\n", fixSpecs[fi].c_str(), err.c_str());
            exit(1);
        }
    }
    buildChoices();
    gLastPrint = time(NULL);
    if (startAtCfg) {
        // The core is given its input configuration; only the left half of the
        // landmark is matched, because the machine transforms the input into a
        // bigger configuration whose right side is different.
        gLoose = true;
        for (int s = 0; s < SLOT_NUM; ++s) gSlotKnown[s] = true;
        gSlotKnown[SLOT_P] = false;
        gSlotKnown[SLOT_Q] = false;
        gSlotKnown[SLOT_R] = false;
        gSlotKnown[SLOT_S] = false;
        startAtConfig();
    } else {
        gLoose = false;
        for (int s = 0; s < SLOT_NUM; ++s) gSlotKnown[s] = true;
        startBlank();
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { usage(); return 1; }
    int i = 1;
    std::string coreName = "fw1_6";
    std::string coreFile = DEFAULT_CORE_FILE;
    std::string logPath;
    std::vector<std::string> fixSpecs;
    std::string left5Override, rightOverride, slotsOverride;
    bool noBlank = false;
    bool doAll = false;
    bool doList = false;
    int nSymbols = 0;                 // 0 = use the core's own count
    int nStates = 0;                  // 0 = use the core's own fixed count
    std::string startMode = "blank";  // blank | cfg
    for (; i < argc; ++i) {
        std::string k = argv[i];
        auto next = [&](const char *def) -> const char * {
            if (i + 1 < argc) return argv[++i];
            return def;
        };
        if      (k == "--core")   coreName = next("fw1_6");
        else if (k == "--states") nStates = atoi(next("0"));
        else if (k == "--cap")    CAP = (long long)strtod(next("50000"), nullptr);
        else if (k == "--budget") BUDGET = (long long)strtod(next("0"), nullptr);
        else if (k == "--fill")   FILLMAX = atoi(next("0"));
        else if (k == "--log")    logPath = next("bbsearch.log");
        else if (k == "--census") gCensus = true;
        else if (k == "--censusL") { gCensus = true; gCensusL = true; }
        else if (k == "--fix")    fixSpecs.push_back(next(""));
        else if (k == "--left5")  left5Override = next("");
        else if (k == "--right")  rightOverride = next("");
        else if (k == "--slots")  slotsOverride = next("");
        else if (k == "--noblank") noBlank = true;
        else if (k == "--start")   startMode = next("blank");
        else if (k == "--startstate") {
            std::string err;
            if (!parseStartState(next(""), err)) { fprintf(stderr, "%s\n", err.c_str()); return 1; }
        }
        else if (k == "--k")       gCfgVal[SLOT_K] = atoi(next("16"));
        else if (k == "--n")       gCfgVal[SLOT_N] = atoi(next("3"));
        else if (k == "--m")       gCfgVal[SLOT_M] = atoi(next("0"));
        else if (k == "--p")       gCfgVal[SLOT_P] = atoi(next("1"));
        else if (k == "--q")       gCfgVal[SLOT_Q] = atoi(next("1"));
        else if (k == "--r")       gCfgVal[SLOT_R] = atoi(next("1"));
        else if (k == "--r5")      gCfgVal[SLOT_R5] = atoi(next("1"));
        else if (k == "--symbols") nSymbols = atoi(next("6"));
        else if (k == "--all")   doAll = true;
        else if (k == "--cores") doList = true;
        else if (k == "--cores-file") coreFile = next(DEFAULT_CORE_FILE);
        else if (k == "--mc" || k == "--rdfs") { gMC = true; gRDFS = true; }
        else if (k == "--seed") gRng = strtoull(next("1"), nullptr, 10) | 1ULL;
        else if (k == "--bias-sym") gBiasSym = atoi(next("-1"));
        else if (k == "--seed-tm") gSeedTM = next("");
        else { fprintf(stderr, "unknown option %s\n", k.c_str()); usage(); return 1; }
    }

    if (!loadCoresFromFile(coreFile)) return 1;

    if (doList) { listCores(); return 0; }

    gCore = -1;
    for (size_t c = 0; c < gCores.size(); ++c) {
        if (coreName == gCores[c].name) { gCore = (int)c; break; }
        char num[8]; snprintf(num, sizeof num, "%d", (int)c);
        if (coreName == num) { gCore = (int)c; break; }
    }
    if (gCore < 0 && !doAll) {
        fprintf(stderr, "bad --core '%s' (use one of:", coreName.c_str());
        for (size_t c = 0; c < gCores.size(); ++c) fprintf(stderr, " %s", gCores[c].name.c_str());
        fprintf(stderr, ")\n");
        return 1;
    }
    if (gCore < 0) gCore = 0;

    if (nSymbols && (nSymbols < 2 || nSymbols > MAXSYM)) {
        fprintf(stderr, "bad --symbols %d (want %d..%d)\n", nSymbols, 2, MAXSYM);
        return 1;
    }
    if (nStates && (nStates < 3 || nStates > MAXST)) {
        fprintf(stderr, "bad --states %d (want %d..%d)\n", nStates, 3, MAXST);
        return 1;
    }

    if (!logPath.empty()) {
        gLog = fopen(logPath.c_str(), "a");
        if (!gLog) {
            fprintf(stderr, "cannot open log file '%s'\n", logPath.c_str());
            return 1;
        }
    }

    initZobrist();

    if (doAll) {
        printf("== all cores: cap=%lld budget=%lld fill=%d ==\n", CAP, BUDGET, FILLMAX);
        for (size_t c = 0; c < gCores.size(); ++c) {
            int st = nStates ? nStates : gCores[c].nfixed;
            if (st < gCores[c].nfixed) st = gCores[c].nfixed;
            int savedNSym = nSymbols;
            gNSym = savedNSym ? savedNSym : gCores[c].nsym;
            if (gNSym < gCores[c].nsym) {
                // a smaller alphabet: the core columns are dropped, the
                // landmark may become impossible -> report and skip
                printf("\n== %s: skipped (--symbols %d < %d symbols of the core)\n",
                       gCores[c].name.c_str(), gNSym, gCores[c].nsym);
                continue;
            }
            if (gStartState >= st) {
                printf("\n== %s: skipped (--startstate %c is outside the machine's %d states)\n",
                       gCores[c].name.c_str(), (char)('A' + gStartState), st);
                continue;
            }
            printf("\n===== core %s (states=%d symbols=%d) =====\n",
                   gCores[c].name.c_str(), st, gNSym);
            fflush(stdout);
            runCore((int)c, st, savedNSym, startMode == "cfg", fixSpecs);
            printf("---- %s done: steps=%lld nodes=%lld abort=%d ----\n",
                   gCores[c].name.c_str(), gSteps, gNodes, (int)gAbort);
            if (bestCfg.step >= 0) {
                emit("best %s\n", fmtLeft(bestCfg.c, bestCfg.shape).c_str());
                emit("  step=%lld states_used=%d\n", bestCfg.step, bestCfg.used);
                emit("  ");
                printTabF(stdout, bestCfg.tab, bestCfg.used);
                if (gLog) printTabF(gLog, bestCfg.tab, bestCfg.used);
            } else {
                emit("no landmark configuration was reached\n");
            }
            fflush(stdout);
        }
        if (gLog) { fflush(gLog); fclose(gLog); gLog = nullptr; }
        return 0;
    }

    const CoreEntry &cd = gCores[gCore];
    int st = nStates ? nStates : cd.nfixed;
    if (st < cd.nfixed) {
        fprintf(stderr, "--core %s needs --states >= %d (A..%c are fixed)\n",
                cd.name.c_str(), cd.nfixed, (char)('A' + cd.nfixed - 1));
        return 1;
    }
    gNSym = nSymbols ? nSymbols : cd.nsym;

    // the spec of the chosen core, then the command-line overrides
    gSpec = gCores[gCore].spec;
    {
        std::string err;
        if (!left5Override.empty() && !parseLeft5(left5Override, err)) {
            fprintf(stderr, "%s\n", err.c_str()); return 1;
        }
        if (!rightOverride.empty() && !parseRight(rightOverride, err)) {
            fprintf(stderr, "%s\n", err.c_str()); return 1;
        }
        if (!slotsOverride.empty() && !parseSlots(slotsOverride, err)) {
            fprintf(stderr, "%s\n", err.c_str()); return 1;
        }
        if (noBlank) gSpec.termBlank = false;
    }

    if (!logPath.empty()) {
        char ts[64];
        time_t now = time(NULL);
        strftime(ts, sizeof ts, "%Y-%m-%d %H:%M:%S", localtime(&now));
        fprintf(gLog, "# %s mode=%s core=%s states=%d symbols=%d cap=%lld budget=%lld fill=%d\n",
                ts, gCensus ? "census" : "maxcfg", cd.name.c_str(), st, gNSym, CAP, BUDGET, FILLMAX);
        fflush(gLog);
    }
    printf("mode=%s core=%s states=%d symbols=%d cap=%lld budget=%lld fill=%d\n",
           gCensus ? "census" : "maxcfg", cd.name.c_str(), st, gNSym, CAP, BUDGET, FILLMAX);
    for (size_t fi = 0; fi < fixSpecs.size(); ++fi)
        emit("fix: %s\n", fixSpecs[fi].c_str());
    printf("landmark: %s\n", fmtTemplate().c_str());
    if (startMode == "cfg") {
        printf("start: the input configuration of the core, k=%d n=%d m=%d p=%d q=%d r=%d r5=%d\n",
               gCfgVal[SLOT_K], gCfgVal[SLOT_N], gCfgVal[SLOT_M], gCfgVal[SLOT_P],
               gCfgVal[SLOT_Q], gCfgVal[SLOT_R], gCfgVal[SLOT_R5]);
        printf("       only the LEFT half of the landmark is matched; the right side is free-form\n");
    } else {
        printf("start: blank tape 0^inf A> 0^inf\n");
    }
    if (gStartState >= 0) {
        printf("       start state %c (overrides the default)\n", (char)('A' + gStartState));
    }
    fflush(stdout);

    runCore(gCore, st, nSymbols, startMode == "cfg", fixSpecs);

    printf("\n---- done ----\n");
    printf("steps=%lld nodes=%lld abort=%d\n", gSteps, gNodes, (int)gAbort);
    if (gCensus) {
        printf("census: %lld observations, %zu distinct shapes\n",
               gCensusTotal, gCensusMap.size());
        std::vector<std::pair<long long, std::string> > v;
        for (std::map<std::string, long long>::const_iterator it = gCensusMap.begin();
             it != gCensusMap.end(); ++it)
            v.push_back(std::make_pair(it->second, it->first));
        std::sort(v.begin(), v.end());
        std::reverse(v.begin(), v.end());
        for (size_t j = 0; j < v.size(); ++j)
            printf("  %8lld  %s\n", v[j].first, v[j].second.c_str());
        if (gLog) {
            for (size_t j = 0; j < v.size(); ++j)
                fprintf(gLog, "census %8lld  %s\n", v[j].first, v[j].second.c_str());
        }
    } else if (bestCfg.step >= 0) {
        emit("best %s\n", fmtLeft(bestCfg.c, bestCfg.shape).c_str());
        emit("  step=%lld states_used=%d\n", bestCfg.step, bestCfg.used);
        emit("  ");
        printTabF(stdout, bestCfg.tab, bestCfg.used);
        if (gLog) printTabF(gLog, bestCfg.tab, bestCfg.used);
    } else {
        emit("no landmark configuration was reached\n");
    }
    if (gLog) { fflush(gLog); fclose(gLog); gLog = nullptr; }
    return 0;
}
