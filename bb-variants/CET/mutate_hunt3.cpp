// mutate_hunt3.cpp — budget-ladder, resumable, hill-climbing mutation hunter for 2-agent CET(S,K).
//  * Budget ladder: every candidate runs to B0 steps, survivors are SUSPENDED (config + tape saved) and resumed at
//    B0*8, B0*8^2, ... so no thread ever gets stuck on one non-halter. Lower levels are always served first.
//  * Exact "escape" rejection (sound): agent A strictly ahead of B (in its direction), standing on the frontier of
//    all visited cells on a blank cell, whose autonomous blank-tape path only ever moves away => runs at max speed
//    1 cell/step forever, B can never catch it => the machine provably never collides. No budget needed.
//  * Heuristic envelope pruning (NOT proofs; validated only on known champions) is ON by default; pass "noheur" to
//    disable the heuristics and rely on the ladder + exact escape rule only (much slower).
//  * Fused 1-lookup transition table, 4M-cell tape, uint64 steps.
// Usage: mutate_hunt3.exe <seedfile> <S> <K> <depth> <topN> <stepLimit> <outfile> [threads=16] [minLog=3000000]
//                         [seedLog=100000000] [budget0=20000000] [noheur]
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <fstream>
#include <mutex>
#include <string>
#include <thread>
#include <unordered_set>
#include <vector>

static constexpr int TS = 1 << 22, OFF = 1 << 21;
static constexpr int MAXLEV = 24;
struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach { Tr t[2][4][3]; };
struct Fused { int8_t d0, d1; uint8_t w0, w1, n0, n1; };
struct Cfg { int p0 = 0, p1 = 2, q0 = 0, q1 = 0, mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2; uint64_t st = 0; };
struct Job { Mach m; Cfg c; int level; int lo; std::vector<uint8_t> seg; };
enum { R_HALT, R_DEAD, R_SUSP, R_LIMIT, R_ESC };

static int S, K, DEPTH, NT, NTR;
static uint64_t LIMIT, MINLOG, SEEDLOG, B0;
static bool HEUR = true;
static std::atomic<uint64_t> best{0}, tested{0}, escaped{0}, heur_dead{0}, limit_hit{0};
static std::mutex pm, qm, seen_m;
static FILE* out;
static std::unordered_set<uint64_t> seen_surv, seen_log;

static std::string fmt(const Mach& m) {
    std::string s;
    for (int a = 0; a < 2; a++) {
        if (a) s += '|';
        for (int q = 0; q < S; q++) {
            if (q) s += '_';
            for (int b = 0; b < K; b++) {
                const Tr& t = m.t[a][q][b];
                s += char('0' + t.w); s += t.m > 0 ? 'R' : 'L'; s += char('A' + t.n);
            }
        }
    }
    return s;
}
static uint64_t hsh(const Mach& m) {
    uint64_t h = 1469598103934665603ULL;
    for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) for (int b = 0; b < K; b++) {
        const Tr& t = m.t[a][q][b];
        h = (h ^ (t.w | (t.m > 0 ? 4 : 0) | (t.n << 3))) * 1099511628211ULL;
    }
    return h;
}
static bool parse(const std::string& str, Mach& m) {
    for (int a = 0; a < 2; a++) for (int q = 0; q < 4; q++) for (int b = 0; b < 3; b++) m.t[a][q][b] = {0, 1, 0};
    int a = 0, q = 0, b = 0;
    for (size_t i = 0; i < str.size(); i++) {
        char c = str[i];
        if (c == '|') { a++; q = 0; b = 0; continue; }
        if (c == '_') { q++; b = 0; continue; }
        if (c >= '0' && c <= '9' && i + 2 < str.size()) {
            if (a > 1 || q > 3 || b > 2) return false;
            m.t[a][q][b] = {uint8_t(c - '0'), int8_t(str[i + 1] == 'R' ? 1 : -1), uint8_t(str[i + 2] - 'A')};
            b++; i += 2;
        }
    }
    return a == 1;
}

struct Sim {
    uint8_t* tape; Fused tab[4 * 3 * 4 * 3];
    int dlo = OFF, dhi = OFF;   // dirty range of the physical tape (to clear between jobs)
    bool escR[2][4], escL[2][4];
    Sim() { tape = (uint8_t*)calloc(TS, 1); }
    void clear() { if (dhi >= dlo) memset(tape + dlo, 0, dhi - dlo + 1); dlo = OFF; dhi = OFF; }
    void prep(const Mach& m) {
        for (int q0 = 0; q0 < S; q0++) for (int b0 = 0; b0 < K; b0++) for (int q1 = 0; q1 < S; q1++) for (int b1 = 0; b1 < K; b1++) {
            const Tr& a = m.t[0][q0][b0]; const Tr& b = m.t[1][q1][b1];
            tab[((q0 * K + b0) * S + q1) * K + b1] = {a.m, b.m, a.w, b.w, a.n, b.n};
        }
        // exact escape tables: autonomous path on blank (symbol 0) from state q moves only R (resp. only L)
        for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) {
            bool seenst[4] = {0, 0, 0, 0}; bool okR = true, okL = true; int cur = q;
            while (!seenst[cur]) { seenst[cur] = true; const Tr& t = m.t[a][cur][0]; if (t.m > 0) okL = false; else okR = false; cur = t.n; }
            escR[a][q] = okR; escL[a][q] = okL;
        }
    }
    // Run from cfg c (tape already loaded) until collision / dead / escape / st>=end.
    int run(const Mach& m, Cfg& c, uint64_t end, int& colx) {
        prep(m);
        int p0 = c.p0, p1 = c.p1, q0 = c.q0, q1 = c.q1;
        int mn0 = c.mn0, mx0 = c.mx0, mn1 = c.mn1, mx1 = c.mx1;
        uint64_t st = c.st;
        uint8_t* T = tape + OFF;
        const Fused* tb = tab;
        int rc = R_SUSP;
        while (true) {
            if (st >= end) { rc = (st >= LIMIT) ? R_LIMIT : R_SUSP; break; }
            bool col = false;
            for (int i = 0; i < 128; i++) {
                const Fused& f = tb[((q0 * K + T[p0]) * S + q1) * K + T[p1]];
                T[p1] = f.w1; T[p0] = f.w0;
                p0 += f.d0; p1 += f.d1; q0 = f.n0; q1 = f.n1;
                if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
                if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
                if (p0 == p1) { st += i + 1; col = true; break; }
            }
            if (col) { colx = p0; c.st = st; rc = R_HALT; goto done; }
            st += 128;
            {
                int mxv = std::max(mx0, mx1), mnv = std::min(mn0, mn1);
                // exact escape rule
                if ((p0 > p1 && p0 == mxv && !T[p0] && escR[0][q0]) || (p1 > p0 && p1 == mxv && !T[p1] && escR[1][q1]) ||
                    (p0 < p1 && p0 == mnv && !T[p0] && escL[0][q0]) || (p1 < p0 && p1 == mnv && !T[p1] && escL[1][q1])) {
                    rc = R_ESC; goto done;
                }
                if (HEUR) {
                    int ap = std::max(std::max(-mn0, mx0), std::max(-mn1, mx1)); int cap = ap;
                    if (mx0 < mn1 || mx1 < mn0) { rc = R_DEAD; goto done; }
                    bool bad = false;
                    if (st <= 512) { bad = ap > 80 || (st == 512 && cap < 5); }
                    else if (st <= 2048) { bad = ap > 160 || (st == 2048 && (cap < 12 || mx0 - mn0 < 4 || mx1 - mn1 < 4)); }
                    else if (st <= 10240) { bad = ap > 360 || (st == 10240 && cap < 28); }
                    else if (st <= 50048) { bad = ap > 800 || (st == 50048 && cap < 65); }
                    else if (st <= 250112) { bad = ap > 2000 || (st == 250112 && cap < 140); }
                    else if (st <= 1000064) { bad = ap > 4500 || (st == 1000064 && cap < 280); }
                    else if (st <= 4000000) { bad = ap > 9000 || (st == 4000000 && cap < 600); }
                    else {
                        double r = std::sqrt((double)st);
                        bad = ap > std::max(9000.0, 2.0 * r) || ap > OFF - 8 || ((st & (st - 1)) == 0 && cap < 0.08 * r);
                    }
                    if (bad) { rc = R_DEAD; goto done; }
                } else if (std::max(-mnv, mxv) > OFF - 8) { rc = R_DEAD; goto done; }
            }
        }
    done:
        c.p0 = p0; c.p1 = p1; c.q0 = q0; c.q1 = q1; c.mn0 = mn0; c.mx0 = mx0; c.mn1 = mn1; c.mx1 = mx1; c.st = st;
        int l = std::min(mn0, mn1) - 1 + OFF, h = std::max(mx0, mx1) + 1 + OFF;
        if (l < 0) l = 0; if (h >= TS) h = TS - 1;
        dlo = std::min(dlo, l); dhi = std::max(dhi, h);
        return rc;
    }
};

struct Tk { Mach base; int p; int w, d, n; int depth; };
static std::deque<Tk> dq;
static std::deque<Job> lev[MAXLEV];
static std::atomic<uint64_t> nsusp{0};

static uint64_t budget(int level) { uint64_t b = B0; for (int i = 0; i < level; i++) b *= 8; return std::min(b, LIMIT); }

static void push_seed(const Mach& m, int depth) {
    std::lock_guard<std::mutex> lk(qm);
    Tk t0{m, -1, 0, 0, 0, depth}; dq.push_back(t0);
    for (int p = 0; p < NTR; p++)
        for (int w = 0; w < K; w++) for (int d = 0; d < 2; d++) for (int n = 0; n < S; n++) {
            Tk t{m, p, w, d, n, depth}; dq.push_back(t);
        }
}

static void record(const Mach& m, uint64_t st, int x) {
    uint64_t h = hsh(m);
    { std::lock_guard<std::mutex> lk(seen_m); if (!seen_log.insert(h).second) return; }
    std::string k = fmt(m);
    {
        std::lock_guard<std::mutex> lk(pm);
        if (st > best.load()) {
            best.store(st);
            printf("\n*** [NEW BEST] %llu steps (x=%d)\n    %s\n", (unsigned long long)st, x, k.c_str());
        }
        fprintf(out, "%llu\t%d\t%s\n", (unsigned long long)st, x, k.c_str());
        fflush(out); fflush(stdout);
    }
    if (st >= SEEDLOG) push_seed(m, DEPTH);
}

static void handle(Sim& sim, const Mach& m, Cfg& c, int level, int rc, int colx) {
    if (rc == R_HALT) { if (c.st >= MINLOG || c.st > best.load()) record(m, c.st, colx); }
    else if (rc == R_ESC) escaped++;
    else if (rc == R_DEAD) heur_dead++;
    else if (rc == R_LIMIT) { limit_hit++; }
    else { // suspended: dedupe and enqueue for next level
        uint64_t h = hsh(m);
        { std::lock_guard<std::mutex> lk(seen_m); if (!seen_surv.insert(h ^ (uint64_t)level * 0x9E3779B97F4A7C15ULL).second) return; }
        Job j; j.m = m; j.c = c; j.level = level + 1;
        int l = std::min(c.mn0, c.mn1) - 1, hh = std::max(c.mx0, c.mx1) + 1;
        j.lo = l; j.seg.assign(sim.tape + OFF + l, sim.tape + OFF + hh + 1);
        nsusp++;
        std::lock_guard<std::mutex> lk(qm);
        lev[std::min(j.level, MAXLEV - 1)].push_back(std::move(j));
    }
}

static void eval(Sim& sim, const Mach& m) {
    tested++;
    sim.clear();
    Cfg c; int x = 0;
    int rc = sim.run(m, c, std::min(B0, LIMIT), x);
    handle(sim, m, c, 0, rc, x);
}

static void rec(Sim& sim, Mach& m, int start, int left) {
    eval(sim, m);
    if (left == 0) return;
    for (int p = start; p < NTR; p++) {
        int a = p / (S * K), q = (p / K) % S, b = p % K;
        Tr old = m.t[a][q][b];
        for (int w = 0; w < K; w++) for (int d = 0; d < 2; d++) for (int n = 0; n < S; n++) {
            Tr nt = {uint8_t(w), int8_t(d ? -1 : 1), uint8_t(n)};
            if (nt.w == old.w && nt.m == old.m && nt.n == old.n) continue;
            m.t[a][q][b] = nt;
            rec(sim, m, p + 1, left - 1);
        }
        m.t[a][q][b] = old;
    }
}

int main(int argc, char** argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    if (argc < 8) { puts("usage: seedfile S K depth topN limit out [threads] [minLog] [seedLog] [budget0] [noheur]"); return 1; }
    S = atoi(argv[2]); K = atoi(argv[3]); DEPTH = atoi(argv[4]);
    int topN = atoi(argv[5]); LIMIT = strtoull(argv[6], 0, 10);
    out = fopen(argv[7], "a");
    NT = argc > 8 ? atoi(argv[8]) : 16;
    MINLOG = argc > 9 ? strtoull(argv[9], 0, 10) : 3000000;
    SEEDLOG = argc > 10 ? strtoull(argv[10], 0, 10) : 100000000;
    B0 = argc > 11 ? strtoull(argv[11], 0, 10) : 20000000ULL;
    B0 = (B0 / 128) * 128;
    for (int i = 12; i < argc; i++) if (!strcmp(argv[i], "noheur")) HEUR = false;
    NTR = 2 * S * K;
    std::ifstream f(argv[1]);
    std::vector<std::pair<uint64_t, std::string>> all;
    std::string line;
    while (std::getline(f, line)) {
        uint64_t st; int x; char buf[256];
        if (sscanf(line.c_str(), "%llu\t%d\t%255s", (unsigned long long*)&st, &x, buf) == 3) all.push_back({st, buf});
    }
    std::sort(all.rbegin(), all.rend());
    std::unordered_set<std::string> sset; int ns = 0;
    for (auto& pr : all) {
        if (ns >= topN) break;
        if (!sset.insert(pr.second).second) continue;
        Mach m; if (!parse(pr.second, m)) continue;
        seen_log.insert(hsh(m)); push_seed(m, DEPTH); ns++;
    }
    printf("seeds=%d S=%d K=%d depth=%d tasks=%zu limit=%llu budget0=%llu heur=%d seedLog=%llu\n", ns, S, K, DEPTH, dq.size(),
           (unsigned long long)LIMIT, (unsigned long long)B0, (int)HEUR, (unsigned long long)SEEDLOG);
    auto t0 = std::chrono::steady_clock::now();
    std::atomic<uint64_t> done{0};
    std::atomic<int> active{NT};
    std::vector<std::thread> pool;
    for (int i = 0; i < NT; i++) pool.emplace_back([&]() {
        Sim sim;
        while (true) {
            Tk tk; Job job; int kind = 0; // 1 fresh, 2 job
            {
                std::lock_guard<std::mutex> lk(qm);
                if (!dq.empty()) { tk = dq.front(); dq.pop_front(); kind = 1; }
                else for (int l = 1; l < MAXLEV; l++) if (!lev[l].empty()) { job = std::move(lev[l].front()); lev[l].pop_front(); kind = 2; break; }
            }
            if (!kind) {
                active--;
                bool again = false;
                for (int w = 0; w < 100 && !again; w++) {
                    if (active.load() == 0) break;
                    std::this_thread::sleep_for(std::chrono::milliseconds(50));
                    std::lock_guard<std::mutex> lk(qm);
                    if (!dq.empty()) again = true;
                    else for (int l = 1; l < MAXLEV; l++) if (!lev[l].empty()) { again = true; break; }
                }
                if (!again) return;
                active++;
                continue;
            }
            if (kind == 1) {
                Mach m = tk.base;
                if (tk.p < 0) eval(sim, m);
                else {
                    int a = tk.p / (S * K), q = (tk.p / K) % S, b = tk.p % K;
                    Tr nt = {uint8_t(tk.w), int8_t(tk.d ? -1 : 1), uint8_t(tk.n)};
                    Tr old = m.t[a][q][b];
                    if (!(nt.w == old.w && nt.m == old.m && nt.n == old.n)) {
                        m.t[a][q][b] = nt;
                        rec(sim, m, tk.p + 1, tk.depth - 1);
                    }
                }
                uint64_t d = ++done;
                if (d % 2000 == 0) {
                    std::lock_guard<std::mutex> lk(pm);
                    double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
                    size_t ql = 0; std::string lv;
                    { std::lock_guard<std::mutex> lq(qm); ql = dq.size(); for (int l = 1; l < MAXLEV; l++) if (!lev[l].empty()) lv += " L" + std::to_string(l) + "=" + std::to_string(lev[l].size()); }
                    printf("[prog] %llu tasks (fresh left %zu) %.0fs tested=%llu esc=%llu heurDead=%llu susp=%llu |%s | best=%llu\n",
                           (unsigned long long)d, ql, el, (unsigned long long)tested.load(), (unsigned long long)escaped.load(),
                           (unsigned long long)heur_dead.load(), (unsigned long long)nsusp.load(), lv.c_str(), (unsigned long long)best.load());
                }
            } else {
                sim.clear();
                memcpy(sim.tape + OFF + job.lo, job.seg.data(), job.seg.size());
                sim.dlo = std::min(sim.dlo, OFF + job.lo); sim.dhi = std::max(sim.dhi, OFF + job.lo + (int)job.seg.size() - 1);
                int x = 0;
                int rc = sim.run(job.m, job.c, budget(job.level), x);
                handle(sim, job.m, job.c, job.level, rc, x);
            }
        }
    });
    for (auto& t : pool) t.join();
    printf("DONE tested=%llu esc=%llu heurDead=%llu limit=%llu best=%llu\n", (unsigned long long)tested.load(),
           (unsigned long long)escaped.load(), (unsigned long long)heur_dead.load(), (unsigned long long)limit_hit.load(),
           (unsigned long long)best.load());
    fclose(out);
}
