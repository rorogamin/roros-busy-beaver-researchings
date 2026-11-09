// mutate_hunt.cpp — seeded k-transition mutation hunter for CET(S,K) (2 agents).
// Usage: mutate_hunt.exe <seedfile> <S> <K> <depth> <topN> <stepLimit> <outfile> [threads=16] [minLog=3000000]
// seedfile lines: "<steps>\t<x>\t<machine>" (machine like 0RB0LC_..|..). Top-N distinct by steps are used.
// If S exceeds a seed's state count, extra states are added (grow), e.g. CET(3) seeds -> CET(4).
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <mutex>
#include <set>
#include <string>
#include <thread>
#include <vector>
#include <chrono>

static constexpr int TS = 131072, OFF = 65536;
struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach { Tr t[2][4][3]; };

static int S, K, DEPTH, NT, NTR;
static uint64_t LIMIT, MINLOG;
static std::atomic<uint64_t> best{0};
static std::mutex pm;
static FILE* out;
static std::atomic<uint64_t> tested{0};

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

static bool parse(const std::string& str, Mach& m) {
    memset(&m, 0, sizeof m);
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
    uint8_t* tape;
    Sim() { tape = (uint8_t*)calloc(TS, 1); }
    // returns collision step or 0 if rejected/limit
    uint64_t run(const Mach& m, int& colx) {
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2, cap = 2;
        int lo = OFF, hi = OFF + 2;
        uint64_t st = 0, res = 0;
        while (st < LIMIT) {
            int b0 = tape[p0 + OFF], b1 = tape[p1 + OFF];
            const Tr t0 = m.t[0][q0][b0], t1 = m.t[1][q1][b1];
            tape[p0 + OFF] = t0.w;
            if (p1 != p0) tape[p1 + OFF] = t1.w;
            p0 += t0.m; q0 = t0.n; p1 += t1.m; q1 = t1.n; st++;
            if (p0 == p1) { res = st; colx = p0; break; }
            if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
            if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
            int a0 = p0 < 0 ? -p0 : p0, a1 = p1 < 0 ? -p1 : p1, ap = a0 > a1 ? a0 : a1;
            if (ap > cap) cap = ap;
            if ((st & 127) == 0) {
                if (mx0 < mn1 || mx1 < mn0) break;
                bool bad = false;
                if (st <= 512) { bad = ap > 80 || (st == 512 && cap < 5); }
                else if (st <= 2048) { bad = ap > 160 || (st == 2048 && (cap < 12 || mx0 - mn0 < 4 || mx1 - mn1 < 4)); }
                else if (st <= 10240) { bad = ap > 360 || (st == 10240 && cap < 28); }
                else if (st <= 50048) { bad = ap > 800 || (st == 50048 && cap < 65); }
                else if (st <= 250112) { bad = ap > 2000 || (st == 250112 && cap < 140); }
                else if (st <= 1000064) { bad = ap > 4500 || (st == 1000064 && cap < 280); }
                else if (st <= 4000000) { bad = ap > 9000 || (st == 4000000 && cap < 600); }
                else bad = ap > 30000;
                if (bad) break;
            }
        }
        int l = std::min(mn0, mn1) - 1 + OFF, h = std::max(mx0, mx1) + 1 + OFF;
        if (l < 0) l = 0; if (h >= TS) h = TS - 1;
        memset(tape + l, 0, h - l + 1);
        (void)lo; (void)hi;
        return res;
    }
};

static void report(const Mach& m, uint64_t st, int x, const char* tag) {
    if (st < MINLOG && st <= best.load()) return;
    std::lock_guard<std::mutex> lk(pm);
    std::string s = fmt(m);
    if (st > best.load()) {
        best.store(st);
        printf("\n*** [NEW BEST %s] %llu steps (x=%d)\n    %s\n", tag, (unsigned long long)st, x, s.c_str());
    }
    fprintf(out, "%llu\t%d\t%s\n", (unsigned long long)st, x, s.c_str());
    fflush(out); fflush(stdout);
}

static std::set<std::string>* seen;
static std::mutex seen_m;

static void eval(Sim& sim, const Mach& m) {
    tested++;
    int x = 0;
    uint64_t st = sim.run(m, x);
    if (st >= MINLOG || (st > best.load() && st > 1000000)) {
        std::string k = fmt(m);
        { std::lock_guard<std::mutex> lk(seen_m); if (!seen->insert(k).second) return; }
        report(m, st, x, "MUT");
    }
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
    if (argc < 8) { puts("usage: seedfile S K depth topN limit out [threads] [minLog]"); return 1; }
    S = atoi(argv[2]); K = atoi(argv[3]); DEPTH = atoi(argv[4]);
    int topN = atoi(argv[5]); LIMIT = strtoull(argv[6], 0, 10);
    out = fopen(argv[7], "a");
    NT = argc > 8 ? atoi(argv[8]) : 16;
    MINLOG = argc > 9 ? strtoull(argv[9], 0, 10) : 3000000;
    NTR = 2 * S * K;
    std::ifstream f(argv[1]);
    std::vector<std::pair<uint64_t, std::string>> all;
    std::string line;
    while (std::getline(f, line)) {
        uint64_t st; int x; char buf[256];
        if (sscanf(line.c_str(), "%llu\t%d\t%255s", (unsigned long long*)&st, &x, buf) == 3) all.push_back({st, buf});
    }
    std::sort(all.rbegin(), all.rend());
    std::set<std::string> sset; std::vector<Mach> seeds;
    for (auto& pr : all) {
        if ((int)seeds.size() >= topN) break;
        if (!sset.insert(pr.second).second) continue;
        Mach m; if (!parse(pr.second, m)) continue;
        seeds.push_back(m);
    }
    seen = new std::set<std::string>();
    // tasks: (seed, first position, first transition value) + also depth-0 baseline
    struct Tk { int seed, p; int w, d, n; };
    std::vector<Tk> tasks;
    for (int s = 0; s < (int)seeds.size(); s++) {
        tasks.push_back({s, -1, 0, 0, 0});
        for (int p = 0; p < NTR; p++)
            for (int w = 0; w < K; w++) for (int d = 0; d < 2; d++) for (int n = 0; n < S; n++)
                tasks.push_back({s, p, w, d, n});
    }
    printf("seeds=%zu S=%d K=%d depth=%d tasks=%zu limit=%llu\n", seeds.size(), S, K, DEPTH, tasks.size(), (unsigned long long)LIMIT);
    std::atomic<size_t> nxt{0};
    auto t0 = std::chrono::steady_clock::now();
    std::vector<std::thread> pool;
    for (int i = 0; i < NT; i++) pool.emplace_back([&]() {
        Sim sim;
        while (true) {
            size_t i = nxt.fetch_add(1);
            if (i >= tasks.size()) break;
            Tk& tk = tasks[i];
            Mach m = seeds[tk.seed];
            if (tk.p < 0) { eval(sim, m); }
            else {
                int a = tk.p / (S * K), q = (tk.p / K) % S, b = tk.p % K;
                Tr nt = {uint8_t(tk.w), int8_t(tk.d ? -1 : 1), uint8_t(tk.n)};
                Tr old = m.t[a][q][b];
                if (!(nt.w == old.w && nt.m == old.m && nt.n == old.n)) {
                    m.t[a][q][b] = nt;
                    rec(sim, m, tk.p + 1, DEPTH - 1);
                }
            }
            if ((i + 1) % 500 == 0) {
                std::lock_guard<std::mutex> lk(pm);
                double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
                printf("[prog] %zu/%zu %.0fs tested=%llu best=%llu\n", i + 1, tasks.size(), el,
                       (unsigned long long)tested.load(), (unsigned long long)best.load());
            }
        }
    });
    for (auto& t : pool) t.join();
    printf("DONE tested=%llu best=%llu\n", (unsigned long long)tested.load(), (unsigned long long)best.load());
    fclose(out);
}
