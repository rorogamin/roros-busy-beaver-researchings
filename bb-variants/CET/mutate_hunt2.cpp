// mutate_hunt2.cpp — "super duper" seeded mutation hunter for 2-agent CET(S,K).
//  * fused 1-lookup transition table (both agents per step), branch-free writes
//  * 4M-cell tape (+-2M), steps are uint64 (limit up to ~1e13), sqrt(t)-scaled envelope pruning
//  * hill-climb queue: any result >= SEEDLOG becomes a new seed and is mutated too
// Usage: mutate_hunt2.exe <seedfile> <S> <K> <depth> <topN> <stepLimit> <outfile> [threads=16] [minLog=3000000] [seedLog=100000000]
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <fstream>
#include <mutex>
#include <set>
#include <string>
#include <thread>
#include <vector>

static constexpr int TS = 1 << 22, OFF = 1 << 21;
struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach { Tr t[2][4][3]; };
struct Fused { int8_t d0, d1; uint8_t w0, w1, n0, n1; };

static int S, K, DEPTH, NT, NTR;
static uint64_t LIMIT, MINLOG, SEEDLOG;
static std::atomic<uint64_t> best{0}, tested{0};
static std::mutex pm, seen_m, qm;
static FILE* out;
static std::set<std::string> seen;

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
    Sim() { tape = (uint8_t*)calloc(TS, 1); }
    uint64_t run(const Mach& m, int& colx) {
        for (int q0 = 0; q0 < S; q0++) for (int b0 = 0; b0 < K; b0++) for (int q1 = 0; q1 < S; q1++) for (int b1 = 0; b1 < K; b1++) {
            const Tr& a = m.t[0][q0][b0]; const Tr& b = m.t[1][q1][b1];
            tab[((q0 * K + b0) * S + q1) * K + b1] = {a.m, b.m, a.w, b.w, a.n, b.n};
        }
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2, cap = 2;
        uint64_t st = 0, res = 0;
        uint8_t* T = tape + OFF;
        const Fused* tb = tab;
        const int Sk = S * K;
        while (st < LIMIT) {
            bool col = false;
            for (int i = 0; i < 128; i++) {
                const Fused& f = tb[((q0 * K + T[p0]) * S + q1) * K + T[p1]];
                T[p1] = f.w1; T[p0] = f.w0;
                p0 += f.d0; p1 += f.d1; q0 = f.n0; q1 = f.n1;
                if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
                if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
                if (p0 == p1) { st += i + 1; col = true; break; }
            }
            (void)Sk;
            if (col) { res = st; colx = p0; break; }
            st += 128;
            int a0 = std::max(-mn0, mx0), a1 = std::max(-mn1, mx1);
            int ap = std::max(a0, a1); cap = ap;
            if (mx0 < mn1 || mx1 < mn0) break;
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
            if (bad) break;
        }
        int l = std::min(mn0, mn1) - 1 + OFF, h = std::max(mx0, mx1) + 1 + OFF;
        if (l < 0) l = 0; if (h >= TS) h = TS - 1;
        memset(tape + l, 0, h - l + 1);
        return res;
    }
};

struct Tk { Mach base; int p; int w, d, n; int depth; };
static std::deque<Tk> dq;
static std::atomic<int> idle_workers{0};

static void push_seed(const Mach& m, int depth) {
    std::lock_guard<std::mutex> lk(qm);
    Tk t0{m, -1, 0, 0, 0, depth}; dq.push_back(t0);
    for (int p = 0; p < NTR; p++)
        for (int w = 0; w < K; w++) for (int d = 0; d < 2; d++) for (int n = 0; n < S; n++) {
            Tk t{m, p, w, d, n, depth}; dq.push_back(t);
        }
}

static void eval(Sim& sim, const Mach& m) {
    tested++;
    int x = 0;
    uint64_t st = sim.run(m, x);
    if (st >= MINLOG || (st > best.load() && st > 1000000)) {
        std::string k = fmt(m);
        { std::lock_guard<std::mutex> lk(seen_m); if (!seen.insert(k).second) return; }
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
    if (argc < 8) { puts("usage: seedfile S K depth topN limit out [threads] [minLog] [seedLog]"); return 1; }
    S = atoi(argv[2]); K = atoi(argv[3]); DEPTH = atoi(argv[4]);
    int topN = atoi(argv[5]); LIMIT = strtoull(argv[6], 0, 10);
    out = fopen(argv[7], "a");
    NT = argc > 8 ? atoi(argv[8]) : 16;
    MINLOG = argc > 9 ? strtoull(argv[9], 0, 10) : 3000000;
    SEEDLOG = argc > 10 ? strtoull(argv[10], 0, 10) : 100000000;
    NTR = 2 * S * K;
    std::ifstream f(argv[1]);
    std::vector<std::pair<uint64_t, std::string>> all;
    std::string line;
    while (std::getline(f, line)) {
        uint64_t st; int x; char buf[256];
        if (sscanf(line.c_str(), "%llu\t%d\t%255s", (unsigned long long*)&st, &x, buf) == 3) all.push_back({st, buf});
    }
    std::sort(all.rbegin(), all.rend());
    std::set<std::string> sset; int ns = 0;
    for (auto& pr : all) {
        if (ns >= topN) break;
        if (!sset.insert(pr.second).second) continue;
        Mach m; if (!parse(pr.second, m)) continue;
        seen.insert(fmt(m)); push_seed(m, DEPTH); ns++;
    }
    printf("seeds=%d S=%d K=%d depth=%d tasks=%zu limit=%llu seedLog=%llu\n", ns, S, K, DEPTH, dq.size(),
           (unsigned long long)LIMIT, (unsigned long long)SEEDLOG);
    auto t0 = std::chrono::steady_clock::now();
    std::atomic<uint64_t> done{0};
    std::atomic<int> active{NT};
    std::vector<std::thread> pool;
    for (int i = 0; i < NT; i++) pool.emplace_back([&]() {
        Sim sim;
        while (true) {
            Tk tk; bool got = false;
            {
                std::lock_guard<std::mutex> lk(qm);
                if (!dq.empty()) { tk = dq.front(); dq.pop_front(); got = true; }
            }
            if (!got) {
                // wait briefly: other workers may still push new seeds
                active--;
                bool again = false;
                for (int w = 0; w < 200 && !again; w++) {
                    if (active.load() == 0) break;
                    std::this_thread::sleep_for(std::chrono::milliseconds(50));
                    std::lock_guard<std::mutex> lk(qm);
                    if (!dq.empty()) again = true;
                }
                if (!again) return;
                active++;
                continue;
            }
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
            if (d % 500 == 0) {
                std::lock_guard<std::mutex> lk(pm);
                double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
                printf("[prog] %llu tasks %.0fs tested=%llu best=%llu\n", (unsigned long long)d, el,
                       (unsigned long long)tested.load(), (unsigned long long)best.load());
            }
        }
    });
    for (auto& t : pool) t.join();
    printf("DONE tested=%llu best=%llu\n", (unsigned long long)tested.load(), (unsigned long long)best.load());
    fclose(out);
}
