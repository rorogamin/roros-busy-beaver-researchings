// mutate_hunt5.cpp
// Fast decoupled run-skip + budget-ladder mutation hunter for 2-agent CET(S,K).
// Fixes from mutate_hunt4:
//   - Fine-grained depth-2 task enqueueing (each worker evaluates ~133 machines per task instead of ~17,500)
//   - Initial tier-0 budget B0 = 4,000,000 steps (climbs 4M -> 32M -> 256M -> 2B -> 16B -> 128B -> 1T)
//   - Behavioral deduplication by (stepCount, mirror-normalized collisionX) so we only climb distinct trajectories
//   - Reachable-transition masking so depth-1 mutations only touch transitions that are actually executed
//   - Progress printed every 10 seconds of wall-clock time

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
static std::atomic<uint64_t> best{0}, tested{0}, escaped{0}, heur_dead{0}, limit_hit{0}, unique_seeds_pushed{0};
static std::mutex pm, qm, seen_m;
static FILE* out;
static std::unordered_set<uint64_t> seen_surv, seen_log, seen_behavior;
static std::chrono::steady_clock::time_point last_print_time;

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

static uint64_t behavior_sig(uint64_t st, int colx) {
    uint64_t ax = (uint64_t)std::min(std::abs(colx), std::abs(colx - 2));
    return (st * 1000003ULL) ^ (ax * 0x9E3779B97F4A7C15ULL);
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
    uint8_t* tape;
    Fused tab[4 * 3 * 4 * 3];
    int8_t loop_dir[2][4][3];
    int dlo = OFF, dhi = OFF;
    bool escR[2][4], escL[2][4];

    Sim() { tape = (uint8_t*)calloc(TS, 1); }
    ~Sim() { free(tape); }

    void clear() {
        if (dhi >= dlo) memset(tape + dlo, 0, dhi - dlo + 1);
        dlo = OFF; dhi = OFF;
    }

    void prep(const Mach& m) {
        for (int q0 = 0; q0 < S; q0++) for (int b0 = 0; b0 < K; b0++)
            for (int q1 = 0; q1 < S; q1++) for (int b1 = 0; b1 < K; b1++) {
                const Tr& a = m.t[0][q0][b0]; const Tr& b = m.t[1][q1][b1];
                tab[((q0 * K + b0) * S + q1) * K + b1] = {a.m, b.m, a.w, b.w, a.n, b.n};
            }
        memset(loop_dir, 0, sizeof(loop_dir));
        for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) for (int b = 0; b < K; b++) {
            const Tr& tr = m.t[a][q][b];
            if (tr.w == b && tr.n == q) loop_dir[a][q][b] = tr.m;
        }
        for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) {
            bool seenst[4] = {0, 0, 0, 0}; bool okR = true, okL = true; int cur = q;
            while (!seenst[cur]) {
                seenst[cur] = true;
                const Tr& t = m.t[a][cur][0];
                if (t.m > 0) okL = false; else okR = false;
                cur = t.n;
            }
            escR[a][q] = okR; escL[a][q] = okL;
        }
    }

    uint32_t find_reachable_mask(const Mach& m) {
        clear();
        uint8_t* T = tape + OFF;
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn = 0, mx = 2;
        uint32_t mask = 0;
        for (int st = 0; st < 100000; st++) {
            uint8_t b0 = T[p0], b1 = T[p1];
            mask |= (1u << (q0 * K + b0));
            mask |= (1u << (S * K + q1 * K + b1));
            const Tr& t0 = m.t[0][q0][b0];
            const Tr& t1 = m.t[1][q1][b1];
            T[p1] = t1.w; T[p0] = t0.w;
            p0 += t0.m; q0 = t0.n;
            p1 += t1.m; q1 = t1.n;
            if (p0 < mn) mn = p0; if (p0 > mx) mx = p0;
            if (p1 < mn) mn = p1; if (p1 > mx) mx = p1;
            if (p0 == p1 || std::max(-mn, mx) > OFF - 16) break;
        }
        dlo = std::min(dlo, mn - 1 + OFF);
        dhi = std::max(dhi, mx + 1 + OFF);
        clear();
        return mask;
    }

    int run(const Mach& m, Cfg& c, uint64_t end, int& colx) {
        prep(m);
        int p0 = c.p0, p1 = c.p1, q0 = c.q0, q1 = c.q1;
        int mn0 = c.mn0, mx0 = c.mx0, mn1 = c.mn1, mx1 = c.mx1;
        uint64_t st = c.st;
        uint8_t* T = tape + OFF;
        const Fused* tb = tab;
        int rc = R_SUSP;
        uint64_t next_check = (st + 512) & ~127ULL;

        while (true) {
            if (st >= end) { rc = (st >= LIMIT) ? R_LIMIT : R_SUSP; break; }

            if (st >= 2048) {
                int dist = std::abs(p0 - p1);
                if (dist >= 24) {
                    uint8_t b0 = T[p0];
                    int8_t d0 = loop_dir[0][q0][b0];
                    if (d0 != 0) {
                        int max_k = (dist - 4) >> 1;
                        uint64_t rem = std::min(end, next_check) - st;
                        if ((uint64_t)max_k > rem) max_k = (int)rem;
                        if (max_k > 8) {
                            int k = 1;
                            uint64_t pat = (uint64_t)b0 * 0x0101010101010101ULL;
                            if (d0 > 0) {
                                while (k + 8 <= max_k && *(const uint64_t*)(T + p0 + k) == pat) k += 8;
                                while (k < max_k && T[p0 + k] == b0) k++;
                            } else {
                                while (k + 8 <= max_k && *(const uint64_t*)(T + p0 - k - 7) == pat) k += 8;
                                while (k < max_k && T[p0 - k] == b0) k++;
                            }
                            if (k > 4) {
                                p0 += d0 * k;
                                if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
                                st += k;
                                for (int i = 0; i < k; i++) {
                                    const Tr& t1 = m.t[1][q1][T[p1]];
                                    T[p1] = t1.w; p1 += t1.m; q1 = t1.n;
                                }
                                if (p1 - k < mn1) mn1 = p1 - k;
                                if (p1 + k > mx1) mx1 = p1 + k;
                                goto check_gate;
                            }
                        }
                    }
                    uint8_t b1 = T[p1];
                    int8_t d1 = loop_dir[1][q1][b1];
                    if (d1 != 0) {
                        int max_k = (dist - 4) >> 1;
                        uint64_t rem = std::min(end, next_check) - st;
                        if ((uint64_t)max_k > rem) max_k = (int)rem;
                        if (max_k > 8) {
                            int k = 1;
                            uint64_t pat = (uint64_t)b1 * 0x0101010101010101ULL;
                            if (d1 > 0) {
                                while (k + 8 <= max_k && *(const uint64_t*)(T + p1 + k) == pat) k += 8;
                                while (k < max_k && T[p1 + k] == b1) k++;
                            } else {
                                while (k + 8 <= max_k && *(const uint64_t*)(T + p1 - k - 7) == pat) k += 8;
                                while (k < max_k && T[p1 - k] == b1) k++;
                            }
                            if (k > 4) {
                                p1 += d1 * k;
                                if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
                                st += k;
                                for (int i = 0; i < k; i++) {
                                    const Tr& t0 = m.t[0][q0][T[p0]];
                                    T[p0] = t0.w; p0 += t0.m; q0 = t0.n;
                                }
                                if (p0 - k < mn0) mn0 = p0 - k;
                                if (p0 + k > mx0) mx0 = p0 + k;
                                goto check_gate;
                            }
                        }
                    }
                }
            }

            {
                int batch = (int)std::min<uint64_t>(128, std::min(end, next_check) - st);
                if (batch <= 0) batch = 1;
                bool col = false;
                for (int i = 0; i < batch; i++) {
                    const Fused& f = tb[((q0 * K + T[p0]) * S + q1) * K + T[p1]];
                    T[p1] = f.w1; T[p0] = f.w0;
                    p0 += f.d0; p1 += f.d1; q0 = f.n0; q1 = f.n1;
                    if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
                    if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
                    if (p0 == p1) { st += i + 1; col = true; break; }
                }
                if (col) { colx = p0; c.st = st; rc = R_HALT; goto done; }
                st += batch;
            }

        check_gate:
            if (st >= next_check) {
                next_check = (st < 4096) ? (st + 128) : (st + 4096);
                int mxv = std::max(mx0, mx1), mnv = std::min(mn0, mn1);
                if ((p0 > p1 && p0 == mxv && !T[p0] && escR[0][q0]) || (p1 > p0 && p1 == mxv && !T[p1] && escR[1][q1]) ||
                    (p0 < p1 && p0 == mnv && !T[p0] && escL[0][q0]) || (p1 < p0 && p1 == mnv && !T[p1] && escL[1][q1])) {
                    rc = R_ESC; goto done;
                }
                if (HEUR) {
                    int ap = std::max(std::max(-mn0, mx0), std::max(-mn1, mx1));
                    if (mx0 < mn1 || mx1 < mn0) { rc = R_DEAD; goto done; }
                    bool bad = false;
                    if (st <= 512) { bad = ap > 80 || (st >= 512 && ap < 5); }
                    else if (st <= 2048) { bad = ap > 160 || (st >= 2048 && (ap < 12 || mx0 - mn0 < 4 || mx1 - mn1 < 4)); }
                    else if (st <= 10240) { bad = ap > 360 || (st >= 10240 && ap < 28); }
                    else if (st <= 50048) { bad = ap > 800 || (st >= 50048 && ap < 65); }
                    else if (st <= 250112) { bad = ap > 2000 || (st >= 250112 && ap < 140); }
                    else if (st <= 1000064) { bad = ap > 4500 || (st >= 1000064 && ap < 280); }
                    else if (st <= 4000000) { bad = ap > 9000 || (st >= 4000000 && ap < 600); }
                    else {
                        double r = std::sqrt((double)st);
                        bad = ap > std::max(9000.0, 2.0 * r) || ap > OFF - 64 || ap < 0.08 * r;
                    }
                    if (bad) { rc = R_DEAD; goto done; }
                } else if (std::max(-mnv, mxv) > OFF - 64) { rc = R_DEAD; goto done; }
            }
        }
    done:
        c.p0 = p0; c.p1 = p1; c.q0 = q0; c.q1 = q1; c.mn0 = mn0; c.mx0 = mx0; c.mn1 = mn1; c.mx1 = mx1; c.st = st;
        int l = std::min(mn0, mn1) - 16 + OFF, h = std::max(mx0, mx1) + 16 + OFF;
        if (l < 0) l = 0; if (h >= TS) h = TS - 1;
        dlo = std::min(dlo, l); dhi = std::max(dhi, h);
        return rc;
    }
};

struct Tk { Mach base; int next_p; int rem_depth; };
static std::deque<Tk> dq;
static std::deque<Job> lev[MAXLEV];
static std::atomic<uint64_t> nsusp{0};

static uint64_t budget(int level) {
    uint64_t b = B0;
    for (int i = 0; i < level; i++) b *= 8;
    return std::min(b, LIMIT);
}

static void push_seed(Sim& reach_sim, const Mach& m, int depth) {
    uint32_t rmask = reach_sim.find_reachable_mask(m);
    std::lock_guard<std::mutex> lk(qm);
    unique_seeds_pushed++;
    dq.push_back({m, NTR, 0}); // evaluate baseline seed itself
    for (int p1 = 0; p1 < NTR; p1++) {
        // First mutation must touch a transition that is actually reachable!
        if (!(rmask & (1u << p1))) continue;
        int a1 = p1 / (S * K), q1 = (p1 / K) % S, b1 = p1 % K;
        Tr old1 = m.t[a1][q1][b1];
        for (int w1 = 0; w1 < K; w1++) for (int d1 = 0; d1 < 2; d1++) for (int n1 = 0; n1 < S; n1++) {
            Tr nt1 = {uint8_t(w1), int8_t(d1 ? -1 : 1), uint8_t(n1)};
            if (nt1.w == old1.w && nt1.m == old1.m && nt1.n == old1.n) continue;
            Mach m1 = m;
            m1.t[a1][q1][b1] = nt1;
            if (depth <= 1) {
                dq.push_back({m1, NTR, 0});
            } else {
                dq.push_back({m1, p1 + 1, 0}); // evaluate depth-1 mutant
                for (int p2 = p1 + 1; p2 < NTR; p2++) {
                    int a2 = p2 / (S * K), q2 = (p2 / K) % S, b2 = p2 % K;
                    Tr old2 = m1.t[a2][q2][b2];
                    for (int w2 = 0; w2 < K; w2++) for (int d2 = 0; d2 < 2; d2++) for (int n2 = 0; n2 < S; n2++) {
                        Tr nt2 = {uint8_t(w2), int8_t(d2 ? -1 : 1), uint8_t(n2)};
                        if (nt2.w == old2.w && nt2.m == old2.m && nt2.n == old2.n) continue;
                        Mach m2 = m1;
                        m2.t[a2][q2][b2] = nt2;
                        dq.push_back({m2, p2 + 1, depth - 2});
                    }
                }
            }
        }
    }
}

static void record(Sim& sim, const Mach& m, uint64_t st, int x) {
    uint64_t h = hsh(m);
    { std::lock_guard<std::mutex> lk(seen_m); if (!seen_log.insert(h).second) return; }
    uint64_t bsig = behavior_sig(st, x);
    bool novel_behavior = false;
    {
        std::lock_guard<std::mutex> lk(seen_m);
        novel_behavior = seen_behavior.insert(bsig).second;
    }
    if (!novel_behavior && st <= best.load()) return;

    std::string k = fmt(m);
    {
        std::lock_guard<std::mutex> lk(pm);
        if (st > best.load()) {
            best.store(st);
            printf("\n*** [NEW RECORD] %llu steps (x=%d) ***\n    %s\n", (unsigned long long)st, x, k.c_str());
        } else if (st >= 50000000ULL) {
            printf("  [50M+ Novel] %llu steps (x=%d): %s\n", (unsigned long long)st, x, k.c_str());
        }
        fprintf(out, "%llu\t%d\t%s\n", (unsigned long long)st, x, k.c_str());
        fflush(out); fflush(stdout);
    }
    if (st >= SEEDLOG && novel_behavior) push_seed(sim, m, DEPTH);
}

static void handle(Sim& sim, const Mach& m, Cfg& c, int level, int rc, int colx) {
    if (rc == R_HALT) { if (c.st >= MINLOG || c.st > best.load()) record(sim, m, c.st, colx); }
    else if (rc == R_ESC) escaped++;
    else if (rc == R_DEAD) heur_dead++;
    else if (rc == R_LIMIT) { limit_hit++; }
    else {
        uint64_t h = hsh(m);
        { std::lock_guard<std::mutex> lk(seen_m); if (!seen_surv.insert(h ^ (uint64_t)level * 0x9E3779B97F4A7C15ULL).second) return; }
        Job j; j.m = m; j.c = c; j.level = level + 1;
        int l = std::min(c.mn0, c.mn1) - 8, hh = std::max(c.mx0, c.mx1) + 8;
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
    if (left <= 0) return;
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
    SEEDLOG = argc > 10 ? strtoull(argv[10], 0, 10) : 50000000;
    B0 = argc > 11 ? strtoull(argv[11], 0, 10) : 4000000ULL;
    B0 = (B0 / 128) * 128;
    for (int i = 12; i < argc; i++) if (!strcmp(argv[i], "noheur")) HEUR = false;
    NTR = 2 * S * K;

    std::ifstream f(argv[1]);
    struct SeedRow { uint64_t st; int x; std::string s; };
    std::vector<SeedRow> all;
    std::string line;
    while (std::getline(f, line)) {
        uint64_t st; int x; char buf[256];
        if (sscanf(line.c_str(), "%llu\t%d\t%255s", (unsigned long long*)&st, &x, buf) == 3) {
            all.push_back({st, x, buf});
        }
    }
    std::sort(all.begin(), all.end(), [](const SeedRow& a, const SeedRow& b) { return a.st > b.st; });

    Sim init_sim;
    int ns = 0;
    for (auto& row : all) {
        if (ns >= topN) break;
        if (row.st > best.load()) best.store(row.st);
        uint64_t bsig = behavior_sig(row.st, row.x);
        if (!seen_behavior.insert(bsig).second) continue;
        Mach m; if (!parse(row.s, m)) continue;
        seen_log.insert(hsh(m));
        push_seed(init_sim, m, DEPTH);
        ns++;
    }

    printf("Distinct seeds=%d | S=%d K=%d depth=%d | fine tasks=%zu | limit=%llu | budget0=%llu | best=%llu\n",
           ns, S, K, DEPTH, dq.size(), (unsigned long long)LIMIT, (unsigned long long)B0, (unsigned long long)best.load());

    auto t0 = std::chrono::steady_clock::now();
    last_print_time = t0;
    std::atomic<uint64_t> done{0};
    std::atomic<int> active{NT};
    std::vector<std::thread> pool;
    for (int i = 0; i < NT; i++) pool.emplace_back([&]() {
        Sim sim;
        while (true) {
            Tk tk; Job job; int kind = 0;
            {
                std::lock_guard<std::mutex> lk(qm);
                for (int l = 1; l < MAXLEV; l++) {
                    if (lev[l].size() >= 8 || (dq.empty() && !lev[l].empty())) {
                        job = std::move(lev[l].front()); lev[l].pop_front(); kind = 2; break;
                    }
                }
                if (!kind && !dq.empty()) { tk = dq.front(); dq.pop_front(); kind = 1; }
                if (!kind) {
                    for (int l = 1; l < MAXLEV; l++) if (!lev[l].empty()) {
                        job = std::move(lev[l].front()); lev[l].pop_front(); kind = 2; break;
                    }
                }
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
                rec(sim, m, tk.next_p, tk.rem_depth);
                ++done;
            } else {
                sim.clear();
                memcpy(sim.tape + OFF + job.lo, job.seg.data(), job.seg.size());
                sim.dlo = std::min(sim.dlo, OFF + job.lo); sim.dhi = std::max(sim.dhi, OFF + job.lo + (int)job.seg.size() - 1);
                int x = 0;
                int rc = sim.run(job.m, job.c, budget(job.level), x);
                handle(sim, job.m, job.c, job.level, rc, x);
            }

            auto now = std::chrono::steady_clock::now();
            if (std::chrono::duration<double>(now - last_print_time).count() >= 10.0) {
                std::lock_guard<std::mutex> lk(pm);
                if (std::chrono::duration<double>(now - last_print_time).count() >= 10.0) {
                    last_print_time = now;
                    double el = std::chrono::duration<double>(now - t0).count();
                    size_t ql = 0; std::string lv;
                    { std::lock_guard<std::mutex> lq(qm); ql = dq.size(); for (int l = 1; l < MAXLEV; l++) if (!lev[l].empty()) lv += " L" + std::to_string(l) + "=" + std::to_string(lev[l].size()); }
                    printf("[%.0fs] tasks=%llu (left=%zu, seeds=%llu) tested=%llu (%.0f/s) esc=%llu heurDead=%llu susp=%llu |%s | best=%llu\n",
                           el, (unsigned long long)done.load(), ql, (unsigned long long)unique_seeds_pushed.load(),
                           (unsigned long long)tested.load(), tested.load() / std::max(1.0, el),
                           (unsigned long long)escaped.load(), (unsigned long long)heur_dead.load(),
                           (unsigned long long)nsusp.load(), lv.c_str(), (unsigned long long)best.load());
                }
            }
        }
    });
    for (auto& t : pool) t.join();
    printf("DONE tested=%llu esc=%llu heurDead=%llu limit=%llu best=%llu\n", (unsigned long long)tested.load(),
           (unsigned long long)escaped.load(), (unsigned long long)heur_dead.load(), (unsigned long long)limit_hit.load(),
           (unsigned long long)best.load());
    fclose(out);
}
