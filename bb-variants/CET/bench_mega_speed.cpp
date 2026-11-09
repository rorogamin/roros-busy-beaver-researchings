#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <chrono>
#include <algorithm>
#include <fstream>

static constexpr int TS = 1 << 23, OFF = 1 << 22;

struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach2 { Tr t[2][4][3]; };
struct Fused2 { int8_t d0, d1; uint8_t w0, w1, n0, n1; };

static bool check_stationary(const Mach2& m, int ag, int mn, int mx, int p_init, int q_init, const uint8_t* T) {
    if (mx - mn > 16 || p_init < mn || p_init > mx) return false;
    int len = mx - mn + 1;
    uint8_t lt[32];
    for (int i = 0; i < len; i++) lt[i] = T ? T[mn + i] : 0;
    int p = p_init - mn;
    int q = q_init;
    uint64_t seen[33];
    int scnt = 0;

    for (int t = 0; t < 32; t++) {
        uint64_t tbits = 0;
        for (int i = 0; i < len; i++) tbits = (tbits << 1) | (lt[i] & 1);
        uint64_t key = (tbits << 10) | (p << 4) | q;
        for (int k = 0; k < scnt; k++) {
            if (seen[k] == key) return true;
        }
        seen[scnt++] = key;
        const Tr& tr = m.t[ag][q][lt[p]];
        lt[p] = tr.w;
        p += tr.m;
        q = tr.n;
        if (p < 0 || p >= len) return false;
    }
    return false;
}

static bool check_blank_drift(const Mach2& m, int ag, int q0, int dir) {
    uint8_t lt[129]{};
    int p = 64, q = q0;
    int hist_p[65];
    int hist_q[65];
    hist_p[0] = 64; hist_q[0] = q0;

    for (int t = 1; t <= 48; t++) {
        const Tr& tr = m.t[ag][q][lt[p]];
        lt[p] = tr.w;
        p += tr.m;
        q = tr.n;
        if ((p - 64) * dir < 0) return false;
        hist_p[t] = p; hist_q[t] = q;
        for (int pt = 0; pt < t; pt++) {
            if (hist_q[pt] == q) {
                int dp = (p - hist_p[pt]) * dir;
                if (dp > 0) {
                    bool valid = true;
                    for (int k = pt; k <= t; k++) {
                        if ((hist_p[k] - hist_p[pt]) * dir < 0) {
                            valid = false; break;
                        }
                    }
                    if (valid) return true;
                }
            }
        }
    }
    return false;
}

struct FastSimMega {
    uint8_t* tape;
    Fused2 tab[4 * 3 * 4 * 3];
    bool driftR[2][4], driftL[2][4];
    int dlo = OFF, dhi = OFF;

    FastSimMega() { tape = (uint8_t*)calloc(TS, 1); }
    ~FastSimMega() { free(tape); }

    void clear() {
        if (dhi >= dlo) memset(tape + dlo, 0, dhi - dlo + 1);
        dlo = OFF; dhi = OFF;
    }

    void prep(const Mach2& m, int S, int K) {
        for (int q0 = 0; q0 < S; q0++) for (int b0 = 0; b0 < K; b0++)
            for (int q1 = 0; q1 < S; q1++) for (int b1 = 0; b1 < K; b1++) {
                const Tr& a = m.t[0][q0][b0]; const Tr& b = m.t[1][q1][b1];
                tab[((q0 * K + b0) * S + q1) * K + b1] = {a.m, b.m, a.w, b.w, a.n, b.n};
            }
        for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) {
            driftR[a][q] = check_blank_drift(m, a, q, +1);
            driftL[a][q] = check_blank_drift(m, a, q, -1);
        }
    }

    uint64_t run(const Mach2& m, int S, int K, uint64_t limit, int& colx) {
        // STEP 0 EARLY PRUNER (Instant 0-step decision!)
        prep(m, S, K);
        if (driftL[0][0] && driftR[1][0]) return 0;
        if (driftR[1][0] && check_stationary(m, 0, -1, 0, 0, 0, nullptr)) return 0;
        if (driftL[0][0] && check_stationary(m, 1, 2, 3, 2, 0, nullptr)) return 0;

        clear();
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2;
        uint64_t st = 0;
        uint8_t* T = tape + OFF;
        const Fused2* tb = tab;
        uint64_t next_check = 64;
        uint64_t ret = UINT64_MAX;

        while (st < limit) {
            uint64_t block_end = std::min(limit, next_check);
            while (st < block_end) {
                int batch = (int)std::min<uint64_t>(64, block_end - st);
                bool col = false;
                // ULTRA-TIGHT BRANCHLESS INNER LOOP
                for (int i = 0; i < batch; i++) {
                    const Fused2& f = tb[((q0 * K + T[p0]) * S + q1) * K + T[p1]];
                    T[p1] = f.w1; T[p0] = f.w0;
                    p0 += f.d0; p1 += f.d1; q0 = f.n0; q1 = f.n1;
                    mn0 = std::min(mn0, p0); mx0 = std::max(mx0, p0);
                    mn1 = std::min(mn1, p1); mx1 = std::max(mx1, p1);
                    if (p0 == p1) { st += i + 1; col = true; break; }
                }
                if (col) { colx = p0; ret = st; goto done; }
                st += batch;
            }

            if (st >= next_check) {
                next_check = (st < 1024) ? (st + 64) : (st < 1000000ULL) ? (st + 4096) : (st + 4194304);

                // DOUBLE CYCLER DECIDER
                if (mx0 < mn1) {
                    if (driftL[0][q0] && driftR[1][q1]) { ret = 0; goto done; }
                    if (driftR[1][q1] && p1 >= mx1 && !T[p1] && check_stationary(m, 0, mn0, mx0, p0, q0, T)) { ret = 0; goto done; }
                    if (driftL[0][q0] && p0 <= mn0 && !T[p0] && check_stationary(m, 1, mn1, mx1, p1, q1, T)) { ret = 0; goto done; }
                } else if (mx1 < mn0) {
                    if (driftL[1][q1] && driftR[0][q0]) { ret = 0; goto done; }
                    if (driftR[0][q0] && p0 >= mx0 && !T[p0] && check_stationary(m, 1, mn1, mx1, p1, q1, T)) { ret = 0; goto done; }
                    if (driftL[1][q1] && p1 <= mn1 && !T[p1] && check_stationary(m, 0, mn0, mx0, p0, q0, T)) { ret = 0; goto done; }
                }

                // Envelope sublinear pruning
                int ap = std::max(std::max(-mn0, mx0), std::max(-mn1, mx1));
                if (st >= 512 && ap < 5) { ret = 0; goto done; }
                if (st >= 2048 && (ap < 12 || mx0 - mn0 < 4 || mx1 - mn1 < 4)) { ret = 0; goto done; }
                if (st >= 10240 && ap < 28) { ret = 0; goto done; }
                if (st >= 50048 && ap < 65) { ret = 0; goto done; }
            }
        }
    done:
        int l = std::min(mn0, mn1) - 4 + OFF, h = std::max(mx0, mx1) + 4 + OFF;
        if (l < 0) l = 0; if (h >= TS) h = TS - 1;
        dlo = std::min(dlo, l); dhi = std::max(dhi, h);
        return ret;
    }
};

static bool parse_mach(const std::string& line, Mach2& m, int S, int K) {
    std::string s = line;
    size_t tab = s.find_last_of("\t ");
    if (tab != std::string::npos) s = s.substr(tab + 1);
    while (!s.empty() && (s.back() == '\r' || s.back() == '\n' || s.back() == ' ')) s.pop_back();
    if (s.find('|') == std::string::npos) return false;
    memset(&m, 0, sizeof(m));
    int a = 0, q = 0, b = 0;
    for (size_t i = 0; i < s.size(); i++) {
        char c = s[i];
        if (c == '|') { a = 1; q = 0; b = 0; }
        else if (c == '_') { q++; b = 0; }
        else {
            if (a >= 2 || q >= S || b >= K) return false;
            m.t[a][q][b].w = c - '0';
            m.t[a][q][b].m = s[i + 1] == 'R' ? 1 : -1;
            m.t[a][q][b].n = s[i + 2] - 'A';
            b++; i += 2;
        }
    }
    return true;
}

int main() {
    std::ifstream in("cet3_all_seeds.txt");
    std::string line;
    std::vector<Mach2> seeds;
    while (std::getline(in, line)) {
        Mach2 m;
        if (parse_mach(line, m, 3, 2)) seeds.push_back(m);
    }
    printf("Benchmarking on %zu seeds with single-thread Mega simulator...\n", seeds.size());
    FastSimMega sim;
    auto t0 = std::chrono::steady_clock::now();
    uint64_t tested = 0;
    int NTR = 2 * 3 * 2;
    int colx = 0;

    for (size_t s = 0; s < std::min<size_t>(seeds.size(), 20); s++) {
        const auto& base = seeds[s];
        for (int p1 = 0; p1 < NTR; p1++) {
            int a1 = p1 / 6, q1 = (p1 / 2) % 3, b1 = p1 % 2;
            Tr old1 = base.t[a1][q1][b1];
            for (int w1 = 0; w1 < 2; w1++) for (int d1 = 0; d1 < 2; d1++) for (int n1 = 0; n1 < 3; n1++) {
                Mach2 m = base;
                m.t[a1][q1][b1] = {uint8_t(w1), int8_t(d1 ? -1 : 1), uint8_t(n1)};
                for (int p2 = p1 + 1; p2 < NTR; p2++) {
                    int a2 = p2 / 6, q2 = (p2 / 2) % 3, b2 = p2 % 2;
                    Tr old2 = m.t[a2][q2][b2];
                    for (int w2 = 0; w2 < 2; w2++) for (int d2 = 0; d2 < 2; d2++) for (int n2 = 0; n2 < 3; n2++) {
                        m.t[a2][q2][b2] = {uint8_t(w2), int8_t(d2 ? -1 : 1), uint8_t(n2)};
                        sim.run(m, 3, 2, 1000000ULL, colx);
                        tested++;
                    }
                    m.t[a2][q2][b2] = old2;
                }
            }
            // m.t[a1][q1][b1] = old1;
        }
    }
    auto t1 = std::chrono::steady_clock::now();
    double el = std::chrono::duration<double>(t1 - t0).count();
    printf("Tested %llu machines in %.3f seconds (%.0f machines/sec on 1 SINGLE THREAD!)\n",
           (unsigned long long)tested, el, tested / el);
    printf("Extrapolated 16 threads = %.0f machines/sec!\n", (tested / el) * 16.0);
    return 0;
}
