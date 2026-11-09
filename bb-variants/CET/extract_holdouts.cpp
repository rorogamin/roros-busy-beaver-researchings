#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <fstream>
#include <cmath>

static constexpr int TS = 1 << 23, OFF = 1 << 22;

struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach2 { Tr t[2][4][3]; };
struct Fused2 { int8_t d0, d1; uint8_t w0, w1, n0, n1; };

static std::string fmt2(const Mach2& m, int S, int K) {
    char buf[256]; char* p = buf;
    for (int a = 0; a < 2; a++) {
        if (a > 0) *p++ = '|';
        for (int q = 0; q < S; q++) {
            if (q > 0) *p++ = '_';
            for (int b = 0; b < K; b++) {
                const Tr& tr = m.t[a][q][b];
                *p++ = '0' + tr.w;
                *p++ = tr.m > 0 ? 'R' : 'L';
                *p++ = 'A' + tr.n;
            }
        }
    }
    *p = 0;
    return std::string(buf);
}

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

struct FastSim {
    uint8_t* tape;
    Fused2 tab[4 * 3 * 4 * 3];
    int8_t loop_dir[2][4][3];

    FastSim() { tape = (uint8_t*)calloc(TS, 1); }
    ~FastSim() { free(tape); }

    void prep(const Mach2& m, int S, int K) {
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
    }

    uint64_t run(const Mach2& m, int S, int K, uint64_t limit, int& colx) {
        prep(m, S, K);
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2;
        uint8_t* T = tape + OFF;
        uint64_t st = 0;
        while (st < limit) {
            int dist = std::abs(p0 - p1);
            if (dist >= 16) {
                int max_k = (dist - 4) >> 1;
                uint64_t rem = limit - st;
                if ((uint64_t)max_k > rem) max_k = (int)rem;
                if (max_k > 4) {
                    uint8_t b0 = T[p0]; int8_t d0 = loop_dir[0][q0][b0];
                    if (d0 != 0) {
                        int k = 1;
                        uint64_t pat = (uint64_t)b0 * 0x0101010101010101ULL;
                        if (d0 > 0) { while (k + 8 <= max_k && *(const uint64_t*)(T + p0 + k) == pat) k += 8; while (k < max_k && T[p0 + k] == b0) k++; }
                        else { while (k + 8 <= max_k && *(const uint64_t*)(T + p0 - k - 7) == pat) k += 8; while (k < max_k && T[p0 - k] == b0) k++; }
                        if (k > 4) {
                            p0 += d0 * k; if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0; st += k;
                            for (int i = 0; i < k; i++) { int b1 = T[p1]; T[p1] = m.t[1][q1][b1].w; p1 += m.t[1][q1][b1].m; q1 = m.t[1][q1][b1].n; if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1; }
                            continue;
                        }
                    }
                    uint8_t b1 = T[p1]; int8_t d1 = loop_dir[1][q1][b1];
                    if (d1 != 0) {
                        int k = 1;
                        uint64_t pat = (uint64_t)b1 * 0x0101010101010101ULL;
                        if (d1 > 0) { while (k + 8 <= max_k && *(const uint64_t*)(T + p1 + k) == pat) k += 8; while (k < max_k && T[p1 + k] == b1) k++; }
                        else { while (k + 8 <= max_k && *(const uint64_t*)(T + p1 - k - 7) == pat) k += 8; while (k < max_k && T[p1 - k] == b1) k++; }
                        if (k > 4) {
                            p1 += d1 * k; if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1; st += k;
                            for (int i = 0; i < k; i++) { int b0 = T[p0]; T[p0] = m.t[0][q0][b0].w; p0 += m.t[0][q0][b0].m; q0 = m.t[0][q0][b0].n; if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0; }
                            continue;
                        }
                    }
                }
            }
            const Fused2& f = tab[((q0 * K + T[p0]) * S + q1) * K + T[p1]];
            T[p1] = f.w1; T[p0] = f.w0;
            p0 += f.d0; p1 += f.d1;
            q0 = f.n0; q1 = f.n1;
            st++;
            if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
            if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
            if (p0 == p1) { colx = p0; return st; }
        }
        return UINT64_MAX; // Survived limit without collision!
    }
};

int main() {
    std::ifstream in("cet3_all_seeds.txt");
    std::string line;
    std::vector<Mach2> seeds;
    while (std::getline(in, line)) {
        Mach2 m;
        if (parse_mach(line, m, 3, 2)) seeds.push_back(m);
    }
    printf("Loaded %zu seeds. Searching for genuine holdouts...\n", seeds.size());
    FastSim sim;
    int NTR = 2 * 3 * 2;
    int found = 0;
    for (const auto& base : seeds) {
        // Mutate up to 1 transition
        for (int p = 0; p < NTR; p++) {
            int a = p / 6, q = (p / 2) % 3, b = p % 2;
            Tr old = base.t[a][q][b];
            for (int w = 0; w < 2; w++) for (int d = 0; d < 2; d++) for (int n = 0; n < 3; n++) {
                Mach2 m = base;
                m.t[a][q][b] = {uint8_t(w), int8_t(d ? -1 : 1), uint8_t(n)};
                memset(sim.tape, 0, TS);
                int colx = 0;
                uint64_t st = sim.run(m, 3, 2, 20000000ULL, colx); // 20 million steps!
                if (st == UINT64_MAX) {
                    found++;
                    printf("\n[CET(3) HOLDOUT #%d] (survived >20,000,000 steps without collision)\n", found);
                    printf("Machine: %s\n", fmt2(m, 3, 2).c_str());
                    if (found >= 3) return 0;
                }
            }
        }
    }
    return 0;
}
