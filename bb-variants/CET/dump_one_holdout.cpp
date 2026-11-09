#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <deque>
#include <fstream>
#include <iostream>
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

// Exactly the Sim2 from hunt_all_families.cpp
struct Sim2 {
    uint8_t* tape;
    Fused2 tab[4 * 3 * 4 * 3];
    int8_t loop_dir[2][4][3];
    int8_t wloop_dir[2][4][3];
    uint8_t wloop_val[2][4][3];
    int8_t w2_dir[2][4][3];
    uint8_t w2_v0[2][4][3], w2_v1[2][4][3];
    bool escR[2][4], escL[2][4];
    int dlo, dhi;

    Sim2() {
        tape = (uint8_t*)calloc(TS, 1);
        dlo = OFF; dhi = OFF;
    }
    ~Sim2() { free(tape); }

    static bool check_ballistic_escape(const Mach2& m, int a, int q0, int dir) {
        uint8_t ltape[65]{};
        int lp = 0, lq = q0;
        for (int t = 1; t <= 32; t++) {
            const Tr& tr = m.t[a][lq][ltape[lp + 32]];
            ltape[lp + 32] = tr.w;
            lp += tr.m;
            lq = tr.n;
            if (lp * dir < t) return false;
        }
        return true;
    }

    static bool check_translated_cycler_escape(const Mach2& m, int a, int q0, int dir, const uint8_t* T, int p_ag, int other_p) {
        int dist = (p_ag - other_p) * dir;
        if (dist < 48) return false;
        uint8_t lt[129];
        for (int i = -64; i <= 64; i++) lt[i + 64] = T[p_ag + i];
        int lp = 0, lq = q0;
        int p_at_24 = 0, q_at_24 = 0;
        for (int t = 1; t <= 80; t++) {
            if (lp < -60 || lp > 60) break;
            const Tr& tr = m.t[a][lq][lt[lp + 64]];
            lt[lp + 64] = tr.w;
            lp += tr.m;
            lq = tr.n;
            if (lp * dir < -4) return false;
            if (t == 24) { p_at_24 = lp; q_at_24 = lq; }
            if (t > 24 && lq == q_at_24) {
                int dp = (lp - p_at_24) * dir;
                int dt = t - 24;
                if (dp > 0 && dp == dt) return true;
            }
        }
        return false;
    }

    void prep(const Mach2& m, int S, int K) {
        for (int q0 = 0; q0 < S; q0++) for (int b0 = 0; b0 < K; b0++)
            for (int q1 = 0; q1 < S; q1++) for (int b1 = 0; b1 < K; b1++) {
                const Tr& a = m.t[0][q0][b0]; const Tr& b = m.t[1][q1][b1];
                tab[((q0 * K + b0) * S + q1) * K + b1] = {a.m, b.m, a.w, b.w, a.n, b.n};
            }
        memset(loop_dir, 0, sizeof(loop_dir));
        memset(wloop_dir, 0, sizeof(wloop_dir));
        memset(w2_dir, 0, sizeof(w2_dir));
        for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) for (int b = 0; b < K; b++) {
            const Tr& tr = m.t[a][q][b];
            if (tr.w == b && tr.n == q) loop_dir[a][q][b] = tr.m;
            if (tr.n == q) {
                wloop_dir[a][q][b] = tr.m;
                wloop_val[a][q][b] = tr.w;
            }
        }
        for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) {
            escR[a][q] = check_ballistic_escape(m, a, q, +1);
            escL[a][q] = check_ballistic_escape(m, a, q, -1);
        }
    }

    uint64_t run(const Mach2& m, int S, int K, uint64_t limit, int& colx) {
        memset(tape, 0, TS);
        prep(m, S, K);
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2;
        int min_nz = 0, max_nz = 0;
        bool has_nz = false;
        uint8_t* T = tape + OFF;
        uint64_t st = 0;
        uint64_t next_check = 128;
        int last_growth_ap = 2;
        uint64_t last_growth_st = 0;
        uint64_t ret = UINT64_MAX;

        while (st < limit) {
            uint64_t block_end = std::min(limit, next_check);
            while (st < block_end) {
                const Fused2& f = tab[((q0 * K + T[p0]) * S + q1) * K + T[p1]];
                T[p1] = f.w1; T[p0] = f.w0;
                p0 += f.d0; p1 += f.d1;
                q0 = f.n0; q1 = f.n1;
                st++;
                if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
                if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
                if (p0 == p1) { colx = p0; return st; }
            }

            if (st >= next_check) {
                next_check = (st < 4096) ? (st + 128) : (st < 1000000ULL) ? (st + 4096) : (st + 4194304);
                if (p0 > p1 && !T[p0] && escR[0][q0]) return 0;
                if (p1 > p0 && !T[p1] && escR[1][q1]) return 0;
                if (p0 < p1 && !T[p0] && escL[0][q0]) return 0;
                if (p1 < p0 && !T[p1] && escL[1][q1]) return 0;

                int ap = std::max(std::max(-mn0, mx0), std::max(-mn1, mx1));
                if (ap > last_growth_ap) {
                    last_growth_ap = ap;
                    last_growth_st = st;
                } else if (st - last_growth_st > std::max<uint64_t>(50000ULL, (uint64_t)ap * 8ULL)) {
                    return 0; // trapped in finite loop
                }
            }
        }
        return UINT64_MAX; // Survived limit!
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
    printf("Scanning first seeds and mutations for machines that survive >10,000,000 steps without collision...\n");
    Sim2 sim;
    int found = 0;
    int NTR = 2 * 3 * 2;
    for (const auto& base : seeds) {
        for (int p = 0; p < NTR; p++) {
            int a = p / 6, q = (p / 2) % 3, b = p % 2;
            Tr old = base.t[a][q][b];
            for (int w = 0; w < 2; w++) for (int d = 0; d < 2; d++) for (int n = 0; n < 3; n++) {
                Mach2 m = base;
                m.t[a][q][b] = {uint8_t(w), int8_t(d ? -1 : 1), uint8_t(n)};
                int cx = 0;
                uint64_t st = sim.run(m, 3, 2, 10000000ULL, cx);
                if (st == UINT64_MAX) {
                    found++;
                    std::string mstr = fmt2(m, 3, 2);
                    printf("\n=======================================================\n");
                    printf(">>> [CET(3) HOLDOUT #%d FOUND] <<<\n", found);
                    printf("Machine: %s\n", mstr.c_str());
                    printf("Status: Survived 10,000,000+ steps with ZERO collision!\n");
                    printf("=======================================================\n");
                    fflush(stdout);
                    if (found >= 2) return 0;
                }
            }
        }
    }
    return 0;
}
