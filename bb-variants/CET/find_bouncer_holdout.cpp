#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
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

int main() {
    std::ifstream in("cet3_all_seeds.txt");
    std::string line;
    std::vector<Mach2> seeds;
    while (std::getline(in, line)) {
        Mach2 m;
        if (parse_mach(line, m, 3, 2)) seeds.push_back(m);
    }
    uint8_t* tape = (uint8_t*)calloc(TS, 1);
    uint8_t* T = tape + OFF;
    int found = 0;
    for (const auto& base : seeds) {
        // Run seed
        memset(tape, 0, TS);
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2;
        int dir_changes0 = 0, last_d0 = 0;
        bool collided = false;
        for (int st = 1; st <= 2000000; st++) {
            int b0 = T[p0], b1 = T[p1];
            Tr tr0 = base.t[0][q0][b0];
            Tr tr1 = base.t[1][q1][b1];
            T[p1] = tr1.w; T[p0] = tr0.w;
            p0 += tr0.m; p1 += tr1.m;
            q0 = tr0.n; q1 = tr1.n;
            if (tr0.m != last_d0) { dir_changes0++; last_d0 = tr0.m; }
            if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
            if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
            if (p0 == p1) { collided = true; break; }
        }
        if (!collided && dir_changes0 > 100 && mx0 >= mn1) {
            found++;
            printf("\n=======================================================\n");
            printf(">>> [CET(3) INTERACTING BOUNCER HOLDOUT #%d] <<<\n", found);
            printf("Machine: %s\n", fmt2(base, 3, 2).c_str());
            printf("Stats: Survived 2,000,000 steps without collision!\n");
            printf("Overlap: Agent 0 reached [%d, %d], Agent 1 reached [%d, %d]\n", mn0, mx0, mn1, mx1);
            printf("Agent 0 direction reversals: %d\n", dir_changes0);
            printf("=======================================================\n");
            if (found >= 2) break;
        }
    }
    free(tape);
    return 0;
}
