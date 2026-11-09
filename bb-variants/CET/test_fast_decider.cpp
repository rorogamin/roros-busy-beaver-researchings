#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <iostream>

struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach2 { Tr t[2][4][3]; };

static bool check_stationary(const Mach2& m, int ag, int mn, int mx, int p_init, int q_init, const uint8_t* T) {
    if (mx - mn > 16 || p_init < mn || p_init > mx) return false;
    int len = mx - mn + 1;
    uint8_t lt[32];
    for (int i = 0; i < len; i++) lt[i] = T[mn + i];
    int p = p_init - mn;
    int q = q_init;
    uint64_t seen[33];
    int scnt = 0;

    for (int t = 0; t < 32; t++) {
        uint64_t tbits = 0;
        for (int i = 0; i < len; i++) tbits = (tbits << 1) | (lt[i] & 1);
        uint64_t key = (tbits << 10) | (p << 4) | q;
        for (int k = 0; k < scnt; k++) {
            if (seen[k] == key) return true; // Exact stationary cycle!
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
    Mach2 m1;
    parse_mach("0LB0RA_0RA0RA_0RA0RA|0RB0RA_0RC0RA_0LA0RA", m1, 3, 2);
    uint8_t tape[100]{};
    uint8_t* T = tape + 50;
    // Test check_stationary on Agent 0:
    bool stat = check_stationary(m1, 0, -1, 0, 0, 0, T);
    printf("Agent 0 check_stationary result: %s\n", stat ? "TRUE (Stationary Cycler!)" : "FALSE");

    bool drift = check_blank_drift(m1, 1, 0, +1);
    printf("Agent 1 check_blank_drift result: %s\n", drift ? "TRUE (Translated Cycler!)" : "FALSE");
    return 0;
}
