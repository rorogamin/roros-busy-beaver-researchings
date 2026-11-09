// test_rle.cpp
// Benchmark RLE Macro-Accelerated Simulator vs Flat Simulator on the 2,755,868,107-step Champion!
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach { Tr t[2][4][3]; };

static bool parse(const std::string& str, Mach& m) {
    for (int a = 0; a < 2; a++) for (int q = 0; q < 4; q++) for (int b = 0; b < 3; b++) m.t[a][q][b] = {0, 1, 0};
    int a = 0, q = 0, b = 0;
    for (size_t i = 0; i < str.size(); i++) {
        char c = str[i];
        if (c == '|') { a++; q = 0; b = 0; continue; }
        if (c == '_') { q++; b = 0; continue; }
        if (c >= '0' && c <= '9' && i + 2 < str.size()) {
            m.t[a][q][b] = {uint8_t(c - '0'), int8_t(str[i + 1] == 'R' ? 1 : -1), uint8_t(str[i + 2] - 'A')};
            b++; i += 2;
        }
    }
    return a == 1;
}

static constexpr int TS = 1 << 22, OFF = 1 << 21;

struct FastSim {
    uint8_t* tape;
    FastSim() { tape = (uint8_t*)calloc(TS, 1); }
    ~FastSim() { free(tape); }

    uint64_t run_macro(const Mach& m, int S, int K, uint64_t limit, int& colx, uint64_t& macro_jumps) {
        // Precompute for each (agent, state, symbol_ahead):
        // 1) 1-step self-loop: wloop_dir[a][q][b] = +1/-1 if (n == q), writing wloop_val[a][q][b]
        // 2) 2-step stride-2 sweep: w2_dir[a][q][b] = +1/-1 if starting on `b` (and next cell `b`), returns to `q` at `2*dir`
        // 3) 3-step stride-1 oscillator ("2 steps forward, 1 step back"): osc3[a][q][b]
        int8_t wloop_dir[2][4][3]{};
        uint8_t wloop_val[2][4][3]{};
        int8_t w2_dir[2][4][3]{};
        uint8_t w2_v0[2][4][3]{}, w2_v1[2][4][3]{};
        struct Osc3 { int8_t dir; uint8_t cur_sym, leave_sym, head_sym; };
        Osc3 osc3[2][4][3]{};

        for (int a = 0; a < 2; a++) {
            for (int q = 0; q < S; q++) {
                for (int b = 0; b < K; b++) {
                    const Tr& tr = m.t[a][q][b];
                    if (tr.n == q) {
                        wloop_dir[a][q][b] = tr.m;
                        wloop_val[a][q][b] = tr.w;
                    } else {
                        const Tr& tr2 = m.t[a][tr.n][b];
                        if (tr2.n == q && tr2.m == tr.m) {
                            w2_dir[a][q][b] = tr.m;
                            w2_v0[a][q][b] = tr.w;
                            w2_v1[a][q][b] = tr2.w;
                        }
                    }
                    for (int c0 = 0; c0 < K; c0++) {
                        for (int dir = -1; dir <= 1; dir += 2) {
                            uint8_t lt[5];
                            lt[2] = uint8_t(c0);
                            if (dir > 0) { lt[3] = lt[4] = uint8_t(b); lt[0] = lt[1] = 255; }
                            else { lt[0] = lt[1] = uint8_t(b); lt[3] = lt[4] = 255; }
                            int lp = 2, lq = q;
                            bool ok = true;
                            for (int s = 0; s < 3; s++) {
                                if (lp < 0 || lp > 4 || lt[lp] == 255) { ok = false; break; }
                                const Tr& ts = m.t[a][lq][lt[lp]];
                                lt[lp] = ts.w;
                                lp += ts.m;
                                lq = ts.n;
                            }
                            if (ok && lp == 2 + dir && lq == q && lt[2 + dir] == c0 && lt[2 + 2 * dir] == b) {
                                osc3[a][q][b] = {int8_t(dir), uint8_t(c0), lt[2], uint8_t(c0)};
                            }
                        }
                    }
                }
            }
        }

        // Helper lambda to advance a single agent `ag` (`p, q`) for `rem` steps using 1-step, 2-step, and 3-step run-skipping!
        uint8_t* T = tape + OFF;
        auto advance_one = [&](int ag, int& p, int& q, int rem) {
            while (rem > 0) {
                uint8_t c = T[p];
                int8_t wd = wloop_dir[ag][q][c];
                if (wd != 0 && rem >= 16) {
                    int k1 = 1;
                    uint64_t pat = (uint64_t)c * 0x0101010101010101ULL;
                    if (wd > 0) {
                        while (k1 + 8 <= rem && *(const uint64_t*)(T + p + k1) == pat) k1 += 8;
                        while (k1 < rem && T[p + k1] == c) k1++;
                    } else {
                        while (k1 + 8 <= rem && *(const uint64_t*)(T + p - k1 - 7) == pat) k1 += 8;
                        while (k1 < rem && T[p - k1] == c) k1++;
                    }
                    if (k1 > 1) {
                        uint8_t wv = wloop_val[ag][q][c];
                        if (wv != c) {
                            if (wd > 0) memset(T + p, wv, k1);
                            else memset(T + p - k1 + 1, wv, k1);
                        }
                        p += wd * k1;
                        rem -= k1;
                        continue;
                    }
                }
                int8_t d2 = w2_dir[ag][q][c];
                if (d2 != 0 && rem >= 16) {
                    int max_k = rem & ~1;
                    int k2 = 0;
                    uint64_t pat = (uint64_t)c * 0x0101010101010101ULL;
                    if (d2 > 0) {
                        while (k2 + 8 <= max_k && *(const uint64_t*)(T + p + k2) == pat) k2 += 8;
                        while (k2 + 2 <= max_k && T[p + k2] == c && T[p + k2 + 1] == c) k2 += 2;
                    } else {
                        while (k2 + 8 <= max_k && *(const uint64_t*)(T + p - k2 - 7) == pat) k2 += 8;
                        while (k2 + 2 <= max_k && T[p - k2] == c && T[p - k2 - 1] == c) k2 += 2;
                    }
                    if (k2 >= 2) {
                        uint8_t v0 = w2_v0[ag][q][c], v1 = w2_v1[ag][q][c];
                        if (v0 != c || v1 != c) {
                            if (v0 == v1) {
                                if (d2 > 0) memset(T + p, v0, k2);
                                else memset(T + p - k2 + 1, v0, k2);
                            } else {
                                for (int j = 0; j < k2; j += 2) {
                                    T[p + d2 * j] = v0;
                                    T[p + d2 * (j + 1)] = v1;
                                }
                            }
                        }
                        p += d2 * k2;
                        rem -= k2;
                        continue;
                    }
                }
                if (rem >= 24) {
                    bool jumped = false;
                    for (int b_ahead = 0; b_ahead < K; b_ahead++) {
                        const Osc3& o = osc3[ag][q][b_ahead];
                        if (o.dir != 0 && c == o.cur_sym && T[p + o.dir] == b_ahead) {
                            int max_m = (rem - 3) / 3;
                            if (max_m > 4) {
                                int m1 = 1;
                                uint64_t pat = (uint64_t)b_ahead * 0x0101010101010101ULL;
                                if (o.dir > 0) {
                                    while (m1 + 8 <= max_m && *(const uint64_t*)(T + p + m1) == pat) m1 += 8;
                                    while (m1 < max_m && T[p + m1] == b_ahead) m1++;
                                } else {
                                    while (m1 + 8 <= max_m && *(const uint64_t*)(T + p - m1 - 7) == pat) m1 += 8;
                                    while (m1 < max_m && T[p - m1] == b_ahead) m1++;
                                }
                                if (m1 > 3) {
                                    int mj = m1 - 1;
                                    if (o.leave_sym != b_ahead || o.cur_sym != o.leave_sym) {
                                        if (o.dir > 0) memset(T + p, o.leave_sym, mj);
                                        else memset(T + p - mj + 1, o.leave_sym, mj);
                                    }
                                    p += o.dir * mj;
                                    T[p] = o.head_sym;
                                    rem -= 3 * mj;
                                    jumped = true;
                                    break;
                                }
                            }
                        }
                    }
                    if (jumped) continue;
                }
                // Unroll single-step advance up to 8 steps if not in a macro jump!
                const Tr& t1 = m.t[ag][q][c];
                T[p] = t1.w;
                p += t1.m;
                q = t1.n;
                rem--;
            }
        };
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn = 0, mx = 2;
        uint64_t st = 0;
        macro_jumps = 0;

        while (st < limit) {
            uint8_t b0 = T[p0];
            uint8_t b1 = T[p1];

            int dist = std::abs(p0 - p1);
            if (dist >= 16) {
                int max_k = (dist - 4) >> 1;
                if ((uint64_t)max_k > limit - st) max_k = (int)(limit - st);
                if (max_k > 4) {
                    // Dual 1-step or 2-step read-only/same-write loop on uniform tape:
                    // If BOTH agents are sweeping across uniform cells in 1-step or 2-step loops:
                    int8_t s0 = wloop_dir[0][q0][b0], s2_0 = w2_dir[0][q0][b0];
                    int8_t s1 = wloop_dir[1][q1][b1], s2_1 = w2_dir[1][q1][b1];
                    int8_t dir0 = s0 ? s0 : s2_0;
                    int8_t dir1 = s1 ? s1 : s2_1;
                    if (dir0 != 0 && dir1 != 0) {
                        // Scan BOTH agents simultaneously 8 cells at a time!
                        int mk = max_k & ~1;
                        int k = 0;
                        uint64_t pat0 = (uint64_t)b0 * 0x0101010101010101ULL;
                        uint64_t pat1 = (uint64_t)b1 * 0x0101010101010101ULL;
                        while (k + 8 <= mk) {
                            const uint8_t* ptr0 = (dir0 > 0) ? (T + p0 + k) : (T + p0 - k - 7);
                            const uint8_t* ptr1 = (dir1 > 0) ? (T + p1 + k) : (T + p1 - k - 7);
                            if (*(const uint64_t*)ptr0 != pat0 || *(const uint64_t*)ptr1 != pat1) break;
                            k += 8;
                        }
                        if (k >= 8) {
                            // Apply write for Agent 0
                            if (s0) {
                                uint8_t wv = wloop_val[0][q0][b0];
                                if (wv != b0) memset((dir0 > 0) ? (T + p0) : (T + p0 - k + 1), wv, k);
                            } else {
                                uint8_t v0 = w2_v0[0][q0][b0], v1 = w2_v1[0][q0][b0];
                                if (v0 != b0 || v1 != b0) {
                                    if (v0 == v1) memset((dir0 > 0) ? (T + p0) : (T + p0 - k + 1), v0, k);
                                    else for (int j = 0; j < k; j += 2) { T[p0 + dir0 * j] = v0; T[p0 + dir0 * (j + 1)] = v1; }
                                }
                            }
                            // Apply write for Agent 1
                            if (s1) {
                                uint8_t wv = wloop_val[1][q1][b1];
                                if (wv != b1) memset((dir1 > 0) ? (T + p1) : (T + p1 - k + 1), wv, k);
                            } else {
                                uint8_t v0 = w2_v0[1][q1][b1], v1 = w2_v1[1][q1][b1];
                                if (v0 != b1 || v1 != b1) {
                                    if (v0 == v1) memset((dir1 > 0) ? (T + p1) : (T + p1 - k + 1), v0, k);
                                    else for (int j = 0; j < k; j += 2) { T[p1 + dir1 * j] = v0; T[p1 + dir1 * (j + 1)] = v1; }
                                }
                            }
                            p0 += dir0 * k;
                            p1 += dir1 * k;
                            st += k;
                            macro_jumps++;
                            if (p0 < mn) mn = p0; if (p0 > mx) mx = p0;
                            if (p1 < mn) mn = p1; if (p1 > mx) mx = p1;
                            continue;
                        }
                    }

                    // Try Agent 0 outer jump (1-step OR 2-step sweep):
                    int8_t wd0 = wloop_dir[0][q0][b0];
                    if (wd0 != 0) {
                        int k = 1;
                        uint64_t pat = (uint64_t)b0 * 0x0101010101010101ULL;
                        if (wd0 > 0) {
                            while (k + 8 <= max_k && *(const uint64_t*)(T + p0 + k) == pat) k += 8;
                            while (k < max_k && T[p0 + k] == b0) k++;
                        } else {
                            while (k + 8 <= max_k && *(const uint64_t*)(T + p0 - k - 7) == pat) k += 8;
                            while (k < max_k && T[p0 - k] == b0) k++;
                        }
                        if (k > 1) {
                            uint8_t wv = wloop_val[0][q0][b0];
                            if (wv != b0) {
                                if (wd0 > 0) memset(T + p0, wv, k);
                                else memset(T + p0 - k + 1, wv, k);
                            }
                            p0 += wd0 * k;
                            st += k;
                            macro_jumps++;
                            advance_one(1, p1, q1, k);
                            if (p0 < mn) mn = p0; if (p0 > mx) mx = p0;
                            if (p1 - k < mn) mn = p1 - k; if (p1 + k > mx) mx = p1 + k;
                            continue;
                        }
                    }
                    int8_t d2_0 = w2_dir[0][q0][b0];
                    if (d2_0 != 0) {
                        int mk2 = max_k & ~1;
                        int k = 0;
                        uint64_t pat = (uint64_t)b0 * 0x0101010101010101ULL;
                        if (d2_0 > 0) {
                            while (k + 8 <= mk2 && *(const uint64_t*)(T + p0 + k) == pat) k += 8;
                            while (k + 2 <= mk2 && T[p0 + k] == b0 && T[p0 + k + 1] == b0) k += 2;
                        } else {
                            while (k + 8 <= mk2 && *(const uint64_t*)(T + p0 - k - 7) == pat) k += 8;
                            while (k + 2 <= mk2 && T[p0 - k] == b0 && T[p0 - k - 1] == b0) k += 2;
                        }
                        if (k >= 2) {
                            uint8_t v0 = w2_v0[0][q0][b0], v1 = w2_v1[0][q0][b0];
                            if (v0 != b0 || v1 != b0) {
                                if (v0 == v1) {
                                    if (d2_0 > 0) memset(T + p0, v0, k);
                                    else memset(T + p0 - k + 1, v0, k);
                                } else {
                                    for (int j = 0; j < k; j += 2) { T[p0 + d2_0 * j] = v0; T[p0 + d2_0 * (j + 1)] = v1; }
                                }
                            }
                            p0 += d2_0 * k;
                            st += k;
                            macro_jumps++;
                            advance_one(1, p1, q1, k);
                            if (p0 < mn) mn = p0; if (p0 > mx) mx = p0;
                            if (p1 - k < mn) mn = p1 - k; if (p1 + k > mx) mx = p1 + k;
                            continue;
                        }
                    }

                    // Try Agent 1 outer jump (1-step OR 2-step sweep):
                    int8_t wd1 = wloop_dir[1][q1][b1];
                    if (wd1 != 0) {
                        int k = 1;
                        uint64_t pat = (uint64_t)b1 * 0x0101010101010101ULL;
                        if (wd1 > 0) {
                            while (k + 8 <= max_k && *(const uint64_t*)(T + p1 + k) == pat) k += 8;
                            while (k < max_k && T[p1 + k] == b1) k++;
                        } else {
                            while (k + 8 <= max_k && *(const uint64_t*)(T + p1 - k - 7) == pat) k += 8;
                            while (k < max_k && T[p1 - k] == b1) k++;
                        }
                        if (k > 1) {
                            uint8_t wv = wloop_val[1][q1][b1];
                            if (wv != b1) {
                                if (wd1 > 0) memset(T + p1, wv, k);
                                else memset(T + p1 - k + 1, wv, k);
                            }
                            p1 += wd1 * k;
                            st += k;
                            macro_jumps++;
                            advance_one(0, p0, q0, k);
                            if (p1 < mn) mn = p1; if (p1 > mx) mx = p1;
                            if (p0 - k < mn) mn = p0 - k; if (p0 + k > mx) mx = p0 + k;
                            continue;
                        }
                    }
                    int8_t d2_1 = w2_dir[1][q1][b1];
                    if (d2_1 != 0) {
                        int mk2 = max_k & ~1;
                        int k = 0;
                        uint64_t pat = (uint64_t)b1 * 0x0101010101010101ULL;
                        if (d2_1 > 0) {
                            while (k + 8 <= mk2 && *(const uint64_t*)(T + p1 + k) == pat) k += 8;
                            while (k + 2 <= mk2 && T[p1 + k] == b1 && T[p1 + k + 1] == b1) k += 2;
                        } else {
                            while (k + 8 <= mk2 && *(const uint64_t*)(T + p1 - k - 7) == pat) k += 8;
                            while (k + 2 <= mk2 && T[p1 - k] == b1 && T[p1 - k - 1] == b1) k += 2;
                        }
                        if (k >= 2) {
                            uint8_t v0 = w2_v0[1][q1][b1], v1 = w2_v1[1][q1][b1];
                            if (v0 != b1 || v1 != b1) {
                                if (v0 == v1) {
                                    if (d2_1 > 0) memset(T + p1, v0, k);
                                    else memset(T + p1 - k + 1, v0, k);
                                } else {
                                    for (int j = 0; j < k; j += 2) { T[p1 + d2_1 * j] = v0; T[p1 + d2_1 * (j + 1)] = v1; }
                                }
                            }
                            p1 += d2_1 * k;
                            st += k;
                            macro_jumps++;
                            advance_one(0, p0, q0, k);
                            if (p1 < mn) mn = p1; if (p1 > mx) mx = p1;
                            if (p0 - k < mn) mn = p0 - k; if (p0 + k > mx) mx = p0 + k;
                            continue;
                        }
                    }
                }
            }

            // Standard single step
            const Tr& t0 = m.t[0][q0][b0];
            const Tr& t1 = m.t[1][q1][b1];
            T[p1] = t1.w;
            T[p0] = t0.w;
            p0 += t0.m; q0 = t0.n;
            p1 += t1.m; q1 = t1.n;
            st++;
            if (p0 == p1) { colx = p0; break; }
            if (p0 < mn) mn = p0; if (p0 > mx) mx = p0;
            if (p1 < mn) mn = p1; if (p1 > mx) mx = p1;
        }
        memset(T + mn - 16, 0, (mx - mn + 33));
        return st;
    }
};

int main() {
    Mach m;
    FastSim sim;
    int colx = 0;
    uint64_t jumps = 0;

    // 1) Test on 4.62B CET(4) champion:
    parse("1LC0LC_1LA1RB_0RB1LC_0RA0RA|1RC0RA_1RA1RB_1LC0RD_0RA0RC", m);
    auto t0 = std::chrono::steady_clock::now();
    uint64_t st = sim.run_macro(m, 4, 2, 10000000000ULL, colx, jumps);
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    printf("[4.62B CET(4) WR] Steps: %llu | colx: %d | Jumps: %llu | Time: %.3f s | Speed: %.2f M steps/s\n",
        (unsigned long long)st, colx, (unsigned long long)jumps, dt, (st / dt) / 1e6);

    // 2) Test on Holdout #1 for 10B steps:
    parse("1LC0RD_1LA1RB_0RB1LC_0RA1LB|1RC0RA_1RA1RB_1LC0RD_0RC0RC", m);
    t0 = std::chrono::steady_clock::now();
    st = sim.run_macro(m, 4, 2, 10000000000ULL, colx, jumps);
    dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    printf("[CET(4) Holdout #1 10B] Steps: %llu | colx: %d | Jumps: %llu | Time: %.3f s | Speed: %.2f M steps/s\n",
        (unsigned long long)st, colx, (unsigned long long)jumps, dt, (st / dt) / 1e6);
    return 0;
}
