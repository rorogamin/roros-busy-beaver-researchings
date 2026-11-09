// hunt_all_families.cpp
// Unified multi-family mutation + hill-climbing hunter for:
//   1. CET(2,3)  : 2 Agents, 2 States, 3 Symbols (pos [0, 2])
//   2. CET(4)    : 2 Agents, 4 States, 2 Symbols (pos [0, 2])
//   3. MCET(3)   : 3 Agents, 3 States, 2 Symbols (pos [0, 2, 4], haltRule = all 3 converge)
//   4. CET(3)    : 2 Agents, 3 States, 2 Symbols (pos [0, 2])
//
// Key design:
//   - Two-phase execution per family (no thread ever gets tied up in multi-hour non-halters
//     while fresh mutants are waiting):
//     * Phase A (Fast Breadth Sweep): Evaluates all fresh mutants up to B_FAST (50,000,000 steps)
//       using decoupled 64-bit run-skipping + exact escape proof + sublinear envelope pruning.
//       Any machine halting with a new record or novel high step count is immediately logged and
//       hill-climbed! Machines surviving past B_FAST are queued as holdouts.
//     * Phase B (Deep Holdout Climb): Runs the top surviving holdouts up to B_DEEP (10,000,000,000 steps).

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
#include <functional>
#include <mutex>
#include <string>
#include <thread>
#include <unordered_set>
#include <vector>

static constexpr int TS = 1 << 22, OFF = 1 << 21;

struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach2 { Tr t[2][4][3]; };
struct Mach3 { Tr t[3][3][2]; };
struct Fused2 { int8_t d0, d1; uint8_t w0, w1, n0, n1; };

static std::string fmt2(const Mach2& m, int S, int K) {
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

static bool parse2(const std::string& str, Mach2& m) {
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

static uint64_t hsh2(const Mach2& m, int S, int K) {
    uint64_t h = 1469598103934665603ULL;
    for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) for (int b = 0; b < K; b++) {
        const Tr& t = m.t[a][q][b];
        h = (h ^ (t.w | (t.m > 0 ? 4 : 0) | (t.n << 3))) * 1099511628211ULL;
    }
    return h;
}

static uint64_t bsig(uint64_t st, int colx) {
    uint64_t ax = (uint64_t)std::min(std::abs(colx), std::abs(colx - 2));
    return (st * 1000003ULL) ^ (ax * 0x9E3779B97F4A7C15ULL);
}

struct Sim2 {
    uint8_t* tape;
    Fused2 tab[4 * 3 * 4 * 3];
    int8_t loop_dir[2][4][3];
    int8_t wloop_dir[2][4][3];
    uint8_t wloop_val[2][4][3];
    int8_t w2_dir[2][4][3];
    uint8_t w2_v0[2][4][3], w2_v1[2][4][3];
    struct Osc3 { int8_t dir; uint8_t cur_sym, leave_sym, head_sym; };
    Osc3 osc3[2][4][3];
    bool escR[2][4], escL[2][4];
    bool driftR[2][4], driftL[2][4];
    int dlo = OFF, dhi = OFF;

    Sim2() { tape = (uint8_t*)calloc(TS, 1); }
    ~Sim2() { free(tape); }

    void clear() {
        if (dhi >= dlo) memset(tape + dlo, 0, dhi - dlo + 1);
        dlo = OFF; dhi = OFF;
    }

    // Exact Translated-Cycler / Ballistic Escape Detector (checks up to 32 steps on blank tape):
    // Returns true if agent `a` starting at cell `p0` in state `q0` on blank tape ahead of `other_p`
    // enters a cycle on blank tape whose net velocity is 1 cell/step away (or stays strictly ahead of
    // any cell `other_p` could ever reach at 1 cell/step)!
    static bool check_ballistic_escape(const Mach2& m, int a, int q0, int dir) {
        // Sound 1-cell/step ballistic escape detector on blank tape:
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

    // Exact Translated-Cycler Escape Detector at boundary `p_ag` when beyond all non-zero tape:
    // Simulates agent `a` locally on its own written symbols for 96 steps; if after 32 warm-up steps
    // it repeats its state at speed 1 cell/step away (`dp == dt`), it can never be caught!
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

    void prep(const Mach2& m, int S, int K) {
        for (int q0 = 0; q0 < S; q0++) for (int b0 = 0; b0 < K; b0++)
            for (int q1 = 0; q1 < S; q1++) for (int b1 = 0; b1 < K; b1++) {
                const Tr& a = m.t[0][q0][b0]; const Tr& b = m.t[1][q1][b1];
                tab[((q0 * K + b0) * S + q1) * K + b1] = {a.m, b.m, a.w, b.w, a.n, b.n};
            }
        memset(loop_dir, 0, sizeof(loop_dir));
        memset(wloop_dir, 0, sizeof(wloop_dir));
        memset(w2_dir, 0, sizeof(w2_dir));
        memset(osc3, 0, sizeof(osc3));
        for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) for (int b = 0; b < K; b++) {
            const Tr& tr = m.t[a][q][b];
            if (tr.w == b && tr.n == q) loop_dir[a][q][b] = tr.m;
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
        for (int a = 0; a < 2; a++) for (int q = 0; q < S; q++) {
            escR[a][q] = check_ballistic_escape(m, a, q, +1);
            escL[a][q] = check_ballistic_escape(m, a, q, -1);
            driftR[a][q] = check_blank_drift(m, a, q, +1);
            driftL[a][q] = check_blank_drift(m, a, q, -1);
        }
    }

    // Returns: >0 = halted at step, 0 = rejected/escaped, UINT64_MAX = survived past limit!
    uint64_t run(const Mach2& m, int S, int K, uint64_t limit, int& colx) {
        prep(m, S, K);
        if (driftL[0][0] && driftR[1][0]) return 0;
        if (driftR[1][0] && check_stationary(m, 0, -1, 0, 0, 0, nullptr)) return 0;
        if (driftL[0][0] && check_stationary(m, 1, 2, 3, 2, 0, nullptr)) return 0;

        clear();
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2;
        int min_nz = 0, max_nz = 0; // actual non-zero tape bounds!
        bool has_nz = false;
        uint64_t st = 0;
        uint8_t* T = tape + OFF;
        const Fused2* tb = tab;
        uint64_t next_check = 64;
        uint64_t ret = UINT64_MAX;

        int last_growth_ap = 0;
        uint64_t last_growth_st = 0;

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
                        int endp = p + wd * (k1 - 1);
                        if (wv != c) {
                            if (wd > 0) memset(T + p, wv, k1);
                            else memset(T + endp, wv, k1);
                        }
                        if (wv) {
                            int lo = std::min(p, endp), hi = std::max(p, endp);
                            if (!has_nz) { has_nz = true; min_nz = lo; max_nz = hi; }
                            else { if (lo < min_nz) min_nz = lo; if (hi > max_nz) max_nz = hi; }
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
                        int endp = p + d2 * (k2 - 1);
                        if (v0 != c || v1 != c) {
                            if (v0 == v1) {
                                if (d2 > 0) memset(T + p, v0, k2);
                                else memset(T + endp, v0, k2);
                            } else {
                                for (int j = 0; j < k2; j += 2) {
                                    T[p + d2 * j] = v0;
                                    T[p + d2 * (j + 1)] = v1;
                                }
                            }
                        }
                        if (v0 || v1) {
                            int lo = std::min(p, endp), hi = std::max(p, endp);
                            if (!has_nz) { has_nz = true; min_nz = lo; max_nz = hi; }
                            else { if (lo < min_nz) min_nz = lo; if (hi > max_nz) max_nz = hi; }
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
                                    int endp = p + o.dir * mj;
                                    if (o.leave_sym != b_ahead || o.cur_sym != o.leave_sym) {
                                        if (o.dir > 0) memset(T + p, o.leave_sym, mj);
                                        else memset(T + p - mj + 1, o.leave_sym, mj);
                                    }
                                    if (o.leave_sym || o.head_sym) {
                                        int lo = std::min(p, endp), hi = std::max(p, endp);
                                        if (!has_nz) { has_nz = true; min_nz = lo; max_nz = hi; }
                                        else { if (lo < min_nz) min_nz = lo; if (hi > max_nz) max_nz = hi; }
                                    }
                                    p = endp;
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
                const Tr& t1 = m.t[ag][q][c];
                T[p] = t1.w;
                if (t1.w) {
                    if (!has_nz) { has_nz = true; min_nz = max_nz = p; }
                    else { if (p < min_nz) min_nz = p; if (p > max_nz) max_nz = p; }
                }
                p += t1.m;
                q = t1.n;
                rem--;
            }
        };

        while (st < limit) {
            if (!has_nz || p0 > max_nz) {
                if (p0 > p1 && !T[p0] && escR[0][q0]) { ret = 0; goto done; }
            }
            if (!has_nz || p1 > max_nz) {
                if (p1 > p0 && !T[p1] && escR[1][q1]) { ret = 0; goto done; }
            }
            if (!has_nz || p0 < min_nz) {
                if (p0 < p1 && !T[p0] && escL[0][q0]) { ret = 0; goto done; }
            }
            if (!has_nz || p1 < min_nz) {
                if (p1 < p0 && !T[p1] && escL[1][q1]) { ret = 0; goto done; }
            }

            if (st >= 2048) {
                int dist = std::abs(p0 - p1);
                if (dist >= 16) {
                    int max_k = (dist - 4) >> 1;
                    uint64_t rem = std::min(limit, next_check) - st;
                    if ((uint64_t)max_k > rem) max_k = (int)rem;
                    if (max_k > 4) {
                        uint8_t b0 = T[p0];
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
                                uint8_t wv0 = wloop_val[0][q0][b0];
                                int end0 = p0 + wd0 * (k - 1);
                                if (wv0 != b0) {
                                    if (wd0 > 0) memset(T + p0, wv0, k);
                                    else memset(T + end0, wv0, k);
                                }
                                if (wv0) {
                                    int lo0 = std::min(p0, end0), hi0 = std::max(p0, end0);
                                    if (!has_nz) { has_nz = true; min_nz = lo0; max_nz = hi0; }
                                    else { if (lo0 < min_nz) min_nz = lo0; if (hi0 > max_nz) max_nz = hi0; }
                                }
                                p0 += wd0 * k;
                                if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
                                st += k;
                                advance_one(1, p1, q1, k);
                                if (p1 - k < mn1) mn1 = p1 - k;
                                if (p1 + k > mx1) mx1 = p1 + k;
                                goto check_gate;
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
                                int end0 = p0 + d2_0 * (k - 1);
                                if (v0 != b0 || v1 != b0) {
                                    if (v0 == v1) {
                                        if (d2_0 > 0) memset(T + p0, v0, k);
                                        else memset(T + end0, v0, k);
                                    } else {
                                        for (int j = 0; j < k; j += 2) { T[p0 + d2_0 * j] = v0; T[p0 + d2_0 * (j + 1)] = v1; }
                                    }
                                }
                                if (v0 || v1) {
                                    int lo0 = std::min(p0, end0), hi0 = std::max(p0, end0);
                                    if (!has_nz) { has_nz = true; min_nz = lo0; max_nz = hi0; }
                                    else { if (lo0 < min_nz) min_nz = lo0; if (hi0 > max_nz) max_nz = hi0; }
                                }
                                p0 += d2_0 * k;
                                if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
                                st += k;
                                advance_one(1, p1, q1, k);
                                if (p1 - k < mn1) mn1 = p1 - k;
                                if (p1 + k > mx1) mx1 = p1 + k;
                                goto check_gate;
                            }
                        }

                        uint8_t b1 = T[p1];
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
                                uint8_t wv1 = wloop_val[1][q1][b1];
                                int end1 = p1 + wd1 * (k - 1);
                                if (wv1 != b1) {
                                    if (wd1 > 0) memset(T + p1, wv1, k);
                                    else memset(T + end1, wv1, k);
                                }
                                if (wv1) {
                                    int lo1 = std::min(p1, end1), hi1 = std::max(p1, end1);
                                    if (!has_nz) { has_nz = true; min_nz = lo1; max_nz = hi1; }
                                    else { if (lo1 < min_nz) min_nz = lo1; if (hi1 > max_nz) max_nz = hi1; }
                                }
                                p1 += wd1 * k;
                                if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
                                st += k;
                                advance_one(0, p0, q0, k);
                                if (p0 - k < mn0) mn0 = p0 - k;
                                if (p0 + k > mx0) mx0 = p0 + k;
                                goto check_gate;
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
                                int end1 = p1 + d2_1 * (k - 1);
                                if (v0 != b1 || v1 != b1) {
                                    if (v0 == v1) {
                                        if (d2_1 > 0) memset(T + p1, v0, k);
                                        else memset(T + end1, v0, k);
                                    } else {
                                        for (int j = 0; j < k; j += 2) { T[p1 + d2_1 * j] = v0; T[p1 + d2_1 * (j + 1)] = v1; }
                                    }
                                }
                                if (v0 || v1) {
                                    int lo1 = std::min(p1, end1), hi1 = std::max(p1, end1);
                                    if (!has_nz) { has_nz = true; min_nz = lo1; max_nz = hi1; }
                                    else { if (lo1 < min_nz) min_nz = lo1; if (hi1 > max_nz) max_nz = hi1; }
                                }
                                p1 += d2_1 * k;
                                if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
                                st += k;
                                advance_one(0, p0, q0, k);
                                if (p0 - k < mn0) mn0 = p0 - k;
                                if (p0 + k > mx0) mx0 = p0 + k;
                                goto check_gate;
                            }
                        }
                    }
                }
            }

            {
                int batch = (int)std::min<uint64_t>(64, std::min(limit, next_check) - st);
                if (batch <= 0) batch = 1;
                bool col = false;
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

        check_gate:
            if (st >= next_check) {
                next_check = (st < 1024) ? (st + 64) : (st < 1000000ULL) ? (st + 4096) : (st + 4194304);
                // Tightened actual non-zero bounds [min_nz, max_nz]: shrink inward if endpoints were erased to 0!
                while (has_nz && min_nz <= max_nz && T[min_nz] == 0) min_nz++;
                while (has_nz && max_nz >= min_nz && T[max_nz] == 0) max_nz--;
                if (min_nz > max_nz) has_nz = false;

                // === DOUBLE CYCLER & INDEPENDENT TRANSLATED CYCLER DECIDER ===
                if (mx0 < mn1) {
                    if (driftL[0][q0] && driftR[1][q1]) { ret = 0; goto done; }
                    if (driftR[1][q1] && p1 >= mx1 && !T[p1] && check_stationary(m, 0, mn0, mx0, p0, q0, T)) { ret = 0; goto done; }
                    if (driftL[0][q0] && p0 <= mn0 && !T[p0] && check_stationary(m, 1, mn1, mx1, p1, q1, T)) { ret = 0; goto done; }
                } else if (mx1 < mn0) {
                    if (driftL[1][q1] && driftR[0][q0]) { ret = 0; goto done; }
                    if (driftR[0][q0] && p0 >= mx0 && !T[p0] && check_stationary(m, 1, mn1, mx1, p1, q1, T)) { ret = 0; goto done; }
                    if (driftL[1][q1] && p1 <= mn1 && !T[p1] && check_stationary(m, 0, mn0, mx0, p0, q0, T)) { ret = 0; goto done; }
                }

                if ((!has_nz || p0 > max_nz) && p0 > p1 && !T[p0] && (escR[0][q0] || check_translated_cycler_escape(m, 0, q0, +1, T, p0, p1))) { ret = 0; goto done; }
                if ((!has_nz || p1 > max_nz) && p1 > p0 && !T[p1] && (escR[1][q1] || check_translated_cycler_escape(m, 1, q1, +1, T, p1, p0))) { ret = 0; goto done; }
                if ((!has_nz || p0 < min_nz) && p0 < p1 && !T[p0] && (escL[0][q0] || check_translated_cycler_escape(m, 0, q0, -1, T, p0, p1))) { ret = 0; goto done; }
                if ((!has_nz || p1 < min_nz) && p1 < p0 && !T[p1] && (escL[1][q1] || check_translated_cycler_escape(m, 1, q1, -1, T, p1, p0))) { ret = 0; goto done; }
                int ap = std::max(std::max(-mn0, mx0), std::max(-mn1, mx1));
                if (ap > last_growth_ap) {
                    last_growth_ap = ap;
                    last_growth_st = st;
                } else if (st - last_growth_st > std::max<uint64_t>(50000ULL, (uint64_t)ap * 8ULL)) {
                    // Tape span hasn't expanded by even 1 cell in max(50K, 8 * span) steps -> trapped in a bounded region / counter!
                    ret = 0; goto done;
                }
                bool bad = false;
                if (st <= 512) { bad = ap > 80 || (st >= 512 && ap < 5); }
                else if (st <= 2048) { bad = ap > 160 || (st >= 2048 && (ap < 12 || mx0 - mn0 < 4 || mx1 - mn1 < 4)); }
                else if (st <= 10240) { bad = ap > 360 || (st >= 10240 && ap < 28); }
                else if (st <= 50048) { bad = ap > 800 || (st >= 50048 && ap < 65); }
                else if (st <= 250112) { bad = ap > 2000 || (st >= 250112 && ap < 140); }
                else if (st <= 1000064) { bad = ap > 4500 || (st >= 1000064 && ap < 280); }
                else if (st <= 4000000) { bad = ap > 9000 || (st >= 4000000 && ap < 550); }
                else {
                    double r = std::sqrt((double)st);
                    bad = ap > std::max(9000.0, 2.0 * r) || ap > OFF - 64 || ap < 0.08 * r;
                }
                if (bad) { ret = 0; goto done; }
            }
        }
    done:
        int l = std::min(mn0, mn1) - 16 + OFF, h = std::max(mx0, mx1) + 16 + OFF;
        if (l < 0) l = 0; if (h >= TS) h = TS - 1;
        dlo = std::min(dlo, l); dhi = std::max(dhi, h);
        return ret;
    }
};

static void hunt_2agent_family(
    const char* name, const char* seedfile, int S, int K, int depth, int topN,
    uint64_t fast_limit, uint64_t deep_limit, uint64_t min_log, uint64_t seed_log,
    uint64_t initial_best, const char* outfile, int num_threads
) {
    FILE* out = fopen(outfile, "a");
    int NTR = 2 * S * K;
    std::unordered_set<uint64_t> seen_log, seen_beh, seen_holdout;
    std::mutex pm, qm, sm;
    std::atomic<uint64_t> best{initial_best}, tested{0};

    struct Task { Mach2 m; int next_p; int rem_depth; };
    std::deque<Task> dq;
    std::vector<Mach2> holdouts;

    auto push_seed = [&](const Mach2& m, int d) {
        std::lock_guard<std::mutex> lk(qm);
        dq.push_back({m, NTR, 0});
        for (int p1 = 0; p1 < NTR; p1++) {
            int a1 = p1 / (S * K), q1 = (p1 / K) % S, b1 = p1 % K;
            Tr old1 = m.t[a1][q1][b1];
            for (int w1 = 0; w1 < K; w1++) for (int d1 = 0; d1 < 2; d1++) for (int n1 = 0; n1 < S; n1++) {
                Tr nt1 = {uint8_t(w1), int8_t(d1 ? -1 : 1), uint8_t(n1)};
                if (nt1.w == old1.w && nt1.m == old1.m && nt1.n == old1.n) continue;
                Mach2 m1 = m; m1.t[a1][q1][b1] = nt1;
                if (d <= 1) {
                    dq.push_back({m1, NTR, 0});
                } else {
                    dq.push_back({m1, p1 + 1, 0});
                    for (int p2 = p1 + 1; p2 < NTR; p2++) {
                        int a2 = p2 / (S * K), q2 = (p2 / K) % S, b2 = p2 % K;
                        Tr old2 = m1.t[a2][q2][b2];
                        for (int w2 = 0; w2 < K; w2++) for (int d2 = 0; d2 < 2; d2++) for (int n2 = 0; n2 < S; n2++) {
                            Tr nt2 = {uint8_t(w2), int8_t(d2 ? -1 : 1), uint8_t(n2)};
                            if (nt2.w == old2.w && nt2.m == old2.m && nt2.n == old2.n) continue;
                            Mach2 m2 = m1; m2.t[a2][q2][b2] = nt2;
                            dq.push_back({m2, p2 + 1, d - 2});
                        }
                    }
                }
            }
        }
    };

    std::ifstream f(seedfile);
    struct Row { uint64_t st; int x; std::string s; };
    std::vector<Row> rows;
    std::string line;
    while (std::getline(f, line)) {
        uint64_t st; int x; char buf[256];
        if (sscanf(line.c_str(), "%llu\t%d\t%255s", (unsigned long long*)&st, &x, buf) == 3)
            rows.push_back({st, x, buf});
    }
    std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) { return a.st > b.st; });

    int ns = 0;
    for (auto& r : rows) {
        if (ns >= topN) break;
        uint64_t bs = bsig(r.st, r.x);
        if (!seen_beh.insert(bs).second) continue;
        Mach2 m; if (!parse2(r.s, m)) continue;
        seen_log.insert(hsh2(m, S, K));
        push_seed(m, depth);
        ns++;
    }

    printf("\n====================================================================\n");
    printf("[%s] Seeds=%d | S=%d K=%d depth=%d | Tasks=%zu | FastLimit=%llu | Best=%llu\n",
           name, ns, S, K, depth, dq.size(), (unsigned long long)fast_limit, (unsigned long long)best.load());
    printf("====================================================================\n");

    auto t0 = std::chrono::steady_clock::now();
    auto last_p = t0;
    std::atomic<uint64_t> done{0};

    auto eval_m = [&](Sim2& sim, const Mach2& m) {
        tested++;
        int x = 0;
        uint64_t st = sim.run(m, S, K, fast_limit, x);
        if (st == 0) return;
        if (st == UINT64_MAX) {
            uint64_t h = hsh2(m, S, K);
            {
                std::lock_guard<std::mutex> lk(sm);
                if (!seen_holdout.insert(h).second) return;
            }
            // Immediately run 1M-step survivor up to 100,000,000 (100M) steps using our ultra-fast macro-skipping simulator!
            // If it beats the current record (>100M), run it up to 25B steps right here so we find new multi-billion records immediately!
            uint64_t inline_lim = std::min<uint64_t>(deep_limit, 100000000ULL);
            st = sim.run(m, S, K, inline_lim, x);
            if (st == 0) return;
            if (st == UINT64_MAX) {
                uint64_t mid_lim = std::min<uint64_t>(deep_limit, 25000000000ULL);
                st = sim.run(m, S, K, mid_lim, x);
                if (st == 0) return;
                if (st == UINT64_MAX) {
                    std::lock_guard<std::mutex> lk(sm);
                    if (holdouts.size() < 65536) holdouts.push_back(m);
                    return;
                }
            }
        }
        if (st >= min_log || st > best.load()) {
            uint64_t h = hsh2(m, S, K);
            bool novel = false;
            {
                std::lock_guard<std::mutex> lk(sm);
                if (!seen_log.insert(h).second) return;
                novel = seen_beh.insert(bsig(st, x)).second;
            }
            if (!novel && st <= best.load()) return;
            std::string ks = fmt2(m, S, K);
            bool is_new_rec = false;
            {
                std::lock_guard<std::mutex> lk(pm);
                if (st > best.load()) {
                    best.store(st);
                    is_new_rec = true;
                    printf("\n*** [NEW %s RECORD] %llu steps (x=%d) ***\n    %s\n",
                           name, (unsigned long long)st, x, ks.c_str());
                } else if (st >= seed_log) {
                    printf("  [%s High] %llu steps (x=%d): %s\n", name, (unsigned long long)st, x, ks.c_str());
                }
                fprintf(out, "%llu\t%d\t%s\n", (unsigned long long)st, x, ks.c_str());
                fflush(out); fflush(stdout);
            }
            if (is_new_rec || (st >= seed_log && novel)) push_seed(m, depth);
        }
    };

    std::function<void(Sim2&, Mach2&, int, int)> rec = [&](Sim2& sim, Mach2& m, int start, int left) {
        eval_m(sim, m);
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
    };

    std::vector<std::thread> pool;
    for (int i = 0; i < num_threads; i++) pool.emplace_back([&]() {
        Sim2 sim;
        while (true) {
            Task tk;
            {
                std::lock_guard<std::mutex> lk(qm);
                if (dq.empty()) break;
                tk = dq.front(); dq.pop_front();
            }
            Mach2 m = tk.m;
            rec(sim, m, tk.next_p, tk.rem_depth);
            uint64_t d = ++done;
            auto now = std::chrono::steady_clock::now();
            if (std::chrono::duration<double>(now - last_p).count() >= 10.0) {
                std::lock_guard<std::mutex> lk(pm);
                if (std::chrono::duration<double>(now - last_p).count() >= 10.0) {
                    last_p = now;
                    double el = std::chrono::duration<double>(now - t0).count();
                    unsigned long long ql = 0; { std::lock_guard<std::mutex> lq(qm); ql = (unsigned long long)dq.size(); }
                    printf("[%s %.0fs] tasks=%llu (left=%llu) tested=%llu (%.0f/s) holdouts=%llu | best=%llu\n",
                           name, el, (unsigned long long)d, ql, (unsigned long long)tested.load(),
                           tested.load() / std::max(1.0, el), (unsigned long long)holdouts.size(), (unsigned long long)best.load());
                }
            }
        }
    });
    for (auto& t : pool) t.join();

    if (!holdouts.empty() && deep_limit > fast_limit) {
        const uint64_t tiers[] = { 25000000ULL, 250000000ULL, 2500000000ULL, 10000000000ULL, deep_limit };
        std::vector<Mach2> current = std::move(holdouts);
        for (int ti = 0; ti < 5 && !current.empty(); ti++) {
            uint64_t tlim = std::min(tiers[ti], deep_limit);
            if (tlim <= fast_limit) continue;
            printf("[%s Phase B Tier %d] Testing %llu survivors up to %llu steps...\n",
                   name, ti + 1, (unsigned long long)current.size(), (unsigned long long)tlim);
            std::vector<Mach2> next_tier;
            std::atomic<size_t> hi{0};
            std::atomic<size_t> hdone{0};
            auto bt0 = std::chrono::steady_clock::now();
            auto blast_p = bt0;
            // Print those machines in Tier 4 & 5 so we can inspect them!
            if (ti >= 3) {
                for (size_t i = 0; i < current.size(); i++) {
                    printf("  [%s Tier %d Holdout #%llu] %s\n", name, ti + 1, (unsigned long long)i, fmt2(current[i], S, K).c_str());
                }
                fflush(stdout);
            }
            size_t max_next = (ti == 0) ? 256 : (ti == 1) ? 64 : (ti == 2) ? 16 : 8;
            std::vector<std::thread> dpool;
            for (int i = 0; i < num_threads; i++) dpool.emplace_back([&]() {
                Sim2 sim;
                while (true) {
                    size_t idx = hi.fetch_add(1);
                    if (idx >= current.size()) break;
                    const Mach2& m = current[idx];
                    int x = 0;
                    uint64_t st = sim.run(m, S, K, tlim, x);
                    size_t hd = ++hdone;
                    if (st == UINT64_MAX) {
                        std::lock_guard<std::mutex> lk(sm);
                        if (next_tier.size() < max_next) next_tier.push_back(m);
                    } else if (st > 0 && (st >= min_log || st > best.load())) {
                        uint64_t bs = bsig(st, x);
                        bool novel = false;
                        { std::lock_guard<std::mutex> lk(sm); novel = seen_beh.insert(bs).second; }
                        if (novel || st > best.load()) {
                            std::string ks = fmt2(m, S, K);
                            std::lock_guard<std::mutex> lk(pm);
                            if (st > best.load()) {
                                best.store(st);
                                printf("\n*** [NEW %s DEEP RECORD] %llu steps (x=%d) ***\n    %s\n",
                                       name, (unsigned long long)st, x, ks.c_str());
                            } else {
                                printf("  [%s Deep] %llu steps (x=%d): %s\n", name, (unsigned long long)st, x, ks.c_str());
                            }
                            fprintf(out, "%llu\t%d\t%s\n", (unsigned long long)st, x, ks.c_str());
                            fflush(out); fflush(stdout);
                        }
                    }
                    auto now = std::chrono::steady_clock::now();
                    if (std::chrono::duration<double>(now - blast_p).count() >= 10.0) {
                        std::lock_guard<std::mutex> lk(pm);
                        if (std::chrono::duration<double>(now - blast_p).count() >= 10.0) {
                            blast_p = now;
                            double el = std::chrono::duration<double>(now - bt0).count();
                            double pct = 100.0 * (double)hd / (double)current.size();
                            printf("[%s Tier %d %.0fs] %llu / %llu (%.1f%%) | next_survivors=%llu | best=%llu\n",
                                   name, ti + 1, el, (unsigned long long)hd, (unsigned long long)current.size(), pct,
                                   (unsigned long long)next_tier.size(), (unsigned long long)best.load());
                        }
                    }
                }
            });
            // Monitor thread so we print a status heartbeat every 15s even while all workers are inside a 1T-step run!
            std::atomic<bool> tier_done{false};
            std::thread mon([&]() {
                while (!tier_done.load()) {
                    std::this_thread::sleep_for(std::chrono::seconds(1));
                    if (tier_done.load()) break;
                    auto now = std::chrono::steady_clock::now();
                    if (std::chrono::duration<double>(now - blast_p).count() >= 15.0) {
                        std::lock_guard<std::mutex> lk(pm);
                        if (std::chrono::duration<double>(now - blast_p).count() >= 15.0) {
                            blast_p = now;
                            double el = std::chrono::duration<double>(now - bt0).count();
                            size_t hd = hdone.load();
                            double pct = 100.0 * (double)hd / (double)current.size();
                            printf("[%s Tier %d %.0fs] %llu / %llu (%.1f%%) | next_survivors=%llu | best=%llu\n",
                                   name, ti + 1, el, (unsigned long long)hd, (unsigned long long)current.size(), pct,
                                   (unsigned long long)next_tier.size(), (unsigned long long)best.load());
                            fflush(stdout);
                        }
                    }
                }
            });
            for (auto& t : dpool) t.join();
            tier_done.store(true);
            mon.join();
            current = std::move(next_tier);
            if (tlim >= deep_limit) break;
        }
    }
    fclose(out);
}

// =========================================================================================
// MCET(3) — 3 Agents, 3 States, 2 Symbols (pos [0, 2, 4], haltRule = all 3 converge)
// =========================================================================================
static void hunt_mcet3(int num_threads) {
    FILE* out = fopen("mcet3_hunt_champions.txt", "a");
    std::atomic<uint64_t> best{211190346ULL}, tested{0};
    std::mutex pm, qm, sm;
    std::unordered_set<std::string> seen;

    const char* seeds[] = {
        // All-time 211M MCET(3) World Record (all 3 agents collide at x = 13,350):
        "1LC1LA_1RA1RB_0RB0RA|1LC1LB_1RC1RB_0LC0RA|0LA1RB_0RC1RB_0RA1RC",
        // Former MCET(3) 4.23M, 1.30M, 14.4k, 12.7k, 8.89k champions from app.js:
        "1LC1LA_1RA1RB_0RB0RA|1LC1LB_1RB0RA_0LC0RA|0LA1RB_0RC1RB_0RA1RC",
        "1RA0LA_1LC1LB_1LC1LB|1RB1LA_1RC1LB_0LA0RB|0RC1RB_0LA0LC_1RB0LC",
        "1RC0RB_1RB1LA_1LA0LC|0RA0RC_0LC1LA_1LB0RB|1LA1RC_0LB1LA_0LB1RA",
        "1RC0RB_1RC1LB_1LA0LC|0RA0RC_0LC1LA_1LB0RB|1LA0RC_1LB1LA_0LA1RB",
        "1RB0RB_1RC0LC_1LA1RB|0RC1RC_1LA1RC_0LB1RA|0LC0RB_1LB0RB_0RA0RA",
        // Previous seed variants:
        "1LB0RB_1LA0LC_1RC1RA|0RB0LB_1RC0LC_1LA1RB|1LB1LA_1RC0RB_0LA1LC",
        "1LB0RB_1LA0LC_0RC1RA|0RB1LB_1RC0LC_1LA1RB|1LB1LA_1RC0RB_0LA1LC",
        // Hybrid combinations using our 2.75B & 759M & 29.7M CET(3) champion agents:
        "1RB0LC_1LA1RB_0RB1LC|1RB0RB_1LB0LC_1RB0RA|1LB1LA_1RC0RB_0LA1LC",
        "1RB0LC_1LA1RB_0RB1LC|1LB0RC_1RA1LB_0LB1RC|1RB0RB_1LB0LC_1RB0RA",
        "0LB0LC_1RC1RC_1RA0LA|1LB0RC_1RA1LB_0LB1RC|1RB0LC_1LA1RB_0RB1LC",
        "0RB0LC_1LC1RB_1RC1LA|1RB1LB_0RC0RA_1LC0RB|1LB1LA_1RC0RB_0LA1LC",
        "1LC1LA_1RA1RB_0RB0RA|1RB0LC_1LA1RB_0RB1LC|1RB0RB_1LB0LC_1RB0RA",
        "1RB0LC_1LA1RB_0RB1LC|1LC1LB_1RB0RA_0LC0RA|0LA1RB_0RC1RB_0RA1RC"
    };
    const int NS = sizeof(seeds) / sizeof(seeds[0]);

    auto parse3 = [](const char* str, Mach3& m) {
        int a = 0, q = 0, b = 0;
        for (int i = 0; str[i]; i++) {
            char c = str[i];
            if (c == '|') { a++; q = 0; b = 0; continue; }
            if (c == '_') { q++; b = 0; continue; }
            if (c == '0' || c == '1') {
                m.t[a][q][b] = {uint8_t(c - '0'), int8_t(str[i + 1] == 'R' ? 1 : -1), uint8_t(str[i + 2] - 'A')};
                b++; i += 2;
            }
        }
    };
    auto fmt3 = [](const Mach3& m) {
        std::string s;
        for (int a = 0; a < 3; a++) {
            if (a) s += '|';
            for (int q = 0; q < 3; q++) {
                if (q) s += '_';
                for (int b = 0; b < 2; b++) {
                    const Tr& t = m.t[a][q][b];
                    s += char('0' + t.w); s += t.m > 0 ? 'R' : 'L'; s += char('A' + t.n);
                }
            }
        }
        return s;
    };

    struct Task3 { Mach3 m; int p1; int rem; };
    std::deque<Task3> dq;
    auto push_seed3 = [&](const Mach3& m) {
        std::lock_guard<std::mutex> lk(qm);
        dq.push_back({m, 18, 0});
        for (int p1 = 0; p1 < 18; p1++) {
            int a1 = p1 / 6, q1 = (p1 / 2) % 3, b1 = p1 % 2;
            Tr old1 = m.t[a1][q1][b1];
            for (int w1 = 0; w1 < 2; w1++) for (int d1 = 0; d1 < 2; d1++) for (int n1 = 0; n1 < 3; n1++) {
                Tr nt1 = {uint8_t(w1), int8_t(d1 ? -1 : 1), uint8_t(n1)};
                if (nt1.w == old1.w && nt1.m == old1.m && nt1.n == old1.n) continue;
                Mach3 m1 = m; m1.t[a1][q1][b1] = nt1;
                dq.push_back({m1, p1 + 1, 1});
                for (int p2 = p1 + 1; p2 < 18; p2++) {
                    int a2 = p2 / 6, q2 = (p2 / 2) % 3, b2 = p2 % 2;
                    Tr old2 = m1.t[a2][q2][b2];
                    for (int w2 = 0; w2 < 2; w2++) for (int d2 = 0; d2 < 2; d2++) for (int n2 = 0; n2 < 3; n2++) {
                        Tr nt2 = {uint8_t(w2), int8_t(d2 ? -1 : 1), uint8_t(n2)};
                        if (nt2.w == old2.w && nt2.m == old2.m && nt2.n == old2.n) continue;
                        Mach3 m2 = m1; m2.t[a2][q2][b2] = nt2;
                        dq.push_back({m2, p2 + 1, 1});
                    }
                }
            }
        }
    };
    for (int s = 0; s < NS; s++) {
        Mach3 m{}; parse3(seeds[s], m);
        push_seed3(m);
    }

    printf("\n====================================================================\n");
    printf("[MCET(3)] Seeds=%d | Tasks=%zu | Best=%llu\n", NS, dq.size(), (unsigned long long)best.load());
    printf("====================================================================\n");

    auto t0 = std::chrono::steady_clock::now();
    auto last_p = t0;
    std::atomic<uint64_t> done{0};

    std::vector<std::thread> pool;
    for (int th = 0; th < num_threads; th++) pool.emplace_back([&]() {
        uint8_t* tape = (uint8_t*)calloc(TS, 1);
        uint8_t* T = tape + OFF;
        auto sim3 = [&](const Mach3& m, uint64_t limit, int& colx) -> uint64_t {
            int p0 = 0, p1 = 2, p2 = 4, q0 = 0, q1 = 0, q2 = 0;
            int mn0 = 0, mx0 = 0, mn1 = 2, mx1 = 2, mn2 = 4, mx2 = 4;
            uint64_t st = 0, res = UINT64_MAX;
            int last_ap = 0;
            uint64_t last_growth = 0;
            while (st < limit) {
                const Tr& t0 = m.t[0][q0][T[p0]];
                const Tr& t1 = m.t[1][q1][T[p1]];
                const Tr& t2 = m.t[2][q2][T[p2]];
                T[p2] = t2.w; T[p1] = t1.w; T[p0] = t0.w;
                p0 += t0.m; q0 = t0.n;
                p1 += t1.m; q1 = t1.n;
                p2 += t2.m; q2 = t2.n;
                st++;
                if (p0 == p1 && p1 == p2) { colx = p0; res = st; break; }
                if (p0 < mn0) mn0 = p0; if (p0 > mx0) mx0 = p0;
                if (p1 < mn1) mn1 = p1; if (p1 > mx1) mx1 = p1;
                if (p2 < mn2) mn2 = p2; if (p2 > mx2) mx2 = p2;
                if ((st & 511) == 0) {
                    int mnv = std::min({mn0, mn1, mn2}), mxv = std::max({mx0, mx1, mx2});
                    int ap = std::max(-mnv, mxv);
                    if (ap > last_ap) { last_ap = ap; last_growth = st; }
                    else if (st - last_growth > std::max<uint64_t>(40000ULL, (uint64_t)ap * 8ULL)) { res = 0; break; }
                    if (st == 2048 && (ap > 220 || ap < 8)) { res = 0; break; }
                    else if (st == 10240 && (ap > 600 || ap < 20)) { res = 0; break; }
                    else if (st == 250368 && (ap > 3000 || ap < 100)) { res = 0; break; }
                    if (ap > 60000) { res = 0; break; }
                }
            }
            int l = std::min({mn0, mn1, mn2}) - 4 + OFF, h = std::max({mx0, mx1, mx2}) + 4 + OFF;
            if (l < 0) l = 0; if (h >= TS) h = TS - 1;
            memset(tape + l, 0, h - l + 1);
            return res;
        };

        auto eval3 = [&](const Mach3& m) {
            tested++;
            int x = 0;
            uint64_t st = sim3(m, 1000000ULL, x);
            if (st == 0) return;
            if (st == UINT64_MAX) {
                st = sim3(m, 250000000ULL, x);
                if (st == 0 || st == UINT64_MAX) return;
            }
            if (st >= 1000000 || st > best.load()) {
                std::string ks = fmt3(m);
                bool is_new = false;
                { std::lock_guard<std::mutex> lk(sm); is_new = seen.insert(ks).second; }
                if (is_new) {
                    bool climb = false;
                    {
                        std::lock_guard<std::mutex> lk(pm);
                        if (st > best.load()) {
                            best.store(st);
                            climb = true;
                            printf("\n*** [NEW MCET(3) RECORD] %llu steps (all 3 at x=%d) ***\n    %s\n",
                                   (unsigned long long)st, x, ks.c_str());
                        } else if (st >= 10000000) {
                            printf("  [MCET(3) High] %llu steps (x=%d): %s\n", (unsigned long long)st, x, ks.c_str());
                        }
                        fprintf(out, "%llu\t%d\t%s\n", (unsigned long long)st, x, ks.c_str());
                        fflush(out); fflush(stdout);
                    }
                    if (climb) push_seed3(m);
                }
            }
        };

        while (true) {
            Task3 tk;
            {
                std::lock_guard<std::mutex> lk(qm);
                if (dq.empty()) break;
                tk = dq.front(); dq.pop_front();
            }
            Mach3 m = tk.m;
            eval3(m);
            if (tk.rem > 0) {
                for (int p2 = tk.p1; p2 < 18; p2++) {
                    int a2 = p2 / 6, q2 = (p2 / 2) % 3, b2 = p2 % 2;
                    Tr old2 = m.t[a2][q2][b2];
                    for (int w2 = 0; w2 < 2; w2++) for (int d2 = 0; d2 < 2; d2++) for (int n2 = 0; n2 < 3; n2++) {
                        Tr nt2 = {uint8_t(w2), int8_t(d2 ? -1 : 1), uint8_t(n2)};
                        if (nt2.w == old2.w && nt2.m == old2.m && nt2.n == old2.n) continue;
                        m.t[a2][q2][b2] = nt2;
                        eval3(m);
                    }
                    m.t[a2][q2][b2] = old2;
                }
            }
            uint64_t d = ++done;
            auto now = std::chrono::steady_clock::now();
            if (std::chrono::duration<double>(now - last_p).count() >= 10.0) {
                std::lock_guard<std::mutex> lk(pm);
                if (std::chrono::duration<double>(now - last_p).count() >= 10.0) {
                    last_p = now;
                    double el = std::chrono::duration<double>(now - t0).count();
                    unsigned long long ql = 0; { std::lock_guard<std::mutex> lq(qm); ql = (unsigned long long)dq.size(); }
                    printf("[MCET(3) %.0fs] tasks=%llu (left=%llu) tested=%llu (%.0f/s) | best=%llu\n",
                           el, (unsigned long long)d, ql, (unsigned long long)tested.load(),
                           tested.load() / std::max(1.0, el), (unsigned long long)best.load());
                }
            }
        }
        free(tape);
    });
    for (auto& t : pool) t.join();
    fclose(out);
}

int main(int argc, char** argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    int nt = (argc > 1) ? atoi(argv[1]) : 16;

    // 1. CET(3): 1M fast screening pass + inline 100M/25B + 1T tiered long run on survivors!
    hunt_2agent_family(
        "CET(3)", "cet3_all_seeds.txt", 3, 2, 3, 50,
        1000000ULL, 1000000000000ULL, 20000000ULL, 100000000ULL, 3092745703ULL,
        "cet3_all_champions.txt", nt
    );

    // 2. CET(4): 1M fast screening pass + inline 100M/25B + 1T tiered long run on survivors!
    hunt_2agent_family(
        "CET(4)", "cet4_all_champions.txt", 4, 2, 3, 35,
        1000000ULL, 1000000000000ULL, 20000000ULL, 100000000ULL, 4622083548ULL,
        "cet4_all_champions.txt", nt
    );

    // 3. CET(2,3): 1M fast screening pass + inline 100M/25B + 1T tiered long run on survivors!
    hunt_2agent_family(
        "CET(2,3)", "cet23_seeds_merged.txt", 2, 3, 3, 40,
        1000000ULL, 1000000000000ULL, 5000000ULL, 30000000ULL, 1528952999ULL,
        "cet23_all_champions.txt", nt
    );

    // 4. MCET(3): 3 agents, 3 states, 2 symbols
    hunt_mcet3(nt);

    printf("\n=== ALL 4 FAMILIES COMPLETE ===\n");
    return 0;
}
