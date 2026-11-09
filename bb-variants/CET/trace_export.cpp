// trace_export.cpp — native fast simulator that exports a space-time trace for the web viewer.
// Usage: trace_export.exe <machine> <out.bin> [snapshots=3000] [S] [K]   (2 agents, positions 0 and 2)
// Binary (little-endian): u32 magic 0x43455431 | u32 nSnap | u32 S | u32 K | f64 finalStep | i32 collisionPos
//   per snapshot: f64 step | i32 p0 | i32 q0 | i32 p1 | i32 q1 | i32 nInt | nInt x (i32 start, i32 end, i32 val)
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
static constexpr int TS = 1 << 23, OFF = 1 << 22;
struct F { int8_t d0, d1; uint8_t w0, w1, n0, n1; };
int main(int argc, char** argv) {
    if (argc < 3) { puts("usage: trace_export machine out.bin [snaps] "); return 1; }
    std::string M = argv[1];
    int nsnap = argc > 3 ? atoi(argv[3]) : 3000;
    int S = 1, K = 2;
    { int u = 0; for (char c : M) { if (c == '_') u++; if (c == '|') break; } S = u + 1;
      int a = M.find('|'); std::string A = M.substr(0, a); K = (int)(A.size() - (S - 1)) / (3 * S); }
    int w[2][4][3], d[2][4][3], n[2][4][3]; int a = 0, q = 0, b = 0;
    for (size_t i = 0; i < M.size(); i++) {
        char c = M[i];
        if (c == '|') { a = 1; q = 0; b = 0; } else if (c == '_') { q++; b = 0; }
        else { w[a][q][b] = c - '0'; d[a][q][b] = M[i + 1] == 'R' ? 1 : -1; n[a][q][b] = M[i + 2] - 'A'; b++; i += 2; }
    }
    std::vector<F> tab(S * K * S * K);
    for (int q0 = 0; q0 < S; q0++) for (int b0 = 0; b0 < K; b0++) for (int q1 = 0; q1 < S; q1++) for (int b1 = 0; b1 < K; b1++)
        tab[((q0 * K + b0) * S + q1) * K + b1] = {(int8_t)d[0][q0][b0], (int8_t)d[1][q1][b1], (uint8_t)w[0][q0][b0], (uint8_t)w[1][q1][b1], (uint8_t)n[0][q0][b0], (uint8_t)n[1][q1][b1]};
    int8_t loop_dir[2][4][3]{};
    for (int ag = 0; ag < 2; ag++) for (int q = 0; q < S; q++) for (int b = 0; b < K; b++)
        if (w[ag][q][b] == b && n[ag][q][b] == q) loop_dir[ag][q][b] = (int8_t)d[ag][q][b];
    uint8_t* tape = (uint8_t*)calloc(TS, 1); uint8_t* T = tape + OFF;
    // pass 1: total steps
    auto sim = [&](uint64_t total, int nsn, FILE* fo, uint64_t& fin, int& fx, uint32_t& snap_cnt) {
        memset(tape, 0, TS);
        int p0 = 0, p1 = 2, q0 = 0, q1 = 0;
        int mn = 0, mx = 2; uint64_t st = 0;
        uint64_t stride = total ? std::max<uint64_t>(1, total / nsn) : UINT64_MAX, next = stride;
        snap_cnt = 0;
        auto snap = [&]() {
            snap_cnt++;
            std::vector<int> iv; int cnt = 0, runS = 0, runV = 0; bool in = false;
            for (int x = mn; x <= mx; x++) {
                int v = T[x];
                if (v) { if (!in) { in = true; runS = x; runV = v; } else if (v != runV) { iv.insert(iv.end(), {runS, x - 1, runV}); cnt++; runS = x; runV = v; } }
                else if (in) { iv.insert(iv.end(), {runS, x - 1, runV}); cnt++; in = false; }
            }
            if (in) { iv.insert(iv.end(), {runS, mx, runV}); cnt++; }
            double sd = (double)st; fwrite(&sd, 8, 1, fo);
            int hdr[5] = {p0, q0, p1, q1, cnt}; fwrite(hdr, 4, 5, fo);
            if (cnt) fwrite(iv.data(), 4, iv.size(), fo);
        };
        if (fo) snap();
        while (true) {
            int dist = std::abs(p0 - p1);
            if (dist >= 24) {
                uint8_t b0 = T[p0]; int8_t d0 = loop_dir[0][q0][b0];
                if (d0 != 0) {
                    int max_k = (dist - 4) >> 1;
                    if (fo && next > st && (uint64_t)max_k > next - st) max_k = (int)(next - st);
                    if (max_k > 8) {
                        int k = 1; uint64_t pat = (uint64_t)b0 * 0x0101010101010101ULL;
                        if (d0 > 0) { while (k + 8 <= max_k && *(const uint64_t*)(T + p0 + k) == pat) k += 8; while (k < max_k && T[p0 + k] == b0) k++; }
                        else { while (k + 8 <= max_k && *(const uint64_t*)(T + p0 - k - 7) == pat) k += 8; while (k < max_k && T[p0 - k] == b0) k++; }
                        if (k > 4) {
                            p0 += d0 * k; if (p0 < mn) mn = p0; if (p0 > mx) mx = p0; st += k;
                            for (int i = 0; i < k; i++) { int b1 = T[p1]; T[p1] = w[1][q1][b1]; p1 += d[1][q1][b1]; q1 = n[1][q1][b1]; if (p1 < mn) mn = p1; if (p1 > mx) mx = p1; }
                            if (fo && st >= next) { snap(); next += stride; }
                            continue;
                        }
                    }
                }
                uint8_t b1 = T[p1]; int8_t d1 = loop_dir[1][q1][b1];
                if (d1 != 0) {
                    int max_k = (dist - 4) >> 1;
                    if (fo && next > st && (uint64_t)max_k > next - st) max_k = (int)(next - st);
                    if (max_k > 8) {
                        int k = 1; uint64_t pat = (uint64_t)b1 * 0x0101010101010101ULL;
                        if (d1 > 0) { while (k + 8 <= max_k && *(const uint64_t*)(T + p1 + k) == pat) k += 8; while (k < max_k && T[p1 + k] == b1) k++; }
                        else { while (k + 8 <= max_k && *(const uint64_t*)(T + p1 - k - 7) == pat) k += 8; while (k < max_k && T[p1 - k] == b1) k++; }
                        if (k > 4) {
                            p1 += d1 * k; if (p1 < mn) mn = p1; if (p1 > mx) mx = p1; st += k;
                            for (int i = 0; i < k; i++) { int b0 = T[p0]; T[p0] = w[0][q0][b0]; p0 += d[0][q0][b0]; q0 = n[0][q0][b0]; if (p0 < mn) mn = p0; if (p0 > mx) mx = p0; }
                            if (fo && st >= next) { snap(); next += stride; }
                            continue;
                        }
                    }
                }
            }
            const F& f = tab[((q0 * K + T[p0]) * S + q1) * K + T[p1]];
            T[p1] = f.w1; T[p0] = f.w0; p0 += f.d0; p1 += f.d1; q0 = f.n0; q1 = f.n1; st++;
            if (p0 < mn) mn = p0; if (p1 < mn) mn = p1; if (p0 > mx) mx = p0; if (p1 > mx) mx = p1;
            if (p0 == p1) { fin = st; fx = p0; if (fo) snap(); return; }
            if (fo && st >= next) { snap(); next += stride; }
        }
    };
    uint64_t total = 0; int fx = 0; uint32_t ns = 0;
    sim(0, 0, nullptr, total, fx, ns);
    printf("total steps = %llu, collision x = %d\n", (unsigned long long)total, fx);
    FILE* fo = fopen(argv[2], "wb");
    uint32_t hd[4] = {0x43455431u, 0, (uint32_t)S, (uint32_t)K}; fwrite(hd, 4, 4, fo);
    double fs = (double)total; fwrite(&fs, 8, 1, fo); fwrite(&fx, 4, 1, fo);
    uint64_t t2; int x2; sim(total, nsnap, fo, t2, x2, ns);
    long end = ftell(fo); fseek(fo, 4, SEEK_SET);
    fwrite(&ns, 4, 1, fo); fclose(fo);
    printf("wrote %s (%ld bytes, %u snapshots)\n", argv[2], end, ns);
}
