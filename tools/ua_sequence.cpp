// Greedy U-a-U-free sequence over {0,1,2,...}.
//
// Maintains R = reverse(S) and the Z-array of R.  A new symbol c is
// forbidden exactly when there is an L >= 1 with
//     R[L] == c  and  Z[L+1] >= L-1,
// which is the reversed form of the forbidden factor U a U.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

int main(int argc, char** argv) {
  const int N = argc > 1 ? std::atoi(argv[1]) : 200000;
  const bool dump = argc > 2;
  std::vector<uint8_t> r(2 * (size_t)N + 16, 0);
  std::vector<uint32_t> z(2 * (size_t)N + 16, 0);
  size_t off = (size_t)N + 8;
  size_t n = 0;
  uint64_t counts[16] = {0};
  long long first[16];
  for (int i = 0; i < 16; ++i) first[i] = -1;
  int halt_at = -1;
  std::string out;
  if (dump) out.reserve(N);

  for (int step = 1; step <= N; ++step) {
    unsigned forb = 0;
    for (size_t L = 1; L <= n / 2; ++L) {
      bool cond;
      if (L + 1 >= n) cond = (L == 1);  // empty suffix when n == 2
      else cond = z[off + L + 1] >= L - 1;
      if (cond) forb |= 1u << r[off + L];
    }
    int c = 0;
    while (c < 16 && ((forb >> c) & 1u)) ++c;
    if (c >= 5) {
      halt_at = step;
      break;
    }
    if (first[c] < 0) first[c] = step;
    counts[c]++;
    if (dump) out.push_back(char('0' + c));

    // R_new = [c] + R_old.  Z_new[i] = 1 + Z_old[i] when R_old[i-1] == c.
    z[off + n] = 0;  // one past the old end
    z[off - 1] = (uint32_t)(n + 1);
    for (size_t i = 1; i <= n; ++i) {
      z[off + i - 1] = (r[off + i - 1] == c) ? z[off + i] + 1u : 0u;
    }
    --off;
    r[off] = (uint8_t)c;
    ++n;
  }

  std::printf("N=%d produced=%zu halt_at=%d max=", N, n, halt_at);
  int mx = 0;
  for (int i = 0; i < 16; ++i) if (first[i] >= 0) mx = i;
  std::printf("%d\n", mx);
  for (int i = 0; i <= mx; ++i)
    std::printf("value=%d first=%lld count=%llu\n", i, first[i],
                (unsigned long long)counts[i]);
  if (halt_at >= 0) std::printf("FIVE at %d\n", halt_at);
  if (dump) {
    std::printf("SEQ ");
    std::fwrite(out.data(), 1, out.size(), stdout);
    std::printf("\n");
  }
  return 0;
}
