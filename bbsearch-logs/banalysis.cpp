// Fast analyzer for a 4-state/6-symbol machine:
//  * dumps the full tape RLE at requested step counts,
//  * logs every new global-minimum cell (the outer loop) as MINLINE,
//  * reports per-outer-iteration deltas.
// usage: ./banalysis MACHINE maxSteps dump1,dump2,...
#include <bits/stdc++.h>
using namespace std;

static int tab[9][6][3];

static unordered_map<long long, int> tape;
static int getv(long long i) { auto it = tape.find(i); return it == tape.end() ? 0 : it->second; }
static void setv(long long i, int v) { if (v == 0) tape.erase(i); else tape[i] = v; }

static string rle(long long lo, long long hi, long long head) {
  string out;
  long long i = lo;
  while (i <= hi) {
    int c = getv(i);
    long long j = i;
    while (j + 1 <= hi && getv(j + 1) == c) j++;
    string s = to_string(c);
    if (i == head) out += "[" + s + "]";
    else {
      long long n = j - i + 1;
      if (n >= 4) out += s + "^" + to_string(n);
      else for (long long k = 0; k < n; k++) out += s;
    }
    i = j + 1;
  }
  return out;
}

int main(int argc, char** argv) {
  if (argc < 3) { cerr << "usage: banalysis MACHINE maxSteps [dumps]\n"; return 1; }
  string m = argv[1];
  long long maxSteps = atoll(argv[2]);
  vector<long long> dumps;
  if (argc > 3) { string s = argv[3]; stringstream ss(s); string t; while (getline(ss, t, ',')) dumps.push_back(atoll(t.c_str())); }

  vector<string> blocks;
  { string cur; for (char ch : m) { if (ch == '_') { blocks.push_back(cur); cur.clear(); } else cur += ch; } blocks.push_back(cur); }
  int NS = blocks[0].size() / 3;
  for (int s = 0; s < (int)blocks.size(); s++)
    for (int y = 0; y < NS; y++) {
      string t = blocks[s].substr(y * 3, 3);
      tab[s][y][0] = t[0] - '0';
      tab[s][y][1] = t[1] == 'L' ? -1 : 1;
      tab[s][y][2] = t[2] == 'Z' ? -1 : t[2] - 'A';
    }

  long long head = 0, steps = 0, minPos = 0;
  int st = 0;
  int di = 0;
  long long idx = 0;
  bool halted = false;
  long long haltStep = -1;

  while (steps < maxSteps) {
    int w = tab[st][getv(head)][0], d = tab[st][getv(head)][1], nx = tab[st][getv(head)][2];
    setv(head, w);
    head += d;
    steps++;
    if (nx < 0) { halted = true; haltStep = steps; break; }
    st = nx;
    while (di < (int)dumps.size() && steps >= dumps[di]) {
      long long lo = head, hi = head;
      for (auto& kv : tape) { lo = min(lo, kv.first); hi = max(hi, kv.first); }
      printf("DUMP step=%lld state=%c pos=%lld span=[%lld,%lld] cells=%zu\n  %s\n",
             steps, 'A' + st, head, lo, hi, tape.size(), rle(lo, hi, head).c_str());
      fflush(stdout);
      di++;
    }
    if (head < minPos) {
      minPos = head;
      long long lo = head, hi = head;
      for (auto& kv : tape) { lo = min(lo, kv.first); hi = max(hi, kv.first); }
      idx++;
      printf("MINLINE %lld %lld %lld %lld %zu\n", idx, steps, head, hi - lo + 1, tape.size());
    }
  }
  long long lo = 0, hi = 0;
  for (auto& kv : tape) { lo = min(lo, kv.first); hi = max(hi, kv.first); }
  printf("END steps=%lld halted=%d haltStep=%lld state=%c pos=%lld span=[%lld,%lld] cells=%zu\n",
         steps, (int)halted, haltStep, 'A' + st, head, lo, hi, tape.size());
  fflush(stdout);
  return 0;
}
