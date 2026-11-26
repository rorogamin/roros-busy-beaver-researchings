// Run a TM from a bbsearch-style start configuration and report the halt step.
// usage: bstart MACHINE "0^inf 3^(1) 2^5 A> 1^2 4 5^11 0^inf" maxSteps
#include <bits/stdc++.h>
using namespace std;

static int tab[9][6][3];
static unordered_map<long long, int> tape;
static int getv(long long i) { auto it = tape.find(i); return it == tape.end() ? 0 : it->second; }

static vector<pair<int, long long>> parseSide(const string& s) {
  vector<pair<int, long long>> out;
  string t = s;
  for (auto& c : t) if (c == '(' || c == ')') c = ' ';
  stringstream ss(t);
  string tok;
  while (ss >> tok) {
    if (tok.find("^inf") != string::npos) continue;
    int sym = -1; long long n = 1;
    size_t caret = tok.find('^');
    if (caret != string::npos) {
      sym = tok[0] - '0';
      string num = tok.substr(caret + 1);
      string digits;
      for (char c : num) if (isdigit((unsigned char)c)) digits += c;
      n = digits.empty() ? 1 : atoll(digits.c_str());
    }
    else if (tok.size() == 1 && isdigit(tok[0])) { sym = tok[0] - '0'; }
    else continue;
    out.push_back({sym, n});
  }
  return out;
}

int main(int argc, char** argv) {
  if (argc < 4) { cerr << "usage: bstart MACHINE CONFIG maxSteps\n"; return 1; }
  string m = argv[1], cfg = argv[2];
  long long maxSteps = atoll(argv[3]);

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

  size_t arrow = cfg.find('>');
  string left = cfg.substr(0, arrow + 1), right = cfg.substr(arrow + 1);
  left = left.substr(0, left.size() - 1);
  string headState = "A";
  { size_t p = left.find_last_of("ABCDEFGH"); if (p != string::npos) { headState = left.substr(p, 1); left = left.substr(0, p); } }

  auto L = parseSide(left), R = parseSide(right);
  long long pos = 0;
  for (auto it = L.rbegin(); it != L.rend(); ++it) {
    for (long long i = 0; i < it->second; i++) { pos--; if (it->first) tape[pos] = it->first; }
  }
  // pos is now one left of the head cell
  pos = 0;
  for (auto& pr : R) for (long long i = 0; i < pr.second; i++) { if (pr.first) tape[pos] = pr.first; pos++; }

  long long head = 0, steps = 0;
  int st = headState[0] - 'A';
  while (steps < maxSteps) {
    int w = tab[st][getv(head)][0], d = tab[st][getv(head)][1], nx = tab[st][getv(head)][2];
    if (w) tape[head] = w; else tape.erase(head);
    head += d; steps++;
    if (nx < 0) { printf("HALT steps=%lld\n", steps); return 0; }
    st = nx;
  }
  printf("NOHALT steps=%lld state=%c pos=%lld cells=%zu tapeHead=%d\n", steps, 'A' + st, head, tape.size(), getv(head));
  return 0;
}
