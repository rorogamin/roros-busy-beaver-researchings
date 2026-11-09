// hunt_cet2_3sym_tnf_ultra.cpp
// 16-Thread Joint TNF Exhaustive Search for CET(2,3) (2 Agents, 2 States, 3 Symbols)!
// Current World Record: 20,350 steps (2LB1LA2LA_2RB2LA0LB|1RB0LB1RB_2LA2LA1RA)
// Total transitions per agent = 6 (2 states * 3 symbols = 6), 12 transitions total!
// Each transition has 3 symbols * 2 dirs * 2 states = 12 choices.
// Build: g++ -O3 -march=native -pthread hunt_cet2_3sym_tnf_ultra.cpp -o hunt_cet2_3sym_tnf_ultra.exe

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

static constexpr int TAPE_SIZE = 131072;
static constexpr int OFFSET = 65536;
static constexpr int SPLIT_DEPTH = 4;

struct Trans {
    uint8_t write;
    int8_t move;
    uint8_t next;
};

struct TNFState {
    Trans t[2][2][3]{};
    uint8_t defined[2][2][3]{};
    int max_state[2]{};
    int max_sym = 0; // Joint symbol TNF: symbol 1 before symbol 2? Wait: let's allow all 3 symbols {0,1,2} or canonical symbol TNF!
    int pos[2]{};
    uint8_t state[2]{};
    int min_p[2]{};
    int max_p[2]{};
    int max_seen_ap = 2;
    uint64_t steps = 0;
};

struct TNFWorker {
    TNFState s;
    uint8_t* tape = nullptr;
    uint32_t* undo = nullptr;
    size_t undo_len = 0;

    TNFWorker() {
        tape = (uint8_t*)std::calloc(TAPE_SIZE, 1);
        undo = (uint32_t*)std::malloc(sizeof(uint32_t) * 32000000);
    }
    ~TNFWorker() {
        std::free(tape);
        std::free(undo);
    }

    inline void write_cell(int p, uint8_t v) {
        uint32_t idx = (uint32_t)(p + OFFSET);
        uint8_t old = tape[idx];
        if (old == v) return;
        undo[undo_len++] = (idx << 2) | old;
        tape[idx] = v;
    }

    inline void undo_to(size_t cp) {
        while (undo_len > cp) {
            uint32_t e = undo[--undo_len];
            tape[e >> 2] = (uint8_t)(e & 3);
        }
    }
};

struct Task {
    TNFState s;
    std::vector<std::pair<int, uint8_t>> cells;
};

static std::deque<Task> task_queue;
static std::mutex queue_mutex;
static std::mutex print_mutex;
static std::atomic<uint64_t> global_best{0};
static std::atomic<uint64_t> tasks_done{0};
static std::atomic<uint64_t> total_tasks{0};
static uint64_t STEP_LIMIT = 15000000ULL;
static FILE* log_fp = nullptr;

static void format_machine(const TNFState& s, char* out) {
    int k = 0;
    for (int i = 0; i < 2; i++) {
        if (i == 1) out[k++] = '|';
        for (int q = 0; q < 2; q++) {
            if (q > 0) out[k++] = '_';
            for (int b = 0; b < 3; b++) {
                if (s.defined[i][q][b]) {
                    Trans tr = s.t[i][q][b];
                    out[k++] = '0' + tr.write;
                    out[k++] = tr.move > 0 ? 'R' : 'L';
                    out[k++] = 'A' + tr.next;
                } else {
                    out[k++] = '0'; out[k++] = 'R'; out[k++] = 'A';
                }
            }
        }
    }
    out[k] = '\0';
}

static void dfs(TNFWorker& w, int depth, bool collecting_tasks) {
    TNFState& s = w.s;
    size_t cp = w.undo_len;
    uint64_t saved_steps = s.steps;
    int p0 = s.pos[0], p1 = s.pos[1];
    uint8_t q0 = s.state[0], q1 = s.state[1];
    int saved_max_ap = s.max_seen_ap;
    int cur_max_ap = saved_max_ap;
    int min0 = s.min_p[0], max0 = s.max_p[0];
    int min1 = s.min_p[1], max1 = s.max_p[1];
    int saved_max_sym = s.max_sym;

    auto restore = [&]() {
        w.undo_to(cp);
        s.steps = saved_steps;
        s.max_seen_ap = saved_max_ap;
        s.min_p[0] = min0; s.max_p[0] = max0;
        s.min_p[1] = min1; s.max_p[1] = max1;
        s.pos[0] = p0; s.pos[1] = p1;
        s.state[0] = q0; s.state[1] = q1;
        s.max_sym = saved_max_sym;
    };

    if (collecting_tasks && depth >= SPLIT_DEPTH) {
        Task tk;
        tk.s = s;
        for (int x = std::min(min0, min1) - 2; x <= std::max(max0, max1) + 2; x++) {
            uint8_t v = w.tape[x + OFFSET];
            if (v) tk.cells.push_back({x, v});
        }
        task_queue.push_back(std::move(tk));
        restore();
        return;
    }

    int c_min0 = min0, c_max0 = max0;
    int c_min1 = min1, c_max1 = max1;
    int ai = -1, qs = -1, bs = -1;

    while (s.steps < STEP_LIMIT) {
        int b0 = w.tape[p0 + OFFSET];
        int b1 = w.tape[p1 + OFFSET];
        if (!s.defined[0][q0][b0]) { ai = 0; qs = q0; bs = b0; break; }
        if (!s.defined[1][q1][b1]) { ai = 1; qs = q1; bs = b1; break; }

        Trans t0 = s.t[0][q0][b0];
        Trans t1 = s.t[1][q1][b1];
        if (p0 == p1) {
            w.write_cell(p0, t0.write);
        } else {
            w.write_cell(p0, t0.write);
            w.write_cell(p1, t1.write);
        }
        p0 += t0.move; q0 = t0.next;
        p1 += t1.move; q1 = t1.next;
        s.steps++;

        if (p0 == p1) {
            uint64_t prev_best = global_best.load(std::memory_order_relaxed);
            if (s.steps > prev_best || s.steps >= 20000) {
                std::lock_guard<std::mutex> lk(print_mutex);
                char buf[128];
                format_machine(s, buf);
                if (s.steps > global_best.load()) {
                    global_best.store(s.steps);
                    std::printf("\n*** [NEW CET(2,3) RECORD] %llu steps (col at x=%d) ***\n    %s\n",
                        (unsigned long long)s.steps, p0, buf);
                    std::fflush(stdout);
                } else if (s.steps >= 20350) {
                    std::printf("  [CET(2,3) 20k+ Club] %llu steps (col at x=%d): %s\n",
                        (unsigned long long)s.steps, p0, buf);
                    std::fflush(stdout);
                }
                if (log_fp && s.steps >= 20000) {
                    std::fprintf(log_fp, "%llu\t%d\t%s\n", (unsigned long long)s.steps, p0, buf);
                    std::fflush(log_fp);
                }
            }
            restore();
            return;
        }

        if (p0 < c_min0) c_min0 = p0;
        if (p0 > c_max0) c_max0 = p0;
        if (p1 < c_min1) c_min1 = p1;
        if (p1 > c_max1) c_max1 = p1;

        int ap0 = p0 >= 0 ? p0 : -p0;
        int ap1 = p1 >= 0 ? p1 : -p1;
        int max_ap = ap0 > ap1 ? ap0 : ap1;
        if (max_ap > cur_max_ap) cur_max_ap = max_ap;

        if ((s.steps & 127) == 0) {
            if (c_max0 < c_min1 || c_max1 < c_min0) {
                restore(); return;
            }
            if (s.steps <= 512) {
                if (max_ap > 80) { restore(); return; }
                if (s.steps == 512 && cur_max_ap < 5) { restore(); return; }
            } else if (s.steps <= 2048) {
                if (max_ap > 160) { restore(); return; }
                if (s.steps == 2048 && (cur_max_ap < 12 || (c_max0 - c_min0) < 4 || (c_max1 - c_min1) < 4)) {
                    restore(); return;
                }
            } else if (s.steps <= 10240) {
                if (max_ap > 360) { restore(); return; }
                if (s.steps == 10240 && cur_max_ap < 28) { restore(); return; }
            } else if (s.steps <= 50048) {
                if (max_ap > 800) { restore(); return; }
                if (s.steps == 50048 && cur_max_ap < 65) { restore(); return; }
            } else if (s.steps <= 250112) {
                if (max_ap > 2000) { restore(); return; }
                if (s.steps == 250112 && cur_max_ap < 140) { restore(); return; }
            } else if (s.steps <= 1000064) {
                if (max_ap > 4500) { restore(); return; }
                if (s.steps == 1000064 && cur_max_ap < 280) { restore(); return; }
            } else {
                if (max_ap > 16000) { restore(); return; }
            }
        }
    }

    if (ai < 0) {
        restore();
        return;
    }

    s.pos[0] = p0; s.pos[1] = p1;
    s.state[0] = q0; s.state[1] = q1;
    s.max_seen_ap = cur_max_ap;
    s.min_p[0] = c_min0; s.max_p[0] = c_max0;
    s.min_p[1] = c_min1; s.max_p[1] = c_max1;

    int oldmax_st = s.max_state[ai];
    int maxnext_st = (oldmax_st + 1 < 1) ? (oldmax_st + 1) : 1; // 2 states: 0 and 1!
    int oldmax_sym = s.max_sym;
    int maxnext_sym = (oldmax_sym + 1 < 2) ? (oldmax_sym + 1) : 2; // Joint symbol TNF: 1 before 2!

    for (int w_sym = 0; w_sym <= maxnext_sym; w_sym++) {
        for (int md = 0; md < 2; md++) {
            for (int n = 0; n <= maxnext_st; n++) {
                s.defined[ai][qs][bs] = 1;
                s.t[ai][qs][bs].write = (uint8_t)w_sym;
                s.t[ai][qs][bs].move = (int8_t)(md == 0 ? 1 : -1);
                s.t[ai][qs][bs].next = (uint8_t)n;
                if (n > s.max_state[ai]) s.max_state[ai] = n;
                if (w_sym > s.max_sym) s.max_sym = w_sym;

                dfs(w, depth + 1, collecting_tasks);

                s.max_state[ai] = oldmax_st;
                s.max_sym = oldmax_sym;
                s.defined[ai][qs][bs] = 0;
                s.pos[0] = p0; s.pos[1] = p1;
                s.state[0] = q0; s.state[1] = q1;
                s.max_seen_ap = cur_max_ap;
                s.min_p[0] = c_min0; s.max_p[0] = c_max0;
                s.min_p[1] = c_min1; s.max_p[1] = c_max1;
            }
        }
    }

    restore();
}

int main(int argc, char** argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    int num_threads = std::thread::hardware_concurrency();
    if (num_threads < 1) num_threads = 8;
    if (argc > 1) num_threads = std::atoi(argv[1]);
    if (argc > 2) STEP_LIMIT = std::strtoull(argv[2], nullptr, 10);

    log_fp = std::fopen("cet2_3sym_tnf_champions.txt", "a");

    {
        TNFWorker collector;
        // Root step: A0(0,0) has w0 in {0, 1} (by symbol symmetry 1 vs 2), move in {R,L}, next in {A,B} -> 8 choices
        // A1(0,0) has w1 in {0..max_sym+1}, move in {R,L}, next in {A,B} -> up to 12 choices
        for (int w0 = 0; w0 <= 1; w0++) {
            for (int m0 = 0; m0 < 2; m0++) {
                for (int n0 = 0; n0 <= 1; n0++) {
                    int max_sym0 = w0;
                    int lim_w1 = (max_sym0 + 1 < 2) ? (max_sym0 + 1) : 2;
                    for (int w1 = 0; w1 <= lim_w1; w1++) {
                        for (int m1 = 0; m1 < 2; m1++) {
                            for (int n1 = 0; n1 <= 1; n1++) {
                                std::memset(&collector.s, 0, sizeof(collector.s));
                                collector.undo_len = 0;
                                collector.s.t[0][0][0] = { uint8_t(w0), int8_t(m0 ? -1 : 1), uint8_t(n0) };
                                collector.s.t[1][0][0] = { uint8_t(w1), int8_t(m1 ? -1 : 1), uint8_t(n1) };
                                collector.s.defined[0][0][0] = 1; collector.s.max_state[0] = n0;
                                collector.s.defined[1][0][0] = 1; collector.s.max_state[1] = n1;
                                collector.s.max_sym = std::max(w0, w1);
                                collector.s.pos[0] = 0; collector.s.pos[1] = 2;
                                collector.s.min_p[0] = 0; collector.s.max_p[0] = 0;
                                collector.s.min_p[1] = 2; collector.s.max_p[1] = 2;
                                collector.s.max_seen_ap = 2;
                                dfs(collector, 2, true);
                            }
                        }
                    }
                }
            }
        }
    }

    total_tasks.store(task_queue.size());
    std::printf("=== ULTRA TNF CET(2,3) SEARCH: %llu depth-%d subtrees, threads=%d, limit=%llu ===\n",
        (unsigned long long)total_tasks.load(), SPLIT_DEPTH, num_threads, (unsigned long long)STEP_LIMIT);

    auto start_time = std::chrono::steady_clock::now();
    std::vector<std::thread> pool;

    for (int th = 0; th < num_threads; th++) {
        pool.emplace_back([&]() {
            TNFWorker worker;
            while (true) {
                Task tk;
                {
                    std::lock_guard<std::mutex> lk(queue_mutex);
                    if (task_queue.empty()) break;
                    tk = std::move(task_queue.front());
                    task_queue.pop_front();
                }
                worker.s = tk.s;
                worker.undo_len = 0;
                for (auto& kv : tk.cells) {
                    worker.tape[kv.first + OFFSET] = kv.second;
                }
                dfs(worker, SPLIT_DEPTH, false);
                for (auto& kv : tk.cells) {
                    worker.tape[kv.first + OFFSET] = 0;
                }

                uint64_t done = tasks_done.fetch_add(1) + 1;
                if (done % 200 == 0 || done == total_tasks.load()) {
                    std::lock_guard<std::mutex> lk(print_mutex);
                    double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start_time).count();
                    std::printf("[CET(2,3) Progress] %llu / %llu (%.1f%%) | elapsed=%.1fs | best=%llu\n",
                        (unsigned long long)done, (unsigned long long)total_tasks.load(),
                        100.0 * done / total_tasks.load(), elapsed,
                        (unsigned long long)global_best.load());
                }
            }
        });
    }

    for (auto& t : pool) t.join();
    if (log_fp) std::fclose(log_fp);

    double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start_time).count();
    std::printf("\n=== ULTRA TNF CET(2,3) FINISHED in %.2f s | Global Best = %llu steps ===\n",
        elapsed, (unsigned long long)global_best.load());
    return 0;
}
