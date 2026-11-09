// cet_v2.cpp — Catch-Em-Turing
// Build: g++ -O3 -march=native -pthread -DNDEBUG -DBAND_BITS=24 -o cet cet_v2.cpp
//
// Commands:
//   ./cet run [--max-steps N] [--halt collision|catcher|pairwise] [--prio low|high] [--pos p0,p1] SPEC1 SPEC2
//   ./cet search [trials] [max_steps] [threads] [halt] [prio]
//   ./cet genetic [population] [generations] [max_steps] [threads] [seed]
//   ./cet tnf [threads] [max_steps] [halt] [prio]
//   ./cet enumerate [max_steps] [threads] [halt] [prio] [canon 0|1]
//
// CET(3) in this program means two agents, three states per agent, two tape symbols.
// The default starts are positions 0 and 2. Collision means equal positions
// AFTER the simultaneous transition. Both agents read before either writes.

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <iostream>
#include <mutex>
#include <random>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#ifndef BAND_BITS
#define BAND_BITS 24
#endif

static constexpr int BAND_SIZE = 1 << BAND_BITS;
static constexpr int BAND_OFF = BAND_SIZE / 2;
static constexpr int STATES = 3;
static constexpr int MAX_AGENTS = 3;
static constexpr uint64_t SPACE_FULL = 2985984ULL; // 12^6
static constexpr uint64_t SPACE_CANON = 1990656ULL; // 8 * 12^5

enum HaltMode { COLLISION, CATCHER, PAIRWISE };
enum Priority { LOW, HIGH };

struct Transition { uint8_t write; int8_t move; uint8_t next; };
struct Agent {
    Transition t[STATES][2]{};
    uint8_t state = 0;
    int pos = 0;
};

static std::mutex best_mutex;
static uint64_t global_best = 0;
static std::atomic<uint64_t> work_done{0};
static std::atomic<bool> stop_search{false};
static int initial_pos[MAX_AGENTS] = {0, 2, 0};

static const char* halt_name(HaltMode h) {
    return h == COLLISION ? "collision" : h == CATCHER ? "catcher" : "pairwise";
}
static bool parse_halt(const std::string& s, HaltMode& h) {
    if (s == "collision") h = COLLISION;
    else if (s == "catcher") h = CATCHER;
    else if (s == "pairwise") h = PAIRWISE;
    else return false;
    return true;
}
static bool parse_priority(const std::string& s, Priority& p) {
    if (s == "low") p = LOW;
    else if (s == "high") p = HIGH;
    else return false;
    return true;
}
static void parse_positions(const std::string& s, int n) {
    std::stringstream ss(s); std::string x; int i = 0;
    while (std::getline(ss, x, ',') && i < n) initial_pos[i++] = std::atoi(x.c_str());
}
static bool parse_transition(const std::string& s, Transition& tr) {
    if (s.size() != 3 || (s[0] != '0' && s[0] != '1')) return false;
    tr.write = uint8_t(s[0] - '0');
    if (s[1] == 'L' || s[1] == 'l') tr.move = -1;
    else if (s[1] == 'R' || s[1] == 'r') tr.move = +1;
    else return false;
    char q = s[2];
    if (q >= 'a' && q <= 'z') q = char(q - 'a' + 'A');
    if (q < 'A' || q >= 'A' + STATES) return false;
    tr.next = uint8_t(q - 'A');
    return true;
}
static bool parse_agent(const std::vector<std::string>& tokens, Agent& a) {
    if (tokens.size() != 6) return false;
    int k = 0;
    for (int q = 0; q < STATES; ++q)
        for (int b = 0; b < 2; ++b)
            if (!parse_transition(tokens[k++], a.t[q][b])) return false;
    a.state = 0;
    return true;
}
static std::string agent_string(const Agent& a, char separator=' ') {
    std::string out;
    for (int q=0; q<STATES; ++q) {
        for (int b=0; b<2; ++b) {
            const auto& t = a.t[q][b];
            char buf[4];
            buf[0] = char('0' + t.write);
            buf[1] = t.move < 0 ? 'L' : 'R';
            buf[2] = char('A' + t.next);
            buf[3] = '\0';
            if (!out.empty()) out += separator;
            out += buf;
        }
    }
    return out;
}
static bool same_table(const Agent& a, const Agent& b) {
    return std::memcmp(a.t, b.t, sizeof(a.t)) == 0;
}
static bool halted(const int* p, int n, HaltMode h) {
    if (h == COLLISION) {
        for (int i=1; i<n; ++i) if (p[i] != p[0]) return false;
        return true;
    }
    if (h == CATCHER) {
        for (int i=1; i<n; ++i) if (p[i] == p[0]) return true;
        return false;
    }
    for (int i=0; i<n; ++i)
        for (int j=0; j<i; ++j)
            if (p[i] == p[j]) return true;
    return false;
}

// Fast complete-machine simulator. Epoch stamps avoid clearing the tape per run.
template<int N>
struct Machine {
    std::vector<uint8_t> tape;
    std::vector<uint32_t> stamp;
    uint32_t epoch = 1;
    Agent agents[N];
    uint64_t steps = 0;
    HaltMode halt;
    Priority priority;

    Machine(HaltMode h, Priority p)
        : tape(BAND_SIZE, 0), stamp(BAND_SIZE, 0), halt(h), priority(p) {}

    void reset(const Agent* a) {
        std::memcpy(agents, a, sizeof(agents));
        steps = 0;
        if (++epoch == 0) {
            std::fill(stamp.begin(), stamp.end(), 0);
            epoch = 1;
        }
    }
    inline uint8_t read_cell(int p) const {
        const uint32_t x = uint32_t(p + BAND_OFF);
        return stamp[x] == epoch ? tape[x] : 0;
    }
    inline void write_cell(int p, uint8_t v) {
        const uint32_t x = uint32_t(p + BAND_OFF);
        tape[x] = v; stamp[x] = epoch;
    }
    int step() {
        uint8_t symbols[N], writes[N], nexts[N];
        int8_t moves[N];
        int oldpos[N], newpos[N];
        for (int i=0; i<N; ++i) {
            oldpos[i] = agents[i].pos;
            const int x = oldpos[i] + BAND_OFF;
            if (x < 0 || x >= BAND_SIZE) return -2;
            symbols[i] = read_cell(oldpos[i]);
        }
        for (int i=0; i<N; ++i) {
            const auto& tr = agents[i].t[agents[i].state][symbols[i]];
            writes[i] = tr.write; moves[i] = tr.move; nexts[i] = tr.next;
        }
        // Resolve simultaneous writes: one final write per occupied cell.
        for (int i=0; i<N; ++i) {
            bool winner = true;
            for (int j=0; j<N; ++j) {
                if (oldpos[j] != oldpos[i]) continue;
                if ((priority == LOW && j < i) || (priority == HIGH && j > i)) {
                    winner = false; break;
                }
            }
            if (winner) write_cell(oldpos[i], writes[i]);
        }
        for (int i=0; i<N; ++i) {
            newpos[i] = oldpos[i] + moves[i];
            agents[i].pos = newpos[i];
            agents[i].state = nexts[i];
        }
        ++steps;
        for (int i=0; i<N; ++i) {
            const int x = newpos[i] + BAND_OFF;
            if (x < 0 || x >= BAND_SIZE) return -2;
        }
        return halted(newpos, N, halt) ? 1 : 0;
    }
    int run(uint64_t limit) {
        while (steps < limit) {
            int r = step();
            if (r != 0) return r;
        }
        return 0;
    }
};

static void print_machine(const Agent* a, int n) {
    for (int i=0; i<n; ++i)
        std::printf("  agent %d: %s\n", i, agent_string(a[i], '_').c_str());
}

// Random baseline search.
template<int N>
static void random_worker(uint64_t trials, uint64_t limit, HaltMode h, Priority p, uint32_t seed) {
    std::mt19937 rng(seed);
    std::uniform_int_distribution<int> bit(0,1), state(0,2);
    Machine<N> m(h,p);
    Agent a[N];
    for (uint64_t k=0; k<trials && !stop_search.load(); ++k) {
        for (int i=0; i<N; ++i) {
            for (int q=0; q<STATES; ++q) for (int b=0; b<2; ++b) {
                a[i].t[q][b] = {uint8_t(bit(rng)), int8_t(bit(rng) ? 1 : -1), uint8_t(state(rng))};
            }
            a[i].state=0; a[i].pos=initial_pos[i];
        }
        bool identical=true;
        for (int i=1; i<N; ++i) if (!same_table(a[0],a[i])) identical=false;
        if (identical) continue;
        m.reset(a);
        int r=m.run(limit);
        work_done.fetch_add(1);
        if (r==1 && m.steps>global_best) {
            std::lock_guard<std::mutex> lock(best_mutex);
            if (m.steps>global_best) {
                global_best=m.steps;
                std::printf("\n[record] %llu steps\n",(unsigned long long)m.steps);
                print_machine(a,N); std::fflush(stdout);
            }
        }
    }
}
template<int N>
static void random_search(uint64_t trials,uint64_t limit,int nt,HaltMode h,Priority p) {
    std::vector<std::thread> pool;
    const uint64_t per=(trials+nt-1)/nt;
    for(int i=0;i<nt;++i) {
        uint32_t seed=uint32_t(0x9E3779B9u*(i+1)) ^ uint32_t(
            std::chrono::steady_clock::now().time_since_epoch().count());
        pool.emplace_back(random_worker<N>,per,limit,h,p,seed);
    }
    for(auto& t:pool)t.join();
}

// Genetic search: fitness is elapsed steps; only actual halts become records.
// Population members are evaluated in parallel. Elites + tournament selection,
// one-point table crossover and random transition mutations.
struct Individual { std::array<Agent,2> a; uint64_t fitness=0; bool halted=false; };
static void randomize(Individual& x,std::mt19937& r) {
    std::uniform_int_distribution<int> bit(0,1), q(0,2);
    for(int i=0;i<2;++i) {
        for(int s=0;s<3;++s)for(int b=0;b<2;++b)
            x.a[i].t[s][b]={uint8_t(bit(r)),int8_t(bit(r)?1:-1),uint8_t(q(r))};
        x.a[i].state=0; x.a[i].pos=initial_pos[i];
    }
}
static void mutate(Individual& x,std::mt19937& r) {
    std::uniform_int_distribution<int> agent(0,1), slot(0,5), field(0,2), bit(0,1), q(0,2);
    int i=agent(r), k=slot(r), s=k/2, b=k%2;
    auto& t=x.a[i].t[s][b];
    switch(field(r)) {
        case 0: t.write=uint8_t(bit(r)); break;
        case 1: t.move=int8_t(bit(r)?1:-1); break;
        default: t.next=uint8_t(q(r)); break;
    }
}
static Individual crossover(const Individual& x,const Individual& y,std::mt19937& r) {
    Individual z=x;
    std::uniform_int_distribution<int> cut(0,12);
    int c=cut(r), k=0;
    for(int i=0;i<2;++i)for(int s=0;s<3;++s)for(int b=0;b<2;++b,++k)
        if(k>=c) z.a[i].t[s][b]=y.a[i].t[s][b];
    return z;
}
static uint64_t evaluate(Individual& x,uint64_t limit) {
    Machine<2> m(COLLISION,LOW);
    x.a[0].state=x.a[1].state=0;
    x.a[0].pos=initial_pos[0]; x.a[1].pos=initial_pos[1];
    m.reset(x.a.data());
    int r=m.run(limit);
    x.halted=(r==1);
    x.fitness=m.steps;
    return x.fitness;
}
static void genetic_search(int popsize,int generations,uint64_t limit,int nt,uint32_t seed) {
    if(popsize<8)popsize=8;
    std::mt19937 rng(seed);
    std::vector<Individual> pop(popsize), next(popsize);
    for(auto& x:pop)randomize(x,rng);
    Machine<2> scratch(COLLISION,LOW);
    auto evaluate_population=[&](std::vector<Individual>& v) {
        std::atomic<int> cursor{0};
        std::vector<std::thread> workers;
        for(int t=0;t<nt;++t) workers.emplace_back([&](){
            for(;;) {
                int i=cursor.fetch_add(1);
                if(i>=int(v.size()))break;
                evaluate(v[i],limit);
            }
        });
        for(auto& t:workers)t.join();
    };
    auto order=[](const Individual& a,const Individual& b) {
        if(a.halted!=b.halted)return a.halted>b.halted;
        return a.fitness>b.fitness;
    };
    evaluate_population(pop);
    for(int gen=0;gen<generations;++gen) {
        std::sort(pop.begin(),pop.end(),order);
        if(pop[0].halted && pop[0].fitness>global_best) {
            std::lock_guard<std::mutex> lock(best_mutex);
            if(pop[0].fitness>global_best) {
                global_best=pop[0].fitness;
                std::printf("\n[gen %d] [record] %llu steps\n",gen,(unsigned long long)global_best);
                print_machine(pop[0].a.data(),2); std::fflush(stdout);
            }
        }
        if((gen%10)==0)
            std::printf("[gen %d] best fitness=%llu, halted=%s, record=%llu\n",
                gen,(unsigned long long)pop[0].fitness,pop[0].halted?"yes":"no",
                (unsigned long long)global_best);
        int elite=std::max(2,popsize/20);
        for(int i=0;i<elite;++i)next[i]=pop[i];
        std::uniform_int_distribution<int> pick(0,popsize-1);
        for(int i=elite;i<popsize;++i) {
            // Tournament selection.
            Individual p1=pop[pick(rng)],p2=pop[pick(rng)];
            for(int z=0;z<3;++z) {auto c=pop[pick(rng)];if(order(c,p1))p1=c;}
            for(int z=0;z<3;++z) {auto c=pop[pick(rng)];if(order(c,p2))p2=c;}
            next[i]=crossover(p1,p2,rng);
            std::uniform_real_distribution<double> chance(0.0,1.0);
            int mutations=chance(rng)<0.15?3:1;
            for(int m=0;m<mutations;++m)if(chance(rng)<0.85)mutate(next[i],rng);
        }
        pop.swap(next);
        evaluate_population(pop);
    }
    std::sort(pop.begin(),pop.end(),order);
    std::printf("\n=== genetic finished ===\nBest fitness: %llu, halted=%s\n",
        (unsigned long long)pop[0].fitness,pop[0].halted?"yes":"no");
    print_machine(pop[0].a.data(),2);
}

// TNF partial-machine search. The undo log packs (tape index, old bit) in uint32_t.
// Since BAND_BITS <= 30, (index << 1) | old_bit fits in uint32_t.
static_assert(BAND_BITS <= 30, "BAND_BITS must be <= 30 for packed undo entries");
static uint64_t tnf_limit=5000000;
struct TNF {
    Agent a[2];
    bool defined[2][3][2]{};
    int max_state[2]{};
    uint64_t steps=0;
    std::vector<uint8_t> tape;
    std::vector<uint32_t> undo;
    Priority priority=LOW;

    void init(int c0,int c1,Priority p) {
        priority=p; steps=0; undo.clear();
        std::fill(tape.begin(),tape.end(),uint8_t(0));
        std::memset(defined,0,sizeof(defined));
        a[0]=Agent{}; a[1]=Agent{};
        int codes[2]={c0,c1};
        for(int i=0;i<2;++i) {
            int c=codes[i], w=c/6, mi=(c/3)%2, n=c%3;
            a[i].t[0][0]={uint8_t(w),int8_t(mi?-1:+1),uint8_t(n)};
            defined[i][0][0]=true;
            max_state[i]=n;
            a[i].state=0; a[i].pos=initial_pos[i];
        }
    }
    inline uint8_t read(int pos) const { return tape[size_t(pos+BAND_OFF)]; }
    inline void write_final(int pos,uint8_t value) {
        uint32_t idx=uint32_t(pos+BAND_OFF);
        uint8_t old=tape[idx];
        if(old==value)return;                 // no-op writes need no undo entry
        undo.push_back((idx<<1)|old);         // packed index + previous bit
        tape[idx]=value;
    }
    void undo_to(size_t cp) {
        while(undo.size()>cp) {
            uint32_t e=undo.back(); undo.pop_back();
            tape[e>>1]=uint8_t(e&1);
        }
    }
    int step() {
        int p0=a[0].pos,p1=a[1].pos;
        int x0=p0+BAND_OFF,x1=p1+BAND_OFF;
        if(x0<0||x0>=BAND_SIZE||x1<0||x1>=BAND_SIZE)return -1;
        int b0=read(p0),b1=read(p1);
        if(!defined[0][a[0].state][b0]||!defined[1][a[1].state][b1])return 2;
        const Transition t0=a[0].t[a[0].state][b0];
        const Transition t1=a[1].t[a[1].state][b1];
        if(p0==p1) {
            write_final(p0,priority==LOW?t0.write:t1.write);
        } else {
            write_final(p0,t0.write);
            write_final(p1,t1.write);
        }
        a[0].pos+=t0.move; a[0].state=t0.next;
        a[1].pos+=t1.move; a[1].state=t1.next;
        ++steps;
        int q0=a[0].pos+BAND_OFF,q1=a[1].pos+BAND_OFF;
        if(q0<0||q0>=BAND_SIZE||q1<0||q1>=BAND_SIZE)return -1;
        return a[0].pos==a[1].pos?1:0;
    }
    std::string str() const {
        std::string out;
        for(int i=0;i<2;++i) {
            out+="  agent ";out+=char('0'+i);out+=": ";
            bool first=true;
            for(int s=0;s<3;++s) {
                for(int b=0;b<2;++b) {
                    char buf[4];
                    if(defined[i][s][b]) {
                        auto t=a[i].t[s][b];
                        buf[0]=char('0'+t.write); buf[1]=t.move<0?'L':'R';
                        buf[2]=char('A'+t.next); buf[3]='\0';
                    } else std::memcpy(buf,"0RA",4);
                    if(!first)out+="_";
                    out+=buf; first=false;
                }
            }
            out+="\n";
        }
        return out;
    }
};

struct TNFTask {
    Agent a[2];
    bool defined[2][3][2]{};
    int max_state[2]{};
    uint64_t steps = 0;
    Priority priority = LOW;

    // Only non-zero tape cells are stored.
    std::vector<uint32_t> ones;

    static TNFTask capture(const TNF& s) {
        TNFTask task;

        task.a[0] = s.a[0];
        task.a[1] = s.a[1];

        std::memcpy(task.defined, s.defined,
                    sizeof(task.defined));

        task.max_state[0] = s.max_state[0];
        task.max_state[1] = s.max_state[1];

        task.steps = s.steps;
        task.priority = s.priority;

        // Save only cells containing 1.
        task.ones.clear();

        for (uint32_t i = 0; i < s.tape.size(); ++i) {
            if (s.tape[i] != 0)
                task.ones.push_back(i);
        }

        return task;
    }

    void restore(TNF& s) const {
        s.a[0] = a[0];
        s.a[1] = a[1];

        std::memcpy(s.defined, defined,
                    sizeof(defined));

        s.max_state[0] = max_state[0];
        s.max_state[1] = max_state[1];

        s.steps = steps;
        s.priority = priority;

        // Reconstruct the tape.
        std::fill(s.tape.begin(), s.tape.end(), uint8_t(0));

        for (uint32_t i : ones) {
            if (i < s.tape.size())
                s.tape[i] = 1;
        }

        // A restored task starts with a fresh undo history.
        s.undo.clear();
    }
};

static std::atomic<int> tnf_done{0};
static std::atomic<uint64_t> tnf_best{0};
static std::mutex tnf_best_mutex;
static std::string tnf_best_machine;

static constexpr int TNF_SPLIT_DEPTH = 6;
static constexpr size_t TNF_MAX_QUEUE = 10000;

struct TNFScheduler {
    std::deque<TNFTask> queue;
    std::mutex mutex;
    std::condition_variable cv;

    // Number of queued + currently executing tasks.
    uint64_t outstanding = 0;
    bool finished = false;

    void initialize(std::deque<TNFTask>&& initial) {
        std::lock_guard<std::mutex> lock(mutex);
        queue = std::move(initial);
        outstanding = queue.size();
        finished = false;
    }

    bool try_enqueue(const TNF& s) {
        // Capture outside the lock: scanning the tape can take time.
        TNFTask task = TNFTask::capture(s);

        std::lock_guard<std::mutex> lock(mutex);

        if (queue.size() >= TNF_MAX_QUEUE)
            return false;

        queue.push_back(std::move(task));
        ++outstanding;

        cv.notify_one();
        return true;
    }

    bool get_task(TNFTask& task) {
        std::unique_lock<std::mutex> lock(mutex);

        cv.wait(lock, [&] {
            return !queue.empty() || outstanding == 0;
        });

        if (outstanding == 0)
            return false;

        task = std::move(queue.front());
        queue.pop_front();

        return true;
    }

    void complete_task() {
        std::lock_guard<std::mutex> lock(mutex);

        if (outstanding > 0)
            --outstanding;

        if (outstanding == 0) {
            finished = true;
            cv.notify_all();
        }
    }
};

// Explore one subtree. Every six new transition definitions,
// attempt to transfer the current subtree to the shared queue.
static void tnf_dfs(
    TNF& s,
    int depth,
    TNFScheduler& scheduler
) {
    if (s.steps >= tnf_limit)
        return;

    if (depth >= TNF_SPLIT_DEPTH) {
        if (scheduler.try_enqueue(s))
            return;
        // Queue full: continue exploring locally.
    }

    size_t checkpoint = s.undo.size();
    uint64_t saved_steps = s.steps;

    int saved_pos[2] = {
        s.a[0].pos,
        s.a[1].pos
    };

    uint8_t saved_state[2] = {
        s.a[0].state,
        s.a[1].state
    };

    auto restore = [&]() {
        s.undo_to(checkpoint);
        s.steps = saved_steps;

        for (int i = 0; i < 2; ++i) {
            s.a[i].pos = saved_pos[i];
            s.a[i].state = saved_state[i];
        }
    };

    while (true) {
        if (s.steps >= tnf_limit) {
            restore();
            return;
        }

        int r = s.step();

        if (r == 1) {
            uint64_t value = s.steps;

            if (value > tnf_best.load()) {
                std::lock_guard<std::mutex> lock(tnf_best_mutex);

                if (value > tnf_best.load()) {
                    tnf_best = value;
                    tnf_best_machine = s.str();

                    std::printf(
                        "\n[TNF RECORD] %llu steps\n%s",
                        (unsigned long long)value,
                        tnf_best_machine.c_str()
                    );

                    std::fflush(stdout);
                }
            }

            restore();
            return;
        }

        if (r == -1) {
            restore();
            return;
        }

        if (r == 2)
            break;
    }

    int ai = -1;
    int qs = -1;
    int bs = -1;

    for (int i = 0; i < 2; ++i) {
        int b = s.read(s.a[i].pos);

        if (!s.defined[i][s.a[i].state][b]) {
            ai = i;
            qs = s.a[i].state;
            bs = b;
            break;
        }
    }

    if (ai < 0) {
        restore();
        return;
    }

    int oldmax = s.max_state[ai];
    int maxnext = std::min(oldmax + 1, 2);

    for (int w = 0; w <= 1; ++w) {
        for (int md = 0; md < 2; ++md) {
            for (int n = 0; n <= maxnext; ++n) {

                s.defined[ai][qs][bs] = true;

                s.a[ai].t[qs][bs] = {
                    uint8_t(w),
                    int8_t(md == 0 ? 1 : -1),
                    uint8_t(n)
                };

                if (n > s.max_state[ai])
                    s.max_state[ai] = n;

                tnf_dfs(s, depth + 1, scheduler);

                s.max_state[ai] = oldmax;
                s.defined[ai][qs][bs] = false;
            }
        }
    }

    restore();
}

static void run_tnf(int nt, uint64_t limit, Priority p) {
    tnf_limit = limit;
    tnf_best = 0;
    tnf_done = 0;
    tnf_best_machine.clear();

    static constexpr int FIRST[8] = {
        0, 1, 3, 4, 6, 7, 9, 10
    };

    constexpr int TASKS = 64;

    std::printf(
        "TNF CET v3: %d canonical initial tasks, "
        "max_steps=%llu, threads=%d, split_depth=%d, max_queue=%zu\n",
        TASKS,
        (unsigned long long)limit,
        nt,
        TNF_SPLIT_DEPTH,
        TNF_MAX_QUEUE
    );

    auto start = std::chrono::steady_clock::now();

    // Build one zero-tape template, avoiding 64 full tape scans.
    TNF base;
    base.tape.assign(BAND_SIZE, 0);
    base.init(FIRST[0], FIRST[0], p);

    TNFTask base_task = TNFTask::capture(base);

    std::deque<TNFTask> initial;

    for (int task = 0; task < TASKS; ++task) {
        TNFTask current = base_task;

        int codes[2] = {
            FIRST[task / 8],
            FIRST[task % 8]
        };

        for (int i = 0; i < 2; ++i) {
            int c = codes[i];
            int w = c / 6;
            int md = (c / 3) % 2;
            int n = c % 3;

            current.a[i].t[0][0] = {
                uint8_t(w),
                int8_t(md ? -1 : +1),
                uint8_t(n)
            };

            current.defined[i][0][0] = true;
            current.max_state[i] = n;
        }

        initial.push_back(std::move(current));
    }

    TNFScheduler scheduler;
    scheduler.initialize(std::move(initial));

    std::mutex progress_mutex;

    if (nt < 1)
        nt = 1;

    std::vector<std::thread> pool;

    for (int th = 0; th < nt; ++th) {
        pool.emplace_back([&, th]() {
            TNF s;
            s.tape.assign(BAND_SIZE, 0);

            TNFTask task;

            while (scheduler.get_task(task)) {
                task.restore(s);

                tnf_dfs(s, 0, scheduler);

                int d = tnf_done.fetch_add(1) + 1;

                if (d % 10 == 0) {
                    std::lock_guard<std::mutex> lock(progress_mutex);

                    std::printf(
                        "[TNF v3] completed=%d, best=%llu\n",
                        d,
                        (unsigned long long)tnf_best.load()
                    );

                    std::fflush(stdout);
                }

                scheduler.complete_task();
            }
        });
    }

    for (auto& t : pool)
        t.join();

    double seconds =
        std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start
        ).count();

    std::printf(
        "\nTNF v3 finished in %.2f s; completed=%d; best=%llu\n",
        seconds,
        tnf_done.load(),
        (unsigned long long)tnf_best.load()
    );

    if (!tnf_best_machine.empty())
        std::printf("%s", tnf_best_machine.c_str());
}

// Exhaustive fixed-table enumeration (useful for small limits, not a practical full CET(3) search).
static void decode_agent(uint64_t code,Agent& a,bool canonical_first) {
    static constexpr int FIRST[8]={0,1,3,4,6,7,9,10};
    for(int k=0;k<6;++k) {
        uint64_t t;
        if(canonical_first&&k==0) {
            t=FIRST[code%8]; code/=8;
        } else { t=code%12; code/=12; }
        int q=k/2,b=k%2;
        a.t[q][b]={uint8_t(t/6),int8_t(((t/3)%2)?-1:+1),uint8_t(t%3)};
    }
    a.state=0;
}
template<int N>
static void enumerate(int nt,uint64_t limit,HaltMode h,Priority p,bool canon) {
    uint64_t spaces[N],total=1;
    for(int i=0;i<N;++i) {
        spaces[i]=(canon&&i==0)?SPACE_CANON:SPACE_FULL;
        if(total>UINT64_MAX/spaces[i]){std::puts("space overflow");return;}
        total*=spaces[i];
    }
    std::atomic<uint64_t> next{0};
    std::mutex out;
    uint64_t best=0;Agent best_agents[N];
    auto worker=[&](){
        Machine<N> m(h,p);Agent a[N];
        for(;;) {
            uint64_t idx=next.fetch_add(1);if(idx>=total)break;
            uint64_t x=idx;
            for(int i=0;i<N;++i) {
                uint64_t code=x%spaces[i];x/=spaces[i];
                decode_agent(code,a[i],canon&&i==0);a[i].pos=initial_pos[i];
            }
            m.reset(a);int r=m.run(limit);
            if(r==1&&m.steps>best) {
                std::lock_guard<std::mutex> lock(out);
                if(m.steps>best){best=m.steps;std::memcpy(best_agents,a,sizeof(a));
                    std::printf("[enum record] %llu\n",(unsigned long long)best);print_machine(a,N);}
            }
        }
    };
    std::vector<std::thread> pool;for(int i=0;i<nt;++i)pool.emplace_back(worker);
    for(auto& t:pool)t.join();
    std::printf("Enumeration done. machines=%llu best=%llu\n",
        (unsigned long long)total,(unsigned long long)best);
}

// Parse specs where transitions may be separated by spaces or underscores.
static std::vector<std::string> split_spec(std::string s) {
    for(char& c:s)if(c=='_')c=' ';
    std::istringstream in(s);std::vector<std::string> v;std::string x;
    while(in>>x) v.push_back(x);
    return v;
}
static void usage() {
    std::puts(
      "Usage:\n"
      " ./cet run [--max-steps N] [--halt MODE] [--prio low|high] [--pos p0,p1] SPEC1 SPEC2\n"
      " ./cet search [trials] [max_steps] [threads] [halt] [prio]\n"
      " ./cet genetic [population] [generations] [max_steps] [threads] [seed]\n"
      " ./cet tnf [threads] [max_steps] [halt] [prio]\n"
      " ./cet enumerate [max_steps] [threads] [halt] [prio] [canon 0|1]");
}
int main(int argc,char** argv) {
    if(argc<2){usage();return 0;}
    std::string cmd=argv[1];HaltMode h=COLLISION;Priority p=LOW;
    if(cmd=="run") {
        uint64_t limit=10000000;std::string pos;std::vector<std::string> flat;
        for(int i=2;i<argc;++i) {
            std::string x=argv[i];
            if(x=="--max-steps"&&i+1<argc)limit=std::strtoull(argv[++i],nullptr,10);
            else if(x=="--halt"&&i+1<argc){if(!parse_halt(argv[++i],h)){std::puts("bad halt");return 1;}}
            else if(x=="--prio"&&i+1<argc){if(!parse_priority(argv[++i],p)){std::puts("bad priority");return 1;}}
            else if(x=="--pos"&&i+1<argc)pos=argv[++i];
            else {auto v=split_spec(x);flat.insert(flat.end(),v.begin(),v.end());}
        }
        if(flat.size()!=12){std::puts("run expects exactly 12 transitions (two agents)");return 1;}
        if(!pos.empty())parse_positions(pos,2);
        Agent a[2];
        for(int i=0;i<2;++i) {
            std::vector<std::string> v(flat.begin()+6*i,flat.begin()+6*i+6);
            if(!parse_agent(v,a[i])){std::puts("invalid transition table");return 1;}
            a[i].pos=initial_pos[i];
        }
        Machine<2> m(h,p);m.reset(a);int r=m.run(limit);
        std::printf("result: %s after %llu steps\n",
            r==1?"HALT":r==0?"TIMEOUT":r==-2?"OUT_OF_BOUNDS":"UNDEFINED",
            (unsigned long long)m.steps);
        return 0;
    }
    if(cmd=="tnf") {
        int nt=argc>2?std::atoi(argv[2]):4;
        uint64_t limit=argc>3?std::strtoull(argv[3],nullptr,10):5000000;
        if(argc>4&&!parse_halt(argv[4],h)){std::puts("bad halt");return 1;}
        if(argc>5&&!parse_priority(argv[5],p)){std::puts("bad priority");return 1;}
        if(h!=COLLISION)std::puts("Note: TNF is specifically the two-agent collision search; using collision semantics.");
        run_tnf(std::max(1,nt),limit,p);return 0;
    }
    if(cmd=="search") {
        uint64_t trials=argc>2?std::strtoull(argv[2],nullptr,10):100000;
        uint64_t limit=argc>3?std::strtoull(argv[3],nullptr,10):1000000;
        int nt=argc>4?std::max(1,std::atoi(argv[4])):4;
        if(argc>5&&!parse_halt(argv[5],h)){std::puts("bad halt");return 1;}
        if(argc>6&&!parse_priority(argv[6],p)){std::puts("bad priority");return 1;}
        global_best=0;work_done=0;stop_search=false;
        random_search<2>(trials,limit,nt,h,p);
        std::printf("search done; tested=%llu best=%llu\n",
            (unsigned long long)work_done.load(),(unsigned long long)global_best);
        return 0;
    }
    if(cmd=="genetic") {
        int pop=argc>2?std::max(8,std::atoi(argv[2])):512;
        int gens=argc>3?std::max(1,std::atoi(argv[3])):500;
        uint64_t limit=argc>4?std::strtoull(argv[4],nullptr,10):5000000;
        int nt=argc>5?std::max(1,std::atoi(argv[5])):4;
        uint32_t seed=argc>6?uint32_t(std::strtoul(argv[6],nullptr,10)):123456789u;
        global_best=0;genetic_search(pop,gens,limit,nt,seed);return 0;
    }
    if(cmd=="enumerate") {
        uint64_t limit=argc>2?std::strtoull(argv[2],nullptr,10):1000000;
        int nt=argc>3?std::max(1,std::atoi(argv[3])):4;
        if(argc>4&&!parse_halt(argv[4],h)){std::puts("bad halt");return 1;}
        if(argc>5&&!parse_priority(argv[5],p)){std::puts("bad priority");return 1;}
        bool canon=argc>6?std::atoi(argv[6])!=0:true;
        enumerate<2>(nt,limit,h,p,canon);return 0;
    }
    usage();return 1;
}
