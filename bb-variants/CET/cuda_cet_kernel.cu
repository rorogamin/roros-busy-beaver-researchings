#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <cuda_runtime.h>

// CUDA Kernel for massive parallel CET screening
// Each thread simulates one machine candidate up to FAST_STEPS
#define BLOCK_SIZE 256
#define LOCAL_TAPE_SIZE 2048
#define LOCAL_TAPE_OFF 1024
#define FAST_STEPS 30000

struct Transition {
    int8_t write;
    int8_t move;
    int8_t next;
};

// 3 states, 2 symbols for each of 2 agents
struct MachineCandidate {
    Transition t[2][3][2];
};

__device__ inline uint64_t splitmix64_dev(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

__global__ void screen_cet3_kernel(uint64_t seed_base, int n_candidates, int *out_steps, int *out_pos, MachineCandidate *out_machines) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_candidates) return;

    uint64_t rng = seed_base + (uint64_t)idx * 104729ULL + 1ULL;
    for (int i = 0; i < 10; i++) splitmix64_dev(&rng);

    MachineCandidate m;
    // Generate Tree Normal Form candidate
    for (int a = 0; a < 2; a++) {
        int max_s = 0;
        for (int s = 0; s < 3; s++) {
            for (int r = 0; r < 2; r++) {
                uint64_t v = splitmix64_dev(&rng);
                m.t[a][s][r].write = v & 1;
                m.t[a][s][r].move = (v & 2) ? 1 : -1;
                int lim = max_s + 1;
                if (lim > 2) lim = 2;
                int ns = (v >> 2) % (lim + 1);
                m.t[a][s][r].next = ns;
                if (ns > max_s) max_s = ns;
            }
        }
    }

    // Fast divergence reject
    if (m.t[0][0][0].move == -1 && m.t[1][0][0].move == 1 && m.t[0][0][0].write == 0 && m.t[1][0][0].write == 0) {
        out_steps[idx] = -1;
        return;
    }

    // Fast local shared or thread-local tape
    uint8_t tape[LOCAL_TAPE_SIZE] = {0};
    int p1 = LOCAL_TAPE_OFF + 0;
    int p2 = LOCAL_TAPE_OFF + 2;
    int s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;

    int res_step = -2;
    int res_pos = 0;

    for (int step = 1; step <= FAST_STEPS; step++) {
        if (p1 <= 10 || p1 >= LOCAL_TAPE_SIZE - 10 || p2 <= 10 || p2 >= LOCAL_TAPE_SIZE - 10) {
            res_step = -1;
            break;
        }

        uint8_t r1 = tape[p1];
        uint8_t r2 = tape[p2];

        Transition tr1 = m.t[0][s1][r1];
        Transition tr2 = m.t[1][s2][r2];

        tape[p2] = tr2.write;
        tape[p1] = tr1.write;

        p1 += tr1.move;
        p2 += tr2.move;
        s1 = tr1.next;
        s2 = tr2.next;

        if (p1 == p2) {
            res_step = step;
            res_pos = p1 - LOCAL_TAPE_OFF;
            break;
        }

        int d = p2 - p1;
        if (d < 0) d = -d;
        if (d > 100) { res_step = -1; break; }

        int l = p1 < p2 ? p1 : p2;
        int h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }

        if (step > 4000 && (step - last_exp > 4000)) { res_step = -3; break; }
    }

    out_steps[idx] = res_step;
    out_pos[idx] = res_pos;
    if (res_step == -2 || res_step > 20000) {
        out_machines[idx] = m;
    }
}
