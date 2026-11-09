#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <cuda_runtime.h>
#include <omp.h>

// ============================================================================
// A100 HIGH-THROUGHPUT CUDA SCREENER + DEEP CPU VERIFIER
// ============================================================================

#define BATCH_SIZE 524288 // 512k candidates per GPU launch
#define LOCAL_TAPE 1024
#define LOCAL_OFF  512
#define GPU_STEPS  20000

#define DEEP_TAPE_SIZE 16777216
#define DEEP_TAPE_OFF  8388608
#define DEEP_HORIZON   250000000ULL

struct Tr { int8_t w, mv, ns; };
struct Cet3Candidate { struct Tr t[2][3][2]; };
struct Cet23Candidate { struct Tr t[2][2][3]; };
struct Cet4Candidate { struct Tr t[2][4][2]; };

__device__ inline uint64_t dev_splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

// ----------------------------------------------------------------------------
// CUDA KERNEL 1: CET(3) Screen
// ----------------------------------------------------------------------------
__global__ void gpu_screen_cet3(uint64_t seed_base, struct Cet3Candidate *d_cand, int *d_res, int *d_pos) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= BATCH_SIZE) return;

    uint64_t rng = seed_base + (uint64_t)idx * 104729ULL + 1ULL;
    for (int i = 0; i < 5; i++) dev_splitmix(&rng);

    struct Cet3Candidate m;
    // Generate Tree Normal Form
    for (int a = 0; a < 2; a++) {
        int max_s = 0;
        for (int s = 0; s < 3; s++) {
            for (int r = 0; r < 2; r++) {
                uint64_t v = dev_splitmix(&rng);
                m.t[a][s][r].w = v & 1;
                m.t[a][s][r].mv = (v & 2) ? 1 : -1;
                int lim = max_s + 1;
                if (lim > 2) lim = 2;
                int ns = (v >> 2) % (lim + 1);
                m.t[a][s][r].ns = ns;
                if (ns > max_s) max_s = ns;
            }
        }
    }

    if (m.t[0][0][0].mv == -1 && m.t[1][0][0].mv == 1 && m.t[0][0][0].w == 0 && m.t[1][0][0].w == 0) {
        d_res[idx] = -1;
        return;
    }

    uint8_t tape[LOCAL_TAPE] = {0};
    int p1 = LOCAL_OFF + 0, p2 = LOCAL_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    int res = -2, pos = 0;

    for (int step = 1; step <= GPU_STEPS; step++) {
        if (p1 <= 10 || p1 >= LOCAL_TAPE - 10 || p2 <= 10 || p2 >= LOCAL_TAPE - 10) { res = -1; break; }
        uint8_t r1 = tape[p1], r2 = tape[p2];
        struct Tr tr1 = m.t[0][s1][r1], tr2 = m.t[1][s2][r2];
        tape[p2] = tr2.w; tape[p1] = tr1.w;
        p1 += tr1.mv; p2 += tr2.mv; s1 = tr1.ns; s2 = tr2.ns;
        if (p1 == p2) { res = step; pos = p1 - LOCAL_OFF; break; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 100) { res = -1; break; }
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = step; }
        if (h > hi) { hi = h; last_exp = step; }
        if (step > 4000 && (step - last_exp > 4000)) { res = -3; break; }
    }

    d_res[idx] = res;
    d_pos[idx] = pos;
    if (res == -2 || res > 15000) {
        d_cand[idx] = m;
    }
}

static void fmt_cet3(const struct Cet3Candidate *m, char *b) {
    char *p = b;
    for (int a = 0; a < 2; a++) {
        if (a) *p++ = '|';
        for (int s = 0; s < 3; s++) {
            if (s) *p++ = '_';
            for (int r = 0; r < 2; r++) {
                struct Tr x = m->t[a][s][r];
                *p++ = '0' + x.w; *p++ = x.mv > 0 ? 'R' : 'L'; *p++ = 'A' + x.ns;
            }
        }
    }
    *p = 0;
}

static int cpu_verify_cet3(const struct Cet3Candidate *m, uint8_t *tape, uint32_t *vis, uint32_t mk, int *pos) {
    int p1 = DEEP_TAPE_OFF, p2 = DEEP_TAPE_OFF + 2, s1 = 0, s2 = 0;
    int lo = p1, hi = p2, last_exp = 0;
    for (uint64_t step = 1; step <= DEEP_HORIZON; step++) {
        if (p1 <= 100 || p1 >= DEEP_TAPE_SIZE - 100 || p2 <= 100 || p2 >= DEEP_TAPE_SIZE - 100) return -1;
        uint8_t r1 = (vis[p1] == mk) ? tape[p1] : 0;
        uint8_t r2 = (vis[p2] == mk) ? tape[p2] : 0;
        struct Tr a = m->t[0][s1][r1], b = m->t[1][s2][r2];
        vis[p2] = mk; tape[p2] = b.w;
        vis[p1] = mk; tape[p1] = a.w;
        p1 += a.mv; p2 += b.mv; s1 = a.ns; s2 = b.ns;
        if (p1 == p2) { *pos = p1 - DEEP_TAPE_OFF; return (int)step; }
        int d = p2 - p1; if (d < 0) d = -d;
        if (d > 7000) return -1;
        int l = p1 < p2 ? p1 : p2, h = p1 > p2 ? p1 : p2;
        if (l < lo) { lo = l; last_exp = (int)step; }
        if (h > hi) { hi = h; last_exp = (int)step; }
        if (step > 1500000 && ((int)step - last_exp > 1500000)) return -3;
    }
    return -2;
}

int main(int argc, char **argv) {
    int duration = 7200; // 2 hours default
    if (argc > 1) duration = atoi(argv[1]);

    printf("=========================================================================================================\n");
    printf("⚡🚀 NVIDIA A100-SXM4 GPU ULTRA-MEGA CET SEARCH (%d s) 🚀⚡\n", duration);
    printf("=========================================================================================================\n");
    printf("Hardware: NVIDIA A100 (40GB VRAM, 6912 CUDA Cores) + Multi-threaded Host\n");
    printf("Batch Size: %d candidates / launch | Fast GPU Screen: %d steps\n", BATCH_SIZE, GPU_STEPS);
    printf("Targets to Beat:\n");
    printf("  • CET(3) Champion:   4,657,368 Steps (Nath76)\n");
    printf("  • CET(2,3) Champion: 20,350 Steps\n");
    printf("  • CET(4) Champion:   65,579,412 Steps\n");
    fflush(stdout);

    struct Cet3Candidate *d_cand;
    int *d_res, *d_pos;
    cudaMalloc(&d_cand, BATCH_SIZE * sizeof(struct Cet3Candidate));
    cudaMalloc(&d_res, BATCH_SIZE * sizeof(int));
    cudaMalloc(&d_pos, BATCH_SIZE * sizeof(int));

    struct Cet3Candidate *h_cand = (struct Cet3Candidate *)malloc(BATCH_SIZE * sizeof(struct Cet3Candidate));
    int *h_res = (int *)malloc(BATCH_SIZE * sizeof(int));
    int *h_pos = (int *)malloc(BATCH_SIZE * sizeof(int));

    uint8_t *cpu_tape = (uint8_t *)calloc(DEEP_TAPE_SIZE, 1);
    uint32_t *cpu_vis = (uint32_t *)calloc(DEEP_TAPE_SIZE, 4);
    uint32_t mk = 1;

    int best_cet3 = 4657368, best_cet3_pos = -224;
    char bb_cet3[128] = "0LB0LB_0RC1LA_1LB1RC|0RB1RC_1RC0RA_1LC0LB";

    uint64_t seed = (uint64_t)time(NULL) * 6364136223846793005ULL;
    double t0 = omp_get_wtime();
    long long total_gpu_screened = 0;
    long long total_deep_evaluated = 0;
    double last_heartbeat = omp_get_wtime();

    int threads = 256;
    int blocks = (BATCH_SIZE + threads - 1) / threads;

    while (omp_get_wtime() - t0 < duration) {
        seed += 0x9e3779b97f4a7c15ULL;
        gpu_screen_cet3<<<blocks, threads>>>(seed, d_cand, d_res, d_pos);
        cudaDeviceSynchronize();

        cudaMemcpy(h_res, d_res, BATCH_SIZE * sizeof(int), cudaMemcpyDeviceToHost);
        cudaMemcpy(h_pos, d_pos, BATCH_SIZE * sizeof(int), cudaMemcpyDeviceToHost);
        cudaMemcpy(h_cand, d_cand, BATCH_SIZE * sizeof(struct Cet3Candidate), cudaMemcpyDeviceToHost);

        total_gpu_screened += BATCH_SIZE;

        for (int i = 0; i < BATCH_SIZE; i++) {
            if (h_res[i] == -2 || h_res[i] > 18000) {
                total_deep_evaluated++;
                if (++mk == 0) { memset(cpu_vis, 0, DEEP_TAPE_SIZE * 4); mk = 1; }
                int pos = 0;
                int s = cpu_verify_cet3(&h_cand[i], cpu_tape, cpu_vis, mk, &pos);
                if (s > best_cet3) {
                    best_cet3 = s; best_cet3_pos = pos;
                    fmt_cet3(&h_cand[i], bb_cet3);
                    printf("\n🔥🔥🔥🏆💥 [NEW A100 ALL-TIME WORLD RECORD: %d STEPS at cell %d!] 💥🏆🔥🔥🔥\n", s, pos);
                    printf("bbchallenge: %s\n\n", bb_cet3);
                    fflush(stdout);
                } else if (s > 1000000) {
                    char b[128]; fmt_cet3(&h_cand[i], b);
                    printf("  [A100 Mega Holdout >1M]: %d steps at cell %d | %s\n", s, pos, b);
                    fflush(stdout);
                }
            }
        }

        if (omp_get_wtime() - last_heartbeat > 30.0) {
            last_heartbeat = omp_get_wtime();
            double el = omp_get_wtime() - t0;
            printf("[T+%.0fs / %ds] Screened %lld machines (%.0f machines/sec) | Deep CPU verifies: %lld | Best: %d\n",
                   el, duration, total_gpu_screened, total_gpu_screened / el, total_deep_evaluated, best_cet3);
            fflush(stdout);
        }
    }

    double total_time = omp_get_wtime() - t0;
    printf("\n=========================================================================================================\n");
    printf("🏁 2-HOUR A100 EXPEDITION FINISHED in %.1fs\n", total_time);
    printf("Total Machines Screened by NVIDIA A100: %lld (%.0f machines/sec)\n", total_gpu_screened, total_gpu_screened / total_time);
    printf("Pushed to Deep CPU Verification: %lld\n", total_deep_evaluated);
    printf("Champion: %d steps at cell %d\n", best_cet3, best_cet3_pos);
    printf("bbchallenge: %s\n", bb_cet3);
    printf("=========================================================================================================\n");

    cudaFree(d_cand); cudaFree(d_res); cudaFree(d_pos);
    free(h_cand); free(h_res); free(h_pos);
    free(cpu_tape); free(cpu_vis);

    return 0;
}
