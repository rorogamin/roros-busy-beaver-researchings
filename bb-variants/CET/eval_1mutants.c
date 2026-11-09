#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

#define N 3
#define TAPE_SIZE 20000000
#define CENTER    10000000
#define MAX_STEPS 10000000

typedef struct {
    int8_t ns, w, d;
} Tr;

// Base champion 4,657,368
// CHAMPION_TA = [
//     [(1, 0, -1), (1, 0, -1)],
//     [(2, 0,  1), (0, 1, -1)],
//     [(1, 1, -1), (2, 1,  1)],
// ]
// CHAMPION_TB = [
//     [(1, 0,  1), (2, 1,  1)],
//     [(2, 1,  1), (0, 0,  1)],
//     [(2, 1, -1), (1, 0, -1)],
// ]

static const Tr base_tA[3][2] = {
    { {1, 0, -1}, {1, 0, -1} },
    { {2, 0,  1}, {0, 1, -1} },
    { {1, 1, -1}, {2, 1,  1} }
};

static const Tr base_tB[3][2] = {
    { {1, 0,  1}, {2, 1,  1} },
    { {2, 1,  1}, {0, 0,  1} },
    { {2, 1, -1}, {1, 0, -1} }
};

long long run_sim(const Tr tA[3][2], const Tr tB[3][2], int8_t *tape) {
    int pA = CENTER;
    int pB = CENTER + 2;
    int sA = 0, sB = 0;
    
    // Track min/max to clear tape efficiently
    int min_pos = pA, max_pos = pB;
    
    long long col_step = -1;

    for (long long step = 0; step < MAX_STEPS; step++) {
        if (pA == pB) {
            col_step = step;
            break;
        }
        
        int8_t symA = tape[pA];
        int8_t symB = tape[pB];
        
        Tr trA = tA[sA][symA];
        Tr trB = tB[sB][symB];
        
        tape[pA] = trA.w;
        tape[pB] = trB.w;
        
        pA += trA.d;
        pB += trB.d;
        
        sA = trA.ns;
        sB = trB.ns;
        
        if (pA < min_pos) min_pos = pA; if (pA > max_pos) max_pos = pA;
        if (pB < min_pos) min_pos = pB; if (pB > max_pos) max_pos = pB;
        
        if (pA < 0 || pA >= TAPE_SIZE || pB < 0 || pB >= TAPE_SIZE) {
            col_step = -2; // OOB
            break;
        }
    }
    
    // Clear tape in used region
    for (int i = min_pos; i <= max_pos; i++) {
        tape[i] = 0;
    }
    
    return col_step;
}

void fmt_agent(const Tr t[3][2], char *buf) {
    char *p = buf;
    for (int s = 0; s < 3; s++) {
        if (s > 0) *p++ = '_';
        for (int sym = 0; sym < 2; sym++) {
            *p++ = '0' + t[s][sym].w;
            *p++ = t[s][sym].d > 0 ? 'R' : 'L';
            *p++ = 'A' + t[s][sym].ns;
        }
    }
    *p = 0;
}

int main() {
    printf("Evaluating all 1-mutants of 4.65M champion...\n");
    fflush(stdout);

    int8_t *tape = (int8_t *)calloc(TAPE_SIZE, 1);
    
    // Sanity check
    long long base_res = run_sim(base_tA, base_tB, tape);
    printf("Sanity check base champion: %lld (expected 4657368)\n", base_res);
    fflush(stdout);

    Tr curA[3][2], curB[3][2];
    
    // Test mutating tA
    for (int s = 0; s < 3; s++) {
        for (int sym = 0; sym < 2; sym++) {
            for (int ns = 0; ns < 3; ns++) {
                for (int w = 0; w < 2; w++) {
                    for (int d = -1; d <= 1; d += 2) {
                        if (ns == base_tA[s][sym].ns && w == base_tA[s][sym].w && d == base_tA[s][sym].d) continue;
                        
                        memcpy(curA, base_tA, sizeof(curA));
                        curA[s][sym].ns = ns;
                        curA[s][sym].w = w;
                        curA[s][sym].d = d;
                        
                        long long res = run_sim(curA, base_tB, tape);
                        if (res > 4000000) {
                            char strA[32], strB[32];
                            fmt_agent(curA, strA);
                            fmt_agent(base_tB, strB);
                            printf("MUT tA[s=%d,sym=%d]: %lld steps | %s|%s\n", s, sym, res, strA, strB);
                            fflush(stdout);
                        }
                    }
                }
            }
        }
    }

    // Test mutating tB
    for (int s = 0; s < 3; s++) {
        for (int sym = 0; sym < 2; sym++) {
            for (int ns = 0; ns < 3; ns++) {
                for (int w = 0; w < 2; w++) {
                    for (int d = -1; d <= 1; d += 2) {
                        if (ns == base_tB[s][sym].ns && w == base_tB[s][sym].w && d == base_tB[s][sym].d) continue;
                        
                        memcpy(curB, base_tB, sizeof(curB));
                        curB[s][sym].ns = ns;
                        curB[s][sym].w = w;
                        curB[s][sym].d = d;
                        
                        long long res = run_sim(base_tA, curB, tape);
                        if (res > 4000000) {
                            char strA[32], strB[32];
                            fmt_agent(base_tA, strA);
                            fmt_agent(curB, strB);
                            printf("MUT tB[s=%d,sym=%d]: %lld steps | %s|%s\n", s, sym, res, strA, strB);
                            fflush(stdout);
                        }
                    }
                }
            }
        }
    }

    free(tape);
    printf("1-mutant scan complete.\n");
    return 0;
}
