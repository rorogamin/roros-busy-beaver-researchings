#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

// Enumerate TNF for single 3-state, 2-symbol Turing Machine.
// Transitions are indexed: state*2 + read_symbol (0..5)
// Initial entry point is (state=0, read=0) -> index 0.

typedef struct {
    int8_t w, mv, ns;
} Tr;

typedef struct {
    Tr t[3][2];
} TM3;

TM3 *tnf_list = NULL;
int tnf_count = 0;
int tnf_cap = 0;

void add_tnf(const TM3 *m) {
    if (tnf_count >= tnf_cap) {
        tnf_cap = tnf_cap ? tnf_cap * 2 : 65536;
        tnf_list = realloc(tnf_list, tnf_cap * sizeof(TM3));
    }
    tnf_list[tnf_count++] = *m;
}

// Generate all standard Tree Normal Form 3-state machines
void gen_tnf(TM3 *cur, int s, int r, int max_state_seen) {
    if (s == 3) {
        add_tnf(cur);
        return;
    }
    int next_s = s;
    int next_r = r + 1;
    if (next_r == 2) {
        next_r = 0;
        next_s++;
    }

    for (int w = 0; w <= 1; w++) {
        for (int mv = -1; mv <= 1; mv += 2) {
            // Next state can be any state seen so far, or at most max_state_seen + 1 (capped at 2)
            int limit = max_state_seen + 1;
            if (limit > 2) limit = 2;
            for (int ns = 0; ns <= limit; ns++) {
                cur->t[s][r].w = w;
                cur->t[s][r].mv = mv;
                cur->t[s][r].ns = ns;
                int new_max = ns > max_state_seen ? ns : max_state_seen;
                gen_tnf(cur, next_s, next_r, new_max);
            }
        }
    }
}

int main() {
    TM3 cur;
    memset(&cur, 0, sizeof(cur));
    // Start at state 0, reading 0, with max_state_seen = 0 (State A)
    // Convention: state 0 reading 0 must transition to state 0 or state 1 (State B)
    gen_tnf(&cur, 0, 0, 0);
    printf("Total Single-Agent 3-State TNF Machines: %d\n", tnf_count);
    return 0;
}
