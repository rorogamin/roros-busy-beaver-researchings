#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

#define TAPE_SIZE 1048576
#define TAPE_OFFSET 524288
#define MAX_STEPS 350000

typedef struct {
    int8_t write;
    int8_t move;
    int8_t next_state;
} Transition;

typedef struct {
    Transition t[2][3][2];
} Machine;

int main() {
    // Agent 1: (0, LEFT, 2), (1, LEFT, 0), (0, LEFT, 2), (0, LEFT, 1), (1, RIGHT, 1), (1, RIGHT, 2)
    // A0: (0, -1, 2)
    // A1: (1, -1, 0)
    // B0: (0, -1, 2)
    // B1: (0, -1, 1)
    // C0: (1,  1, 1)
    // C1: (1,  1, 2)

    // Agent 2: (1, RIGHT, 2), (0, RIGHT, 2), (1, RIGHT, 0), (1, LEFT, 1), (0, ...
    // A0: (1,  1, 2)
    // A1: (0,  1, 2)
    // B0: (1,  1, 0)
    // B1: (1, -1, 1)
    // C0: write = 0, move = ?, next_state = ?
    // C1: write = ?, move = ?, next_state = ?

    printf("Searching 72 completions of Agent 2 in C...\n");

    #pragma omp parallel for schedule(dynamic, 1)
    for (int idx = 0; idx < 72; idx++) {
        uint8_t *tape = (uint8_t*)calloc(TAPE_SIZE, 1);
        uint32_t *visited = (uint32_t*)calloc(TAPE_SIZE, sizeof(uint32_t));
        uint32_t marker = 1;

        int c0_move = (idx / 36) ? 1 : -1;
        int c0_next = (idx / 12) % 3;
        int c1_write = (idx / 6) % 2;
        int c1_move = ((idx / 3) % 2) ? 1 : -1;
        int c1_next = idx % 3;

        Machine m;
        // Agent 1
        m.t[0][0][0] = (Transition){0, -1, 2};
        m.t[0][0][1] = (Transition){1, -1, 0};
        m.t[0][1][0] = (Transition){0, -1, 2};
        m.t[0][1][1] = (Transition){0, -1, 1};
        m.t[0][2][0] = (Transition){1,  1, 1};
        m.t[0][2][1] = (Transition){1,  1, 2};

        // Agent 2
        m.t[1][0][0] = (Transition){1,  1, 2};
        m.t[1][0][1] = (Transition){0,  1, 2};
        m.t[1][1][0] = (Transition){1,  1, 0};
        m.t[1][1][1] = (Transition){1, -1, 1};
        m.t[1][2][0] = (Transition){0, c0_move, c0_next};
        m.t[1][2][1] = (Transition){c1_write, c1_move, c1_next};

        int p1 = TAPE_OFFSET;
        int p2 = TAPE_OFFSET + 2;
        int s1 = 0;
        int s2 = 0;
        int halted = 0;
        int step = 1;

        for (; step <= MAX_STEPS; step++) {
            uint8_t r1 = (visited[p1] == marker) ? tape[p1] : 0;
            uint8_t r2 = (visited[p2] == marker) ? tape[p2] : 0;

            Transition tr1 = m.t[0][s1][r1];
            Transition tr2 = m.t[1][s2][r2];

            visited[p2] = marker; tape[p2] = tr2.write;
            visited[p1] = marker; tape[p1] = tr1.write;

            p1 += tr1.move;
            p2 += tr2.move;

            s1 = tr1.next_state;
            s2 = tr2.next_state;

            if (p1 == p2) {
                halted = 1;
                break;
            }

            int dist = abs(p2 - p1);
            if (dist > 150) break; // diverged
        }

        if (halted && step > 200000) {
            #pragma omp critical
            {
                printf("\n>>> FOUND EXACT RECORD! <<<\n");
                printf("Steps: %d\n", step);
                printf("C0: (0, %s, %c), C1: (%d, %s, %c)\n",
                       c0_move > 0 ? "RIGHT" : "LEFT", 'A' + c0_next,
                       c1_write, c1_move > 0 ? "RIGHT" : "LEFT", 'A' + c1_next);
                printf("Agent 2 C-transitions: %d%c%c%d%c%c\n",
                       0, c0_move > 0 ? 'R' : 'L', 'A' + c0_next,
                       c1_write, c1_move > 0 ? 'R' : 'L', 'A' + c1_next);
                fflush(stdout);
            }
        }

        free(tape);
        free(visited);
    }

    printf("\nFinished checking all 72 branches.\n");
    return 0;
}
