#include <stdio.h>
#include <stdint.h>
#include <string.h>
int main() {
    // 0LB---_0RC0LB_1LB1RC | 0RB0LA_1LA0RC_0LB0RA
    int w1[3][2]={{0,-1},{0,0},{1,1}}, d1[3][2]={{-1,0},{1,-1},{-1,1}}, n1[3][2]={{1,0},{2,1},{1,2}};
    int w2[3][2]={{0,0},{1,0},{0,0}}, d2[3][2]={{1,-1},{-1,1},{-1,1}}, n2[3][2]={{1,0},{0,2},{1,0}};
    static uint8_t tp[4096];
    int p1=2048, p2=2050, s1=0, s2=0, mn=2048, mx=2050;
    for (long long t=1; t<=100000000LL; t++) {
        int r1=tp[p1], r2=tp[p2];
        tp[p2]=w2[s2][r2]; tp[p1]=w1[s1][r1];
        if (p1<mn) mn=p1; if (p1>mx) mx=p1;
        if (p2<mn) mn=p2; if (p2>mx) mx=p2;
        p1+=d1[s1][r1]; s1=n1[s1][r1];
        p2+=d2[s2][r2]; s2=n2[s2][r2];
        if (p1==p2) { printf("HALT at %lld\n", t); return 0; }
    }
    printf("100M: p1=%d p2=%d [%d,%d]\n", p1-2048, p2-2048, mn-2048, mx-2048);
    return 0;
}
