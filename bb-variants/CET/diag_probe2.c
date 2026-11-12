#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { int w, d, ns; } Tr;
static int parse_ag(const char *s, Tr *T, int *NS, int *NSYM) {
    int states = 1, len = (int)strlen(s);
    for (int i = 0; i < len; i++) if (s[i] == '_') states++;
    *NS = states;
    const char *us = strchr(s, '_');
    int per = us ? (int)(us - s) : len;
    *NSYM = per / 3;
    const char *p = s;
    for (int q = 0; q < *NS; q++) {
        for (int b = 0; b < *NSYM; b++) {
            T[q * (*NSYM) + b] = (Tr){p[0]-'0', p[1]=='R'?1:-1, p[2]-'A'};
            p += 3;
        }
        if (*p == '_') p++;
    }
    return 1;
}

int main(void) {
    Tr T1[12], T2[12]; int NS, NSYM;
    parse_ag("1LB0RA_1LC1RB_0RB0LC", T1, &NS, &NSYM);
    parse_ag("1RB0LB_0RC0LA_1LB1RC", T2, &NS, &NSYM);
    /* Run full CET3_3round from scratch for L_1=10 simulated via clean setup vs concrete tape at gap=16 */
    /* Wait: look at what gap=16 left when lp1 < OFF - 8 */
    uint8_t tp[2048]; int OFF = 1000, L = 12, gap = 16;
    for (int i=0;i<OFF-L;i++) tp[i]=0;
    for (int i=OFF-L;i<OFF+gap;i++) tp[i]=1;
    for (int i=OFF+gap;i<2048;i++) tp[i]=0;
    /* Wait: pat for CET3_3round at gap=16: let's just copy from t=5000! */
    uint8_t *t0 = calloc(131072, 1);
    int p1=2000, p2=2002, s1=0, s2=0;
    for (int t=1;t<=5000;t++){ Tr x=T1[s1*2+t0[p1]], y=T2[s2*2+t0[p2]]; t0[p2]=y.w; t0[p1]=x.w; p1+=x.d; s1=x.ns; p2+=y.d; s2=y.ns; }
    /* Advance p2 until s2==C (gl_s) */
    for (int k=0;k<13;k++) { if (s2==2) break; Tr y=T2[s2*2+t0[p2]]; t0[p2]=y.w; p2+=y.d; s2=y.ns; }
    for (int i=0;i<96;i++) tp[OFF+gap-11+i] = t0[p2-11+i];
    int lp1=OFF, ls1=1, lp2=OFF+gap, ls2=s2;
    for (long long t=1; t<=450; t++) {
        Tr x=T1[ls1*2+tp[lp1]], y=T2[ls2*2+tp[lp2]];
        tp[lp2]=y.w; tp[lp1]=x.w; lp1+=x.d; ls1=x.ns; lp2+=y.d; ls2=y.ns;
        if (lp1<OFF-8 && lp2>OFF+gap && lp2-lp1>16) {
            printf("After bounce t=%lld lp1=%d ls1=%c tape[985..1020]=", t, lp1-OFF, 'A'+ls1);
            for (int z=OFF-15; z<=OFF+20; z++) putchar('0'+tp[z]);
            putchar('\n');
            for (int i=lp2-5; i<2048; i++) if (i>=OFF+gap) tp[i]=1;
            int mx = lp1;
            for (long long st=t+1; st<=10000000; st++) {
                Tr xx=T1[ls1*2+tp[lp1]]; tp[lp1]=xx.w; lp1+=xx.d; ls1=xx.ns;
                if (lp1 > mx) mx = lp1;
                if (lp1 > OFF + 40) { printf("Exceeded OFF+40 at st=%lld!\n", st); break; }
                if (st < t+30) {}
            }
            break;
        }
    }
    return 0;
}
