#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
int main(){
    const char* H[] = {
        "1RB0LC_1LA1RB_1LA1LC_0RA0RA|1RC0RA_1RA1RB_1LC0LA_0RA0RC",
        "1LC0RD_1LA1RB_0RB1LC_0RA1LB|1RC0RA_1RA1RB_1LC0RD_0RC0RC",
        "1LC0LC_1LA1RB_1RD1LC_0RA1LD|0RC0RA_1RA1RB_1LC0RD_0RA0RC",
        "1LC0RD_1LA1RB_0RB1LC_0RA1LB|1RC0RA_1RA1RB_1LC0RD_0LA0RC",
        "1LC0RC_1LA1RB_0RB1LB_0RA0RA|1RC0RA_1RA1RB_1LC0RD_0LA0RC",
        "1LC0LC_1LA1RB_0RB1RB_0RD0RA|1RC0RA_1RA1RB_1LC0RD_0RC0RC",
        "1LC0LC_1LA1RB_0RB1RB_0LB0RA|1RC0RA_1RA1RB_1LC0RD_0RC0RC",
        "1LC0RC_1LA1RB_0RB1LB_0RA0RA|1RC0RA_1RA1RB_1LC0RD_0RC0RC"
    };
    const int T=1<<22,O=T/2;uint8_t*t=(uint8_t*)calloc(T,1);
    for(int h=0;h<8;h++){
        std::string M=H[h];
        int w[2][4][2],d[2][4][2],n[2][4][2];int a=0,q=0,b=0;
        for(size_t i=0;i<M.size();i++){char c=M[i];if(c=='|'){a=1;q=0;b=0;}else if(c=='_'){q++;b=0;}else{w[a][q][b]=c-'0';d[a][q][b]=M[i+1]=='R'?1:-1;n[a][q][b]=M[i+2]-'A';b++;i+=2;}}
        memset(t,0,T); int p0=0,p1=2,q0=0,q1=0; uint64_t s=0;
        printf("=== Holdout #%d: %s ===\n",h,H[h]);
        while(s<40000015ULL){
            int b0=t[p0+O],b1=t[p1+O];
            if(s>=40000000ULL) printf("  s=%llu p0=%d(%c%d) p1=%d(%c%d)\n",(unsigned long long)s,p0,'A'+q0,b0,p1,'A'+q1,b1);
            int w0=w[0][q0][b0],w1=w[1][q1][b1];int d0=d[0][q0][b0],d1=d[1][q1][b1],n0=n[0][q0][b0],n1=n[1][q1][b1];
            t[p0+O]=w0;if(p1!=p0)t[p1+O]=w1;p0+=d0;q0=n0;p1+=d1;q1=n1;s++;if(p0==p1)break;
        }
    }
}
