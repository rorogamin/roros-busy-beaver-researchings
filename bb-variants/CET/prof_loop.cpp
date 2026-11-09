#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
int main(){std::string M="1RB0LC_1LA1RB_0RB1LC|1RB0RB_1LB0LC_1RB0RA";int w[2][3][2],d[2][3][2],n[2][3][2];int a=0,q=0,b=0;for(size_t i=0;i<M.size();i++){char c=M[i];if(c=='|'){a=1;q=0;b=0;}else if(c=='_'){q++;b=0;}else{w[a][q][b]=c-'0';d[a][q][b]=M[i+1]=='R'?1:-1;n[a][q][b]=M[i+2]-'A';b++;i+=2;}}
const int T=1<<22,O=T/2;uint8_t*t=(uint8_t*)calloc(T,1);int p0=0,p1=2,q0=0,q1=0;uint64_t s=0,both=0,one0=0,one1=0;
auto loop=[&](int ag,int qq,int bb){return n[ag][qq][bb]==qq&&w[ag][qq][bb]==bb;};
while(1){int b0=t[p0+O],b1=t[p1+O];bool l0=loop(0,q0,b0),l1=loop(1,q1,b1);if(l0&&l1)both++;else if(l0)one0++;else if(l1)one1++;
int w0=w[0][q0][b0],w1=w[1][q1][b1];int d0=d[0][q0][b0],d1=d[1][q1][b1],n0=n[0][q0][b0],n1=n[1][q1][b1];t[p0+O]=w0;if(p1!=p0)t[p1+O]=w1;p0+=d0;q0=n0;p1+=d1;q1=n1;s++;if(p0==p1)break;if(s>3000000000ULL)break;}
printf("steps=%llu both=%.3f only0=%.3f only1=%.3f\n",(unsigned long long)s,(double)both/s,(double)one0/s,(double)one1/s);}
