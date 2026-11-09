#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <vector>
int main(){const char*M="1RB0LC_1LA1RB_0RB1LC|1RB0RB_1LB0LC_1RB0RA";int w[2][3][2],d[2][3][2],n[2][3][2];int a=0,q=0,b=0;for(const char*c=M;*c;c++){if(*c=='|'){a=1;q=0;b=0;}else if(*c=='_'){q++;b=0;}else{w[a][q][b]=c[0]-'0';d[a][q][b]=c[1]=='R'?1:-1;n[a][q][b]=c[2]-'A';b++;c+=2;}}
const int T=1<<22,O=T/2;uint8_t*t=(uint8_t*)calloc(T,1);int p0=0,p1=2,q0=0,q1=0;uint64_t s=0;int mn=0,mx=2;
while(1){int b0=t[p0+O],b1=t[p1+O];int w0=w[0][q0][b0],w1=w[1][q1][b1];int d0=d[0][q0][b0],d1=d[1][q1][b1],n0=n[0][q0][b0],n1=n[1][q1][b1];t[p0+O]=w0;if(p1!=p0)t[p1+O]=w1;p0+=d0;q0=n0;p1+=d1;q1=n1;s++;if(p0==p1)break;if(p0<mn)mn=p0;if(p1<mn)mn=p1;if(p0>mx)mx=p0;if(p1>mx)mx=p1;if(s>20000000000ULL){puts("limit");return 0;}}
long ones=0;for(int i=mn+O;i<=mx+O;i++)ones+=t[i];printf("steps=%llu x=%d span=[%d,%d] ones=%ld\n",(unsigned long long)s,p0,mn,mx,ones);}
