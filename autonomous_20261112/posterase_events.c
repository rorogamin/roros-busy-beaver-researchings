#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static const Tr A[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define OFF 3000000
#define SZ 7000000
static unsigned char t[SZ];
int main(int c,char**v){long cap=c>1?atol(v[1]):1000000000L;for(long W=4;W<=30;W++){memset(t,0,sizeof t);for(long x=W;x<SZ-OFF;x++)t[x+OFF]=1;long p=-2+OFF;int s=2;long cross=-1,p0=0;int s0=0;
 for(long k=1;k<=cap;k++){Tr r=A[s][t[p]];t[p]=r.w;p+=r.d;s=r.n;if(cross<0&&p-OFF>W){cross=k;p0=p-OFF;s0=s;}if(k==cap||(cross>0&&k==cross+1000)){if(cross>0){printf("W=%ld cross_t=%ld p0=%ld s0=%d at+1000 p=%ld s=%d max?\n",W,cross,p0,s0,p-OFF,s);}else printf("W=%ld no cross cap p=%ld s=%d\n",W,p-OFF,s);break;}}
 }
}
