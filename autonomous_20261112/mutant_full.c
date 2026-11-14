#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static const Tr A1[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
static const Tr CH[3][2]={{{1,+1,1},{0,-1,1}},{{0,+1,2},{0,-1,0}},{{1,-1,1},{1,+1,2}}};
#define OFF 3000000
#define SZ 9000000
static unsigned char t[SZ];
static int run(Tr a2[3][2],long cap,long*when){memset(t,0,sizeof t);long p1=OFF,p2=OFF+2;int s1=0,s2=0;
 for(long k=1;k<=cap;k++){Tr x=A1[s1][t[p1]],y=a2[s2][t[p2]];t[p1]=x.w;t[p2]=y.w;p1+=x.d;s1=x.n;p2+=y.d;s2=y.n;if(p1==p2){*when=k;return 1;}if(p1<SZ-1000||p2>=SZ-1000)return -1;}
 *when=cap;return 0;}
int main(int c,char**v){long cap=c>1?atol(v[1]):2000000;int ws[2]={0,1},ds[2]={-1,1},ns[3]={0,1,2};long best=0;
 for(int base=0;base<2;base++)for(int e=0;e<6;e++)for(int wi=0;wi<2;wi++)for(int di=0;di<2;di++)for(int ni=0;ni<3;ni++){Tr a2[3][2];memcpy(a2,CH,sizeof a2);if(base==1)a2[0][1]=(Tr){0,-1,0};a2[e/2][e%2]=(Tr){ws[wi],ds[di],ns[ni]};long when;int r=run(a2,cap,&when);if(r==1){printf("base%d e%d %d%c%c HALT %ld\n",base,e,ws[wi],ds[di]<0?'L':'R',"ABC"[ns[ni]],when);if(when>best)best=when;}}
 printf("best=%ld cap=%ld\n",best,cap);}
