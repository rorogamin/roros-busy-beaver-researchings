#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static const Tr A1[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
static const Tr A2[3][2]={{{1,+1,1},{0,-1,0}},{{0,+1,2},{0,-1,0}},{{1,-1,1},{1,+1,2}}};
#define OFF 3000000
#define SZ 10000000
static unsigned char t[SZ];
int main(int c,char**v){long D=atol(v[1]),P=atol(v[2]),cap=atol(v[3]);memset(t,1,sizeof t);for(long z=-2;z<=2;z++)t[P+z+OFF]=0;t[P-1+OFF]=1;t[P+OFF]=1;t[P+1+OFF]=1;
 long p1=P-D+OFF,p2=P+OFF;int s1=1,s2=1;
 for(long k=1;k<=cap;k++){Tr x=A1[s1][t[p1]],y=A2[s2][t[p2]];t[p1]=x.w;t[p2]=y.w;p1+=x.d;s1=x.n;p2+=y.d;s2=y.n;if(p1==p2){printf("HALT D=%ld P=%ld k=%ld pos=%ld\n",D,P,k,p1-OFF);return 0;}}
 printf("NO D=%ld P=%ld p1=%ld p2=%ld s1=%d s2=%d\n",D,P,p1-OFF,p2-OFF,s1,s2);}
