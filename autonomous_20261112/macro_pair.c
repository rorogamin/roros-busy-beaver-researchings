#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static const Tr A1[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
static const Tr A2[3][2]={{{1,+1,1},{0,-1,0}},{{0,+1,2},{0,-1,0}},{{1,-1,1},{1,+1,2}}};
#define OFF 1000000
#define SZ 20000000
static unsigned char t[SZ];
int main(int c,char**v){long W=atol(v[1]),P=atol(v[2]),cap=atol(v[3]);memset(t,0,sizeof t);for(long x=W;x<SZ-OFF;x++)t[x+OFF]=1;
 long p1=-2+OFF,p2=P+OFF;int s1=2,s2=1;t[p2-2+OFF]=0;t[p2-1+OFF]=1;t[p2+OFF]=1;t[p2+1+OFF]=1;t[p2+2+OFF]=0;
 for(long k=1;k<=cap;k++){Tr x=A1[s1][t[p1]],y=A2[s2][t[p2]];t[p1]=x.w;t[p2]=y.w;p1+=x.d;s1=x.n;p2+=y.d;s2=y.n;if(p1==p2){printf("HALT W=%ld P=%ld k=%ld pos=%ld\n",W,P,k,p1-OFF);return 0;}if(p2>=SZ-100){printf("EDGE\n");return 0;}}
 printf("NOHALT W=%ld P=%ld p1=%ld p2=%ld s1=%d s2=%d\n",W,P,p1-OFF,p2-OFF,s1,s2);}
