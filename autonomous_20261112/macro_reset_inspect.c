#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static const Tr A1[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
static const Tr A2[3][2]={{{1,+1,1},{0,-1,0}},{{0,+1,2},{0,-1,0}},{{1,-1,1},{1,+1,2}}};
#define OFF 2000000
#define SZ 12000000
static unsigned char t[SZ];
int main(int c,char**v){long W=atol(v[1]),P=atol(v[2]),cap=atol(v[3]);memset(t,0,sizeof t);for(long x=W;x<SZ-OFF;x++)t[x+OFF]=1;t[P+OFF]=0;t[P+1+OFF]=1;t[P+2+OFF]=1;t[P-1+OFF]=1;t[P-2+OFF]=0;
 long p1=-2+OFF,p2=P+OFF;int s1=2,s2=1;int was=0;
 for(long k=1;k<=cap;k++){Tr x=A1[s1][t[p1]],y=A2[s2][t[p2]];t[p1]=x.w;t[p2]=y.w;p1+=x.d;s1=x.n;p2+=y.d;s2=y.n;if(p1==p2){printf("HALT\n");return 0;}if(p1-OFF>W)was=1;if(was&&p1-OFF==-2){printf("reset k=%ld p2=%ld s2=%d tape p2",k,p2-OFF,s2);for(long z=-5;z<=10;z++)printf("%d",t[p2+z]);printf("\n");return 0;}}
}
