#include <stdio.h>
#include <stdlib.h>
typedef struct{int w,d,n;}Tr;
static const Tr A[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define N 50000000L
#define OFF 1000000L
static unsigned char t[N];
int main(int c,char**v){long L=70,M=c>1?atol(v[1]):100000L,cap=c>2?atol(v[2]):2000000L;
 for(long x=-1;x<L-1;x++)t[x+OFF]=1;t[L-1+OFF]=0;
 for(long x=L;x<M;x++)t[x+OFF]=1;
 long p=L-1;int s=0;long mn=0,mx=0;
 for(long tt=1;tt<=cap;tt++){Tr r=A[s][t[p+OFF]];if(r.d==0){printf("HALT %ld\n",tt);return 0;}t[p+OFF]=r.w;p+=r.d;s=r.n;if(p<mn)mn=p;if(p>mx)mx=p;}
 printf("M=%ld cap=%ld p=%ld s=%d min=%ld max=%ld\n",M,cap,p,s,mn,mx);}
