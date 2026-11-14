#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static const Tr A[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define N 50000000L
#define OFF 1000000L
static unsigned char t[N];
int main(int c,char**v){long L=70,M=c>1?atol(v[1]):1000000L,cap=c>2?atol(v[2]):500000000L;
 for(long x=-1;x<L-1;x++)t[x+OFF]=1;t[L-1+OFF]=0;for(long x=L;x<M;x++)t[x+OFF]=1;
 long p=L-1;int s=1; unsigned char seen[3*32*8];memset(seen,0,sizeof seen);int count=0;
 for(long tt=1;tt<=cap;tt++){Tr r=A[s][t[p+OFF]];if(r.d==0){printf("HALT %ld p=%ld\n",tt,p);return 0;}t[p+OFF]=r.w;p+=r.d;s=r.n;
  if(p>=66&&p<=71){int bits=0;for(int k=0;k<5;k++)bits|=t[67+k+OFF]<<k;int idx=(s*32+bits)*8+(p-66);if(!seen[idx]){seen[idx]=1;count++;printf("BOUND %d t=%ld p=%ld s=%d bits=%d\n",count,tt,p,s,bits);}}
  if(p>71){printf("EXCEED %ld p=%ld\n",tt,p);return 0;}
 }
 printf("END p=%ld s=%d count=%d\n",p,s,count);}
