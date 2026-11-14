#include <stdio.h>
#include <stdlib.h>
typedef struct{int w,d,n;}Tr;
static const Tr A[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define N 20000000L
#define OFF 1000000L
static unsigned char t[N];
int main(int c,char**v){long L=c>1?atol(v[1]):70,cap=c>2?atol(v[2]):100000000L;
 for(long x=-1;x<L-1;x++)t[x+OFF]=1; t[L-1+OFF]=0;
 for(long x=L;x<10000000;x++)t[x+OFF]=1;
 long p=L-1;int s=0;long mn=0,mx=0;
 for(long tt=1;tt<=cap;tt++){
  Tr r=A[s][t[p+OFF]]; if(r.d==0){printf("HALT %ld p=%ld\n",tt,p);return 0;}
  t[p+OFF]=r.w;p+=r.d;s=r.n;if(p<mn)mn=p;if(p>mx)mx=p;
  if(tt%100000000L==0)printf("t=%ld p=%ld s=%d min=%ld max=%ld\n",tt,p,s,mn,mx);
 }
 printf("END t=%ld p=%ld s=%d min=%ld max=%ld\n",cap,p,s,mn,mx);}
