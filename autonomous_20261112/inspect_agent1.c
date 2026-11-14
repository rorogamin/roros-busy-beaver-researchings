#include <stdio.h>
#include <stdlib.h>
typedef struct{int w,d,n;}Tr;
static const Tr A[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define N 1000000
static unsigned char t[N]; static long OFF=100000;
int main(int c,char**v){long L=c>1?atol(v[1]):70; for(long x=-1;x<L-1;x++)t[x+OFF]=1; t[L-1+OFF]=0; long p=L-1; int s=0;
 for(long tt=1;tt<20000000;tt++){Tr r=A[s][t[p+OFF]]; if(r.d==0){printf("HALT %ld\n",tt);break;}
  t[p+OFF]=r.w; p+=r.d; s=r.n;
  if(p>=L-1 && tt<10000){printf("t=%ld p=%ld s=%d local=",tt,p,s);for(long x=L-6;x<=L+4;x++)putchar(t[x+OFF]?'1':'0');putchar('\n');}
  if(p>L){printf("EXCEED t=%ld p=%ld s=%d local=",tt,p,s);for(long x=L-6;x<=L+4;x++)putchar(t[x+OFF]?'1':'0');putchar('\n');return 0;}
 }
 printf("done p=%ld s=%d\n",p,s);}
