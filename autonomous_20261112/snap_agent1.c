#include <stdio.h>
#include <stdlib.h>
typedef struct{int w,d,n;}Tr;
static const Tr A1[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define N 20000000L
#define OFF 1000000L
static unsigned char t[N];
int main(int c,char**v){long L=c>1?atol(v[1]):70; long cap=c>2?atol(v[2]):100000000L;
 for(long x=-1;x<L-1;x++)t[x+OFF]=1;t[L-1+OFF]=0;
 long p=L-1;int s=0;
 for(long tt=1;tt<=cap;tt++){
  Tr r=A1[s][t[p+OFF]]; if(r.d==0){printf("HALT %ld\n",tt);return 0;}
  t[p+OFF]=r.w;p+=r.d;s=r.n;
  if((tt==1000000||tt==10000000||tt==50000000||tt==100000000||tt==200000000) && p==-1 && s==1){
   printf("SNAP t=%ld p=%ld s=%d bits=",tt,p,s);
   for(long x=-2;x<=L;x++)putchar(t[x+OFF]?'1':'0');putchar('\n');
  }
 }
 printf("END p=%ld s=%d\n",p,s);return 0;}
