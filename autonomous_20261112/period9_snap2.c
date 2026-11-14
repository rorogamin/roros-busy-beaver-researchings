#include <stdio.h>
#include <stdlib.h>
typedef struct{int w,d,n;}Tr;
static const Tr A1[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
static const Tr A2[3][2]={{{1,+1,1},{0,-1,0}},{{0,+1,2},{0,-1,0}},{{1,-1,1},{1,+1,2}}};
#define N 300000000L
#define OFF 1000000L
static unsigned char t[N];
static int G(long p){return t[p+OFF];}
int main(int c,char**v){long L=c>1?atol(v[1]):10,X=c>2?atol(v[2]):20,cap=c>3?atol(v[3]):100000015L;
 for(long x=L;x<X;x++)t[x+OFF]=1; t[X+OFF]=0;t[X+1+OFF]=1;t[X+2+OFF]=1;
 long p1=-1,p2=X;int s1=0,s2=0;
 for(long tt=1;tt<=cap;tt++){
  Tr r1=A1[s1][G(p1)],r2=A2[s2][G(p2)];
  t[p1+OFF]=r1.w;t[p2+OFF]=r2.w;p1+=r1.d;s1=r1.n;p2+=r2.d;s2=r2.n;
  if(p1==p2){printf("HALT %ld\n",tt);return 0;}
  if(tt==100000000L||tt==100000015L||tt==100000030L||tt==100000045L){
   printf("SNAP t=%ld p1=%ld s1=%d p2=%ld s2=%d q1=%ld q2=%ld\n",tt,p1,s1,p2,s2,3*p1-tt,5*p2-tt);
   printf("a1 ");for(long x=p1-30;x<=p1+30;x++)putchar(G(x)?'1':'0');putchar('\n');
   printf("a2 ");for(long x=p2-30;x<=p2+30;x++)putchar(G(x)?'1':'0');putchar('\n');
  }
 }
 printf("END p1=%ld s1=%d p2=%ld s2=%d diff=%ld\n",p1,s1,p2,s2,p1-p2);
}
