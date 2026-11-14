#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef struct{int w,d,n;}Tr;
static const Tr A1[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
static const Tr A2[3][2]={{{1,+1,1},{0,-1,0}},{{0,+1,2},{0,-1,0}},{{1,-1,1},{1,+1,2}}};
#define N 20000000L
#define OFF 2000000L
static unsigned char t[N];
static int G(long p){return t[p+OFF];}
static uint64_t H(long p){uint64_t h=1469598103934665603ULL;for(long x=p-100;x<=p+300;x++){h^=G(x);h*=1099511628211ULL;}return h;}
#define HB 23
#define HS (1u<<HB)
int main(int c,char**v){long L=70,P2=c>1?atol(v[1]):100000L,cap=c>2?atol(v[2]):100000000L;
 for(long x=-1;x<L-2;x++)t[x+OFF]=1;t[L-1+OFF]=0;
 for(long x=L;x<P2;x++)t[x+OFF]=1;
 /* phase 5 initial local tape: run 5 steps of A2 from canonical at P2 */
 long q=P2;int s=0;
 for(int k=0;k<5;k++){Tr r=A2[s][G(q)];t[q+OFF]=r.w;q+=r.d;s=r.n;}
 long p1=L-1,p2=q;int s1=1,s2=s;long mn=0,mx=0;
 uint64_t *ht=calloc(HS,sizeof(uint64_t)),*hh=calloc(HS,sizeof(uint64_t));unsigned char *hu=calloc(HS,1);
 for(long tt=1;tt<=cap;tt++){
  Tr r1=A1[s1][G(p1)],r2=A2[s2][G(p2)];t[p1+OFF]=r1.w;t[p2+OFF]=r2.w;p1+=r1.d;s1=r1.n;p2+=r2.d;s2=r2.n;
  if(p1==p2){printf("HALT %ld pos=%ld\n",tt,p1);return 0;} if(p1<mn)mn=p1;if(p1>mx)mx=p1;
  if(tt>1000 && p1==69 && s1==1){
   uint64_t h=H(p1);uint32_t i=(uint32_t)(h>>(64-HB));
   for(int k=0;k<64;k++){uint32_t j=(i+k)&(HS-1);if(!hu[j]){hu[j]=1;hh[j]=h;ht[j]=tt;break;}if(hh[j]==h){printf("CYCLE first=%llu now=%ld dt=%ld p2=%ld min=%ld max=%ld\n",(unsigned long long)ht[j],tt,tt-(long)ht[j],p2,mn,mx);return 0;}}
  }
  if(tt%10000000L==0)printf("t=%ld p1=%ld s1=%d p2=%ld s2=%d min=%ld max=%ld\n",tt,p1,s1,p2,s2,mn,mx);
 }
 printf("END p1=%ld s1=%d p2=%ld s2=%d min=%ld max=%ld\n",p1,s1,p2,s2,mn,mx);}
