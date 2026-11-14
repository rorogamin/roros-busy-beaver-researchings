#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { int w,d,n; } Tr;
static const Tr A1[3][2] = {
  {{1,-1,1},{0,-1,0}}, /* A: 1LB, halt */
  {{1,-1,2},{1,+1,1}}, /* B: 1LC, 1RB */
  {{0,+1,1},{0,-1,2}}, /* C: 0RB, 0LC */
};
#define N 20000000L
#define OFF 1000000L
static unsigned char *t;
static inline int get(long p){return t[p+OFF];}
static inline void put(long p,int v){t[p+OFF]=v;}
static uint64_t hlocal(long p){
  uint64_t h=1469598103934665603ULL;
  for(long x=-200;x<=400;x++){h^=get(x);h*=1099511628211ULL;}
  return h;
}
#define HB 22
#define HS (1u<<HB)
int main(int argc,char**argv){
  long L=argc>1?atol(argv[1]):70;
  long cap=argc>2?atol(argv[2]):500000000L;
  t=calloc(N,1);
  if(!t){fprintf(stderr,"alloc\n");return 2;}
  for(long x=-1;x<L-1;x++)put(x,1);
  put(L-1,0);
  long p=L-1,mn=0,mx=0; int s=0;
  uint64_t *ht=calloc(HS,sizeof(uint64_t));
  uint64_t *hh=calloc(HS,sizeof(uint64_t));
  unsigned char *hu=calloc(HS,1);
  for(long tt=1;tt<=cap;tt++){
    Tr r=A1[s][get(p)];
    if(r.d==0){printf("HALT t=%ld p=%ld s=%d\n",tt,p,s);return 0;}
    put(p,r.w);p+=r.d;s=r.n;
    if(p<mn)mn=p;if(p>mx)mx=p;
    if(p==-1 && s==2 && tt>1000){
      uint64_t h=hlocal(p); uint32_t i=(uint32_t)(h>>(64-HB));
      for(int k=0;k<64;k++){
        uint32_t j=(i+k)&(HS-1);
        if(!hu[j]){hu[j]=1;hh[j]=h;ht[j]=(uint64_t)tt;break;}
        if(hh[j]==h){printf("CYCLE first=%llu now=%ld dt=%ld p=%ld s=%d min=%ld max=%ld\n",
          (unsigned long long)ht[j],tt,(long)(tt-(long)ht[j]),p,s,mn,mx);return 0;}
      }
    }
    if(tt%100000000L==0){printf("t=%ld p=%ld s=%d min=%ld max=%ld\n",tt,p,s,mn,mx);fflush(stdout);}
  }
  printf("NOCYCLE cap=%ld p=%ld s=%d min=%ld max=%ld\n",cap,p,s,mn,mx);
  return 0;
}
