#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

/* Agent tables: 0=1RB, 1=0LA, 2=0RC, 3=0LA, 4=1LB, 5=1RC
   A1: 1LB --- / 1LC 1RB / 0RB 0LC
   A2: 1RB 0LA / 0RC 0LA / 1LB 1RC
   encode transition as (write, dir, next). */
typedef struct { int w, d, n; } Tr;
static const Tr A1[3][2] = {
  {{1,-1,1},{0,-1,0}}, /* A */
  {{1,-1,2},{1,+1,1}}, /* B */
  {{0,+1,1},{0,-1,2}}, /* C */
};
static const Tr A2[3][2] = {
  {{1,+1,1},{0,-1,0}}, /* A */
  {{0,+1,2},{0,-1,0}}, /* B */
  {{1,-1,1},{1,+1,2}}, /* C */
};

#define N 250000000L
#define OFF 5000000L
static unsigned char *tape;
static inline int get(long p){ return tape[p+OFF]; }
static inline void put(long p,int v){ tape[p+OFF]=(unsigned char)v; }

static uint64_t hash_local(long p){
  uint64_t h=1469598103934665603ULL;
  for(long x=-600;x<=1600;x++){ h ^= (uint64_t)get(x); h *= 1099511628211ULL; }
  return h;
}

#define HBITS 24
#define HSIZE (1u<<HBITS)
static uint64_t *htime;
static uint64_t *hhash;
static long *hpos;
static unsigned char *hused;

int main(int argc,char**argv){
  long L = argc>1?atol(argv[1]):10;
  long X = argc>2?atol(argv[2]):20;
  long cap = argc>3?atol(argv[3]):2000000000L;
  tape = calloc(N,1);
  if(!tape){fprintf(stderr,"alloc fail\n");return 2;}
  /* zeros to the left of -2; the clean counter block [-1..L-1]; ones up to the glider. */
  for(long x=L;x<X;x++) put(x,1);
  put(X,0); put(X+1,1); put(X+2,1);
  long p1=-1,p2=X; int s1=0,s2=0;
  long mn=0,mx=0;
  long prevdiff=p1-p2;
  int crossings=0;
  htime=calloc(HSIZE,sizeof(uint64_t));
  hhash=calloc(HSIZE,sizeof(uint64_t));
  hpos=malloc(HSIZE*sizeof(long));
  hused=calloc(HSIZE,1);
  if(!htime||!hhash||!hpos||!hused){fprintf(stderr,"hash alloc fail\n");return 2;}
  for(long t=1;t<=cap;t++){
    Tr t1=A1[s1][get(p1)], t2=A2[s2][get(p2)];
    put(p1,t1.w); put(p2,t2.w);
    p1+=t1.d; s1=t1.n; p2+=t2.d; s2=t2.n;
    if(p1==p2){ printf("HALT t=%ld pos=%ld states=%d/%d\n",t,p1,s1,s2); return 0; }
    long diff=p1-p2;
    if((prevdiff<0 && diff>0) || (prevdiff>0 && diff<0)){
      crossings++;
      printf("CROSSING %d t=%ld p1=%ld s1=%d p2=%ld s2=%d prevdiff=%ld diff=%ld\n",
             crossings,t,p1,s1,p2,s2,prevdiff,diff);
      fflush(stdout);
      if(crossings<=6){
        for(long x=p2-8;x<=p2+8;x++) putchar(get(x)?'1':'0');
        putchar('\n'); fflush(stdout);
      }
    }
    prevdiff=diff;
    if(p1<mn) mn=p1; if(p1>mx) mx=p1;
    if(t>50000 && p1==-3 && s1==2){
      uint64_t h=hash_local(p1);
      uint32_t idx=(uint32_t)(h>>(64-HBITS));
      int inserted=0;
      for(int probe=0;probe<64;probe++){
        uint32_t j=(idx+probe)&(HSIZE-1);
        if(!hused[j]){
          hused[j]=1; hhash[j]=h; htime[j]=(uint64_t)t; hpos[j]=p2; inserted=1; break;
        }
        if(hhash[j]==h){
          printf("REPEAT_LOCAL first=%llu now=%ld dt=%ld oldp2=%ld p2=%ld p1=%ld s1=%d\n",
                 (unsigned long long)htime[j],t,(long)(t-(long)htime[j]),hpos[j],p2,p1,s1);
          fflush(stdout);
          return 0;
        }
      }
      if(!inserted && t%1000000L==0) fprintf(stderr,"hash full at %ld\n",t);
    }
    if(t<=10000 && t%1000==0){
      printf("early t=%ld p1=%ld s1=%d p2=%ld s2=%d diff=%ld\n",t,p1,s1,p2,s2,diff);
      fflush(stdout);
    }
    if(t%100000000L==0){
      printf("t=%ld p1=%ld s1=%d p2=%ld s2=%d min=%ld max=%ld\n",t,p1,s1,p2,s2,mn,mx);
      fflush(stdout);
    }
  }
  printf("NO HALT cap=%ld p1=%ld s1=%d p2=%ld s2=%d min=%ld max=%ld\n",cap,p1,s1,p2,s2,mn,mx);
  return 0;
}
