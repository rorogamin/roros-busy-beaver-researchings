#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* 2026 regrouped table.  Tokens:
   0 A, 1 2>, 2 22, 3 14, 4 24, 5 21, 6 214, 7 224, 8 221, 9 21$ */
enum { A=0, B=1, T22=2, T14=3, T24=4, T21=5, T214=6, T224=7, T221=8, T21S=9 };
static const char *name[10] = {"A","2>","22","14","24","21","214","224","221","21$"};

/* output length and tokens; len 255 means halt */
static uint8_t olen[2][10];
static uint8_t out[2][10][4];

static void rule(int c, int b, int *n, uint8_t *v) {
  *n = olen[c][b];
  for (int i=0;i<*n;i++) v[i]=out[c][b][i];
}

static void setrule(int c,int b,int n,const uint8_t *v){
  olen[c][b]=(uint8_t)n;
  for(int i=0;i<n;i++) out[c][b][i]=v[i];
}

int main(int argc,char**argv){
  unsigned long long limit = argc>1 ? strtoull(argv[1],0,10) : 1000000000ULL;
  memset(olen,255,sizeof(olen));
  { uint8_t v[]={T22,A,A}; setrule(A,T22,3,v); }
  { uint8_t v[]={T24}; setrule(A,T14,1,v); }
  { uint8_t v[]={T21}; setrule(A,T24,1,v); }
  { uint8_t v[]={T14,A}; setrule(A,T21,2,v); }
  { uint8_t v[]={T14,B,A}; setrule(A,T214,3,v); }
  { uint8_t v[]={T22,A,B,A}; setrule(A,T224,4,v); }
  { uint8_t v[]={T22,A,B}; setrule(A,T221,3,v); }
  { uint8_t v[]={T14,T21S}; setrule(A,T21S,2,v); }
  { uint8_t v[]={T22,B}; setrule(B,T22,2,v); }
  { uint8_t v[]={T214}; setrule(B,T14,1,v); }
  { uint8_t v[]={T224}; setrule(B,T24,1,v); }
  { uint8_t v[]={T221}; setrule(B,T21,1,v); }
  { uint8_t v[]={T22,T14}; setrule(B,T214,2,v); }
  { uint8_t v[]={T22,T24}; setrule(B,T224,2,v); }
  { uint8_t v[]={T22,T21}; setrule(B,T221,2,v); }

  const int CAP=1<<20;
  uint8_t *w=malloc(CAP), *st=malloc(CAP);
  if(!w||!st){ fprintf(stderr,"alloc\n"); return 2; }
  int len=3; w[0]=T22; w[1]=T14; w[2]=T21S;
  int sp=0;
  for(int i=0;i<1000000;i++){ st[sp++]=(i&1)?B:A; } /* top is B */

  for(unsigned long long step=0; step<limit; step++){
    int i=len-1;
    while(i>=0 && w[i]!=A && w[i]!=B) i--;
    if(i<0){
      if(sp==0){ printf("STACK EMPTY at %llu\n",step); return 3; }
      if(len>=CAP-16){ printf("WORD CAP at %llu len=%d\n",step,len); return 4; }
      memmove(w+1,w,len); w[0]=st[--sp]; len++; i=0;
    }
    if(i+1>=len){ printf("NO BLOCK at %llu i=%d len=%d\n",step,i,len); return 5; }
    int c=w[i], b=w[i+1];
    if(c==B && b==T21S){ printf("HALT at %llu\n",step); return 0; }
    int n; uint8_t v[4];
    rule(c,b,&n,v);
    if(olen[c][b]==255){ printf("MISSING %s %s at %llu\n",name[c],name[b],step); return 6; }
    int newlen=len-2+n;
    if(newlen>=CAP-16){ printf("WORD CAP2 at %llu len=%d\n",step,newlen); return 4; }
    memmove(w+i+n,w+i+2,len-(i+2));
    for(int k=0;k<n;k++) w[i+k]=v[k];
    len=newlen;
    if((step & 0xFFFFFFFULL)==0 && step){ printf("step %llu len %d sp %d\n",step,len,sp); fflush(stdout); }
  }
  printf("NO HALT %llu len=%d sp=%d\n",limit,len,sp);
  return 0;
}
