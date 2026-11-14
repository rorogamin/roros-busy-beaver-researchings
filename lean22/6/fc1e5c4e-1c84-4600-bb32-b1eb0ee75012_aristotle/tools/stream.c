#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
typedef unsigned char u8;
static int nst[8][2]; static int nout[8][2]; static u8 outl[8][2][2];
static void init(){
  for(int c=0;c<8;c++)for(int x=0;x<2;x++){nst[c][x]=-1;nout[c][x]=0;}
  nst[0][0]=3*2+1; nout[0][0]=1; outl[0][0][0]=1;
  nst[0][1]=2*2+0;
  for(int f=0;f<2;f++){
    int c1=1*2+f,c2=2*2+f,c3=3*2+f;
    nst[c1][0]=2*2+1; nout[c1][0]=1; outl[c1][0][0]=0;
    nst[c1][1]=3*2+f;
    nst[c2][0]=1*2+f;
    if(f){nst[c2][1]=2*2+1;nout[c2][1]=2;outl[c2][1][0]=1;outl[c2][1][1]=0;}
    else {nst[c2][1]=3*2+1;nout[c2][1]=1;outl[c2][1][0]=1;}
    if(f){nst[c3][0]=2*2+1;nout[c3][0]=1;outl[c3][0][0]=1;} else nst[c3][0]=-1;
    nst[c3][1]=1*2+1;nout[c3][1]=1;outl[c3][1][0]=0;
  }
}
static int runw(int st,const u8*w,size_t n,u8*out,size_t*on,size_t*hpos){
  size_t o=*on;
  for(size_t i=0;i<n;i++){int x=w[i];int ns=nst[st][x];if(ns<0){*hpos=i;*on=o;return -1;}
    for(int k=0;k<nout[st][x];k++)out[o++]=outl[st][x][k]; st=ns;}
  *on=o;return st;
}
#define MAXL 2000
int state[MAXL]; uint64_t cnt[MAXL]; char head[MAXL][17]; int hlen[MAXL];
u8 *bufs[MAXL];
size_t CH;
int top; // number of levels with started words
int c0;
static void note(int lev,const u8*w,size_t n){
  cnt[lev]+=n; while(hlen[lev]<16 && n){head[lev][hlen[lev]++]="AB"[*w++];n--;}
}
// push chunk w (len n) into level lev (relative index)
static void push(int lev,const u8*w,size_t n){
  while(n){
    if(lev>=MAXL-1){printf("too deep\n");exit(1);}
    size_t m = n>CH?CH:n;
    note(lev,w,m);
    size_t on=0,hp; int st=runw(state[lev],w,m,bufs[lev],&on,&hp);
    if(st<0){printf("HALT at cell %d after %llu letters (pos %zu in chunk of %zu) head=%s\n",lev+c0,(unsigned long long)cnt[lev],hp,m,head[lev]);
      for(int l=0;l<=lev;l++) printf("cell %d letters(chunk-granular) %llu head %s state %d\n",l+c0,(unsigned long long)cnt[l],head[l],state[l]);
      fflush(stdout);exit(0);}
    state[lev]=st;
    if(lev+1>top) top=lev+1;
    if(on) push(lev+1,bufs[lev],on);
    w+=m;n-=m;
  }
}
int main(int argc,char**argv){
  init();
  c0=atoi(argv[1]); size_t cap=(size_t)atoll(argv[2]); double reps=atof(argv[3]); CH=atoll(argv[4]);
  u8*pre=malloc(64),*per=malloc(cap);
  size_t np=1,nq=5; pre[0]=0; u8 p0[5]={1,0,1,0,1}; memcpy(per,p0,5);
  u8*buf=malloc(cap*2+1024);
  for(int c=0;c<c0;c++){
    size_t on=0,hp;int st=runw(0,pre,np,buf,&on,&hp);
    if(st<0){printf("HALT cell %d\n",c);return 0;}
    int seenst[8];size_t seenpos[8];for(int i=0;i<8;i++)seenst[i]=-1;
    int k=0;
    while(seenst[st]<0){seenst[st]=k;seenpos[st]=on;
      if(on+2*nq>cap*2+1000){printf("cap exceeded\n");return 1;}
      st=runw(st,per,nq,buf,&on,&hp); if(st<0){printf("HALT cell %d\n",c);return 0;}
      k++;}
    size_t ps=seenpos[st]; size_t newq=on-ps;
    size_t s0=ps; while(s0>0 && buf[s0-1]==buf[s0-1+newq]) s0--;
    free(pre); pre=malloc(s0+1); memcpy(pre,buf,s0); np=s0;
    memcpy(per,buf+s0,newq); nq=newq;
    for(size_t d=1;d<nq;d++){ if(nq%d) continue; if(memcmp(per,per+d,nq-d)==0){nq=d;break;} }
  }
  free(buf);
  fprintf(stderr,"exact cell %d: pre %zu per %zu\n",c0,np,nq);
  for(int i=0;i<MAXL;i++){state[i]=0;bufs[i]=NULL;}
  for(int i=0;i<MAXL;i++) bufs[i]=malloc(2*CH+16);
  time_t t0=time(0);
  push(0,pre,np);
  uint64_t total=(uint64_t)(reps*nq);
  uint64_t fed=0; int lastrep=-1;
  while(fed<total){
    size_t m = nq; if(total-fed<m) m=total-fed;
    push(0,per,m); fed+=m;
    fprintf(stderr,"fed %.2f periods, top level %d, t=%lds\n",(double)fed/nq,top+c0,(long)(time(0)-t0));
  }
  for(int l=0;l<=top;l++) printf("cell %d letters %llu head %s state %d\n",l+c0,(unsigned long long)cnt[l],head[l],state[l]);
  return 0;
}
