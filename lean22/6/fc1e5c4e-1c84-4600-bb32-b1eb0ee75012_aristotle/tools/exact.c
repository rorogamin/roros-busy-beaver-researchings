#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
// states: s in 0..3, f in 0/1 -> code s*2+f
// letters 0=A 1=B
typedef unsigned char u8;
static int nst[8][2]; static int nout[8][2]; static u8 outl[8][2][2];
static void init(){
  for(int c=0;c<8;c++)for(int x=0;x<2;x++){nst[c][x]=-1;nout[c][x]=0;}
  // (0,F)=0
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
// run from state st over w[0..n), append to out; return state or -1 (halt), *hpos
static int runw(int st,const u8*w,size_t n,u8*out,size_t*on,size_t*hpos){
  size_t o=*on;
  for(size_t i=0;i<n;i++){int x=w[i];int ns=nst[st][x];if(ns<0){*hpos=i;*on=o;return -1;}
    for(int k=0;k<nout[st][x];k++)out[o++]=outl[st][x][k]; st=ns;}
  *on=o;return st;
}
int main(int argc,char**argv){
  init();
  int maxc=atoi(argv[1]);
  size_t cap=(size_t)atoll(argv[2]);
  u8*pre=malloc(64),*per=malloc(cap),*npre,*nper;
  size_t np=1,nq=5; pre[0]=0; u8 p0[5]={1,0,1,0,1}; memcpy(per,p0,5);
  u8*buf=malloc(cap*2+1024);
  for(int c=0;c<maxc;c++){
    size_t na=0;for(size_t i=0;i<nq;i++)na+=(per[i]==0);
    printf("%d pre=%zu per=%zu A=%zu B=%zu  ",c,np,nq,na,nq-na);
    for(size_t i=0;i<np&&i<8;i++)putchar("AB"[pre[i]]);putchar('|');
    for(size_t i=0;i<nq&&i<24;i++)putchar("AB"[per[i]]);putchar('\n');fflush(stdout);
    size_t on=0,hp;int st=runw(0,pre,np,buf,&on,&hp);
    if(st<0){printf("HALT cell %d in prefix pos %zu\n",c,hp);return 0;}
    size_t preOut=on; int seenst[8];size_t seenpos[8];for(int i=0;i<8;i++)seenst[i]=-1;
    int k=0;
    while(seenst[st]<0){seenst[st]=k;seenpos[st]=on;
      if(on+2*nq>cap*2+1000){printf("cap exceeded\n");return 1;}
      st=runw(st,per,nq,buf,&on,&hp); if(st<0){printf("HALT cell %d in period copy %d pos %zu\n",c,k,hp);return 0;}
      k++;}
    size_t ps=seenpos[st]; size_t newq=on-ps;
    if(newq>cap){printf("period cap exceeded %zu\n",newq);return 1;}
    // new prefix buf[0..ps), period buf[ps..on)
    // minimize: rotate
    size_t pl=ps; u8*P=buf+ps;
    // rotate while prefix last == period last
    // do by index: period start moves back
    size_t s0=ps;
    while(s0>0 && buf[s0-1]==buf[s0-1+newq]) s0--;
    pl=s0;
    free(pre); pre=malloc(pl+1); memcpy(pre,buf,pl); np=pl;
    memcpy(per,buf+s0,newq); nq=newq;
    // primitive period
    for(size_t d=1;d<nq;d++){ if(nq%d) continue; if(memcmp(per,per+d,nq-d)==0){nq=d;break;} }
  }
  return 0;
}
