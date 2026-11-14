#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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
static int runw(int st,const u8*w,size_t n,u8*out,size_t*on){
  size_t o=*on;
  for(size_t i=0;i<n;i++){int x=w[i];int ns=nst[st][x];if(ns<0){*on=o;return -1;}
    for(int k=0;k<nout[st][x];k++)out[o++]=outl[st][x][k]; st=ns;}
  *on=o;return st;
}
int main(int argc,char**argv){
  init(); int maxc=atoi(argv[1]); size_t cap=atoll(argv[2]);
  u8*x=malloc(cap),*y=malloc(cap),*bx=malloc(2*cap),*by=malloc(2*cap);
  size_t nx=1,ny=5; x[0]=0; u8 p0[5]={1,0,1,0,1}; memcpy(y,p0,5);
  double a=0,b=1;
  for(int c=0;c<maxc;c++){
    printf("%d nx=%zu ny=%zu a=%.6e b=%.6e\n",c,nx,ny,a,b);fflush(stdout);
    int done=0;
    for(int r=0;r<=2&&!done;r++){
      size_t ox=0,oy=0; int s=runw(0,x,nx,bx,&ox); if(s<0) {printf("halt\n");return 0;}
      int bad=0; for(int i=0;i<r;i++){ s=runw(s,y,ny,bx,&ox); if(s<0){bad=1;break;} }
      if(bad) continue;
      int s1=s; int s2=runw(s1,y,ny,by,&oy); if(s2<0) continue;
      if(s2==s1){ memcpy(x,bx,ox);nx=ox; memcpy(y,by,oy);ny=oy; a=a+r*b; done=1; break;}
      int s3=runw(s2,y,ny,by,&oy); if(s3<0) continue;
      if(s3==s1){ memcpy(x,bx,ox);nx=ox; memcpy(y,by,oy);ny=oy; a=a+r*b; b=2*b; done=1; break;}
    }
    if(!done){printf("step failed at %d\n",c);return 1;}
    if(nx>cap/2||ny>cap/2){printf("cap\n");return 1;}
  }
}
