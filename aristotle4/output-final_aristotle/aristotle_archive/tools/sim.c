#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { int w,d,ns; } Tr;
int main(int argc,char**argv){
  long long LIMIT = atoll(argv[1]);
  int N=4000; unsigned char *tape=calloc(N,1);
  // T[state][sym] = write*100 + (dir+1)*10 + newstate ; state 0=A,1=B
  int W[2][5]={{1,-1,3,2,2},{2,3,4,4,0}};
  int D[2][5]={{1,0,1,-1,1},{-1,-1,-1,1,1}};
  int S[2][5]={{1,0,0,0,1},{1,0,1,0,0}};
  int pos=N/2, st=0, lo=pos, hi=pos, m=-1;
  long long steps=0, t0=0;
  int lastA=-1; long long lastAt=-1; int cstart=-1, cend=-1;
  int bestend=1<<30;
  while(steps<LIMIT){
    int s=tape[pos];
    if(st==0&&s==1){printf("HALT %lld\n",steps);return 0;}
    int w=W[st][s], d=D[st][s], ns=S[st][s];
    if(st==0&&d==-1){
      if(lastAt<0 || steps-lastAt>6){ // new cascade
        if(cstart>=0 && cstart-cend>=5 && cend-m<bestend) bestend=cend-m;
        cstart=pos; cend=pos;
      }
      cend=pos-1; lastAt=steps;
    }
    tape[pos]=w; pos+=d; st=ns; steps++;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(w==1 && (m<0 || pos-d<m)){
      if(m>=0){
        if(cstart>=0 && cstart-cend>=5 && cend-m<bestend) bestend=cend-m;
        printf("epoch t0=%lld len=%lld width=%d closest_cascade=%d\n",t0,steps-t0,hi-lo+1,bestend==(1<<30)?-1:bestend);
        fflush(stdout);
      }
      m=pos-d; t0=steps; bestend=1<<30; cstart=-1;
    }
  }
  printf("no halt in %lld steps, width %d\n",LIMIT,hi-lo+1);
  return 0;
}
