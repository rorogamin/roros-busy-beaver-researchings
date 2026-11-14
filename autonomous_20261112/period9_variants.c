#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static const Tr A1[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define P 1000
#define SZ 8000000
#define OFF 2000000
static unsigned char t[SZ];
static Tr a2[3][2];
static int run(int w1,int d1,int n1,long cap,long*when){
 memset(t,0,sizeof(t));
 for(int x=0;x<69;x++)t[x+OFF]=1;
 long p1=69+OFF,p2=P+OFF;int s1=1,s2=1;
 t[p1]=0; t[p2]=0; t[p2+1]=1;t[p2+2]=1;
 for(long k=1;k<=cap;k++){
  Tr r1=A1[s1][t[p1]],r2=a2[s2][t[p2]];
  t[p1]=r1.w;t[p2]=r2.w;p1+=r1.d;s1=r1.n;p2+=r2.d;s2=r2.n;
  if(p1==p2){*when=k;return 1;}
 }
 *when=cap;return 0;
}
int main(){int ws[2]={0,1},ds[2]={-1,1},ns[3]={0,1,2};
 for(int wi=0;wi<2;wi++)for(int di=0;di<2;di++)for(int ni=0;ni<3;ni++){
  a2[0][0]=(Tr){1,+1,1}; a2[0][1]=(Tr){ws[wi],ds[di],ns[ni]};
  a2[1][0]=(Tr){0,+1,2}; a2[1][1]=(Tr){0,-1,0};
  a2[2][0]=(Tr){1,-1,1}; a2[2][1]=(Tr){1,+1,2};
  long when; int hit=run(ws[wi],ds[di],ns[ni],5000000,&when);
  printf("A1=%d%c%c hit=%d t=%ld\n",ws[wi],ds[di]<0?'L':'R',"ABC"[ns[ni]],hit,when);
 }
}
