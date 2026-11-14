#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static const Tr A[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define OFF 1000000
#define SZ 4000000
static unsigned char t[SZ];
int main(int c,char**v){long cap=c>1?atol(v[1]):1000000000L; memset(t,0,sizeof t); long p=-2+OFF;int s=2;long mx=-2,mxt=0;
 for(long k=1;k<=cap;k++){Tr r=A[s][t[p]];t[p]=r.w;p+=r.d;s=r.n;if(p-OFF>mx){mx=p-OFF;mxt=k;if(mx%100==0||mx<30)printf("newmax %ld at t=%ld\n",mx,mxt);}}
 printf("END t=%ld p=%ld s=%d max=%ld mxt=%ld\n",cap,p-OFF,s,mx,mxt);}
