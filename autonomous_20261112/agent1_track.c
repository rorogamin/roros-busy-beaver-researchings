#include <stdio.h>
#include <stdlib.h>
typedef struct{int w,d,n;}Tr;
static const Tr A[3][2]={{{1,-1,1},{0,-1,0}},{{1,-1,2},{1,+1,1}},{{0,+1,1},{0,-1,2}}};
#define N 5000000L
#define OFF 1000000L
static unsigned char t[N];
int main(int c,char**v){long M=c>1?atol(v[1]):2000000L,cap=c>2?atol(v[2]):500000000L;
 for(long x=-1;x<70-1;x++)t[x+OFF]=1;t[69+OFF]=0;for(long x=70;x<M;x++)t[x+OFF]=1;
 long p=69;int s=1;long mx=p;long mxt=0;
 for(long tt=1;tt<=cap;tt++){Tr r=A[s][t[p+OFF]];if(r.d==0){printf("HALT %ld p=%ld\n",tt,p);return 0;}t[p+OFF]=r.w;p+=r.d;s=r.n;if(p>mx){mx=p;mxt=tt;}}
 printf("END t=%ld p=%ld s=%d max=%ld mxt=%ld\n",cap,p,s,mx,mxt);

}
