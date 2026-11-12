#include <stdio.h>
#include <string.h>
#include <stdlib.h>
typedef struct{int w,d,n;}Tr;
static Tr A1[4][2],A2[4][2];static unsigned char t[8000000];static const int OFF=2000000;
static void pa(const char*s,Tr a[4][2]){for(int i=0;i<4;i++)for(int j=0;j<2;j++){if(*s=='-'){a[i][j]=(Tr){0,1,-1};s+=3;}else{a[i][j]=(Tr){s[0]-'0',s[1]=='R'?1:-1,s[2]-'A'};s+=3;}if(*s=='_')s++;}}
static void run(const char*a,const char*b,long cap){char x[64],y[64];strncpy(x,a,63);strncpy(y,b,63);pa(x,A1);pa(y,A2);memset(t,0,sizeof t);long p1=OFF,p2=OFF+2;int s1=0,s2=0;long mx=0;
 for(long k=1;k<=cap;k++){Tr u=A1[s1][t[p1]],v=A2[s2][t[p2]];t[p1]=u.w;t[p2]=v.w;p1+=u.d;s1=u.n;p2+=v.d;s2=v.n;long d=labs(p2-p1);if(d>mx)mx=d;if(p1==p2){printf("collision %ld p=%ld\n",k,p1-OFF);return;}if(p1<0||p1>=8000000||p2<0||p2>=8000000){printf("edge %ld\n",k);return;}}
 printf("no halt %ld maxdist=%ld p1=%ld p2=%ld\n",cap,mx,p1-OFF,p2-OFF);}
int main(){run("0LC0LD_0LC1RB_0RA1RB_1LC1RB","0RD0RC_1RB0LA_1LB1LB_0LC0LB",1000000000L);run("0LC0LC_1LC0LC_0RB0RD_1RB0LA","0LC0RA_1LA0LB_1RA1RD_0LC0LD",1000000000L);}
