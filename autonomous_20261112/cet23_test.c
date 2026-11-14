#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w,d,n;}Tr;
static Tr a1[2][3],a2[2][3];
static unsigned char t[8000000];static const int OFF=2000000;
static int parse(const char*s,Tr*a,int n,int k){int z=0;for(int st=0;st<n;st++)for(int sy=0;sy<k;sy++){if(s[0]=='-'){a[st*k+sy]=(Tr){0,1,0};s+=3;}else{a[st*k+sy]=(Tr){s[0]-'0',s[1]=='R'?1:-1,s[2]-'A'};s+=3;}z++;if(*s=='_')s++;}return z==n*k;}
static int run(const char*b,long cap,long*when){Tr A2[2][3];if(!parse(b,&A2[0][0],2,3)){printf("parse fail\n");return -2;}memset(t,0,sizeof t);long p1=OFF,p2=OFF+2;int s1=0,s2=0;
 for(long z=1;z<=cap;z++){Tr x=a1[s1][t[p1]],y=A2[s2][t[p2]];t[p1]=x.w;t[p2]=y.w;p1+=x.d;s1=x.n;p2+=y.d;s2=y.n;if(p1==p2){*when=z;return 1;}if(p1<0||p1>=8000000||p2<0||p2>=8000000)return -1;}
 *when=cap;return 0;}
int main(int c,char**v){parse("1RB0RA2LB_2LA2RB1LB",&a1[0][0],2,3);const char*bs[]={"2RB2LB0LA_1LB0RB0RB","1RB1RB1RA_1LB0RB0RB","2RB2LA2LA_1LB0RB0RB"};for(int i=0;i<3;i++){long w;int r=run(bs[i],1000000000,&w);printf("%s r=%d when=%ld\n",bs[i],r,w);}}
