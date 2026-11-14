/* Accelerated simulator for the closed block system, implementing
   TM25.arun_counter_jump: whenever the head is '>' and both words start with
   genuine counter prefixes, advance m = min(2^lam-1-L, 2^N-1-R) cycles at once.
   Prefixes are capped at 62 bits (any shorter prefix is still a legal instance
   of the theorem).  Block-step counts use the closed form
   2*(F(L+m)-F(L)) + 2*(F(R+m)-F(R)) + 2m  with F(n) = n - popcount(n).       */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
enum { W = 0, U = 1, D = 2 };
enum { V = 0, C = 3, C1 = 4, G = 5, P = 6, S = 7, Q = 8 };
enum { LT = 0, GT = 1, WGT = 2, LB = 3 };
static unsigned char *L, *R; static long ln, rn, lcap, rcap;
static void lpush(int b){ if(ln==lcap){lcap*=2;L=realloc(L,lcap);} L[ln++]=b; }
static void rpush(int b){ if(rn==rcap){rcap*=2;R=realloc(R,rcap);} R[rn++]=b; }
typedef unsigned __int128 u128;
static void pr128(u128 x){ char b[44]; int i=43; b[i--]=0; if(!x) b[i--]='0';
  while(x){ b[i--]='0'+(int)(x%10); x/=10; } fputs(b+i+1, stdout); }
static unsigned long long Ffun(unsigned long long n){ return n - __builtin_popcountll(n); }

int main(int argc,char**argv){
  long maxres = (argc>1)?atol(argv[1]):20;
  double maxsec = (argc>2)?atof(argv[2]):1e9;
  lcap=rcap=1<<20; L=malloc(lcap); R=malloc(rcap); ln=rn=0;
  int h=LT; lpush(W); rpush(C);
  u128 t=0; long resets=0, bottoms=0; int ateV=0; int turned=0;
  unsigned long long njump=0, nstep=0;
  clock_t t0=clock();
  for(;;){
    if((nstep&0xFFFFFFull)==0 && (double)(clock()-t0)/CLOCKS_PER_SEC > maxsec){
      printf("time limit; t="); pr128(t);
      printf("  resets=%ld jumps=%llu steps=%llu |L|=%ld |R|=%ld\n",resets,njump,nstep,ln,rn);
      return 0; }
    /* ---- accelerated jump ---- */
    if(h==GT && turned){
      turned=0;
      long lam=0; while(lam<ln && lam<32 && (L[ln-1-lam]==U||L[ln-1-lam]==W)) lam++;
      long NN=0;  while(NN<rn && NN<32 && (R[rn-1-NN]==C||R[rn-1-NN]==C1)) NN++;
      if(lam>0 && NN>0){
        unsigned long long Lv=0,Rv=0;
        for(long i=0;i<lam;i++) if(L[ln-1-i]==W) Lv|=1ULL<<i;
        for(long i=0;i<NN;i++)  if(R[rn-1-i]==C1) Rv|=1ULL<<i;
        unsigned long long ml=(1ULL<<lam)-1-Lv, mr=(1ULL<<NN)-1-Rv;
        unsigned long long m = ml<mr?ml:mr;
        if(m>0){
          unsigned long long L2=Lv+m, R2=Rv+m;
          t += (u128)2*(Ffun(L2)-Ffun(Lv)) + (u128)2*(Ffun(R2)-Ffun(Rv)) + (u128)2*m;
          for(long i=0;i<lam;i++) L[ln-1-i] = ((L2>>i)&1)?W:U;
          for(long i=0;i<NN;i++)  R[rn-1-i] = ((R2>>i)&1)?C1:C;
          njump++; continue;
        }
      }
    }
    /* ---- one exact block step ---- */
    nstep++; t++;
    if(h==LT){
      if(ln==0){ h=WGT; ateV=0; resets++;
        long n=0; int ok = (rn>=2 && R[0]==Q && R[1]==P);
        if(ok){ long k=2; while(k<rn && R[k]==C1){ n++; k++; } }
        long nv=0,nd=0; for(long i=0;i<rn;i++){ if(R[i]==V) nv++; else if(R[i]==C||R[i]==C1) nd++; }
        printf("RESET %ld at block step ", resets); pr128(t-1);
        printf("  |R|=%ld #V=%ld #digits=%ld  bottom = %s",rn,nv,nd, ok?"23^":"NOT 23^n 21 $");
        if(ok) printf("%ld 21 $",n);
        printf("   [jumps=%llu steps=%llu]\n",njump,nstep); fflush(stdout);
        if(resets>=maxres) {
          printf("SEED_RIGHT ");
          for(long ii=rn;ii>0;--ii){
            int v=R[ii-1];
            if(v==V) putchar('V'); else if(v==C) putchar('0');
            else if(v==C1) putchar('1'); else if(v==P) putchar('P');
            else if(v==Q) putchar('Q'); else if(v==G) putchar('G');
            else putchar('S');
          }
          puts(""); return 0;
        }
        continue; }
      int b=L[--ln];
      if(b==W) rpush(V); else if(b==U){ lpush(W); h=GT; turned=1; } else rpush(C);
    } else if(h==GT){
      if(rn==0){ rpush(Q); rpush(P); h=LT; continue; }
      int a=R[--rn];
      switch(a){ case V: lpush(U); break; case C: rpush(C1); h=LT; break;
        case C1: lpush(D); break; case G: rpush(C); h=LT; break;
        case P: h=WGT; ateV=0; break; case S: rpush(Q); h=LT; break;
        case Q: rpush(P); h=LT; break; }
    } else if(h==WGT){
      if(rn==0 || (rn==2 && R[1]==P && R[0]==Q)){
        long j=ln; int good=1; while(j>0 && L[j-1]==W) j--;
        if(j>0 && L[j-1]==D) good=0;
        bottoms++;
        printf("  BOTTOM %ld at ",bottoms); pr128(t-1);
        printf("  rs=%s  left %s  V eaten: %s\n", rn==0?"[]":"PQ",
               good?"Good":"BAD (halt!)", ateV?"yes":"NO");
        fflush(stdout);
        if(!good){ printf("BAD BOTTOM -- machine halts\n"); return 1; }
      }
      if(rn==0){ rpush(G); h=LB; continue; }
      int a=R[--rn];
      switch(a){ case V: lpush(U); ateV=1; break;
        case C: rpush(S); rpush(C); h=LT; break;
        case C1: rpush(V); rpush(P); h=LT; break;
        case G: rpush(Q); rpush(C); h=LT; break;
        case P: lpush(U); h=GT; break; case S: lpush(D); h=GT; break;
        case Q: rpush(C); h=LT; break; }
    } else {
      if(ln==0){ printf("LEFT-END LOOP: never halts\n"); return 0; }
      int b=L[--ln];
      if(b==U){ rpush(C); h=LT; } else if(b==W) rpush(G);
      else { printf("HALT\n"); return 1; }
    }
  }
}
