/* cyc.c -- exact translated-configuration cycle detector.
 * usage: cyc CAP INTERVAL SPEC
 * Simulates from blank tape and compares normalized tape/state at checkpoint
 * times.  A confirmed repeat is a finite cycle up to translation.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 8
#define MAXM 8
typedef struct { int n,m; int8_t w[MAXN][MAXM],d[MAXN][MAXM],nx[MAXN][MAXM]; } TM;

static int parse_tm(const char *line, TM *tm) {
  int len=(int)strlen(line), n=1;
  for(int i=0;i<len;i++) if(line[i]=='_') n++;
  int blen=0; while(blen<len && line[blen]!='_') blen++;
  if(n<1||n>MAXN||blen%3||blen/3<1||blen/3>MAXM) return -1;
  int m=blen/3;
  if(len!=n*blen+(n-1)) return -1;
  const char *p=line;
  for(int s=0;s<n;s++) {
    for(int sym=0;sym<m;sym++) {
      const char *tok=p+3*sym;
      if(tok[0]=='-'&&tok[1]=='-'&&tok[2]=='-') { tm->w[s][sym]=-1; tm->d[s][sym]=0; tm->nx[s][sym]=-1; }
      else {
        int w=tok[0]-'0', d=tok[1]=='R'?1:(tok[1]=='L'?-1:0);
        int nx=(tok[2]=='Z'||tok[2]=='H')?-1:tok[2]-'A';
        if(w<0||w>=m||d==0||nx>=n) return -1;
        tm->w[s][sym]=w; tm->d[s][sym]=d; tm->nx[s][sym]=nx;
      }
    }
    p+=blen+1;
  }
  tm->n=n; tm->m=m; return 0;
}

static int8_t *tape; static size_t cap; static long long head,lo,hi;

static void init(void) {
  cap=1u<<20; tape=(int8_t*)calloc(cap,1); if(!tape){perror("calloc");exit(2);}
  head=(long long)(cap/2); lo=hi=head;
}
static void grow(void) {
  size_t nc=cap*2; int8_t *nt=(int8_t*)calloc(nc,1); if(!nt){perror("calloc");exit(2);}
  size_t sh=(nc-cap)/2; memcpy(nt+sh,tape,cap); free(tape); tape=nt; cap=nc;
  head+=sh; lo+=sh; hi+=sh;
}
static inline void write_cell(int v) {
  tape[head]=(int8_t)v;
  if(v) { if(head<lo) lo=head; if(head>hi) hi=head; }
  else {
    while(lo<=hi && tape[lo]==0) lo++;
    while(hi>=lo && tape[hi]==0) hi--;
    if(lo>hi) lo=hi=head;
  }
}

typedef struct { uint64_t hash; long long t; int len,hoff,state,dir; int8_t *cells; } Snap;
static Snap *tab; static size_t tabsz;
static uint64_t mix(uint64_t h,uint64_t x){ h^=x; h*=1099511628211ULL; return h; }
static uint64_t hash_snap(int a,int len,int hoff,int state,int dir){
  uint64_t h=1469598103934665603ULL;
  h=mix(h,(uint64_t)len); h=mix(h,(uint64_t)hoff); h=mix(h,(uint64_t)state);
  for(int i=0;i<len;i++) h=mix(h,(uint64_t)(uint8_t)tape[a+i]);
  return h;
}
static int insert_snap(long long t,int state,int dir,int interval){
  int a=(int)(head<lo?head:lo), b=(int)(head>hi?head:hi);
  int len=b-a+1; if(len<=0) return 0;
  int hoff=(int)(head-a);
  uint64_t h=hash_snap(a,len,hoff,state,dir);
  size_t idx=(size_t)h & (tabsz-1);
  for(size_t probe=0;probe<tabsz;probe++){
    Snap *s=&tab[idx];
    if(!s->cells){
      s->cells=(int8_t*)malloc((size_t)len); if(!s->cells) return 0;
      memcpy(s->cells,tape+a,(size_t)len); s->hash=h; s->t=t; s->len=len; s->hoff=hoff; s->state=state; s->dir=dir;
      return 0;
    }
    if(s->hash==h && s->len==len && s->hoff==hoff && s->state==state &&
       !memcmp(s->cells,tape+a,(size_t)len)) {
      printf("CYCLE t1=%lld t2=%lld period=%lld state=%d dir=%d head=%lld len=%d hoff=%d\n",
             s->t,t,t-s->t,state,dir,head,len,hoff);
      printf("cells1="); for(int i=0;i<s->len;i++) printf("%d",s->cells[i]); printf("\n");
      printf("cells2="); for(int i=0;i<len;i++) printf("%d",tape[a+i]); printf("\n");
      return 1;
    }
    idx=(idx+1)&(tabsz-1);
  }
  return 0;
}

int main(int argc,char**argv){
  if(argc<4){fprintf(stderr,"usage: cyc CAP INTERVAL SPEC\n");return 2;}
  long long capsteps=atoll(argv[1]); long long interval=atoll(argv[2]); const char *spec=argv[3];
  TM tm; if(parse_tm(spec,&tm)){fprintf(stderr,"bad spec\n");return 2;}
  tabsz=1u<<20; tab=(Snap*)calloc(tabsz,sizeof(Snap)); if(!tab){perror("calloc");exit(2);}
  init(); int state=0,dir=0; long long t=0;
  for(t=0;t<capsteps;t++){
    if(t && interval>0 && t%interval==0){
      if(insert_snap(t,state,dir,(int)interval)) return 0;
    }
    int sym=tape[head];
    int w=tm.w[state][sym], d=tm.d[state][sym], nx=tm.nx[state][sym];
    if(nx<0){ printf("HALT t=%lld state=%d head=%lld\n",t,state,head); return 0; }
    write_cell(w); dir=d; state=nx; head+=d;
    if(head<0 || head>=(long long)cap) grow();
  }
  if(insert_snap(t,state,dir,(int)interval)){
    /* repeat printed by insert */
  } else {
    printf("NO_CYCLE t=%lld state=%d head=%lld lo=%lld hi=%lld\n",t,state,head,lo,hi);
  }
  return 0;
}
