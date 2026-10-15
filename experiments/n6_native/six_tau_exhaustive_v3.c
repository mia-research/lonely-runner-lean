/* v3: counts residual sets meeting the resonant-chain conditions on the four largest (staircase 5x<7y for
   consecutive pairs, lap-2 return 11z<7x<13z for pairs two apart), split by tau <= 5/6 or > 5/6.
   v2: as v1, and prints every residual set with tau > 5/6 (one line each).
   Exhaustive tau = v1 * T over primitive SixResidual 5-subsets of [1,HI], T the cascade's fixed point from
   1/(6 v1), in exact integer arithmetic. Every cascade time is an opening p/q = (6c+1)/(6x) (start: 1/(6 v1)).
   d is in the way at p/q iff 6*(d*p mod q) < q or 6*(d*p mod q) > 5q. Its next opening is
   (6c+1)/(6d) with c = ceil(d p/q - 1/6) = ceil((6 d p - q)/(6 q)). The move goes to the latest such opening.
   Reports per bucket of 12 in max: residual sets, max tau (as a fraction) and its set, moves; and the count
   with tau > 5/6 (outside runner 1's first clear lap) and tau > 1. Residual predicate as six_named_c_v1.c.
   Usage: six_tau_exhaustive_v1 HI */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
static int free_flank(const int*S,int e){
  for(int i=0;i<5;i++){int d=S[i]; if(d!=e && d%6==0){ll r=d%(6LL*e); if(!(e<=r && r<=5LL*e)) return 0;}}
  for(int k=0;k<6;k++){int ok=1; for(int i=0;i<5;i++){int d=S[i]; if(d%6){int v=(int)(((ll)d*k + d/e)%6); if(v==0||v==5){ok=0;break;}}} if(ok) return 1;}
  return 0;}
static int residual(const int*S){
  int f4=0,f5=0,M=0,all3=1;
  for(int i=0;i<5;i++){int d=S[i]; if(d%4==0)f4=1; if(d%5==0)f5=1; if(d%6==0)M++; if(d%3)all3=0;}
  if(!f4||!f5) return 0; if(!(5*S[0]<S[4])) return 0;
  int E=5-M; if(!((M==1&&E==4)||(M==2&&E==3)||(M==3&&all3))) return 0;
  for(int i=0;i<5;i++) if(S[i]%6==0 && free_flank(S,S[i])) return 0;
  for(int i=0;i<5;i++){int V=S[i],ok=0; for(int j=0;j<5;j++) if(j!=i && V<=5*S[j]){ok=1;break;} if(!ok) return 0;}
  return 1;}
static ll ceil_div(ll a, ll b){ return a>=0 ? (a+b-1)/b : -((-a)/b); }  /* b > 0 */
/* returns moves; sets *P,*Q to the fixed point p/q */
static int cascade(const int*S, ll*P, ll*Q){
  ll p=1, q=6LL*S[0]; int moves=0;
  for(;;){
    int any=0; ll bp=0,bq=1;
    for(int i=0;i<5;i++){ ll d=S[i]; ll r=(d*p)%q;
      if(6*r<q || 6*r>5*q){ any=1;
        ll c=ceil_div(6*d*p - q, 6*q); ll np=6*c+1, nq=6*d;
        if(np*bq > bp*nq){bp=np;bq=nq;} } }
    if(!any){*P=p;*Q=q;return moves;}
    p=bp;q=bq;moves++;
    if(moves>100000){*P=-1;*Q=1;return moves;} } }
#define NB 32
static ll chain_in=0, chain_over=0, nochain_over=0;
int main(int argc,char**argv){
  int HI=atoi(argv[1]); int S[5];
  ll cnt[NB]={0}, over56[NB]={0}, over1[NB]={0}; ll bn[NB], bd[NB]; int bs[NB][5], bm[NB];
  for(int i=0;i<NB;i++){bn[i]=0;bd[i]=1;}
  for(int e=5;e<=HI;e++){ S[4]=e;
    for(int a=1;a<e;a++) for(int b=a+1;b<e;b++) for(int c=b+1;c<e;c++) for(int d=c+1;d<e;d++){
      if(gcd(gcd(gcd(a,b),gcd(c,d)),e)!=1) continue;
      S[0]=a;S[1]=b;S[2]=c;S[3]=d;
      if(!residual(S)) continue;
      ll p,q; int mv=cascade(S,&p,&q);
      ll tn=(ll)a*p, td=q;   /* tau = v1 * p / q */
      int bk=(e-1)/12; if(bk>=NB) bk=NB-1;
      cnt[bk]++;
      { int t1=S[1],t2=S[2],t3=S[3],t4=S[4];
        int chain = 5*t2<7*t1 && 5*t3<7*t2 && 5*t4<7*t3 && 11*t1<7*t3 && 7*t3<13*t1 && 11*t2<7*t4 && 7*t4<13*t2;
        int over = 6*tn > 5*td; if(over) over56[bk]++;
        if(chain){ if(over) chain_over++; else chain_in++; } else if(over) nochain_over++; }
      if(tn > td) over1[bk]++;
      if(tn*bd[bk] > bn[bk]*td){bn[bk]=tn;bd[bk]=td; for(int i=0;i<5;i++) bs[bk][i]=S[i]; bm[bk]=mv;}
    } }
  printf("chain conditions hold: stays in first lap %lld, leaves it %lld; leaves without chain: %lld\n", chain_in, chain_over, nochain_over);
  for(int b=0;b<NB;b++) if(0 && cnt[b])
    printf("max in [%d,%d]: residual=%lld max tau=%lld/%lld=%.4f at (%d,%d,%d,%d,%d) moves=%d; tau>5/6: %lld; tau>1: %lld\n",
      12*b+1,12*b+12,cnt[b],bn[b],bd[b],(double)bn[b]/bd[b],bs[b][0],bs[b][1],bs[b][2],bs[b][3],bs[b][4],bm[b],over56[b],over1[b]);
  return 0;}
