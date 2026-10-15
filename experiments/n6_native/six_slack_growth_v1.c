/* Per bucket of 12 in e: minimum and mean number G of good openings at the largest flank, and min G/e,
   for primitive SixResidual sets (exceptions with G = 0 excluded from the minimum).  Residual predicate as in
   six_named_c_v1.c / six_largest_flank_v2.c (cross-checked against the Lean SixResidual).
   Usage: six_tight_dump_v1 HI */
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
static ll cnt[64],sum[64]; static int mn[64]; static double mf[64]; static int ar[64][5];
int main(int argc,char**argv){ for(int i=0;i<64;i++){mn[i]=1<<30; mf[i]=1e9;}
  int HI=atoi(argv[1]); int S[5]; ll res=0, tight=0;
  for(int e=5;e<=HI;e++){ S[4]=e;
    for(int a=1;a<e;a++) for(int b=a+1;b<e;b++) for(int c=b+1;c<e;c++) for(int d=c+1;d<e;d++){
      if(gcd(gcd(gcd(a,b),gcd(c,d)),e)!=1) continue;
      S[0]=a;S[1]=b;S[2]=c;S[3]=d;
      if(!residual(S)) continue; res++;
      int G=0, js=-1; ll m6=6LL*e;
      for(int k=0;k<e;k++){ ll m=6LL*k+1; int ok=1;
        for(int i=0;i<5;i++){ll r=((ll)S[i]*m)%m6; if(r<e||r>5LL*e){ok=0;break;}}
        if(ok){G++; js=k;} }
      if(G>0){int bk=(e-1)/12; cnt[bk]++; sum[bk]+=G; if(G<mn[bk]){mn[bk]=G; for(int q=0;q<5;q++) ar[bk][q]=S[q];} double f=(double)G/e; if(f<mf[bk]) mf[bk]=f;} } }
  for(int b=0;b<64;b++) if(cnt[b]) printf("e in [%d,%d]: sets=%lld min G=%d at (%d,%d,%d,%d,%d) mean G=%.1f min G/e=%.3f\n",12*b+1,12*b+12,cnt[b],mn[b],ar[b][0],ar[b][1],ar[b][2],ar[b][3],ar[b][4],(double)sum[b]/cnt[b],mf[b]);
  return 0;}
