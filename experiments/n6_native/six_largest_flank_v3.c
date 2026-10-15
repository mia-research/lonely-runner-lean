/* v3: as v2, with a third argument ALL to test every primitive set (not only the residual); each failure is tagged RESIDUAL or settled-by-rules.
 Fast search: primitive 5-subsets of [1,HI] in SixResidual (OrderSixN.lean, field by field, as
   six_residual_v1.py) whose LARGEST element carries no certificate (residue search k < max).
   Prints each failure and totals per max element bucket. Integers only.
   Usage: six_largest_flank_v2 HI [LO_MAX]  (only sets with max >= LO_MAX are examined) */
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
  if(!f4||!f5) return 0;
  if(!(5*S[0]<S[4])) return 0;               /* spread: exists a,b with 5a<b  <=> 5*min<max */
  int E=5-M; if(!((M==1&&E==4)||(M==2&&E==3)||(M==3&&all3))) return 0;
  for(int i=0;i<5;i++) if(S[i]%6==0 && free_flank(S,S[i])) return 0;
  for(int i=0;i<5;i++){int V=S[i],ok=0; for(int j=0;j<5;j++) if(j!=i && V<=5*S[j]){ok=1;break;} if(!ok) return 0;}
  return 1;}
static int largest_cert(const int*S){
  int b=S[4]; ll m=6LL*b;
  for(int k=0;k<b;k++){ll mult=6LL*k+1; int ok=1;
    for(int i=0;i<5;i++){ll r=((ll)S[i]*mult)%m; if(r<b || r>5LL*b){ok=0;break;}}
    if(ok) return 1;}
  return 0;}
static int ALL=0;
int main(int argc,char**argv){ if(argc>3) ALL=1;
  int HI=atoi(argv[1]); int LO=argc>2?atoi(argv[2]):1;
  ll tot=0,res=0,fail=0; int S[5];
  for(int e=LO>5?LO:5;e<=HI;e++){ S[4]=e;
    for(int a=1;a<e;a++) for(int b=a+1;b<e;b++) for(int c=b+1;c<e;c++) for(int d=c+1;d<e;d++){
      if(gcd(gcd(gcd(a,b),gcd(c,d)),e)!=1) continue;
      S[0]=a;S[1]=b;S[2]=c;S[3]=d; tot++;
      int isres=residual(S); res+=isres; if(!ALL && !isres) continue;
      if(!largest_cert(S)){ fail++; printf("FAIL %d %d %d %d %d %s\n",a,b,c,d,e,isres?"RESIDUAL":"settled-by-rules"); fflush(stdout);} }
    if(e%25==0){fprintf(stderr,"max<=%d: sets=%lld residual=%lld fail=%lld\n",e,tot,res,fail);} }
  printf("HI=%d LO=%d: primitive sets=%lld residual=%lld largest-flank failures=%lld\n",HI,LO,tot,res,fail);
  return 0;}
