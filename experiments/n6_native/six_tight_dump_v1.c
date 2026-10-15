/* Dump primitive SixResidual 5-subsets of [1,HI] whose largest flank e has exactly ONE good opening
   j* < e (every d(6j*+1) mod 6e in [e,5e]). Output: a b c d e j*.  Residual predicate as in
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
int main(int argc,char**argv){
  int HI=atoi(argv[1]); int S[5]; ll res=0, tight=0;
  for(int e=5;e<=HI;e++){ S[4]=e;
    for(int a=1;a<e;a++) for(int b=a+1;b<e;b++) for(int c=b+1;c<e;c++) for(int d=c+1;d<e;d++){
      if(gcd(gcd(gcd(a,b),gcd(c,d)),e)!=1) continue;
      S[0]=a;S[1]=b;S[2]=c;S[3]=d;
      if(!residual(S)) continue; res++;
      int G=0, js=-1; ll m6=6LL*e;
      for(int k=0;k<e && G<2;k++){ ll m=6LL*k+1; int ok=1;
        for(int i=0;i<5;i++){ll r=((ll)S[i]*m)%m6; if(r<e||r>5LL*e){ok=0;break;}}
        if(ok){G++; js=k;} }
      if(G==1){ tight++; printf("%d %d %d %d %d %d\n",a,b,c,d,e,js); } } }
  fprintf(stderr,"HI=%d residual=%lld tight=%lld\n",HI,res,tight);
  return 0;}
