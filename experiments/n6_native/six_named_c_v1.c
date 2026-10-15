/* Least c naming a good opening at the largest flank, for primitive SixResidual 5-subsets of [1,HI].
   Good opening: j < e with every d*(6j+1) mod 6e in [e, 5e]. Named by (x, c): x*(6j+1) mod e in {c, e-c},
   x ranging over the elements other than e, all pairwise differences, and pairwise sums of non-e elements
   (x mod e != 0). Least c = min over good j and x of min(x*m mod e, e - x*m mod e), ignoring 0.
   Categories: D = largest is the unique multiple of 6; C = gcd(e,6)=1; G2, G3 = gcd 2, 3; M2 = otherwise.
   Prints per category and per bucket of 12 in e: sets, exceptions (no good opening), max least c, argmax,
   and count with least c > 5.  Residual predicate as in six_largest_flank_v2.c (cross-checked).
   Usage: six_named_c_v1 HI */
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
#define NB 64
#define NC 5
static ll sets[NC][NB], exc[NC][NB], gt5[NC][NB]; static int mx[NC][NB]; static int arg[NC][NB][5];
static const char* cname[NC]={"D (largest = unique mult of 6)","C (gcd(e,6)=1)","G2 (gcd 2)","G3 (gcd 3)","M2 (other)"};
int main(int argc,char**argv){
  int HI=atoi(argv[1]); int S[5]; int X[32];
  for(int e=5;e<=HI;e++){ S[4]=e;
    for(int a=1;a<e;a++) for(int b=a+1;b<e;b++) for(int c=b+1;c<e;c++) for(int d=c+1;d<e;d++){
      if(gcd(gcd(gcd(a,b),gcd(c,d)),e)!=1) continue;
      S[0]=a;S[1]=b;S[2]=c;S[3]=d;
      if(!residual(S)) continue;
      int M=0; for(int i=0;i<5;i++) if(S[i]%6==0) M++;
      int g=gcd(e,6), cat;
      if(e%6==0 && M==1) cat=0; else if(g==1) cat=1; else if(g==2) cat=2; else if(g==3) cat=3; else cat=4;
      int nx=0;
      for(int i=0;i<4;i++){int x=S[i]%e; if(x) X[nx++]=x;}
      for(int i=0;i<5;i++) for(int j=i+1;j<5;j++){int x=(S[j]-S[i])%e; if(x) X[nx++]=x;}
      for(int i=0;i<4;i++) for(int j=i+1;j<4;j++){int x=(S[i]+S[j])%e; if(x) X[nx++]=x;}
      int best=1<<30, anygood=0; ll m6=6LL*e;
      for(int k=0;k<e;k++){ ll m=6LL*k+1; int ok=1;
        for(int i=0;i<5;i++){ll r=((ll)S[i]*m)%m6; if(r<e||r>5LL*e){ok=0;break;}}
        if(!ok) continue; anygood=1;
        for(int t=0;t<nx;t++){ int w=(int)(((ll)X[t]*m)%e); if(w==0) continue; int cc=w<e-w?w:e-w; if(cc<best) best=cc; } }
      int bk=(e-1)/12; if(bk>=NB) bk=NB-1;
      sets[cat][bk]++;
      if(!anygood){exc[cat][bk]++; continue;}
      if(best>5) gt5[cat][bk]++;
      if(best>mx[cat][bk]){mx[cat][bk]=best; for(int i=0;i<5;i++) arg[cat][bk][i]=S[i];}
    }
  }
  for(int c=0;c<NC;c++){ printf("%s\n",cname[c]);
    for(int b=0;b<NB;b++) if(sets[c][b]) printf("  e in [%d,%d]: sets=%lld exceptions=%lld least-c>5: %lld  max least c=%d at (%d,%d,%d,%d,%d)\n",
       12*b+1,12*b+12,sets[c][b],exc[c][b],gt5[c][b],mx[c][b],arg[c][b][0],arg[c][b][1],arg[c][b][2],arg[c][b][3],arg[c][b][4]); }
  return 0;}
