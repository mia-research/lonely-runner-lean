/* E51: all primitive 5-sets v1<...<v5 <= H in BHK §7 (3v1 < v3, D = v3-v2 divides neither v1 nor v3), exact integer
   arithmetic. Meeting times t = k/D. Scale time by 6*D*v1*v2*v3 is too big; instead work per runner with rationals in
   long long: runner d at t = k/D reads d*k/D; its sixth-band window around t: clear iff (6 d k mod 6D) in [D, 5D].
   Window J123 around t: left = min over i in 1..3 of (x_i - 1/6)/v_i, right = min of (5/6 - x_i)/v_i, where
   x_i = (v_i k mod D)/D. Compare with 6*: full3 iff left = 1/(3 v3)... we compare lengths with common denominators.
   BHK main route: some k with J123(t_k) = the full 3-gap (left + right = 2/(3 v3)).
   Relaxed: some k with left + right >= L(rho)/v4, L(rho) = max(1/3 + 1/(3 rho), (m + 1/3)/rho), rho = v5/v4,
   m = largest integer < (rho+1)/3, i.e. 3m < (v5 + v4)/v4.
   Lengths: window length W = l + r with l = min_i (x_i - 1/6)/v_i, r = min_i (5/6 - x_i)/v_i. Use doubles with a
   1e-12 guard and report any near-ties for exact recheck.
   Prints: sets where the main route fails, and whether the relaxed route works; orbit size n = D/gcd(D,v1,v3). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static long gcd(long a,long b){if(a<0)a=-a;if(b<0)b=-b;while(b){long t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){int H=atoi(argv[1]);long tot=0,exc=0,relok=0,ties=0;long byn[64]={0},byn_ok[64]={0};
for(int v1=1;v1<=H;v1++)for(int v2=v1+1;v2<=H;v2++)for(int v3=v2+1;v3<=H;v3++){
 if(!(3*v1<v3))continue; int D=v3-v2; if(v1%D==0||v3%D==0)continue;
 for(int v4=v3+1;v4<=H;v4++)for(int v5=v4+1;v5<=H;v5++){
  if(gcd(gcd(gcd(v1,v2),gcd(v3,v4)),v5)!=1)continue; tot++;
  int vs[3]={v1,v2,v3}; int main=0,rel=0,relstrict=0;
  double rho=(double)v5/v4; int m=0; while(3*(m+1)*v4 < v5+v4) m++;  /* largest m with 3m < rho+1 */
  double L=fmax(1.0/3+1.0/(3*rho),(m+1.0/3)/rho)/v4;
  for(int k=1;k<=D;k++){double l=1e9,r=1e9;int ok=1;
   for(int i=0;i<3;i++){double x=(double)((long)vs[i]*k%D)/D; if(x<1.0/6-1e-12||x>5.0/6+1e-12){ok=0;break;}
     double li=(x-1.0/6)/vs[i], ri=(5.0/6-x)/vs[i]; if(li<l)l=li; if(ri<r)r=ri;}
   if(!ok)continue; double W=l+r;
   if(fabs(W-2.0/(3*v3))<1e-12)main=1;
   if(W>=L-1e-12){rel=1; if(fabs(W-L)<1e-12)ties++; else relstrict=1;}
  }
  if(!main){exc++; long n=D/gcd(gcd(D,v1),v3); if(n>63)n=63; byn[n]++; if(rel){relok++;byn_ok[n]++;}
    else printf("RELAXED FAILS %d %d %d %d %d (n=%ld)\n",v1,v2,v3,v4,v5,n);
    if(rel&&!relstrict)printf("TIEONLY %d %d %d %d %d\n",v1,v2,v3,v4,v5);}
 }}
printf("H=%d §7 primitive sets %ld; main route fails %ld; relaxed works there %ld; near-ties %ld\n",H,tot,exc,relok,ties);
for(int n=0;n<64;n++)if(byn[n])printf("  orbit n=%d: %ld (relaxed works %ld)\n",n,byn[n],byn_ok[n]);
return 0;}
