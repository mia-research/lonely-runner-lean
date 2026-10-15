/* E55: min over all orbits <(a,b)> of order n (a,b not 0 mod n, gcd(a,b,n)=1) of R(G), for n <= N, in exact
   integer arithmetic. Point (i/n, j/n) in the strip 1/6<=x,y<=5/6 (6i>=n, 6i<=5n, same for j). Its bound is
   min((6j-n)/(6i-n), (5n-6j)/(5n-6i)) (each when its denominator > 0). R(G) >= 1/3 iff some point has both
   3(6j-n) >= (6i-n) [or 6i == n with 6j >= n] and 3(5n-6j) >= (5n-6i) [or 6i == 5n with 6j <= 5n].
   Prints every orbit with R < 1/3 (no point in P_{1/3}), and per n the count of orbits. */
#include <stdio.h>
#include <stdlib.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){int N=atoi(argv[1]);long tot=0,bad=0;
 for(int n=2;n<=N;n++){
  for(int a=1;a<n;a++)for(int b=1;b<n;b++){
   if(gcd(gcd(a,b),n)!=1)continue;
   /* canonical generator: skip unless (a,b) is the lexicographically least generator of its group */
   int canon=1;
   for(int u=2;u<n&&canon;u++){ if(gcd(u,n)!=1)continue; int a2=(int)((long)a*u%n), b2=(int)((long)b*u%n);
     if(a2<a||(a2==a&&b2<b))canon=0;}
   if(!canon)continue; tot++;
   int hit=0;
   for(int k=1;k<n&&!hit;k++){long i=(long)a*k%n, j=(long)b*k%n;
     if(6*i<n||6*i>5L*n||6*j<n||6*j>5L*n)continue;
     int lo = (6*i==n) ? (6*j>=n) : (3*(6*j-n) >= (6*i-n));
     int hi = (6*i==5L*n) ? (6*j<=5L*n) : (3*(5L*n-6*j) >= (5L*n-6*i));
     if(lo&&hi)hit=1;}
   if(!hit){bad++;printf("R<1/3: n=%d generator (%d,%d)\n",n,a,b);}
  }}
 printf("N=%d orbits (up to unit multiples) %ld; with no point in P_1/3: %ld\n",N,tot,bad);return 0;}
