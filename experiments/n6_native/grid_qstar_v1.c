/* Observation only. Exhaustive q* (least q with a unit instant c/q, gcd(c,q)=1, at which all five readings
   (d c mod q)/q lie in [1/6, 5/6], i.e. q <= 6x <= 5q with x = d c mod q) over all primitive 5-subsets of [1,H].
   Prints the distribution and the sets attaining the maximum. Usage: grid_qstar_v1 H */
#include <stdio.h>
#include <stdlib.h>
static int g(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){
  int H=atoi(argv[1]); long dist[200]={0}; int maxq=0; int ex[12][5]; int nex=0; long tot=0;
  int a[5];
  for(a[0]=1;a[0]<=H;a[0]++)for(a[1]=a[0]+1;a[1]<=H;a[1]++)for(a[2]=a[1]+1;a[2]<=H;a[2]++)
  for(a[3]=a[2]+1;a[3]<=H;a[3]++)for(a[4]=a[3]+1;a[4]<=H;a[4]++){
    int gg=g(g(g(g(a[0],a[1]),a[2]),a[3]),a[4]); if(gg!=1) continue; tot++;
    int q;
    for(q=2;q<200;q++){int found=0;
      for(int c=1;c<q&&!found;c++){ if(g(c,q)!=1) continue; int ok=1;
        for(int i=0;i<5&&ok;i++){ long x=((long)a[i]*c)%q; if(6*x<q||6*x>5L*q) ok=0; }
        if(ok) found=1; }
      if(found) break; }
    dist[q]++;
    if(q>maxq){maxq=q;nex=0;}
    if(q==maxq&&nex<12){for(int i=0;i<5;i++)ex[nex][i]=a[i];nex++;}
  }
  printf("H=%d primitive 5-sets %ld\n",H,tot);
  for(int q=0;q<200;q++) if(dist[q]) printf("  q*=%d: %ld\n",q,dist[q]);
  printf("max q* = %d at:",maxq); for(int k=0;k<nex;k++) printf(" (%d,%d,%d,%d,%d)",ex[k][0],ex[k][1],ex[k][2],ex[k][3],ex[k][4]); printf("\n");
  return 0;}
