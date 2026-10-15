/* E25: the face case by residues. On the face, T = {s u + t y}, y on the three middle coordinates (values c).
   Take s = i/Q, t = j/Q: coordinate k reads (i u_k + j y_k)/Q mod 1, which depends only on y mod Q. So if for a
   modulus Q every residue vector r = y mod Q with gcd(r1,r2,r3,Q) = 1 (forced by y primitive) has some (i,j) with
   every coordinate strictly in (Q/6, 5Q/6) mod Q, the face case holds for ALL y. Prints, per Q, the number of
   failing residue classes. Usage: six_face_mod_v1 maxQ */
#include <stdio.h>
#include <stdlib.h>
static int gcd(int a,int b){if(a<0)a=-a;if(b<0)b=-b;while(b){int t=a%b;a=b;b=t;}return a;}
static int in(long x,int Q){x%=Q;if(x<0)x+=Q;return 6*x>Q && 6*x<5*Q;}
int main(int argc,char**argv){int maxQ=atoi(argv[1]);
 int U[2][5]={{1,2,3,4,5},{1,3,4,5,9}};
 for(int ui=0;ui<2;ui++){int *u=U[ui];int e=0,l=-1,mid[3],nm=0;for(int k=0;k<5;k++){if(u[k]==5)l=k;else if(u[k]!=1)mid[nm++]=k;}
  for(int Q=2;Q<=maxQ;Q++){long fail=0,cls=0;
   for(int r0=0;r0<Q;r0++)for(int r1=0;r1<Q;r1++)for(int r2=0;r2<Q;r2++){
    if(gcd(gcd(gcd(r0,r1),r2),Q)!=1)continue; cls++; int r[3]={r0,r1,r2},ok=0;
    for(int i=0;i<Q&&!ok;i++){ if(!in((long)i*u[e],Q)||!in((long)i*u[l],Q))continue;
     for(int j=0;j<Q&&!ok;j++){int g=1;for(int m=0;m<3;m++)if(!in((long)i*u[mid[m]]+(long)j*r[m],Q)){g=0;break;} if(g)ok=1;}}
    if(!ok){fail++; if(fail<=4)printf("   u%d Q=%d fails r=(%d,%d,%d)\n",ui,Q,r0,r1,r2);}}
   printf("u=(%d,%d,%d,%d,%d) Q=%d classes %ld failing %ld\n",u[0],u[1],u[2],u[3],u[4],Q,cls,fail);
   if(fail==0)break;}}
 return 0;}
