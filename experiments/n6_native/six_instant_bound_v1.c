/* Step 3 (E23): earliest lonely instant T = min over certificates (b,k) of (6k+1)/(6b), all primitive 5-sets in [1,H].
   Reports max of d_min*T (the quantity a bound (B) would control), the sets attaining the top values, and the
   max of d_min*T by spread bucket floor(d_max/d_min). Usage: six_instant_bound_v1 H */
#include <stdio.h>
#include <stdlib.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
typedef struct{long num,den;int s[5];}R;
int main(int argc,char**argv){int H=atoi(argv[1]);int s[5];R top[12];int nt=0;
 double bucket[64]={0}; long tot=0, over1=0;
for(s[0]=1;s[0]<=H;s[0]++)for(s[1]=s[0]+1;s[1]<=H;s[1]++)for(s[2]=s[1]+1;s[2]<=H;s[2]++)for(s[3]=s[2]+1;s[3]<=H;s[3]++)for(s[4]=s[3]+1;s[4]<=H;s[4]++){
 if(gcd(gcd(gcd(s[0],s[1]),gcd(s[2],s[3])),s[4])!=1)continue; tot++;
 long bn=-1,bd=1; /* best T = bn/bd */
 for(int bi=0;bi<5;bi++){long b=s[bi];for(long k=0;k<b;k++){
   if(bn>=0 && (6*k+1)*bd >= bn*6*b) break; /* later k only larger */
   int ok=1; for(int i=0;i<5;i++){long r=((long)s[i]*(6*k+1))%(6*b); if(r<b||r>5*b){ok=0;break;}}
   if(ok){bn=6*k+1;bd=6*b;break;}}}
 long nn=bn*s[0], dd=bd; /* d_min*T */
 if(nn>dd) over1++;
 int sp=s[4]/s[0]; if(sp>63)sp=63; double v=(double)nn/dd; if(v>bucket[sp])bucket[sp]=v;
 R r={nn,dd,{s[0],s[1],s[2],s[3],s[4]}};
 int pos=nt; while(pos>0 && top[pos-1].num*r.den < r.num*top[pos-1].den) pos--;
 if(pos<12){ if(nt<12)nt++; for(int j=nt-1;j>pos;j--)top[j]=top[j-1]; top[pos]=r; }
}
printf("H=%d primitive sets %ld; d_min*T > 1 in %ld\n",H,tot,over1);
for(int j=0;j<nt;j++){long g=gcd(top[j].num,top[j].den);printf("  d_min*T = %ld/%ld = %.4f  at (%d %d %d %d %d)\n",top[j].num/g,top[j].den/g,(double)top[j].num/top[j].den,top[j].s[0],top[j].s[1],top[j].s[2],top[j].s[3],top[j].s[4]);}
printf("max d_min*T by spread floor(d_max/d_min):\n");for(int i=1;i<64;i++)if(bucket[i]>0)printf("  %d: %.4f\n",i,bucket[i]);
return 0;}
