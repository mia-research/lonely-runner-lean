/* E26: earliest lonely instant T over primitive 5-sets in [1,H]; tau = d_min*T. Records the lap of the slowest
   runner at T (k1 = floor(tau - 1/6)), the earliest box's lap vector for the top sets, and for each spread bucket
   floor(d_max/d_min) the number of sets with no box in the slowest runner's first lap (k1 >= 1).
   Usage: six_instant_bound_v2 H */
#include <stdio.h>
#include <stdlib.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
typedef struct{long num,den;int s[5];long b,k;}R;
int main(int argc,char**argv){int H=atoi(argv[1]);int s[5];R top[16];int nt=0;
 long k1hist[8]={0}; long late[64]={0}, inb[64]={0}; long tot=0;
for(s[0]=1;s[0]<=H;s[0]++)for(s[1]=s[0]+1;s[1]<=H;s[1]++)for(s[2]=s[1]+1;s[2]<=H;s[2]++)for(s[3]=s[2]+1;s[3]<=H;s[3]++)for(s[4]=s[3]+1;s[4]<=H;s[4]++){
 if(gcd(gcd(gcd(s[0],s[1]),gcd(s[2],s[3])),s[4])!=1)continue; tot++;
 long bn=-1,bd=1,bb=0,bk=0;
 for(int bi=0;bi<5;bi++){long b=s[bi];for(long k=0;k<b;k++){
   if(bn>=0 && (6*k+1)*bd >= bn*6*b) break;
   int ok=1; for(int i=0;i<5;i++){long r=((long)s[i]*(6*k+1))%(6*b); if(r<b||r>5*b){ok=0;break;}}
   if(ok){bn=6*k+1;bd=6*b;bb=b;bk=k;break;}}}
 long nn=bn*s[0], dd=bd;               /* tau = nn/dd */
 long k1=(6*nn-dd)/(6*dd); if(k1>7)k1=7; k1hist[k1]++;
 int sp=s[4]/s[0]; if(sp>63)sp=63; inb[sp]++; if(k1>=1)late[sp]++;
 R r={nn,dd,{s[0],s[1],s[2],s[3],s[4]},bb,bk};
 int pos=nt; while(pos>0 && top[pos-1].num*r.den < r.num*top[pos-1].den) pos--;
 if(pos<16){ if(nt<16)nt++; for(int j=nt-1;j>pos;j--)top[j]=top[j-1]; top[pos]=r; }
}
printf("H=%d primitive sets %ld\nlap of the slowest runner at T (k1): ",H,tot);for(int i=0;i<8;i++)printf("%d:%ld ",i,k1hist[i]);printf("\n");
printf("sets with k1>=1 by spread floor(d_max/d_min): ");for(int i=1;i<64;i++)if(late[i])printf("%d:%ld/%ld ",i,late[i],inb[i]);printf("\n");
for(int j=0;j<nt;j++){long g=gcd(top[j].num,top[j].den);
  printf("  tau=%ld/%ld=%.4f (%d %d %d %d %d) flank %ld opening %ld laps",top[j].num/g,top[j].den/g,(double)top[j].num/top[j].den,top[j].s[0],top[j].s[1],top[j].s[2],top[j].s[3],top[j].s[4],top[j].b,top[j].k);
  for(int i=0;i<5;i++){long x=(long)top[j].s[i]*(6*top[j].k+1); printf(" %ld",(x-top[j].b)/(6*top[j].b) + 0*((x%(6*top[j].b))));} printf("\n");}
return 0;}
