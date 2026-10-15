/* Step 2 (E23): degenerate (tight) integer configurations at order six.
   S = {a1<..<a5} in [1,H], gcd 1. Certificate (b,k): every a has a(6k+1) mod 6b in [b,5b] (Bridge.lean).
   The lonely interval starting at that opening has positive length iff no a reads exactly at 5/6 there,
   i.e. no residue equals 5b. S is TIGHT iff it has certificates and every one has some residue = 5b.
   Prints tight sets. Usage: six_tight_v1 H */
#include <stdio.h>
#include <stdlib.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){int H=atoi(argv[1]);long nt=0,nl=0,tot=0;int s[5];
for(s[0]=1;s[0]<=H;s[0]++)for(s[1]=s[0]+1;s[1]<=H;s[1]++)for(s[2]=s[1]+1;s[2]<=H;s[2]++)for(s[3]=s[2]+1;s[3]<=H;s[3]++)for(s[4]=s[3]+1;s[4]<=H;s[4]++){
 if(gcd(gcd(gcd(s[0],s[1]),gcd(s[2],s[3])),s[4])!=1)continue; tot++;
 int cert=0,pos=0;
 for(int bi=0;bi<5&&!pos;bi++){long b=s[bi];for(long k=0;k<b&&!pos;k++){int ok=1,ex=0;
   for(int i=0;i<5;i++){long r=((long)s[i]*(6*k+1))%(6*b); if(r<b||r>5*b){ok=0;break;} if(r==5*b)ex=1;}
   if(ok){cert=1; if(!ex)pos=1;}}}
 if(!cert){printf("COUNTEREXAMPLE %d %d %d %d %d\n",s[0],s[1],s[2],s[3],s[4]);continue;}
 if(!pos){nt++;printf("TIGHT %d %d %d %d %d\n",s[0],s[1],s[2],s[3],s[4]);}
}
printf("H=%d primitive sets %ld tight %ld\n",H,tot,nt);return 0;}
