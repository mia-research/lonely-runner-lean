/* E44: tight (degenerate) primitive configurations at order n (n-1 speeds in [1,H]): lonely at 1/n but every lonely
   interval a single point. Certificate (b,k): every a has a(nk+1) mod nb in [b,(n-1)b]; positive length iff no
   residue equals (n-1)b. For each tight set: lonely points in [0,1) with #entering (residue b) and #leaving
   (residue (n-1)b). Usage: tight_general_v1 n H */
#include <stdio.h>
#include <stdlib.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int n,H,m,s[8];long tot=0,nt=0;
void test(void){int g=0;for(int i=0;i<m;i++)g=gcd(g,s[i]);if(g!=1)return;tot++;
 int cert=0,pos=0;
 for(int bi=0;bi<m&&!pos;bi++){long b=s[bi];for(long k=0;k<b&&!pos;k++){int ok=1,ex=0;
   for(int i=0;i<m;i++){long r=((long)s[i]*(n*k+1))%(n*b);if(r<b||r>(n-1)*b){ok=0;break;}if(r==(n-1)*b)ex=1;}
   if(ok){cert=1;if(!ex)pos=1;}}}
 if(!cert){printf("COUNTEREXAMPLE");for(int i=0;i<m;i++)printf(" %d",s[i]);printf("\n");return;}
 if(pos)return; nt++; printf("TIGHT");for(int i=0;i<m;i++)printf(" %d",s[i]);printf(" :");
 int pts=0,simple=1;
 for(int bi=0;bi<m;bi++){long b=s[bi];for(long k=0;k<b;k++){int ok=1,en=0,ex=0,dup=0;
   for(int i=0;i<m;i++){long r=((long)s[i]*(n*k+1))%(n*b);if(r<b||r>(n-1)*b){ok=0;break;}if(r==b){en++;if(i<bi)dup=1;}if(r==(n-1)*b)ex++;}
   if(ok&&!dup){long g2=gcd(n*k+1,n*b);pts++;printf(" t=%ld/%ld(in",(n*k+1)/g2,n*b/g2);
     for(int i=0;i<m;i++){long r=((long)s[i]*(n*k+1))%(n*b);if(r==b)printf(" %d",s[i]);}printf(";out");
     for(int i=0;i<m;i++){long r=((long)s[i]*(n*k+1))%(n*b);if(r==(n-1)*b)printf(" %d",s[i]);}printf(")");
     if(en!=1||ex!=1)simple=0;}}}
 printf(" | points %d %s\n",pts,simple?"SIMPLE":"NONSIMPLE");}
void rec(int i,int lo){if(i==m){test();return;}for(int v=lo;v<=H;v++){s[i]=v;rec(i+1,v+1);}}
int main(int c,char**v){n=atoi(v[1]);H=atoi(v[2]);m=n-1;rec(0,1);printf("n=%d H=%d primitive sets %ld tight %ld\n",n,H,tot,nt);return 0;}
