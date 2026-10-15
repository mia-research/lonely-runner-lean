/* E24: tight integer 5-sets at order six, with simplicity. As six_tight_v1.c, plus: for each tight set, every
   lonely point (certificate (b,k)) lists the number of elements reading exactly at an entry (residue b) and at an
   exit (residue 5b). SIMPLE = every point has exactly one of each. Usage: six_tight_v2 H */
#include <stdio.h>
#include <stdlib.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){int H=atoi(argv[1]);long nt=0,tot=0,nonsimple=0;int s[5];
for(s[0]=1;s[0]<=H;s[0]++)for(s[1]=s[0]+1;s[1]<=H;s[1]++)for(s[2]=s[1]+1;s[2]<=H;s[2]++)for(s[3]=s[2]+1;s[3]<=H;s[3]++)for(s[4]=s[3]+1;s[4]<=H;s[4]++){
 if(gcd(gcd(gcd(s[0],s[1]),gcd(s[2],s[3])),s[4])!=1)continue; tot++;
 int cert=0,pos=0;
 for(int bi=0;bi<5&&!pos;bi++){long b=s[bi];for(long k=0;k<b&&!pos;k++){int ok=1,ex=0;
   for(int i=0;i<5;i++){long r=((long)s[i]*(6*k+1))%(6*b); if(r<b||r>5*b){ok=0;break;} if(r==5*b)ex=1;}
   if(ok){cert=1; if(!ex)pos=1;}}}
 if(!cert){printf("COUNTEREXAMPLE %d %d %d %d %d\n",s[0],s[1],s[2],s[3],s[4]);continue;}
 if(pos)continue;
 nt++; int simple=1; printf("TIGHT %d %d %d %d %d :",s[0],s[1],s[2],s[3],s[4]);
 /* lonely points in [0,1): entries of each element b at (6k+1)/(6b); report (t, #entering, #leaving) once per t */
 for(int bi=0;bi<5;bi++){long b=s[bi];for(long k=0;k<b;k++){int ok=1,en=0,ex=0,dup=0;
   for(int i=0;i<5;i++){long r=((long)s[i]*(6*k+1))%(6*b); if(r<b||r>5*b){ok=0;break;} if(r==b){en++; if(i<bi)dup=1;} if(r==5*b)ex++;}
   if(ok&&!dup){long g=gcd(6*k+1,6*b);printf(" t=%ld/%ld(in %d,out %d)",(6*k+1)/g,6*b/g,en,ex); if(en!=1||ex!=1)simple=0;}}}
 printf(" %s\n",simple?"SIMPLE":"NONSIMPLE"); if(!simple)nonsimple++;
}
printf("H=%d primitive sets %ld tight %ld nonsimple %ld\n",H,tot,nt,nonsimple);return 0;}
