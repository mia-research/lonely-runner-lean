/* E25: every v in (Z/11)^5 not of the form lambda*u (mod 11) has (i,j) in (Z/11)^2 with all five coordinates
   (i u_k + j v_k) mod 11 strictly in (11/6, 55/6), i.e. in {2,...,9}. Also counts the classes lambda*u (expected
   to fail: the tight circle). */
#include <stdio.h>
static int in(int x){x%=11;if(x<0)x+=11;return x>=2&&x<=9;}
int main(void){int U[2][5]={{1,2,3,4,5},{1,3,4,5,9}};
 for(int ui=0;ui<2;ui++){int*u=U[ui];long cls=0,fail=0,failprop=0,prop=0;int v[5];
  for(v[0]=0;v[0]<11;v[0]++)for(v[1]=0;v[1]<11;v[1]++)for(v[2]=0;v[2]<11;v[2]++)for(v[3]=0;v[3]<11;v[3]++)for(v[4]=0;v[4]<11;v[4]++){
   int isprop=0;for(int lam=0;lam<11;lam++){int ok=1;for(int k=0;k<5;k++)if((lam*u[k])%11!=v[k]){ok=0;break;}if(ok)isprop=1;}
   int ok=0;for(int i=0;i<11&&!ok;i++)for(int j=0;j<11&&!ok;j++){int g=1;for(int k=0;k<5;k++)if(!in(i*u[k]+j*v[k])){g=0;break;}if(g)ok=1;}
   cls++; if(isprop){prop++; if(!ok)failprop++;} else if(!ok){fail++;printf("  FAIL v=(%d,%d,%d,%d,%d)\n",v[0],v[1],v[2],v[3],v[4]);}}
  printf("u=(%d,%d,%d,%d,%d): classes %ld; lambda*u classes %ld (no witness %ld); other classes without witness %ld\n",u[0],u[1],u[2],u[3],u[4],cls,prop,failprop,fail);}
 return 0;}
