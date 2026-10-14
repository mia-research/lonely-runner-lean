// seven_eight_enum_v1.c  (Task CD, 2026-10-10).  Exact integer enumeration, no floats, every loop bounded.
// mode "lonely K N w nw": K-subsets of {1..N}, only those whose first element e1 satisfies e1 % nw == w;
//    prints each subset with NO lonely instant (least-clear-opening test: opening j of flank e is lonely iff
//    d(8j+1) mod 8e lies in [e,7e] for every d; j in 0..e-1 suffices by periodicity).
// mode "cross K N w nw": K-subsets of {1..N} (a1 % nw == w); runs the exact integer cascade from t0 = 1/(8 a1)
//    (T = 8t = num/den; reading of d at T is d*num/(8 den)); prints the subset if some state has R = a1*T > 7
//    (a "gate crosser"; includes sets with no lonely instant at all), with a move limit of 100000.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static ll gcdl(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static int K, N;
static int lonely_exists(const int *a){
  for(int ie=0; ie<K; ie++){
    int e=a[ie];
    for(int j=0;j<e;j++){
      int ok=1;
      for(int id=0; id<K; id++){
        ll r=((ll)a[id]*(8*j+1))%(8*(ll)e);
        if(r<e || r>7*(ll)e){ ok=0; break; }
      }
      if(ok) return 1;
    }
  }
  return 0;
}
// returns 1 if some state exceeds R=7 (or move limit hit: returns 2)
static int crosses(const int *a){
  ll num=1, den=a[0];  // T = 1/a1  (R = 1)
  for(int it=0; it<100000; it++){
    ll on=-1, od=1; int any=0;
    for(int i=0;i<K;i++){
      ll x=(ll)a[i]*num, M=8*den, r=x%M, Nn;
      if(r<den) Nn=(x-r)/M; else if(r>7*den) Nn=(x-r)/M+1; else continue;
      ll pn=8*Nn+1, pd=a[i];
      if(!any || pn*od > on*pd){ on=pn; od=pd; any=1; }
    }
    if(!any) return 0;
    ll g=gcdl(on,od); num=on/g; den=od/g;
    if((ll)a[0]*num > 7*den) return 1;
  }
  return 2;
}
int main(int argc,char**argv){
  if(argc<6){ fprintf(stderr,"usage\n"); return 1; }
  int mode = strcmp(argv[1],"lonely")==0 ? 0 : 1;
  K=atoi(argv[2]); N=atoi(argv[3]); int w=atoi(argv[4]), nw=atoi(argv[5]);
  int c[16]; for(int i=0;i<K;i++) c[i]=1+i;
  ll cnt=0, hit=0;
  while(1){
    if(c[0]%nw==w){
      cnt++;
      int f = mode==0 ? !lonely_exists(c) : crosses(c);
      if(f){ hit++; printf("%s",mode==0?"E":"X"); for(int i=0;i<K;i++) printf(" %d",c[i]); printf("\n"); }
    }
    int i=K-1; while(i>=0 && c[i]==N-(K-1-i)) i--; if(i<0) break; c[i]++; for(int j=i+1;j<K;j++) c[j]=c[j-1]+1;
  }
  printf("# mode=%s K=%d N=%d worker %d/%d subsets_tested %lld flagged %lld\n",argv[1],K,N,w,nw,cnt,hit);
  return 0;
}
