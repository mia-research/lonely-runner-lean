#!/usr/bin/env python3
"""law_of_position_v1.py -- Task BA (2026-10-09): the law of position of the cascade, K = 4 and K = 5 readings.

Everything is exact: C++ __int128 integers and Python Fractions; no floats decide anything (numpy floats are used ONLY to find
a witness reading, which is then re-verified with Fractions).  Every cascade loop has a move limit (400; reported if reached,
0 times).  Nothing is random.  Nothing is sampled: every K-subset of {p/Q : Q <= p <= M Q} of the stated populations is run.

Coordinates.  Unit m = 1 (readings p/Q >= 1), R = 8t, the cascade starts at R = 1.  Reading x is IN THE WAY at R when
|x R - 8 l| < 1 for its lap l (= distInt(x t) < 1/8); its WINDOW of lap l is ((8l-1)/x, (8l+1)/x); a move goes to the largest right
end (8l+1)/x among the windows that contain R.  dev(z,R) = z R - 8 l, l = round(z R / 8): the signed residue in (-4, 4].
Rank 0 = slowest reading.  A word is the sequence of setter ranks of a chain.

Sections
  1  census of chains: entered-anew, two-step law, zones at a landing, lap budget, landing R by rank  (populations)
  2  words over K letters (length <= 8) that satisfy the additive budget, against the words that occur
  3  local test of the first return of the slowest from ANY landing of it (reachable or not)
  4  exact named exceptions to the local form; the lap form of the budget; the K = 5 extension
  5  hypothesis audit and the position law as it stands
Lean: Fresh/LawOfPosition.lean (entered_anew, two_step_law, lap_identity, lap_budget, budget_of_reset; check.sh clean).
Grades: [L] Lean, [OBS] exact data on the stated population, [reasoned] argument not formalised, [OWED].
"""
import subprocess, tempfile, os, sys, math, itertools
from fractions import Fraction as F
from collections import Counter

CENSUS_CPP = r'''// law_of_position_v1 : exact integer census of cascade chains over all K-subsets of {p/Q : Q <= p <= M*Q}.
// Readings are p/Q relative to the unit m = 1; R = 8t; cascade starts at R = 1.  Rank 0 = slowest.  Move limit 400 per set.
// Window picture: reading x has windows ((8l-1)/x, (8l+1)/x) in R; a move goes to the largest right end among windows containing R.
#include <vector>
#include <thread>
#include <atomic>
#include <functional>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <map>
#include <string>
using namespace std;
typedef long long ll; typedef __int128 LL;
int K; ll Q, M;
struct Fr { ll n=0,d=1; };
static bool lessF(const Fr&a,const Fr&b){ return (LL)a.n*b.d < (LL)b.n*a.d; }
struct Mm { bool have=false; Fr mn, mx; ll cnt=0; void add(ll n,ll d){ Fr f; f.n=n; f.d=d; cnt++; if(!have){mn=f;mx=f;have=true;} else { if(lessF(f,mn)) mn=f; if(lessF(mx,f)) mx=f; } } };
struct Stat {
  ll sets=0, limitHit=0, maxlen=0;
  map<string,ll> wordsLap, wordsPlain;
  ll anewTests=0, anewViol=0;           // entered-anew: z in the way at R_s on lap l  =>  z*R_{s-1} <= 8l-1
  ll upTests=0, upViol=0;               // d_s < 2/x_s
  ll loTests=0, loViol=0;               // d_s + d_{s-1} >= 2/x_s   (s>=2), i.e. R_{s+1} - R_{s-1} >= 2/x_s
  ll preInNowIn=0, preInNowOut=0, preOutNowIn=0, preOutNowOut=0;
  Mm devPrevInNowOut;                    // dev of z relative to its OLD lap, z in way before and clear now: expect >= 1
  Mm devNowInPrevOut;                    // dev (signed residue) of z in the way now, clear before
  Mm devOutOutNeg, devOutOutPos;         // signed residue of z clear both times (negative part / positive part)
  map<int,ll> dlap;                      // lap change of a reading that was in the way before and is in the way again now
  map<string,ll> rankLap;                // "rank:lap" -> count of settings
  ll slowSet=0;
  map<string,Mm> zoneA; map<int,ll> lbTests, lbViol; map<int,Fr> lbMinRatio; Mm landR[8];
};
static inline ll rnd_div(LL num, LL den){ LL v=2*num+den; LL d=2*den; LL q=v/d; if((v%d!=0)&&((v<0)!=(d<0))) q--; return (ll)q; }
void run(const ll* p,int k,Stat& st){
  ll Rn[512], Rd[512]; int setter[512]; int lapv[512]; unsigned mask[512]; int lapOf[512][8];
  Rn[0]=1; Rd[0]=1; int len=0; bool hit=false;
  while(true){
    ll A=Rn[len],B=Rd[len];
    bool any=false; ll bA=0,bB=1; int bi=-1; ll bn=0; unsigned mk=0;
    for(int i=0;i<k;i++){
      LL num=(LL)p[i]*A; LL den=(LL)8*Q*B; ll n=rnd_div(num,den); lapOf[len][i]=(int)n;
      LL diff=num-(LL)n*den; if(diff<0) diff=-diff;
      if(8*diff<den){ mk|=1u<<i; ll a2=(8*n+1)*Q,b2=p[i]; if(!any||(LL)a2*bB>(LL)bA*b2){bA=a2;bB=b2;any=true;bi=i;bn=n;} }
    }
    mask[len]=mk;
    if(!any) break;
    setter[len]=bi; lapv[len]=(int)bn; len++; Rn[len]=bA; Rd[len]=bB;
    if(len>=400){hit=true;break;}
  }
  st.sets++; if(hit){ st.limitHit++; return; }
  if(len>st.maxlen) st.maxlen=len;
  string kp, kl; char buf[48];
  for(int s=0;s<len;s++){ snprintf(buf,sizeof buf,"%d",setter[s]); kp+=buf; snprintf(buf,sizeof buf,"%d:%d ",setter[s],lapv[s]); kl+=buf;
    snprintf(buf,sizeof buf,"%d:%d",setter[s],lapv[s]); st.rankLap[buf]++; }
  st.wordsPlain[kp]++; st.wordsLap[kl]++;
  for(int s=1;s<=len;s++){
    // landing s = R_s ; previous R_{s-1}
    ll A=Rn[s],B=Rd[s],Ap=Rn[s-1],Bp=Rd[s-1];
    for(int z=0;z<k;z++){
      int pin=(mask[s-1]>>z)&1, nin=(mask[s]>>z)&1;
      // current lap and signed residue dev = z*R_s - 8*l  (over denominator Q*B)
      ll l=lapOf[s][z]; LL devn=(LL)p[z]*A-(LL)8*l*Q*B;      // dev = devn/(Q*B)
      if(z==setter[s-1]) continue;
      if(setter[s-1]==0){ char kb[48]; LL dv=devn; snprintf(kb,sizeof kb,"L%d z%d p%d n%d",lapv[s-1],z,pin,nin); st.zoneA[kb].add((ll)dv,(ll)(Q*B)); }
      if(pin&&nin) st.preInNowIn++; else if(pin&&!nin) st.preInNowOut++; else if(!pin&&nin) st.preOutNowIn++; else st.preOutNowOut++;
      if(nin){ // entered anew: z*R_{s-1} <= 8l-1  <=>  p_z*Ap <= (8l-1)*Q*Bp
        st.anewTests++; if(!((LL)p[z]*Ap <= (LL)(8*l-1)*Q*Bp)) st.anewViol++;
        if(!pin) st.devNowInPrevOut.add((ll)devn,(ll)(Q*B));
      }
      if(pin){ ll lo=lapOf[s-1][z]; LL dold=(LL)p[z]*A-(LL)8*lo*Q*B;
        if(!nin) st.devPrevInNowOut.add((ll)dold,(ll)(Q*B));
        else st.dlap[(int)(l-lo)]++; }
      if(!pin&&!nin){ if(devn<0) st.devOutOutNeg.add((ll)devn,(ll)(Q*B)); else st.devOutOutPos.add((ll)devn,(ll)(Q*B)); }
    }
  }
  // d_s < 2/x_s and d_s + d_{s-1} >= 2/x_s : in R units, x_s = p/Q ; R_{s+1}-R_s < 2Q/p
  for(int s=0;s<len;s++){
    LL num=(LL)Rn[s+1]*Rd[s]-(LL)Rn[s]*Rd[s+1]; LL den=(LL)Rd[s]*Rd[s+1];   // d = num/den
    st.upTests++; if(!(num*p[setter[s]] < (LL)2*Q*den)) st.upViol++;
    if(s>=1){ LL num2=(LL)Rn[s+1]*Rd[s-1]-(LL)Rn[s-1]*Rd[s+1]; LL den2=(LL)Rd[s+1]*Rd[s-1];
      st.loTests++; if(!(num2*p[setter[s]] >= (LL)2*Q*den2)) st.loViol++; }
  }

  // landing R per rank
  for(int s=0;s<len;s++) st.landR[setter[s]].add(Rn[s+1],Rd[s+1]);
  // lap budget: x set at n and again at k>n, j = lap_k - lap_n :  4j - 1 < sum_{n<s<k} x/w_s   (exact, integers)
  { LL D=1; for(int i=0;i<k;i++) D*=p[i];
    for(int n=0;n<len;n++) for(int kk=n+1;kk<len;kk++) if(setter[kk]==setter[n]){
      int j=lapv[kk]-lapv[n]; LL N=0; for(int s=n+1;s<kk;s++) N+=(LL)p[setter[n]]*(D/p[setter[s]]);
      st.lbTests[j]++; if(!(N>(LL)(4*j-1)*D)) st.lbViol[j]++;
      Fr f; f.n=(ll)(N-(LL)(4*j-1)*D); f.d=(ll)D; // margin = sum - (4j-1)
      auto it=st.lbMinRatio.find(j); if(it==st.lbMinRatio.end()) st.lbMinRatio[j]=f; else if(lessF(f,it->second)) it->second=f;
    } }
  if(setter[0]==0 || true){ for(int s=0;s<len;s++) if(setter[s]==0) st.slowSet++; }
}
static void pm(const char*name,const Mm&m){ if(!m.have){ printf("  %s: none\n",name); return; } printf("  %s: n=%lld min=%lld/%lld max=%lld/%lld\n",name,m.cnt,m.mn.n,m.mn.d,m.mx.n,m.mx.d); }
int main(int argc,char**argv){
  K=atoi(argv[1]);Q=atoll(argv[2]);M=atoll(argv[3]); bool dumpwords=(argc>4);
  int nv=(int)(M*Q-Q+1); vector<ll> vals(nv); for(int i=0;i<nv;i++) vals[i]=Q+i;
  int nt=10; vector<Stat> sts(nt); vector<thread> th; atomic<int> nxt(0);
  for(int t=0;t<nt;t++) th.emplace_back([&,t]{ ll p[16];
    while(true){ int i0=nxt++; if(i0>=nv) break; p[0]=vals[i0];
      function<void(int,int)> rec=[&](int pos,int start){ if(pos==K-1){run(p,K,sts[t]);return;} for(int j=start;j<nv;j++){p[pos+1]=vals[j];rec(pos+1,j+1);} };
      rec(0,i0+1);} });
  for(auto&x:th) x.join();
  Stat T;
  auto mg=[&](Mm&a,const Mm&b){ if(!b.have) return; a.cnt+=b.cnt; if(!a.have){a.mn=b.mn;a.mx=b.mx;a.have=true;} else { if(lessF(b.mn,a.mn)) a.mn=b.mn; if(lessF(a.mx,b.mx)) a.mx=b.mx; } };
  for(auto&s:sts){ T.sets+=s.sets;T.limitHit+=s.limitHit;if(s.maxlen>T.maxlen)T.maxlen=s.maxlen;
    for(auto&kv:s.wordsLap)T.wordsLap[kv.first]+=kv.second; for(auto&kv:s.wordsPlain)T.wordsPlain[kv.first]+=kv.second; for(auto&kv:s.rankLap)T.rankLap[kv.first]+=kv.second; for(auto&kv:s.dlap)T.dlap[kv.first]+=kv.second;
    T.anewTests+=s.anewTests;T.anewViol+=s.anewViol;T.upTests+=s.upTests;T.upViol+=s.upViol;T.loTests+=s.loTests;T.loViol+=s.loViol;
    T.preInNowIn+=s.preInNowIn;T.preInNowOut+=s.preInNowOut;T.preOutNowIn+=s.preOutNowIn;T.preOutNowOut+=s.preOutNowOut;
    mg(T.devPrevInNowOut,s.devPrevInNowOut);mg(T.devNowInPrevOut,s.devNowInPrevOut);mg(T.devOutOutNeg,s.devOutOutNeg);mg(T.devOutOutPos,s.devOutOutPos); T.slowSet+=s.slowSet; for(auto&kv:s.lbTests)T.lbTests[kv.first]+=kv.second; for(auto&kv:s.lbViol)T.lbViol[kv.first]+=kv.second; for(auto&kv:s.lbMinRatio){ auto it=T.lbMinRatio.find(kv.first); if(it==T.lbMinRatio.end()) T.lbMinRatio[kv.first]=kv.second; else if(lessF(kv.second,it->second)) it->second=kv.second; } for(int r=0;r<8;r++) mg(T.landR[r],s.landR[r]); for(auto&kv:s.zoneA) mg(T.zoneA[kv.first],kv.second); }
  printf("CENSUS K=%d Q=%lld M=%lld sets=%lld moveLimitHit=%lld maxChain=%lld distinctChains(word+laps)=%zu distinctWords(ranks)=%zu\n",K,Q,M,T.sets,T.limitHit,T.maxlen,T.wordsLap.size(),T.wordsPlain.size());
  printf("  ENTERED-ANEW (z in the way at landing R_s on lap l  =>  z*R_{s-1} <= 8l-1): tests=%lld violations=%lld\n",T.anewTests,T.anewViol);
  printf("  TWO-STEP upper (R_{s+1}-R_s < 2/x_s): tests=%lld violations=%lld ; lower (R_{s+1}-R_{s-1} >= 2/x_s, s>=1): tests=%lld violations=%lld\n",T.upTests,T.upViol,T.loTests,T.loViol);
  printf("  other readings at a landing (setter excluded): in the way before & now=%lld ; before & clear now=%lld ; clear before & in the way now=%lld ; clear both=%lld\n",T.preInNowIn,T.preInNowOut,T.preOutNowIn,T.preOutNowOut);
  pm("dev (vs its OLD lap) of z in the way before, clear now [expect >= 1]",T.devPrevInNowOut);
  pm("signed residue of z clear before, in the way now",T.devNowInPrevOut);
  pm("signed residue of z clear before and now, negative part",T.devOutOutNeg);
  pm("signed residue of z clear before and now, positive part",T.devOutOutPos);
  printf("  lap change l_new - l_old of a reading in the way before AND now:"); for(auto&kv:T.dlap) printf(" %d:%lld",kv.first,kv.second); printf("\n");
  for(auto&kv:T.lbTests) printf("  LAP BUDGET (x set at n and k, j = lap_k - lap_n = %d): 4j-1 < sum x/w : tests=%lld violations=%lld ; min(sum - (4j-1)) = %lld/%lld\n",kv.first,kv.second,T.lbViol[kv.first],T.lbMinRatio[kv.first].n,T.lbMinRatio[kv.first].d);
  for(int r=0;r<K;r++) if(T.landR[r].have) printf("  landing R of rank %d (n=%lld): min %lld/%lld max %lld/%lld\n",r,T.landR[r].cnt,T.landR[r].mn.n,T.landR[r].mn.d,T.landR[r].mx.n,T.landR[r].mx.d);
  for(auto&kv:T.zoneA) printf("  ZONE at a landing of the slowest (rank 0) [%s]: n=%lld dev in [%lld/%lld, %lld/%lld] = [%.4f, %.4f]\n",kv.first.c_str(),kv.second.cnt,kv.second.mn.n,kv.second.mn.d,kv.second.mx.n,kv.second.mx.d,(double)kv.second.mn.n/kv.second.mn.d,(double)kv.second.mx.n/kv.second.mx.d);
  printf("  settings by rank:lap :"); for(auto&kv:T.rankLap) printf(" %s=%lld",kv.first.c_str(),kv.second); printf("\n");
  if(dumpwords){ for(auto&kv:T.wordsPlain) printf("WORD %s %lld\n",kv.first.c_str(),kv.second); for(auto&kv:T.wordsLap) printf("WORDLAP %s| %lld\n",kv.first.c_str(),kv.second); }
}
'''
LOCAL_CPP = r'''// law_of_position_v1 local test (see py header).  Local test: start the cascade at an arbitrary landing of the slowest reading a = p[0] on lap L (R = (8L+1)/a, need R >= 1),
// find the first later state with a in the way; count the distinct setters strictly between (a never in the way in between by definition of first).
// Also records whether the landing is REACHED by the real cascade from R=1 (a is a setter on lap L in the real chain).
#include <vector>
#include <thread>
#include <atomic>
#include <functional>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <string>
#include <mutex>
using namespace std;
typedef long long ll; typedef __int128 LL;
int K; ll Q, M; int LMAX=12; bool FIXA=false; bool ANYR=false;
struct Stat { ll byL[256]={0}; ll pairs=0, reach=0, ret=0, retReach=0, retViol=0, retViolReach=0, limit=0; map<string,ll> hist; map<string,ll> exs; map<string,pair<ll,int>> wordsRet; };
static inline ll rnd_div(LL num, LL den){ LL v=2*num+den; LL d=2*den; LL q=v/d; if((v%d!=0)&&((v<0)!=(d<0))) q--; return (ll)q; }
// one move from R=A/B : returns -1 if nobody in way, else setter; sets A,B,lap, mask
static int step(const ll* p,int k,ll&A,ll&B,int&lap,unsigned&mk){
  bool any=false; ll bA=0,bB=1; int bi=-1; ll bn=0; mk=0;
  for(int i=0;i<k;i++){
    LL num=(LL)p[i]*A; LL den=(LL)8*Q*B; ll n=rnd_div(num,den);
    LL diff=num-(LL)n*den; if(diff<0) diff=-diff;
    if(8*diff<den){ mk|=1u<<i; ll a2=(8*n+1)*Q,b2=p[i]; if(!any||(LL)a2*bB>(LL)bA*b2){bA=a2;bB=b2;any=true;bi=i;bn=n;} }
  }
  if(!any) return -1;
  A=bA;B=bB;lap=(int)bn; return bi;
}
void run(const ll* p,int k,Stat& st){
  // real chain: laps at which a is a setter
  bool reachL[256]={0}; { ll A=1,B=1; int lap; unsigned mk; for(int it=0;it<400;it++){ int s=step(p,k,A,B,lap,mk); if(s<0) break; if(s==0 && lap>=0 && lap<256) reachL[lap]=true; } }
  for(int L=1;L<=LMAX;L++){
    // R = (8L+1)Q/p0 ; need R>=1 : (8L+1)Q >= p0
    ll A=(8*L+1)*Q,B=p[0]; if(!ANYR && A<B) continue;
    st.pairs++; bool reached=(L<256)&&reachL[L]; if(reached) st.reach++;
    unsigned seen=0; int moves=0; bool ret=false; int lap; unsigned mk; string wd;
    for(int it=0;it<400;it++){
      // state: check a in the way
      LL num=(LL)p[0]*A; LL den=(LL)8*Q*B; ll n=rnd_div(num,den); LL diff=num-(LL)n*den; if(diff<0) diff=-diff;
      if(8*diff<den && it>0){ ret=true; break; }
      int s=step(p,k,A,B,lap,mk); if(s<0) break;
      { char cb[8]; snprintf(cb,sizeof cb,"%d",s); wd+=cb; }
      if(it>0) seen|=1u<<s;
      if(it==0){ /* setter at landing state counts as intermediate setter */ seen|=1u<<s; }
      moves++;
    }
    if(ret){
      st.ret++; if(reached) st.retReach++;
      int cnt=__builtin_popcount(seen & ~1u);
      char b[64]; snprintf(b,sizeof b,"distinct=%d reached=%d",cnt,(int)reached); st.hist[b]++;
      { auto& e=st.wordsRet[wd+(reached?" R":" U")]; if(e.first==0||L<e.second) e.second=L; e.first++; }
      bool viol = (k==4) ? true : (cnt<4);
      if(viol){ st.byL[L]++; st.retViol++; if(reached) st.retViolReach++;
        if(st.exs.size()<20){ char e[200]; int o=0; o+=snprintf(e+o,sizeof e-o,"L=%d reached=%d set:",L,(int)reached); for(int i=0;i<k;i++) o+=snprintf(e+o,sizeof e-o," %lld",p[i]); st.exs[e]=1; } }
    }
  }
}
int main(int argc,char**argv){
  K=atoi(argv[1]);Q=atoll(argv[2]);M=atoll(argv[3]); if(argc>4) LMAX=atoi(argv[4]); if(argc>5) FIXA=true; if(argc>6) ANYR=true;
  int nv=(int)(M*Q-Q+1); vector<ll> vals(nv); for(int i=0;i<nv;i++) vals[i]=Q+i;
  int nt=10; vector<Stat> sts(nt); vector<thread> th; atomic<int> nxt(0);
  for(int t=0;t<nt;t++) th.emplace_back([&,t]{ ll p[16];
    while(true){ int i0=nxt++; if(i0>=nv) break; if(FIXA && i0!=0) break; p[0]=vals[i0];
      function<void(int,int)> rec=[&](int pos,int start){ if(pos==K-1){run(p,K,sts[t]);return;} for(int j=start;j<nv;j++){p[pos+1]=vals[j];rec(pos+1,j+1);} };
      rec(0,i0+1);} });
  for(auto&x:th) x.join();
  Stat T; for(auto&s:sts){ T.pairs+=s.pairs;T.reach+=s.reach;T.ret+=s.ret;T.retReach+=s.retReach;T.retViol+=s.retViol;T.retViolReach+=s.retViolReach; for(int i=0;i<256;i++) T.byL[i]+=s.byL[i]; for(auto&kv:s.wordsRet){ auto&e=T.wordsRet[kv.first]; if(e.first==0||kv.second.second<e.second) e.second=kv.second.second; e.first+=kv.second.first; } for(auto&kv:s.hist)T.hist[kv.first]+=kv.second; for(auto&kv:s.exs) if(T.exs.size()<20) T.exs[kv.first]=1; }
  printf("LOCAL K=%d Q=%lld M=%lld : (set,L) pairs=%lld reached-by-real-chain=%lld ; first returns of a: all=%lld reached=%lld ; violations of the law (K=4: any return; K=5: <4 distinct): all=%lld reached=%lld\n",K,Q,M,T.pairs,T.reach,T.ret,T.retReach,T.retViol,T.retViolReach);
  printf("  violations by L:"); for(int i=0;i<256;i++) if(T.byL[i]) printf(" %d:%lld",i,T.byL[i]); printf("\n");
  for(auto&kv:T.wordsRet) printf("  RETURN WORD %s : %lld (smallest L %d)\n",kv.first.c_str(),kv.second.first,kv.second.second);
  for(auto&kv:T.hist) printf("  %s : %lld\n",kv.first.c_str(),kv.second);
  for(auto&kv:T.exs) printf("  EX %s\n",kv.first.c_str());
}
'''

TMP = tempfile.mkdtemp(prefix="lop_")
def build(name, src):
    p = os.path.join(TMP, name + ".cpp"); b = os.path.join(TMP, name)
    open(p, "w").write(src)
    r = subprocess.run(["g++", "-O2", "-std=c++17", "-pthread", "-o", b, p], capture_output=True, text=True)
    if r.returncode != 0: print(r.stderr); sys.exit(1)
    return b
CENSUS = build("census", CENSUS_CPP); LOCAL = build("local", LOCAL_CPP)
def run(binp, args):
    return subprocess.run([binp] + [str(a) for a in args], capture_output=True, text=True, timeout=1150).stdout
def section(t): print("\n" + "=" * 110 + "\n" + t + "\n" + "=" * 110); sys.stdout.flush()

# ---------------------------------------------------------------------------------------------------------- 1. census
section("1. CENSUS OF CHAINS (C++ exact integers; all K-subsets of {p/Q : Q <= p <= M Q}; cascade from R = 1; unit m = 1)")
print("""Window picture [reasoned, from IsMove]: a landing R_{s+1} is the right end of the chosen window; the windows that contain R_{s+1}
all began at or after R_s (entered anew, Lean: LawOfPosition.entered_anew); every chosen window is longer than the jump it makes and
not longer than the two consecutive jumps ending with it: d_s < 2/x_s <= d_s + d_{s-1} (Lean: LawOfPosition.two_step_law).
Tests below are on EVERY landing / every move of the populations.""")
CEN = {}
for (K, Q, M, dump) in [(4, 12, 20, True), (5, 12, 10, True), (5, 8, 14, False)]:
    txt = run(CENSUS, [K, Q, M] + (["dump"] if dump else []))
    CEN[(K, Q, M)] = txt
    for line in txt.splitlines():
        if not (line.startswith("WORD")): print(line)
    print()

# ---------------------------------------------------------------------------------------------------------- 2. words
section("2. WORDS OVER K LETTERS (length <= 8) THAT SATISFY THE ADDITIVE BUDGET, AGAINST THE WORDS THAT OCCUR")
print("""A word w_1..w_m (ranks 0..K-1, no letter twice in a row) is BUDGET-FEASIBLE if there are readings x_0 < ... < x_{K-1} with
sum_{i<s<j} x_{w_i}/x_{w_s} > 3 for every pair i < j with w_i = w_j (nearest earlier occurrence; this contains the triple law 3y < x and the
pair law).  Witness search: deterministic grid of consecutive ratios in {2001/2000, 51/50, 11/10, 13/10, 8/5, 2, 3, 5, 9, 20} (numpy floats
with margin to find it), then the witness is re-verified EXACTLY with Fractions.  A word with no witness on the grid is not counted
as feasible (UNDECIDED, not 'infeasible').  OCCURS = factor (contiguous subword) of the setter word of some chain of the population.
MINIMAL = budget-feasible, does not occur, and both proper factors (drop first letter, drop last letter) occur or are empty.""")
import numpy as np
GAPS = [F(2001, 2000), F(51, 50), F(11, 10), F(13, 10), F(8, 5), F(2), F(3), F(5), F(9), F(20)]
def grid(K):
    pts = []
    for g in itertools.product(range(len(GAPS)), repeat=K - 1):
        x = [F(1)]
        for i in g: x.append(x[-1] * GAPS[i])
        pts.append(x)
    return pts
def exact_ok(w, x):
    last = {}
    for j, c in enumerate(w):
        if c in last:
            i = last[c]
            if not sum(x[c] / x[w[s]] for s in range(i + 1, j)) > 3: return False
        last[c] = j
    return True
def load_words(txt):
    occ = {}
    for l in txt.splitlines():
        if l.startswith('WORD '):
            parts = l.split(' ')
            occ[parts[1].strip() if len(parts) > 2 else ''] = int(parts[-1])
    return occ
MIN = {}
for K, key in [(4, (4, 12, 20)), (5, (5, 12, 10))]:
    occ = load_words(CEN[key])
    facs = set()
    for w in occ:
        for i in range(len(w)):
            for j in range(i + 1, len(w) + 1): facs.add(w[i:j])
    pts = grid(K); X = np.array([[float(v) for v in p] for p in pts])
    level = [((), np.ones(len(pts), bool))]; nfeas = {}; res = []
    for L in range(1, 9):
        new = []
        for w, mask in level:
            for c in range(K):
                if w and w[-1] == c: continue
                m = mask; prev = None
                for i in range(len(w) - 1, -1, -1):
                    if w[i] == c: prev = i; break
                if prev is not None:
                    S = sum(X[:, c] / X[:, w[s]] for s in range(prev + 1, len(w)))
                    m = m & (S > 3.0 + 1e-9)
                    if not m.any(): continue
                new.append((w + (c,), m))
        level = new; nfeas[L] = len(level); res.extend(level)
    occurring = [w for w, m in res if ''.join(map(str, w)) in facs]
    nonocc = [(w, m) for w, m in res if ''.join(map(str, w)) not in facs]
    minimal = []
    for w, m in nonocc:
        s = ''.join(map(str, w))
        if (s[1:] == '' or s[1:] in facs) and (s[:-1] == '' or s[:-1] in facs): minimal.append((s, m))
    print("K=%d  population Q=%d M=%d: distinct chain words (ranks) = %d" % (K, key[1], key[2], len(occ)))
    print("   budget-feasible words (exact witness found) by length 1..8:", nfeas)
    print("   of these, occurring as a factor of some chain: %d ; NOT occurring: %d ; MINIMAL non-occurring: %d" % (len(occurring), len(nonocc), len(minimal)))
    MIN[K] = []
    for s, m in minimal:
        i = int(np.argmax(m)); x = pts[i]; assert exact_ok(tuple(int(c) for c in s), x)
        MIN[K].append(s)
        print("     minimal non-occurring  %-6s  exact witness x_0..x_%d = %s" % (s, K - 1, ", ".join(str(v) for v in x)))
    print()
print("""Reading of section 2 [OBS]: the additive budget leaves many words that the populations never produce, down to length 2 at K = 5
('01': after the slowest sets, the next setter is never the second slowest) and length 3 at K = 4 ('101': x_1 sets, the slowest sets,
x_1 sets again, which the triple law only asks 3 x_0 < x_1 for).  So the budget is far from the whole law of position; a pattern such as
'after a landing the next setter is longer-windowed than the jump just made' (below) is part of it.""")

# ---------------------------------------------------------------------------------------------------------- 3. local
section("3. LOCAL TEST: the first return of the slowest reading a from ANY landing of it (lap L >= 1), reachable from R = 1 or not")
print("""The cascade is memoryless in R.  From a landing of a on lap L (R = (8L+1)/a, a = p_0/Q the smallest reading of the subset) run the
cascade until a is in the way again; count the distinct setters strictly between (the setter at the landing state included).  'reached'
= the real cascade from R = 1 does set a on that lap.  Law tested (the FourDistinctLaw context, local form): K = 4: a never returns;
K = 5: at least 4 distinct setters.  (set,L) pairs with R_a >= 1 are run for L = 1..12 (populations).""")
for (K, Q, M) in [(4, 12, 20), (5, 12, 10)]:
    print(run(LOCAL, [K, Q, M, 12]).rstrip()); print()
print("""FINE GRIDS, a = 1 exactly (readings rho = p/Q relative to a), L = 1..LMAX, any R (the landing need not be >= 1), nothing reached from R = 1:""")
for (K, Q, M, LM) in [(4, 400, 2, 40), (5, 60, 3, 80)]:
    print(run(LOCAL, [K, Q, M, LM, "fixa", "anyr"]).rstrip()); print()

# ---------------------------------------------------------------------------------------------------------- 4. exceptions
section("4. EXACT NAMED EXCEPTIONS TO THE LOCAL FORM; THE LAP FORM OF THE BUDGET; THE K = 5 EXTENSION (Python Fractions)")
def rnd(y): return math.floor(y + F(1, 2))
def inway(x, R):
    y = x * R / 8; return abs(y - rnd(y)) < F(1, 8)
def chain_from_landing(E, L):
    a = E[0]; R = (8 * L + 1) / a; out = []
    for it in range(400):
        if it > 0 and inway(a, R): out.append(("a returns", R)); return out
        blk = [(x, rnd(x * R / 8)) for x in E if inway(x, R)]
        if not blk: return out
        b = max(blk, key=lambda t: (8 * t[1] + 1) / t[0])
        out.append((E.index(b[0]), b[1], R, [E.index(x) for x, _ in blk])); R = F(8 * b[1] + 1) / b[0]
    raise Exception("move limit")
def show(E, L):
    print("  set (a = 1 first):", [str(x) for x in E], " landing of a on lap L =", L, " (R = (8L+1)/a, tau = a R)")
    laps = []
    for c in chain_from_landing(E, L):
        if c[0] == "a returns":
            print("     a in the way again at tau = %s = %.5f  (its lap-%d window is (%d, %d))" % (c[1] * E[0], float(c[1] * E[0]), L + 1, 8 * (L + 1) - 1, 8 * (L + 1) + 1)); continue
        r, l, R, bl = c
        print("     setter rank %d lap %-3d  in the way at tau = %-10.5f  in the way: %-6s right end tau = %.5f   window length 2/rho = %.5f" %
              (r, l, float(R * E[0]), bl, float((8 * l + 1) / E[r] * E[0]), float(2 * E[0] / E[r])))
        laps.append((r, l))
    return laps
E1 = [F(1), F(41, 40), F(26, 25), F(329, 200)]
E2 = [F(1), F(81, 80), F(51, 50), F(649, 400)]
print("EXCEPTION E1 (K = 4, word v u t v = 3 2 1 3, three distinct setters, a returns; local form of 'a never returns' FAILS):")
l1 = show(E1, 15)
print("EXCEPTION E2 (K = 4, word v t u v = 3 1 2 3):")
l2 = show(E2, 30)
def devs(E, L):
    out = []
    for z in E[1:]:
        q = z * (8 * L + 1); l = rnd(q / 8); out.append(float(q - 8 * l))
    return out
print("  signed residues dev(z) of the other readings at the landing of a: E1 (L=15):", ["%.4f" % d for d in devs(E1, 15)], " E2 (L=30):", ["%.4f" % d for d in devs(E2, 30)])
print("  Compare the ZONE lines of section 1 (landing of the slowest, rank 0): the clear-before-and-now class fills about [-4, 3.9] for every other reading, so these residues are not outside any zone interval that the reachable landings leave.")
print("""
Lap form of the v-return budget [reasoned, from the chain of window ends t_L < v1_R <= u_L < t_R <= v2_L < u_R of the word v t u v with
the three reading windows of laps a (v first), b (t), c (u), j = 1 lap of v between its two settings; not formalised]:
    (8a+7)(8b-1)(8c-1) < (8a+1)(8b+1)(8c+1)   <=>   64ab + 64ac - 192bc + 32b + 32c - 3 > 0 .
For large laps this is 1/b + 1/c > 3/a, i.e. v/t + v/u > 3: the budget law with its lattice correction.  Check on E1, E2 (laps from the chains above):""")
for nm, laps in [("E1", l1), ("E2", l2)]:
    a, b, c = laps[0][1], laps[1][1], laps[2][1]
    val = 64 * a * b + 64 * a * c - 192 * b * c + 32 * b + 32 * c - 3
    print("   %s: laps (a,b,c) = (%d,%d,%d): 64ab+64ac = %d, 192bc = %d, expression = %d > 0 : %s ; sympy-free expansion identity checked by cross-multiplication below" % (nm, a, b, c, 64*a*b+64*a*c, 192*b*c, val, val > 0))
# exact expansion identity
import random
ok = all((8*a+1)*(8*b+1)*(8*c+1) - (8*a+7)*(8*b-1)*(8*c-1) == 2*(64*a*b+64*a*c-192*b*c+32*b+32*c-3) for a in range(0, 12) for b in range(0, 12) for c in range(0, 12))
print("   expansion identity (8a+1)(8b+1)(8c+1) - (8a+7)(8b-1)(8c-1) = 2(64ab+64ac-192bc+32b+32c-3) verified for 0 <= a,b,c < 12:", ok)
print("""
Why the populations never show these words [OBS, reasoned]: in E1 the landing of a is at lap 15, in E2 at lap 30.  The real cascade from R = 1 sets
the slowest reading only on laps 1 and 2 in the K = 4 and K = 5 populations (section 1, 'settings by rank:lap').  The local form of the
law (no history) is FALSE; the cascade's history (the stretch [1, R_a) is covered by windows) is what keeps L small.  In the window
language: a closed gap of a, [(8L+1)/a, (8L+7)/a], of length 6/a, is covered by windows of three faster readings when L is large enough
for their laps to fit the near-equality (8a+7)(8b-1)(8c-1) ~ (8a+1)(8b+1)(8c+1).""")
print("\nK = 5 extension of E1: add a fifth reading z = q/400 (q = 401..1699) to {1, 41/40, 26/25, 329/200}, landing of a on lap 15, first return of a:")
cnt = Counter(); ex5 = []
for q in range(401, 1700):
    z = F(q, 400)
    if z in E1: continue
    E = sorted(E1 + [z]); ch = chain_from_landing(E, 15)
    if ch and ch[-1][0] == "a returns":
        w = [c[0] for c in ch[:-1]]; k = len(set(w)); cnt[k] += 1
        if k < 4 and len(ex5) < 3: ex5.append((E, w))
print("   distinct setters before a is in the way again -> number of z:", dict(sorted(cnt.items())), "(1296 values of z tried, z not in the set)")
for E, w in ex5:
    print("   e.g.", [str(x) for x in E], "word", "".join(map(str, w)), "(3 distinct setters, 4 moves)")
print("   => the local form of 'at least four distinct setters' FAILS at K = 5 for", sum(v for k, v in cnt.items() if k < 4), "of", sum(cnt.values()), "fifth readings (those with a return) at lap 15.")

print("\nWORKED CHAIN, readings {49,62,70,79,85}/12 from R = 1 (the AU example, a = 49/12 returns): window ends, jumps, lap budget")
def trace(E):
    R = F(1); mv = []
    for _ in range(500):
        blk = [(x, rnd(x * R / 8)) for x in E if inway(x, R)]
        if not blk: return mv, R
        b = max(blk, key=lambda t: (8 * t[1] + 1) / t[0])
        mv.append((R, b[0], b[1], [E.index(x) for x, _ in blk])); R = F(8 * b[1] + 1) / b[0]
    raise Exception("move limit")
E = [F(x, 12) for x in (49, 62, 70, 79, 85)]
mv, Rf = trace(E); a = E[0]
for i, (R, x, l, bl) in enumerate(mv):
    r = (8 * l + 1) / x
    print("   move %2d  tau=%8.4f  setter rank %d lap %d  in the way %-7s  jump d = %.4f  window 2/rho = %.4f" %
          (i, float(a * R), E.index(x), l, bl, float(a * (r - R)), float(2 * a / x)))
sets = [i for i, m in enumerate(mv) if m[1] == a]
n0, k0 = sets[0], sets[1]
j = mv[k0][2] - mv[n0][2]
S = sum(a / mv[s][1] for s in range(n0 + 1, k0))
print("   a is set at moves %d and %d, laps %d and %d, j = %d ; sum_{inter} a/w = %s = %.5f ; lap budget 4j-1 = %d < sum : %s ; additive budget 3 < sum : %s" %
      (n0, k0, mv[n0][2], mv[k0][2], j, S, float(S), 4*j-1, 4*j-1 < S, 3 < S))
rt = [F(8*m[2]+1)/m[1] for m in mv]          # right end (landing R_{s+1}) of move s
print("   two-step check on this chain, all moves s >= 1 (R units): R_{s+1}-R_{s-1} >= 2/x_s and R_{s+1}-R_s < 2/x_s:",
      all((rt[s] - mv[s-1][0]) >= 2/mv[s][1] and (rt[s] - mv[s][0]) < 2/mv[s][1] for s in range(1, len(mv))), " ; entered anew: every reading in the way at R_{s+1} had z R_s <= 8l-1:",
      all(all(z*mv[s][0] <= 8*rnd(z*rt[s]/8) - 1 for z in E if inway(z, rt[s])) for s in range(len(mv))))

# ---------------------------------------------------------------------------------------------------------- 5. audit
section("5. HYPOTHESIS AUDIT (REQUIRED / NOT REQUIRED / UNDECIDED), exact")
print("entered_anew (Lean), hypothesis 'y is a member of ds' -- REQUIRED.  Exact counterexample with y not in ds:")
def nxt(x, t): n = rnd(x * t); return (n + F(1, 8)) / x
found = None
for xn in range(1, 25):
    x = F(xn, 4)
    for tn in range(1, 200):
        t = F(tn, 32)
        if not inway(x, t): continue
        t2 = nxt(x, t)
        for yn in range(1, 40):
            y = F(yn, 4)
            if y == x: continue
            l = rnd(y * t2)
            if inway(y, t2) and y * t > l - F(1, 8):
                found = (x, t, t2, y, l); break
        if found: break
    if found: break
x, t, t2, y, l = found
print("   ds = {%s}, t = %s (%s in the way, lap %d), t' = nextOpening = %s ; y = %s is NOT in ds, in the way at t' on lap %d, and y t = %s > l - 1/8 = %s : the conclusion fails." %
      (x, t, x, rnd(x*t), t2, y, l, y*t, l - F(1, 8)))
print("""
STATEMENT                                  HYPOTHESIS                                      VERDICT
entered_anew [L]                           positive disparities                            REQUIRED (comparison of y t with y t', division by y)
                                           y in ds                                         REQUIRED (exact counterexample above)
                                           0 < t, ordering of readings, base m, laps >= 1  NOT REQUIRED (not used by the Lean proof)
two_step_lower / two_step_law [L]          x is the setter at s+1                          REQUIRED (the landing is x's opening)
                                           the move s -> s+1 is a cascade move             REQUIRED (entered_anew)
lap_identity [L]                           x set at n and at k                             REQUIRED as stated (both landings are openings of x)
                                           n < k, cascade moves                            NOT REQUIRED
lap_budget [L]                             x set at n and at k, setters between            REQUIRED
                                           the cascade moves hmv                           NOT REQUIRED (compiler flagged it unused; removed)
                                           ordering of readings, base m, 0 < seq 0         NOT REQUIRED
budget_of_reset [L]                        x set again at k                                REQUIRED for this proof; whether '3 <' holds when x is only IN THE WAY
                                                                                           at k with a one-lap difference is Ladder5.budget_sum (it needs only 'in the way')
'a never returns' at K = 4 (local form)    reachability of the landing from R = 1          REQUIRED (exceptions E1, E2 at laps 15 and 30; none reached)
'>= 4 distinct setters' at K = 5 (local)   reachability of the landing from R = 1          REQUIRED (1269 of 1296 fifth readings at lap 15, section 4)
FourDistinctLaw (Ladder5, OWED)            seq 0 = 1/(8m), readings >= m                   UNDECIDED which part is used; the local form without it is false
single-landing zone law                    (interval of dev(z) depending on (w, L, z))     NOT SUFFICIENT: the zones of E1 at its landing are inside the same
                                                                                           intervals as the reachable landings (section 1 'zones'); see below
budget-feasible but non-occurring words    history from R = 1                              the budget alone does NOT exclude them (section 2)
""")
print("""THE POSITION LAW AS IT STANDS (graded)
 P1 [L]   Every window that contains a landing began at or after the previous instant: y t <= lap(y,t') - 1/8 (LawOfPosition.entered_anew).
          Data [OBS]: 0 violations in every landing of every chain of the populations (section 1).  Consequence [L]: a reading in the way
          at two consecutive instants is on a strictly higher lap at the second (lap_lt_of_inWay_both); [OBS] such readings change lap by exactly 1 (K=4 population Q=12 M=20: 12411 cases, all +1; none at K=5).
 P2 [L]   Two-step law: 1/(4x) lies in (d_s, d_s + d_{s-1}] for the setter x at s: LawOfPosition.two_step_law.  [OBS] 0 violations (section 1).
 P3 [L]   Lattice: x (seq(k+1) - seq(n+1)) = lap_k - lap_n for a reading set at n and k; lap budget 4j - 1 < sum x/w (lap_budget).  [OBS]: j = 1 and j = 2
          occur and satisfy it (section 1, 0 violations).
 P4 [reasoned]  The cascade is the greedy right-end walk over the union of windows; a return of a reading to the way is the covering of its closed gap
          [(8l+1)/x, (8l+7)/x] by windows of the others (budget = total window length > 6/x; lattice = the windows sit at (8l -+ 1)/z).
 P5 [OBS, exact]  The law of position for the first return of the slowest is NOT local: the word v t u v (and v u t v) with three distinct setters is produced
          by the cascade from a landing of a on lap 15 (K = 4) and lap 30, and with a fifth reading at K = 5 (section 4); it is never produced by a landing that
          the real cascade from R = 1 reaches (a is set on laps 1 and 2 only).  So any statement that excludes it must carry the history of the landing: the
          stretch [1, R_a) is covered by windows (a covering statement; rule 7: [PROVISIONAL: covering] if used in a proof).
 P6 [OBS]  Single-landing zones: at a landing, a reading in the way before and clear now has dev >= 1 against its old lap; a reading clear before and in the way now
          has dev in (-1, 1) (entering from below) -- the entered-anew zone and nothing else is excluded; the signed residue of readings clear before and now fills
          (-4,-1] and [1, 4) (section 1).  So the zone law 'dev in an interval depending only on (w, L, z)' reduces to entered-anew plus the definitions.
 P7 [OBS]  The one narrow single-landing zone found: in the K = 5 populations the landings of the slowest on lap 2 are exactly the returning sets (n = 303 for
          Q=12 M=10; n = 286 for Q=8 M=14), and at them the second-slowest reading (z1) and the fastest (z4) both sit at a NEGATIVE signed residue about
          [-3.6, -1.5] (z1 in [-3.38,-2.18] and [-3.38,-1.52]; z4 in [-3.59,-1.85] and [-3.58,-1.46]; section 1 ZONE lines, L2).  This describes the returning
          landing; it is a consequence of the chain that returns, not a precondition for one, and it differs between the two populations at z3.
 OWED     A proof that FourDistinctLaw follows from P1-P5: not found.  The exclusion of the minimal non-occurring words of section 2 is not proved for any of them.""")
print("\nDONE")
