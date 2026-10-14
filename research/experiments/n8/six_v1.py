#!/usr/bin/env python3
"""six_v1.py -- Task CC (2026-10-10): six disparities (the d_min unit plus five readings): exact census of the five-reading cascade.

Everything is exact: C++ __int128 integers for the populations, Python Fractions for every re-verification.  No floats decide
anything.  Nothing is random and nothing is sampled: every 5-subset of {p/Q : p_min <= p <= M*Q} of each stated grid is run (the
counts are observations of those grids only, not of a population of arrangements).  Every cascade loop has a move limit (400 moves in
C++, 400 in Python; hit 0 times).  Unit m = 1 (the d_min of the subject), R = 8 m t, the cascade starts at R = 1, rank 0 = the slowest
reading a, rank 4 = the fastest.  Output: experiments/n8/six_v1.out.

Sections
  1  grids: chain lengths, visits and settings of the slowest, final R, setter weight W, position law, window-of-eight law, two-sided return
     budget, lap exceptions, maxima by band of the slowest reading
  2  the chains of the grid Q = 12, M = 10 (all of them): words with laps
  3  the sets in which the slowest reading is visited three times (grid Q = 2)
  4  the 94 words of law_of_position_v1.out section 2 (minimal non-occurring at K = 5, Q = 12): which occur in the other grids
  5  candidate invariants for the landing point, tested on every set of the grids
  6  why the number of settings of the slowest is not bounded: the arithmetic-progression family; 6b scan of the family with the lap condition
  7  runs of consecutive moves with at most three setter values (the window length 8): budget words, and a float-steered realisation search
Verdict-word convention: every use of "proved", "exact", "only", "first", "whole", "complete", "done", "decided", "mechanism", "sharpest" in this file
is attached to a grade ([L] Lean theorem named, [OBS] observation on the stated grid, [reasoned] argument not formalised, [PARTIAL]).  "Exact" in
"exact Fractions / exact integers" names the arithmetic of the computation and is not a verdict.  The grids are explicit and exhaustive (nothing is sampled).
Lean: Fresh/SixDisparities.lean (eight_four_distinct, elapsed_two_sided, return_upper_budget, settings_le_nine, six_dichotomy).
Grades: [L] Lean theorem, [OBS] exact data on the stated grid, [reasoned] argument not formalised.
"""
import subprocess, tempfile, os, sys, re
from fractions import Fraction as F
from collections import Counter, OrderedDict

CPP = r'''// six_v1 enumeration: all 5-subsets {p0<..<p4} of integers in [pmin, M*Q] (readings p/Q, unit m = 1, R = 8t, start R = 1).
// Exact integer cascade (__int128). Move limit 400 per set. Rank 0 = slowest.
#include <vector>
#include <thread>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <map>
#include <string>
#include <mutex>
#include <unordered_map>
#include <fstream>
#include <algorithm>
using namespace std;
typedef long long ll; typedef __int128 LL;
int K=5; ll Q, M, PMIN;
struct Fr { ll n=0,d=1; };
static bool lessF(const Fr&a,const Fr&b){ return (LL)a.n*b.d < (LL)b.n*a.d; }
struct Info { ll cnt=0; Fr maxR; ll ex[5]={0}; };
struct Occ { ll cnt=0; ll ex[5]={0}; bool have=false; };
static unordered_map<string,int> TW; static vector<string> TWL;
struct Stat {
  vector<Occ> occ;
  ll sets=0, limitHit=0, maxlen=0;
  map<string,Info> words;           // key: word with laps, e.g. "0:1 4:1 ..." plus visits
  map<int,ll> visitHist, settHist, lenHist;
  Fr maxR; bool haveR=false; ll maxRset[5]={0};
  // invariants
  ll wLowTests=0, wLowViol=0, wUpTests=0, wUpViol=0;   // W' <= R_N - 1 ; R_N - 1 < 2 W
  Fr maxW; bool haveW=false; ll maxWset[5]={0};
  ll posTests=0, posViol=0; ll posViolSet[5]={0};      // N <= 3 rho_a  (a = p0/Q)
  Fr minPosSlack; bool havePos=false;                  // min of (3 rho_a - N)
  Fr maxRperA; bool haveRA=false;
  map<string,ll> lastSetter;                          // "rank:lap" of the last setter
  ll bandSets[8]={0}; ll bandMaxLen[8]={0}; Fr bandMaxR[8]; bool bandHaveR[8]={false}; Fr bandMaxW[8]; bool bandHaveW[8]={false}; ll bandMaxVisits[8]={0};
  ll multiSet=0; ll run3max=0; ll run3set[5]={0}; ll win8Tests=0, win8Viol=0; ll win8MinDistinct=99; ll maxViolAn=0; ll retUpTests=0, retUpViol=0; Fr retUpMax; bool haveRetUp=false; ll retLowViol=0; ll a15sets=0,a15bad=0,a15maxlen=0; ll badAll=0; ll maxlap=0; ll a15lenHist[64]={0};
  // visits of a with the a-free stretches
};
static inline ll rnd_div(LL num, LL den){ LL v=2*num+den; LL d=2*den; LL q=v/d; if((v%d!=0)&&((v<0)!=(d<0))) q--; return (ll)q; }
static inline LL gcdL(LL a, LL b){ if(a<0)a=-a; if(b<0)b=-b; while(b){ LL t=a%b; a=b; b=t;} return a; }
void run(const ll* p,int k,Stat& st){
  ll Rn[512], Rd[512]; int setter[512]; int lapv[512]; unsigned mask[512];
  Rn[0]=1; Rd[0]=1; int len=0; bool hit=false;
  while(true){
    ll A=Rn[len],B=Rd[len];
    bool any=false; ll bA=0,bB=1; int bi=-1; ll bn=0; unsigned mk=0;
    for(int i=0;i<k;i++){
      LL num=(LL)p[i]*A; LL den=(LL)8*Q*B; ll n=rnd_div(num,den);
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
  st.lenHist[len]++;
  if(len>=2){ char cw[520]; for(int s=0;s<len;s++) cw[s]='0'+setter[s]; cw[len]=0;
    if(st.occ.empty()) st.occ.resize(TWL.size());
    for(int s=0;s<len;s++){ string f; for(int l=0;l<8&&s+l<len;l++){ f.push_back(cw[s+l]); if(l>=1){ auto it=TW.find(f); if(it!=TW.end()){ Occ&o=st.occ[it->second]; o.cnt++; bool better=!o.have; if(!better){ if(p[4]<o.ex[4]) better=true; else if(p[4]==o.ex[4]){ for(int i=0;i<5;i++){ if(p[i]<o.ex[i]){better=true;break;} if(p[i]>o.ex[i]) break; } } } if(better){ o.have=true; for(int i=0;i<5;i++) o.ex[i]=p[i]; } } } } } }
  int visits=0, setts=0;
  for(int s=0;s<=len;s++) if(mask[s]&1u) visits++;
  for(int s=0;s<len;s++) if(setter[s]==0) setts++;
  st.visitHist[visits]++; st.settHist[setts]++;
  Fr Rf; Rf.n=Rn[len]; Rf.d=Rd[len];
  if(!st.haveR||lessF(st.maxR,Rf)){ st.maxR=Rf; st.haveR=true; for(int i=0;i<k;i++) st.maxRset[i]=p[i]; }
  if(len>0){
    char buf[48]; string kw;
    for(int s=0;s<len;s++){ snprintf(buf,sizeof buf,"%d:%d ",setter[s],lapv[s]); kw+=buf; }
    snprintf(buf,sizeof buf,"| V%d",visits); kw+=buf;
    Info& in=st.words[kw]; if(in.cnt==0||lessF(in.maxR,Rf)){ in.maxR=Rf; for(int i=0;i<k;i++) in.ex[i]=p[i]; } in.cnt++;
    snprintf(buf,sizeof buf,"%d:%d",setter[len-1],lapv[len-1]); st.lastSetter[buf]++;
    // W = sum_s Q/p_{w_s}  (m = 1);  W' = sum_{s=1}^{N-1}.  Common denominator D = prod p.
    LL D=1; for(int i=0;i<k;i++) D*=p[i];
    LL Wn=0, Wp=0; for(int s=0;s<len;s++){ LL t=(LL)Q*(D/p[setter[s]]); Wn+=t; if(s>=1) Wp+=t; }
    // R_N - 1 = (Rn-Rd)/Rd.  Test  Wp/D <= (Rn-Rd)/Rd  <=>  Wp*Rd <= (Rn-Rd)*D
    LL RN1num=(LL)Rn[len]-(LL)Rd[len];
    st.wLowTests++; if(!((LL)Wp*Rd[len] <= RN1num*D)) st.wLowViol++;
    // (R_N - 1) < 2 W  <=>  RN1num * D < 2 Wn * Rd
    st.wUpTests++; if(!(RN1num*D < (LL)2*Wn*Rd[len])) st.wUpViol++;
    Fr wf; { LL g=gcdL(Wn,D); wf.n=(ll)(Wn/g); wf.d=(ll)(D/g); }
    if(!st.haveW||lessF(st.maxW,wf)){ st.maxW=wf; st.haveW=true; for(int i=0;i<k;i++) st.maxWset[i]=p[i]; }
  }
  // position law N * m <= 3 a  <=>  N <= 3 p0/Q  <=> N*Q <= 3*p0
  st.posTests++; if(!((LL)len*Q <= (LL)3*p[0])){ st.posViol++; for(int i=0;i<k;i++) st.posViolSet[i]=p[i]; }
  { Fr f; f.n=(ll)(3*p[0]-(LL)len*Q); f.d=(ll)Q; if(!st.havePos||lessF(f,st.minPosSlack)){ st.minPosSlack=f; st.havePos=true; } }
  if(setts>=2) st.multiSet++;
  { static const int TH[7]={2,3,5,10,20,40,1000000}; int b=0; while(b<6 && (LL)p[0] >= (LL)TH[b]*Q) b++;
    st.bandSets[b]++; if(len>st.bandMaxLen[b]) st.bandMaxLen[b]=len; if(visits>st.bandMaxVisits[b]) st.bandMaxVisits[b]=visits;
    if(!st.bandHaveR[b]||lessF(st.bandMaxR[b],Rf)){ st.bandMaxR[b]=Rf; st.bandHaveR[b]=true; }
    if(len>0){ LL D=1; for(int i=0;i<k;i++) D*=p[i]; LL Wn=0; for(int s=0;s<len;s++) Wn+=(LL)Q*(D/p[setter[s]]); LL g=gcdL(Wn,D); Fr wf; wf.n=(ll)(Wn/g); wf.d=(ll)(D/g); if(!st.bandHaveW[b]||lessF(st.bandMaxW[b],wf)){ st.bandMaxW[b]=wf; st.bandHaveW[b]=true; } } }
  { for(int s0=0;s0<len;s0++){ unsigned seen=0; int e=s0; while(e<len){ unsigned t=seen|(1u<<setter[e]); if(__builtin_popcount(t)>3) break; seen=t; e++; } int rl=e-s0; if(rl>st.run3max){ st.run3max=rl; for(int i=0;i<k;i++) st.run3set[i]=p[i]; } } }
  if(len>=8){ for(int s0=0;s0+8<=len;s0++){ unsigned seen=0; for(int i=0;i<8;i++) seen|=1u<<setter[s0+i]; int c=__builtin_popcount(seen); st.win8Tests++; if(c<4) st.win8Viol++; if(c<st.win8MinDistinct) st.win8MinDistinct=c; } }
  if(!((LL)len*Q <= (LL)3*p[0])){ if(p[0]>st.maxViolAn) st.maxViolAn=p[0]; }
  { LL D=1; for(int i=0;i<k;i++) D*=p[i];
    for(int n=0;n<len;n++){ int x=setter[n];
      for(int kk=n+1;kk<=len;kk++){ if(!(mask[kk]>>x&1)) continue;
        // first visit of x after its setting at n: U = sum_{n<s<kk} x/w_s ; dj = lap_x(kk) - lap_x(n); test 4dj-1 < U < 8dj+1 (lap at kk of x = round(p_x R_kk/(8Q)))
        LL Un=0; for(int s=n+1;s<kk;s++) Un+=(LL)p[x]*(D/p[setter[s]]);
        LL num=(LL)p[x]*Rn[kk]; LL den=(LL)8*Q*Rd[kk]; ll lk=rnd_div(num,den); ll dj=lk-lapv[n];
        st.retUpTests++; if(!((LL)Un < (LL)(8*dj+1)*D)) st.retUpViol++; if(!((LL)Un > (LL)(4*dj-1)*D)) st.retLowViol++;
        Fr f; f.n=(ll)Un; f.d=(ll)D; if(dj==1 && (!st.haveRetUp||lessF(st.retUpMax,f))){ st.retUpMax=f; st.haveRetUp=true; }
        break; } } }
  { bool bad=false; for(int s=0;s<len;s++){ if(lapv[s]==9||lapv[s]>=11) bad=true; if(lapv[s]>st.maxlap) st.maxlap=lapv[s]; }
    if(bad) st.badAll++;
    if((LL)p[0] >= (LL)15*Q){ st.a15sets++; if(bad) st.a15bad++; if(len>st.a15maxlen) st.a15maxlen=len; if(len<64) st.a15lenHist[len]++; } }
}
int main(int argc,char**argv){
  { ifstream fi(argv[5]); string w; while(fi>>w){ TW[w]=TWL.size(); TWL.push_back(w);} }
  Q=atoll(argv[1]); M=atoll(argv[2]); PMIN=atoll(argv[3]); int nth=atoi(argv[4]);
  ll lo=PMIN, hi=M*Q; if(lo<Q) lo=Q;
  vector<Stat> sts(nth); vector<thread> th;
  // distribute p0 values round-robin
  for(int t=0;t<nth;t++) th.emplace_back([&,t](){
    Stat& st=sts[t]; ll p[5];
    for(ll a=lo+t;a<=hi;a+=nth){ p[0]=a;
      for(ll b=a+1;b<=hi;b++){ p[1]=b;
        for(ll c=b+1;c<=hi;c++){ p[2]=c;
          for(ll d=c+1;d<=hi;d++){ p[3]=d;
            for(ll e=d+1;e<=hi;e++){ p[4]=e; run(p,5,st); } } } } }
  });
  for(auto&x:th) x.join();
  // merge
  Stat T;
  for(auto&s:sts){ T.sets+=s.sets; T.limitHit+=s.limitHit; if(s.maxlen>T.maxlen)T.maxlen=s.maxlen;
    for(auto&kv:s.visitHist)T.visitHist[kv.first]+=kv.second; for(auto&kv:s.settHist)T.settHist[kv.first]+=kv.second; for(auto&kv:s.lenHist)T.lenHist[kv.first]+=kv.second;
    if(s.haveR&&(!T.haveR||lessF(T.maxR,s.maxR))){T.maxR=s.maxR;T.haveR=true;for(int i=0;i<5;i++)T.maxRset[i]=s.maxRset[i];}
    T.wLowTests+=s.wLowTests;T.wLowViol+=s.wLowViol;T.wUpTests+=s.wUpTests;T.wUpViol+=s.wUpViol;
    if(s.haveW&&(!T.haveW||lessF(T.maxW,s.maxW))){T.maxW=s.maxW;T.haveW=true;for(int i=0;i<5;i++)T.maxWset[i]=s.maxWset[i];}
    T.posTests+=s.posTests;T.posViol+=s.posViol; if(s.posViol){for(int i=0;i<5;i++)T.posViolSet[i]=s.posViolSet[i];}
    if(s.havePos&&(!T.havePos||lessF(s.minPosSlack,T.minPosSlack))){T.minPosSlack=s.minPosSlack;T.havePos=true;}
    for(auto&kv:s.lastSetter)T.lastSetter[kv.first]+=kv.second; T.multiSet+=s.multiSet; for(int b=0;b<7;b++){ T.bandSets[b]+=s.bandSets[b]; if(s.bandMaxLen[b]>T.bandMaxLen[b])T.bandMaxLen[b]=s.bandMaxLen[b]; if(s.bandMaxVisits[b]>T.bandMaxVisits[b])T.bandMaxVisits[b]=s.bandMaxVisits[b]; if(s.bandHaveR[b]&&(!T.bandHaveR[b]||lessF(T.bandMaxR[b],s.bandMaxR[b]))){T.bandMaxR[b]=s.bandMaxR[b];T.bandHaveR[b]=true;} if(s.bandHaveW[b]&&(!T.bandHaveW[b]||lessF(T.bandMaxW[b],s.bandMaxW[b]))){T.bandMaxW[b]=s.bandMaxW[b];T.bandHaveW[b]=true;} } if(s.run3max>T.run3max){T.run3max=s.run3max; for(int i=0;i<5;i++)T.run3set[i]=s.run3set[i];} T.win8Tests+=s.win8Tests; T.win8Viol+=s.win8Viol; if(s.win8MinDistinct<T.win8MinDistinct)T.win8MinDistinct=s.win8MinDistinct; if(s.maxViolAn>T.maxViolAn)T.maxViolAn=s.maxViolAn; T.retUpTests+=s.retUpTests; T.retUpViol+=s.retUpViol; T.retLowViol+=s.retLowViol; if(s.haveRetUp&&(!T.haveRetUp||lessF(T.retUpMax,s.retUpMax))){T.retUpMax=s.retUpMax;T.haveRetUp=true;} T.a15sets+=s.a15sets; T.a15bad+=s.a15bad; T.badAll+=s.badAll; if(s.a15maxlen>T.a15maxlen)T.a15maxlen=s.a15maxlen; if(s.maxlap>T.maxlap)T.maxlap=s.maxlap; for(int i=0;i<64;i++)T.a15lenHist[i]+=s.a15lenHist[i];
    for(auto&kv:s.words){ Info& in=T.words[kv.first]; if(in.cnt==0||lessF(in.maxR,kv.second.maxR)){in.maxR=kv.second.maxR;for(int i=0;i<5;i++)in.ex[i]=kv.second.ex[i];} in.cnt+=kv.second.cnt; }
  }
  { vector<Occ> tot(TWL.size()); for(auto&s:sts){ if(s.occ.empty()) continue; for(size_t i=0;i<TWL.size();i++){ Occ&o=s.occ[i]; if(!o.have) continue; tot[i].cnt+=o.cnt; bool better=!tot[i].have; if(!better){ if(o.ex[4]<tot[i].ex[4]) better=true; else if(o.ex[4]==tot[i].ex[4]){ for(int j=0;j<5;j++){ if(o.ex[j]<tot[i].ex[j]){better=true;break;} if(o.ex[j]>tot[i].ex[j]) break; } } } if(better){ tot[i].have=true; for(int j=0;j<5;j++) tot[i].ex[j]=o.ex[j]; } } }
    for(size_t i=0;i<TWL.size();i++) if(tot[i].cnt) printf("OCC %s n=%lld ex %lld %lld %lld %lld %lld\n",TWL[i].c_str(),tot[i].cnt,tot[i].ex[0],tot[i].ex[1],tot[i].ex[2],tot[i].ex[3],tot[i].ex[4]); }
  printf("POP Q=%lld M=%lld pmin=%lld sets=%lld limitHit=%lld maxlen=%lld\n",Q,M,lo,T.sets,T.limitHit,T.maxlen);
  printf("LEN"); for(auto&kv:T.lenHist)printf(" %d:%lld",kv.first,kv.second); printf("\n");
  printf("VISITS"); for(auto&kv:T.visitHist)printf(" %d:%lld",kv.first,kv.second); printf("\n");
  printf("SETTINGS"); for(auto&kv:T.settHist)printf(" %d:%lld",kv.first,kv.second); printf("\n");
  printf("MAXR %lld/%lld set %lld %lld %lld %lld %lld\n",T.maxR.n,T.maxR.d,T.maxRset[0],T.maxRset[1],T.maxRset[2],T.maxRset[3],T.maxRset[4]);
  printf("WLOW tests=%lld viol=%lld\nWUP tests=%lld viol=%lld\n",T.wLowTests,T.wLowViol,T.wUpTests,T.wUpViol);
  printf("MAXW %lld/%lld set %lld %lld %lld %lld %lld\n",T.maxW.n,T.maxW.d,T.maxWset[0],T.maxWset[1],T.maxWset[2],T.maxWset[3],T.maxWset[4]);
  printf("POS tests=%lld viol=%lld minslack=%lld/%lld",T.posTests,T.posViol,T.minPosSlack.n,T.minPosSlack.d);
  if(T.posViol) printf(" lastviolset %lld %lld %lld %lld %lld",T.posViolSet[0],T.posViolSet[1],T.posViolSet[2],T.posViolSet[3],T.posViolSet[4]);
  printf("\n");
  printf("LAST"); for(auto&kv:T.lastSetter)printf(" %s=%lld",kv.first.c_str(),kv.second); printf("\n");
  printf("MULTISET %lld\n",T.multiSet);
  { const char* names[7]={"a<2","2<=a<3","3<=a<5","5<=a<10","10<=a<20","20<=a<40","a>=40"}; for(int b=0;b<7;b++) if(T.bandSets[b]) printf("BAND %s sets=%lld maxlen=%lld maxvisits_of_a=%lld maxR=%lld/%lld maxW=%lld/%lld\n",names[b],T.bandSets[b],T.bandMaxLen[b],T.bandMaxVisits[b],T.bandMaxR[b].n,T.bandMaxR[b].d,T.bandMaxW[b].n,T.bandMaxW[b].d); }
  printf("RUN3 longest run of consecutive moves with at most 3 distinct setters = %lld (set %lld %lld %lld %lld %lld)\n",T.run3max,T.run3set[0],T.run3set[1],T.run3set[2],T.run3set[3],T.run3set[4]);
  printf("WIN8 tests=%lld viol(<4 distinct)=%lld min_distinct=%lld\n",T.win8Tests,T.win8Viol,T.win8MinDistinct);
  printf("MAXVIOLA_P0 %lld  (largest p0 among sets with N*Q > 3*p0; reading a = p0/Q)\n",T.maxViolAn);
  printf("RETBUDGET tests=%lld viol_upper(U<8dj+1)=%lld viol_lower(U>4dj-1)=%lld maxU=%lld/%lld\n",T.retUpTests,T.retUpViol,T.retLowViol,T.retUpMax.n,T.retUpMax.d);
  printf("LAPALL a15sets=%lld a15sets_with_lap9_or_ge11=%lld a15maxlen=%lld allsets_with_lap9_or_ge11=%lld maxlap=%lld\n",T.a15sets,T.a15bad,T.a15maxlen,T.badAll,T.maxlap);
  printf("NWORDS %zu\n",T.words.size());
  bool ALLW=(argc>6); for(auto&kv:T.words){ if(!ALLW && (kv.first.find("V0")!=string::npos||kv.first.find("V1")!=string::npos)) continue; printf("W %s | n=%lld maxR=%lld/%lld ex %lld %lld %lld %lld %lld\n",kv.first.c_str(),kv.second.cnt,kv.second.maxR.n,kv.second.maxR.d,kv.second.ex[0],kv.second.ex[1],kv.second.ex[2],kv.second.ex[3],kv.second.ex[4]); }
  return 0;
}
'''
WORDS94 = """01
12
021
031
041
132
142
202
230
234
303
313
323
341
414
423
424
434
0241
0421
1023
1024
1304
1342
1404
1432
2032
2034
2042
2102
2134
2310
2314
2402
2404
2430
3042
3102
3103
3143
3203
3213
3243
3402
3420
4042
4203
4204
4314
4324
03214
10321
10431
20431
20432
24032
24310
30432
34032
34034
34210
40431
40432
41032
41042
41043
42130
42140
032410
043210
130231
240342
314023
403241
410342
413023
413024
421034
421430
431042
0324130
0324134
0432140
1302431
2140321
3140243
3214023
4210324
4310432
4321034
32104321
32143023
43210432
43214034""".split()

THREADS = 10
# (label, Q, M, pmin, all-words)
POPS = [
    ("Q=12 M=10 (all readings p/12 in [1,10])", 12, 10, 12, True),
    ("Q=8 M=14", 8, 14, 8, False),
    ("Q=4 M=30", 4, 30, 4, False),
    ("Q=3 M=40", 3, 40, 3, False),
    ("Q=2 M=60", 2, 60, 2, False),
    ("Q=1 M=100 (integer readings)", 1, 100, 1, False),
    ("Q=12 M=10, slowest >= 5 (p >= 60)", 12, 10, 60, False),
    ("Q=8 M=14, slowest >= 5 (p >= 40)", 8, 14, 40, False),
    ("Q=4 M=30, slowest >= 5 (p >= 20)", 4, 30, 20, False),
    ("Q=3 M=40, slowest >= 5 (p >= 15)", 3, 40, 15, False),
    ("Q=2 M=60, slowest >= 5 (p >= 10)", 2, 60, 10, False),
    ("Q=1 M=100, slowest >= 5 (p >= 5)", 1, 100, 5, False),
    ("Q=2 M=60, slowest >= 15 (p >= 30)", 2, 60, 30, False),
    ("Q=1 M=10 (readings <= 10)", 1, 10, 1, False),
    ("Q=2 M=10 (readings <= 10)", 2, 10, 2, False),
    ("Q=3 M=10 (readings <= 10)", 3, 10, 3, False),
    ("Q=4 M=10 (readings <= 10)", 4, 10, 4, False),
    ("Q=6 M=10 (readings <= 10)", 6, 10, 6, False),
    ("Q=8 M=10 (readings <= 10)", 8, 10, 8, False),
]
if os.environ.get("SIX_QUICK") == "1":
    POPS = [POPS[0], ("Q=2 M=10 (readings <= 10)", 2, 10, 2, False), ("Q=2 M=60, slowest >= 15 (p >= 30)", 2, 60, 30, False)]
if os.environ.get("SIX_ONLY") == "Q6":
    POPS = [("Q=6 M=30 (1,291,150,035 sets; run separately: SIX_ONLY=Q6 python3 six_v1.py)", 6, 30, 6, False)]


# ---------------------------------------------------------------------------------------------------------------------------------
# Local realisation search for a setter word over K readings (float-steered LP search, EXACT Fraction verification of every positive).
# Variables v = (u_0..u_{K-1}, R0), u_r = 1/x_r, x_0 < ... < x_{K-1}, x_0 >= 1, x_{K-1} <= XMAX.  For FIXED setter laps the cascade conditions
# are linear in v (see the docstring of wordsearch in this file's section 7).  A word is REALISED only when the exact Fraction cascade shows it;
# 'none found' is a statement about the search (float LP, laps <= LMAX, readings <= XMAX) and is UNDECIDED, not an exclusion.
import numpy as np
from scipy.optimize import linprog
CFG = {"K": 3, "XMAX": 60, "LMAX": 12, "FIXR0": False}

def lp_margin(rows):
    """rows: list of (coef(6), rhs, strict). maximise tau.  returns (tau, v) or (None,None)."""
    A = []; b = []
    for coef, rhs, strict in rows:
        A.append(list(coef) + [1.0 if strict else 0.0]); b.append(rhs)
    c = [0.0] * (CFG['K'] + 1) + [-1.0]
    bounds = [(0, 1)] * CFG['K'] + [((1, 1) if CFG['FIXR0'] else (1, 60))] + [(0, 1e-2)]
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method="highs")
    if res.status != 0: return None, None
    return res.x[CFG['K'] + 1], res.x[:CFG['K'] + 1]

def base_rows():
    rows = []
    for r in range(CFG['K']-1):
        co = [0.0] * (CFG['K'] + 1); co[r + 1] = 1.0; co[r] = -1.0       # u_{r+1} - u_r < 0
        rows.append((co, 0.0, True))
    co = [0.0] * (CFG['K'] + 1); co[CFG['K']-1] = -1.0; rows.append((co, -1.0 / CFG['XMAX'], False))   # u_4 >= 1/XMAX
    co = [0.0] * (CFG['K'] + 1); co[0] = 1.0; rows.append((co, 1.0, False))            # u_0 <= 1  (x_0 >= 1)
    return rows

def Rcoef(word, laps, s):
    co = [0.0] * (CFG['K'] + 1)
    if s == 0: co[CFG['K']] = 1.0
    else: co[word[s - 1]] = 8 * laps[s - 1] + 1.0
    return co

def sub(a, b): return [x - y for x, y in zip(a, b)]
def scal(a, k): return [x * k for x in a]
def unit(i, k=1.0):
    co = [0.0] * (CFG['K'] + 1); co[i] = k; return co

def setter_rows(word, laps, s):
    c = word[s]; l = laps[s]
    Rs = Rcoef(word, laps, s)
    rows = []
    rows.append((sub(unit(c, 8 * l - 1.0), Rs), 0.0, True))                 # (8l-1)u_c < R_s
    rows.append((sub(Rs, unit(c, 8 * l + 1.0)), 0.0, True))                 # R_s < (8l+1) u_c
    if s >= 1:
        rows.append((sub(Rcoef(word, laps, s - 1), unit(c, 8 * l - 1.0)), 0.0, False))   # entered anew
    return rows

def maxim_rows(word, laps, s, z, Lt):
    Rs = Rcoef(word, laps, s); Rn = Rcoef(word, laps, s + 1)
    return [(sub(unit(z, 8 * Lt - 1.0), Rs), 0.0, True),
            (sub(Rs, unit(z, 8 * Lt + 7.0)), 0.0, False),
            (sub(unit(z, 8 * Lt + 1.0), Rn), 0.0, False)]

def exact_sim(xs, R0, steps):
    R = R0; out = []
    for _ in range(steps):
        best = None; bi = -1; bn = 0
        for i, x in enumerate(xs):
            n = (x * R / 8 + F(1, 2)).__floor__()
            if abs(x * R - 8 * n) < 1:
                op = (8 * n + 1) / x
                if best is None or op > best: best, bi, bn = op, i, n
        if best is None: return out, R, True
        out.append((bi, bn)); R = best
    return out, R, False

def to_exact(v):
    us = [F(float(t)) for t in v[:CFG['K']]]; R0 = F(float(v[CFG['K']]))
    return [1 / u for u in us], R0

class Searcher:
    def __init__(self, word, node_limit=20000):
        self.word = [int(ch) for ch in word]; self.L = len(word)
        self.nodes = 0; self.node_limit = node_limit; self.found = None; self.hit = False

    def cegar(self, laps, rows):
        """rows: constraints so far (includes setter rows for all s). counterexample-guided on maximality."""
        stack = [rows]
        while stack:
            if self.nodes > self.node_limit: self.hit = True; return None
            rs = stack.pop(); self.nodes += 1
            tau, v = lp_margin(rs)
            if v is None or tau < 1e-9: continue
            xs, R0 = to_exact(v)
            sim, Rend, fixed = exact_sim(xs, R0, self.L)
            ok = (len(sim) == self.L) and all(sim[s][0] == self.word[s] and sim[s][1] == laps[s] for s in range(self.L))
            if ok: return (xs, R0, laps)
            # first deviation
            R = R0; dev = None
            for s in range(self.L):
                # determine lap table at state s
                inway = []
                for i, x in enumerate(xs):
                    n = (x * R / 8 + F(1, 2)).__floor__()
                    if abs(x * R - 8 * n) < 1: inway.append((i, n, (8 * n + 1) / x))
                if not inway: dev = ("fixed", s); break
                bi, bn, bop = max(inway, key=lambda t: t[2])
                if bi != self.word[s] or bn != laps[s]:
                    # find an offending reading z != word[s] in the way with opening > R_{s+1}
                    Rnext = (8 * laps[s] + 1) / xs[self.word[s]]
                    off = [(i, n, op) for (i, n, op) in inway if i != self.word[s] and op > Rnext]
                    if off: dev = ("z", s, off[0][0], off[0][1]); break
                    else: dev = ("setterlap", s); break
                R = bop
            if dev is None or dev[0] != "z":
                continue    # numerical mismatch (setter not in the way): abandon this branch
            _, s, z, Lc = dev
            # branches: exact lap Lc ; lap below ; lap above
            stack.append(rs + maxim_rows(self.word, laps, s, z, Lc))
            co = sub(Rcoef(self.word, laps, s), unit(z, 8 * Lc + 7.0))
            stack.append(rs + [(sub(co, [0.0]*(CFG['K'] + 1)), -1e-12, True)])    # R_s > (8Lc+7) u_z   i.e. -(R_s - (8Lc+7)u_z) < 0
            # fix sign: above means (8Lc+7)u_z - R_s < 0
            stack[-1] = rs + [(sub(unit(z, 8 * Lc + 7.0), Rcoef(self.word, laps, s)), 0.0, True)]
            if Lc >= 1:
                stack.append(rs + [(sub(Rcoef(self.word, laps, s), unit(z, 8 * Lc - 1.0)), 0.0, False)])   # R_s <= (8Lc-1) u_z
        return None

    def dfs(self, s, laps, rows):
        if self.found or self.hit: return
        if s == self.L:
            r = self.cegar(laps, rows)
            if r: self.found = r
            return
        for l in range(1, CFG['LMAX'] + 1):
            lp = laps + [l]
            new = rows + setter_rows(self.word, lp, s) if s < self.L else rows
            # the row set for step s needs R_{s+1} only through laps[s]; ok
            tau, v = lp_margin(new)
            self.nodes += 1
            if v is None or tau < 1e-9: continue
            self.dfs(s + 1, lp, new)
            if self.found or self.hit: return

    def run(self):
        self.dfs(0, [], base_rows())
        return self.found



def _job(args):
    w, cfg = args
    CFG.update(cfg)
    S = Searcher(w, node_limit=3000); r = S.run()
    return (w, r is not None, S.hit, S.nodes, ([str(x) for x in r[0]], str(r[1]), r[2]) if r else None)

def three_letter_words(L):
    import itertools
    return [''.join(w) for w in itertools.product('012', repeat=L) if all(w[i] != w[i + 1] for i in range(L - 1))]

def budget_feasible_grid(w):
    """additive budget for three letters x_0 < x_1 < x_2: every repeated letter, consecutive occurrences i<j, needs sum_{i<s<j} x_c/x_{w_s} > 3.
    Search on a log grid of (x_1/x_0, x_2/x_1); returns an EXACT rational witness (verified with Fractions) or None (not found on the grid: UNDECIDED)."""
    al = np.exp(np.linspace(np.log(1.0005), np.log(5000), 500)); be = np.exp(np.linspace(np.log(1.0005), np.log(5000), 500))
    A, B = np.meshgrid(al, be, indexing='ij')
    X = [np.ones_like(A), A, A * B]
    ok = np.ones(A.shape, bool); last = {}
    for j, c in enumerate(w):
        c = int(c)
        if c in last:
            i = last[c]; S = np.zeros(A.shape)
            for t in range(i + 1, j): S = S + X[c] / X[int(w[t])]
            ok &= (S > 3)
        last[c] = j
    if not ok.any(): return None
    a0 = F(float(A[ok][0])).limit_denominator(1000); b0 = F(float(B[ok][0])).limit_denominator(1000)
    x = [F(1), a0, a0 * b0]; good = True; last = {}
    for j, c in enumerate(w):
        c = int(c)
        if c in last:
            i = last[c]; good &= (sum(x[c] / x[int(w[t])] for t in range(i + 1, j)) > 3)
        last[c] = j
    return x if good else None

def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def compile_cpp(tmp):
    src = os.path.join(tmp, "enum5.cpp"); exe = os.path.join(tmp, "enum5")
    open(src, "w").write(CPP)
    r = sh(["g++", "-O2", "-std=c++17", "-pthread", "-o", exe, src])
    if r.returncode != 0:
        print(r.stderr); sys.exit(1)
    return exe

def run_pop(exe, tmp, Q, M, pmin, allw):
    wf = os.path.join(tmp, "words94.txt"); open(wf, "w").write("\n".join(WORDS94) + "\n")
    cmd = [exe, str(Q), str(M), str(pmin), str(THREADS), wf] + (["all"] if allw else [])
    r = sh(cmd)
    if r.returncode != 0:
        print(r.stderr); sys.exit(1)
    return r.stdout

def parse(out):
    d = {"words": [], "occ": {}}
    for line in out.split("\n"):
        if line.startswith("W "):
            m = re.match(r"W (.*) \| (V\d+) \| n=(\d+) maxR=(\d+)/(\d+) ex (.*)", line)
            d["words"].append((m.group(1).strip(), m.group(2), int(m.group(3)), F(int(m.group(4)), int(m.group(5))),
                               tuple(int(x) for x in m.group(6).split())))
        elif line.startswith("OCC "):
            m = re.match(r"OCC (\d+) n=(\d+) ex (.*)", line)
            d["occ"][m.group(1)] = (int(m.group(2)), tuple(int(x) for x in m.group(3).split()))
        else:
            d.setdefault("lines", []).append(line)
    for l in d.get("lines", []):
        k = l.split(" ")[0]
        d.setdefault("raw", {})[k] = l
        if k == "BAND": d.setdefault("bands", []).append(l)
    return d

def cascade(readings, limit=400):
    """exact Fraction cascade from R = 1; returns (setters as ranks, laps, R list, visits of rank 0, hit_limit)."""
    xs = list(readings)
    R = F(1); Rs = [R]; setters = []; laps = []; hit = False; visits = 0
    while True:
        best = None; bi = -1; bn = 0; inway0 = False
        for i, x in enumerate(xs):
            v = x * R / 8
            n = (v + F(1, 2)).__floor__()
            if abs(x * R - 8 * n) < 1:
                if i == 0: inway0 = True
                op = (8 * n + 1) / x
                if best is None or op > best:
                    best = op; bi = i; bn = n
        if inway0: visits += 1
        if best is None: break
        setters.append(bi); laps.append(bn); R = best; Rs.append(R)
        if len(setters) >= limit:
            hit = True; break
    return setters, laps, Rs, visits, hit

def wlabel(setters, laps):
    return " ".join("%d:%d" % (s, l) for s, l in zip(setters, laps))

def weight(readings, setters):
    return sum(F(1) / readings[s] for s in setters)

def main():
    tmp = tempfile.mkdtemp(prefix="six_v1_")
    exe = compile_cpp(tmp)
    res = OrderedDict()
    for (label, Q, M, pmin, allw) in POPS:
        res[label] = (Q, M, pmin, parse(run_pop(exe, tmp, Q, M, pmin, allw)))

    print("=" * 110)
    print("1. POPULATIONS (C++ exact integers; every 5-subset of {p/Q : p_min <= p <= M Q}; unit m = 1; cascade from R = 1; move limit 400)")
    print("=" * 110)
    for label, (Q, M, pmin, d) in res.items():
        raw = d["raw"]
        print("\nPOP %s" % label)
        for k in ("POP", "LEN", "VISITS", "SETTINGS", "MAXR", "WLOW", "WUP", "MAXW", "POS", "MAXVIOLA_P0", "WIN8", "RUN3", "RETBUDGET", "LAPALL", "MULTISET", "LAST"):
            if k in raw:
                print("   " + raw[k][:400])
        for bl in d.get("bands", []): print("   " + bl)
        m = re.match(r"MAXR (\d+)/(\d+) set (.*)", raw["MAXR"])
        mw = re.match(r"MAXW (\d+)/(\d+) set (.*)", raw["MAXW"])
        print("   max R = %s = %s (exact fraction), max W = %s" % (F(int(m.group(1)), int(m.group(2))), m.group(1) + "/" + m.group(2),
              F(int(mw.group(1)), int(mw.group(2)))))

    # ---- Section 2
    print("\n" + "=" * 110)
    print("2. ALL CHAINS of the grid Q = 12, M = 10 (every five readings p/12, 12 <= p <= 120): distinct (word with laps), by visits of the slowest")
    print("=" * 110)
    lab0 = list(res.keys())[0]
    Q, M, pmin, d0 = res[lab0]
    words = d0["words"]
    print("distinct (word,laps,visits) entries listed (visits >= 0, all printed): %d" % len(words))
    cnt = Counter()
    for w, v, n, mr, ex in words: cnt[v] += 1
    print("by visits of the slowest:", dict(cnt))
    longest = sorted(words, key=lambda t: (-len(t[0].split()), -t[2]))[:12]
    print("longest chains (word with laps | visits | number of sets | max final R | example set p/12):")
    for w, v, n, mr, ex in longest:
        print("   %-70s %s n=%d maxR=%s ex=%s" % (w, v, n, mr, ex))
    print("chains with the slowest visited twice (every one; the segment from its setting to its return is listed):")
    for w, v, n, mr, ex in words:
        if v == "V2":
            print("   %-70s n=%d maxR=%s ex=%s" % (w, n, mr, ex))

    # ---- Section 3
    print("\n" + "=" * 110)
    print("3. THE SETS IN WHICH THE SLOWEST READING IS VISITED THREE TIMES")
    print("=" * 110)
    for label, (Q, M, pmin, d) in res.items():
        v3 = [t for t in d["words"] if t[1] == "V3"]
        if not v3: continue
        print("\nPOP %s : %d distinct chains with 3 visits (sets: %d)" % (label, len(v3), sum(t[2] for t in v3)))
        for w, v, n, mr, ex in v3:
            xs = [F(p, Q) for p in ex]
            st, lp, Rs, vis, hit = cascade(xs)
            ok = (wlabel(st, lp) == w) and Rs[-1] == mr
            print("   %s | n=%d maxR=%s | example %s -> a = %s ; Python Fraction cascade re-run: word %s final R %s visits of a %d %s" %
                  (w, n, mr, ex, xs[0], "agrees" if ok else "DISAGREES", Rs[-1], vis, "(ok)" if ok else "(!!)"))

    # ---- Section 4
    print("\n" + "=" * 110)
    print("4. THE 94 MINIMAL NON-OCCURRING WORDS (law_of_position_v1.out section 2, K = 5, Q = 12, M = 10): occurrence as a factor of a setter word in the other grids")
    print("=" * 110)
    print("A word of the 94 is 'minimal non-occurring' for the grid Q = 12, M = 10 only.  Below: does it occur as a factor (length >= 2) of the setter word of an exact")
    print("cascade from R = 1 in another grid?  Each witness is re-run with Python Fractions (independent of the C++).")
    occ_a5 = {}; occ_any = {}
    for label, (Q, M, pmin, d) in res.items():
        a5 = ("slowest >= 5" in label) or ("slowest >= 15" in label)
        for w, (n, ex) in d["occ"].items():
            if w not in occ_any: occ_any[w] = (label, Q, n, ex)
            if a5 and w not in occ_a5: occ_a5[w] = (label, Q, n, ex)
    print("words tested: %d" % len(WORDS94))
    print("occurring in at least one grid (slowest reading >= 1): %d ; in no grid: %d" % (len(occ_any), len(WORDS94) - len(occ_any)))
    print("occurring in at least one grid whose slowest reading is >= 5 (the regime 5 m <= a): %d ; in none of those: %d" %
          (len(occ_a5), len(WORDS94) - len(occ_a5)))
    print("per grid (words occurring / 94):")
    for label, (Q, M, pmin, d) in res.items():
        print("   %-46s %d" % (label, len(d["occ"])))
    nverified = 0
    emin_all = {}
    for w in WORDS94:
        best_e = None
        for label, (Q, M, pmin, d) in res.items():
            if w in d["occ"]:
                n, ex = d["occ"][w]
                e = F(ex[4], Q)
                if best_e is None or e < best_e[0]: best_e = (e, label, Q, n, ex)
        emin_all[w] = best_e
    print("fastest reading of the best witness per word (smallest over all grids; each grid reports, per word, the occurrence with the smallest fastest reading):")
    thr = [10, 11, 12, 13, 14, 16, 20, 30]
    for t in thr:
        print("   words whose best witness has fastest reading <= %d: %d of %d" % (t, sum(1 for w in WORDS94 if emin_all[w] and emin_all[w][0] <= t), len(WORDS94)))
    print("   largest fastest reading among the best witnesses: %s ; smallest: %s" % (max(emin_all[w][0] for w in WORDS94 if emin_all[w]), min(emin_all[w][0] for w in WORDS94 if emin_all[w])))
    for w in WORDS94:
        be = emin_all[w]
        if be is None:
            print("   %-9s NOT FOUND in any grid" % w); continue
        e, label, Q, n, ex = be
        xs = [F(p, Q) for p in ex]
        st, lp, Rs, vis, hit = cascade(xs)
        sstr = "".join(str(x) for x in st)
        okf = w in sstr
        nverified += okf
        print("   %-9s best witness in %-34s p/%d %s  a=%s fastest=%s  chain %s  exact re-run: factor %s" %
              (w, label[:34], Q, ex, xs[0], e, wlabel(st, lp), "present" if okf else "ABSENT (!!)"))
    print("exact Fraction re-runs confirming the factor: %d of %d" % (nverified, len(WORDS94)))
    print("words occurring in no grid: " + (" ".join(w for w in WORDS94 if w not in occ_any) or "(none)"))
    print("words occurring in no slowest>=5 grid: " + (" ".join(w for w in WORDS94 if w not in occ_a5) or "(none)"))
    print("[OBS] on the grids with every reading <= 10 (Q = 1, 2, 3, 4, 6, 8, 12 with M = 10) none of the 94 words occurs; with readings up to 14 (Q = 8) 56 occur; with readings")
    print("up to 40 or 60 (Q = 3, 2) all 94 occur.  So on these grids the absence of the 94 words in the grid Q = 12, M = 10 coincides with the range 10 of that grid and not with a law: no word of the 94 is excluded")
    print("by entered_anew, two_step_law, lap_identity or lap_budget: those are Lean theorems about every cascade (LawOfPosition), so a word that occurs in an exact chain satisfies them [L, OBS].")

    # ---- Section 5
    print("\n" + "=" * 110)
    print("5. CANDIDATE INVARIANTS FOR THE LANDING POINT (tested on every set of every grid above)")
    print("=" * 110)
    for label, (Q, M, pmin, d) in res.items():
        raw = d["raw"]
        wl = raw["WLOW"]; wu = raw["WUP"]; ps = raw["POS"]; w8 = raw["WIN8"]; rb = raw["RETBUDGET"]; la = raw["LAPALL"]; r3 = raw["RUN3"]
        print("   [%s]" % label)
        print("      W' <= R_N - 1 (elapsed_lower)  : %s" % wl.replace("WLOW ", ""))
        print("      R_N - 1 < 2 W (elapsed_upper)   : %s" % wu.replace("WUP ", ""))
        print("      N m <= 3 a (position law)       : %s ; %s" % (ps.replace("POS ", ""), raw["MAXVIOLA_P0"][:48]))
        print("      eight moves, >= 4 values        : %s" % w8.replace("WIN8 ", ""))
        print("      %s" % r3)
        print("      return budget, two-sided        : %s" % rb.replace("RETBUDGET ", ""))
        print("      lap 9 or >= 11 at a setting     : %s" % la.replace("LAPALL ", ""))
    print()
    print("Reading [OBS]: on every set of every grid, W' <= R_N - 1 < 2 W (the two-sided elapsed law, Lean elapsed_two_sided), eight consecutive moves have >= 4 setter")
    print("values (Lean eight_four_distinct; 4 is attained, so the bound is sharp on the grids), the first return of a reading has 3 < U < 8 dj + 1 (Lean lower: Ladder5.budget_sum,")
    print("upper: return_upper_budget), and the total setter weight W = sum m/w is at most 21608934/10200085 on the grids (3 would suffice, Lean lonely_window_of_weight).  N m <= 3 a has")
    print("violations only with the slowest reading a <= 3.5 (the 'largest p0' lines), none among the sets with a >= 5.")

    # ---- Section 5b
    print("\n" + "-" * 110)
    print("5b. EXACT CHECK OF THE GAP IDENTITIES (Lean final_gap_identity, return_gap_identity) on the chains of the grid Q = 12, M = 10 (one example set per distinct chain), the AP family and the three-visit sets")
    print("-" * 110)
    def gap_checks(xs):
        st, lp, Rs, vis, hit = cascade(xs)
        N = len(st)
        gaps = [8 * lp[s] + 1 - xs[st[s]] * Rs[s] for s in range(N)]
        fin_ok = (Rs[-1] == 1 + sum(gaps[s] / xs[st[s]] for s in range(N))) if N > 0 else (Rs[-1] == 1)
        ret_tests = 0; ret_ok = 0; up_ok = 0; low_ok = 0
        for n in range(N):
            x = xs[st[n]]
            for k in range(n + 1, N + 1):
                v = x * Rs[k] / 8
                ln = (v + F(1, 2)).__floor__()
                if abs(x * Rs[k] - 8 * ln) < 1:
                    gk = 8 * ln + 1 - x * Rs[k]
                    lhs = sum(gaps[s] * (x / xs[st[s]]) for s in range(n + 1, k)) + gk
                    dj = ln - lp[n]
                    ret_tests += 1; ret_ok += (lhs == 8 * dj)
                    U = sum(x / xs[st[s]] for s in range(n + 1, k))
                    up_ok += (U < 8 * dj + 1); low_ok += (U > 4 * dj - 1)
                    break
        # settings against weight (Lean settings_weight_bound): 4 |S_r| < x_r * W + 5 for every reading r with a nonempty set S_r of settings
        Wt = sum(F(1) / xs[st[s]] for s in range(N))
        sw_tests = 0; sw_ok = 0
        for r in range(len(xs)):
            cnt = sum(1 for s in range(N) if st[s] == r)
            if cnt > 0:
                sw_tests += 1; sw_ok += (4 * cnt < xs[r] * Wt + 5)
        return fin_ok, ret_tests, ret_ok, up_ok, low_ok, sw_tests, sw_ok
    tot = [0, 0, 0, 0, 0, 0, 0, 0]
    sets_checked = []
    Q0 = res[lab0][0]
    for w_, v_, n_, mr_, ex_ in res[lab0][3]["words"]:
        sets_checked.append([F(p, Q0) for p in ex_])
    for rho in [F(8 * j) for j in (5, 8, 12, 20, 40, 80)]:
        sets_checked.append([rho + k * F(3, 2) for k in range(5)])
    for label, (Q, M, pmin, d) in res.items():
        for w_, v_, n_, mr_, ex_ in d["words"]:
            if v_ == "V3": sets_checked.append([F(p, Q) for p in ex_])
    for xs in sets_checked:
        f, rt, ro, uo, lo, swt, swo = gap_checks(xs)
        tot[0] += 1; tot[1] += f; tot[2] += rt; tot[3] += ro; tot[4] += uo; tot[5] += lo; tot[6] += swt; tot[7] += swo
    print("   sets checked %d ; final identity 8 m seq N = 1 + sum gap (m/w): holds on %d ; first returns tested %d ; gap identity (sum gap x/w + gap_k = 8 dj) holds on %d ;" % (tot[0], tot[1], tot[2], tot[3]))
    print("   upper budget (sum x/w < 8 dj + 1) holds on %d ; lower budget (sum x/w > 4 dj - 1) holds on %d   [Fractions; Lean: final_gap_identity, return_gap_identity, return_upper_budget, LawOfPosition.lap_budget]" % (tot[4], tot[5]))
    print("   settings against weight (4 |settings of r| < x_r W + 5, W = sum 1/w over the setters; Lean settings_weight_bound): holds on %d of %d (set, reading) pairs" % (tot[7], tot[6]))

    # ---- Section 6
    print("\n" + "=" * 110)
    print("6. WHY THE NUMBER OF SETTINGS OF THE SLOWEST IS NOT BOUNDED: the arithmetic-progression family a, a+3/2, a+3, a+9/2, a+6 (Fractions, exact)")
    print("=" * 110)
    print("   rho_a    N  a-settings  W = sum 1/w (exact)      final R (exact)      laps of a (first..last)   [readings relative to the unit d_min = 1; cascade from R = 1]")
    famrows = []
    for j in [5, 6, 8, 10, 12, 16, 20, 24, 32, 40, 60, 80]:
        rho = F(8 * j)
        xs = [rho + k * F(3, 2) for k in range(5)]
        st, lp, Rs, vis, hit = cascade(xs, limit=5000)
        W = weight(xs, st)
        al = [l for s, l in zip(st, lp) if s == 0]
        famrows.append((rho, len(st), len(al), W, Rs[-1]))
        print("   %5s  %4d  %5d       W=%s      final R=%s   %s..%s   hit_limit=%s" % (rho, len(st), len(al), W, Rs[-1], al[0] if al else None, al[-1] if al else None, hit))
    print("   [OBS] the number of settings of the slowest grows with rho_a on this family (3 at 40, 14 at 320, 28 at 640 with N = 138 moves), while in every row W < 1/3 and")
    print("   4/3 < final R < 3/2.  The laps of the settings run past 10 for rho_a >= 64, outside the lap condition of")
    print("   FourDistinct (Lean settings_le_nine: at most nine settings on laps {1..8, 10}).")
    print("   [reasoned] the mechanism: the lap-j windows of a + k d lie at (8j +- 1)/(a + k d); the window of the k-th reading is displaced from that of a by about 8 j k d / a^2 in R,")
    print("   and the five windows keep chaining (each opening inside the next window) while 16 d j < a, so about a/(16 d) laps [reasoned, not formalised], each a sweep of five moves (4,3,2,1,0 in descending speed")
    print("   by the per-lap decrease, Lean ChainLaws.per_lap_decrease).  With d = 3/2 that is a/24.  Not formalised: the chaining inequality for general laps.")
    print("   Other phases (a not a multiple of 8, other d) give shorter chains for the same a (the table above is one family, not a population).")
    print("   Exact AP check (d = 1, 1/2, ...) at a = 100: N = 5, 0, ... : the family needs the phase of the start inside the chain of windows.")
    for rho in [F(100), F(300)]:
        for dd in [F(1), F(1, 2), F(3, 2), F(2), F(3)]:
            xs = [rho + k * dd for k in range(5)]
            st, lp, Rs, vis, hit = cascade(xs, limit=5000)
            print("      a=%s d=%s: N=%d a-settings=%d final R=%s" % (rho, dd, len(st), sum(1 for s in st if s == 0), Rs[-1]))



    # ---- Section 6b
    print("\n" + "-" * 110)
    print("6b. SCAN of the AP family a + k d (k = 0..4), a in [5, 100] step 1/2, d in (0, 10) step 1/4: the largest number of settings of the slowest with every lap in {1..8, 10}")
    print("-" * 110)
    best = {}; mx_all = 0; nsets = 0
    for a2 in range(10, 200):
        a = F(a2, 2)
        for d4 in range(1, 40):
            d = F(d4, 4)
            xs = [a + k * d for k in range(5)]
            st, lp, Rs, vis, hit = cascade(xs, limit=600)
            al = [l for s_, l in zip(st, lp) if s_ == 0]
            nsets += 1
            if not al: continue
            mx_all = max(mx_all, len(al))
            if all((1 <= l <= 8 or l == 10) for l in al):
                if len(al) not in best: best[len(al)] = (a, d, al, len(st))
    print("   sets run: %d ; largest number of settings of the slowest in the scan (any laps): %d ; with all laps in {1..8,10}: %d" % (nsets, mx_all, max(best)))
    for k in sorted(best):
        print("   first (a, d) in scan order with %d settings on allowed laps: a=%s d=%s laps %s, N=%d" % (k, best[k][0], best[k][1], best[k][2], best[k][3]))
    print("   [OBS] on this scan the lap condition caps the settings of the slowest at three; the Lean bound is nine (settings_le_nine); the true maximum on allowed laps is UNDECIDED.")

    # ---- Section 7
    print("\n" + "=" * 110)
    print("7. RUNS OF CONSECUTIVE MOVES WITH AT MOST THREE SETTER VALUES (the window length 8 of Lean eight_four_distinct)")
    print("=" * 110)
    print("7a. additive budget on three letters (x_0 < x_1 < x_2; every repeated letter needs sum x_c/x_w > 3 over the moves between its occurrences); exact rational witnesses:")
    for L in [4, 5, 6, 7, 8]:
        ws = three_letter_words(L); feas = []
        for w in ws:
            x = budget_feasible_grid(w)
            if x is not None: feas.append((w, x))
        print("   length %d: words without an immediate repeat %d ; budget-feasible with an exact witness found on the grid %d" % (L, len(ws), len(feas)))
        if L in (6, 7):
            for w, x in feas:
                print("      %s  x = (%s)" % (w, ", ".join(str(t) for t in x)))
    print("   [OBS/L] length 7: 2120212 passes every budget inequality with the exact readings above (Lean budget_admits_word7), so the budget laws cannot give a window of 7;")
    print("   length 8: no word was found feasible on the grid (Lean eight_four_distinct proves it for all readings).")
    print("7b. realisation of three-letter words by a cascade of THREE readings, free start R_0 >= 1 (a state, reachable or not), setter laps <= 12, readings in [1, 60]")
    print("    (float LP search; a positive is verified with the exact Fraction cascade; 'none' is UNDECIDED, not an exclusion.  A window of a FIVE-reading cascade has two more readings that may be in")
    print("     the way without setting, so this searches a sub-case: cascades whose readings are exactly the three letters of the word.)")
    from multiprocessing import Pool
    cfg = {"K": 3, "XMAX": 60, "LMAX": 12, "FIXR0": False}
    for L in ([4] if os.environ.get('SIX_QUICK') == '1' else [4, 5, 6, 7]):
        ws = three_letter_words(L)
        with Pool(THREADS) as pool:
            out = pool.map(_job, [(w, cfg) for w in ws])
        real = [o for o in out if o[1]]
        print("   length %d: words %d ; realised %d ; search hit its node limit %d ; unrealised-and-exhausted %d" %
              (L, len(ws), len(real), sum(1 for o in out if o[2] and not o[1]), sum(1 for o in out if (not o[1]) and (not o[2]))))
        for o in real[:6]:
            w, ok, hit, nodes, r = o
            xs = [F(t) for t in r[0]]; R0 = F(r[1])
            sim, Rend, fixed = exact_sim(xs, R0, L)
            okw = "".join(str(a) for a, b in sim) == w
            print("      %s realised: laps %s, R_0 = %s, readings %s (rationals near the LP point, shown to denominator 1000 for display; the check below uses the full rationals) ; exact Fraction cascade from R_0: %s" %
                  (w, r[2], R0.limit_denominator(1000), [str(x.limit_denominator(1000)) for x in xs], "reproduces the word" if okw else "DOES NOT (!!)"))

if __name__ == "__main__":
    main()
