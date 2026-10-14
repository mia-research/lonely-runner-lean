#!/usr/bin/env python3
"""ladder5_v1.py -- Task AY (2026-10-09): the budget law of a return, and the exceptional sets at five readings.

Everything is exact (Python Fractions, C++ __int128 integers).  No floats decide anything.  Every cascade loop has a
move limit (Python: 500 moves, raises; C++: 400 moves, reported as moveLimitHit).  Nothing is random.

Sections
  1  populations (C++): additive budget law, first-entry law, visits of the slowest, distinct readings between visits,
     return shapes, weight after the slowest sets.
  2  exceptional sets (slowest reading in the way twice), K = 5, Q = 12 / M = 10 and Q = 8 / M = 14 listed in full;
     Q = 6 / M = 30 summarised: setters (rank 0 = slowest), laps, budget used at the return, exact identity, AU product form.
  3  candidate laws tested on the whole population, with exact counterexamples where they fail.
  4  hypothesis audit: x must be the SETTER (exact counterexample); the intermediates must be >= x for 'four moves'.
  5  the budget laws are necessary, not sufficient: a word that satisfies every budget inequality and is not realised.
Theorem names refer to Fresh/Ladder5.lean.
"""
import subprocess, tempfile, os, sys, math, itertools
from fractions import Fraction as F
from collections import Counter

CPP = r"""// Exact integer cascade over all K-subsets of {p/Q : Q <= p <= M*Q} (readings of a set relative to the unit m = 1, start R = 1).
// Move limit 400 per set (reported if reached).  All comparisons in integers (__int128), no floating point.
#include <vector>
#include <thread>
#include <atomic>
#include <functional>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <set>
#include <map>
#include <string>
#include <mutex>
using namespace std;
typedef long long ll; typedef __int128 LL;
int K; ll Q, M; bool DUMP=false; static mutex dumpmu;
struct Frac { ll n=0,d=1; };           // exact fraction n/d, d>0
static bool lessF(const Frac&a,const Frac&b){ return (LL)a.n*b.d < (LL)b.n*a.d; }
struct Stat {
  ll sets=0, maxlen=0, limitHit=0; Frac maxAfter; bool haveAfter=false; ll afterSet[8]={0};
  vector<ll> lenHist;
  // additive budget law
  ll returnsTested=0, addViol=0; Frac minS3; bool haveMin=false; ll minSet[8]={0}; ll minInfo[4]={0};
  // first-entry law
  ll entriesTested=0, entryViol=0; Frac minEntry; bool haveMinE=false;
  // slowest visits
  vector<ll> slowVisitHist; ll slowMulti=0;
  ll distinctViol4=0; ll allOthersViol=0; vector<ll> distinctHist; // distinct other readings between consecutive visits of slowest
  Frac aminExc; bool haveAmin=false; Frac ratioMaxExc; bool haveRatio=false; Frac ratioMinExc; bool haveRatioMin=false;
  Frac maxR; bool haveR=false;
  // pareto stats for returns of any reading: (faster moves, slower moves) minimal
  map<pair<int,int>,ll> retShape;
  // descending prefix
  ll descPrefix=0, excTotal=0;
};
static inline ll rnd_div(LL num, LL den){ LL v=2*num+den; LL d=2*den; LL q=v/d; if((v%d!=0)&&((v<0)!=(d<0))) q--; return (ll)q; }
void run(const ll* p,int k,Stat& st){
  // trace
  ll A=1,B=1; int len=0;
  vector<int> setter; vector<ll> lapv; vector<unsigned> mask; vector<Frac> R; R.push_back({1,1});
  bool hit=false;
  while(true){
    bool any=false; ll bA=0,bB=1; int bi=-1; ll bn=0; unsigned mk=0;
    for(int i=0;i<k;i++){
      LL num=(LL)p[i]*A; LL den=(LL)8*Q*B; ll n=rnd_div(num,den);
      LL diff=num-(LL)n*den; if(diff<0) diff=-diff;
      if(8*diff<den){ mk|=1u<<i; ll a2=(8*n+1)*Q,b2=p[i]; if(!any||(LL)a2*bB>(LL)bA*b2){bA=a2;bB=b2;any=true;bi=i;bn=n;} }
    }
    mask.push_back(mk);
    if(!any) break;
    setter.push_back(bi); lapv.push_back(bn);
    A=bA;B=bB; len++; R.push_back({A,B});
    if(len>=400){hit=true;break;}
  }
  st.sets++; if(hit) st.limitHit++;
  if(len>st.maxlen) st.maxlen=len;
  if((int)st.lenHist.size()<=len) st.lenHist.resize(len+1,0); st.lenHist[len]++;
  Frac Rf=R.back(); if(!st.haveR || lessF(st.maxR,Rf)){ st.maxR=Rf; st.haveR=true; }
  // states: 0..len ; moves 0..len-1 (setter[s]); mask[s] = in-the-way set at state s
  LL D=1; for(int i=0;i<k;i++) D*=p[i];
  // additive law: x set at n; every later state kk with x in the way
  for(int n=0;n<len;n++){
    int x=setter[n];
    for(int kk=n+1;kk<=len;kk++){
      if(!(mask[kk]>>x&1)) continue;
      LL N=0; int fast=0,slow=0;
      for(int s=n+1;s<kk;s++){ int y=setter[s]; N+=(LL)p[x]*(D/p[y]); if(y>x) fast++; else if(y<x) slow++; }
      st.returnsTested++;
      if(!(N>3*D)) st.addViol++;
      // min of S/3 = N/(3D)
      Frac f; f.n=(ll)N; f.d=(ll)(3*D);
      if(!st.haveMin || lessF(f,st.minS3)){ st.minS3=f; st.haveMin=true; for(int i=0;i<k;i++) st.minSet[i]=p[i]; st.minInfo[0]=x; st.minInfo[1]=n; st.minInfo[2]=kk; }
      st.retShape[{fast,slow}]++;
      break; // only the first visit after the setting
    }
  }
  // first-entry law: y first in the way at state kk: sum_{s<kk} y/w_s > 7/2 - y/2   (y = p/Q, unit m = 1)
  for(int y=0;y<k;y++){
    int kk=-1; for(int s=0;s<=len;s++) if(mask[s]>>y&1){kk=s;break;}
    if(kk<0) continue;
    // lhs = sum_{s<kk} p_y/p_w + p_y/(2Q)   ; compare with 7/2 : multiply by 2*Q*D
    LL N=0; for(int s=0;s<kk;s++){ int w=setter[s]; N+=(LL)p[y]*(D/p[w]); }
    LL lhsN = 2*Q*N + (LL)p[y]*D;      // lhs * (2 Q D)
    LL rhsN = 7*Q*D;                   // (7/2) * (2 Q D)
    st.entriesTested++;
    if(!(lhsN>rhsN)) st.entryViol++;
    // margin ratio lhs/(7/2)
    Frac f; f.n=(ll)lhsN; f.d=(ll)rhsN;
    if(!st.haveMinE || lessF(f,st.minEntry)){ st.minEntry=f; st.haveMinE=true; }
  }
  // slowest (index 0) visits
  { int n0=-1; for(int s=0;s<len;s++) if(setter[s]==0){n0=s;break;}
    if(n0>=0){ LL N=0; for(int s=n0+1;s<len;s++) N+=(LL)p[0]*(D/p[setter[s]]);
      Frac f; f.n=(ll)N; f.d=(ll)D; if(!st.haveAfter||lessF(st.maxAfter,f)){st.maxAfter=f;st.haveAfter=true;for(int i=0;i<k;i++)st.afterSet[i]=p[i];} } }
  int sv=0; vector<int> visits; for(int s=0;s<=len;s++) if(mask[s]&1u){ sv++; visits.push_back(s);} 
  if((int)st.slowVisitHist.size()<=sv) st.slowVisitHist.resize(sv+1,0); st.slowVisitHist[sv]++;
  if(sv>=2){
    if(DUMP){ lock_guard<mutex> g(dumpmu); for(int i=0;i<k;i++) printf("%lld ",p[i]); printf("\n"); }
    st.slowMulti++; st.excTotal++;
    // ratio / smallest slowest among exceptional sets
    Frac a; a.n=p[0]; a.d=Q; if(!st.haveAmin||lessF(a,st.aminExc)){st.aminExc=a;st.haveAmin=true;}
    Frac r; r.n=p[k-1]; r.d=p[0]; if(!st.haveRatio||lessF(st.ratioMaxExc,r)){st.ratioMaxExc=r;st.haveRatio=true;}
    if(!st.haveRatioMin||lessF(r,st.ratioMinExc)){st.ratioMinExc=r;st.haveRatioMin=true;}
    for(int vi=0;vi+1<(int)visits.size();vi++){
      int v1=visits[vi],v2=visits[vi+1]; unsigned seen=0;
      for(int s=v1;s<v2;s++){ if(setter[s]!=0) seen|=1u<<setter[s]; }
      int cnt=__builtin_popcount(seen);
      if((int)st.distinctHist.size()<=cnt) st.distinctHist.resize(cnt+1,0); st.distinctHist[cnt]++;
      if(cnt<4) st.distinctViol4++;
      if(cnt<k-1) st.allOthersViol++;
    }
    // descending prefix: first k-1 setters after the slowest's first visit-setting are k-1,k-2,...,1
    int v1=visits[0]; int st0=(setter[v1]==0)?v1+1:v1; bool desc=true;
    for(int j=0;j<k-1;j++){ int s=st0+j; if(s>=len||setter[s]!=k-1-j){desc=false;break;} }
    if(desc) st.descPrefix++;
  }
}
int main(int argc,char**argv){
  if(argc<4){fprintf(stderr,"usage: laws K Q M\n");return 1;}
  K=atoi(argv[1]);Q=atoll(argv[2]);M=atoll(argv[3]); DUMP=(argc>=5);
  int nv=(int)(M*Q-Q+1); vector<ll> vals(nv); for(int i=0;i<nv;i++) vals[i]=Q+i;
  int nt=10; vector<Stat> sts(nt); vector<thread> th; atomic<int> next(0);
  for(int t=0;t<nt;t++) th.emplace_back([&,t]{
    ll p[16];
    while(true){ int i0=next++; if(i0>=nv) break; p[0]=vals[i0];
      function<void(int,int)> rec=[&](int pos,int start){ if(pos==K-1){run(p,K,sts[t]);return;} for(int j=start;j<nv;j++){p[pos+1]=vals[j];rec(pos+1,j+1);} };
      rec(0,i0+1);} });
  for(auto&x:th) x.join();
  Stat T;
  auto addv=[&](vector<ll>&a,const vector<ll>&b){ if(a.size()<b.size()) a.resize(b.size(),0); for(size_t i=0;i<b.size();i++) a[i]+=b[i]; };
  for(auto&s:sts){
    T.sets+=s.sets; T.limitHit+=s.limitHit; if(s.maxlen>T.maxlen)T.maxlen=s.maxlen; addv(T.lenHist,s.lenHist);
    T.returnsTested+=s.returnsTested; T.addViol+=s.addViol;
    if(s.haveMin&&(!T.haveMin||lessF(s.minS3,T.minS3))){T.minS3=s.minS3;T.haveMin=true;for(int i=0;i<8;i++)T.minSet[i]=s.minSet[i];for(int i=0;i<4;i++)T.minInfo[i]=s.minInfo[i];}
    T.entriesTested+=s.entriesTested; T.entryViol+=s.entryViol;
    if(s.haveMinE&&(!T.haveMinE||lessF(s.minEntry,T.minEntry))){T.minEntry=s.minEntry;T.haveMinE=true;}
    addv(T.slowVisitHist,s.slowVisitHist); T.slowMulti+=s.slowMulti; T.distinctViol4+=s.distinctViol4; T.allOthersViol+=s.allOthersViol; addv(T.distinctHist,s.distinctHist);
    if(s.haveAmin&&(!T.haveAmin||lessF(s.aminExc,T.aminExc))){T.aminExc=s.aminExc;T.haveAmin=true;}
    if(s.haveRatio&&(!T.haveRatio||lessF(T.ratioMaxExc,s.ratioMaxExc))){T.ratioMaxExc=s.ratioMaxExc;T.haveRatio=true;}
    if(s.haveRatioMin&&(!T.haveRatioMin||lessF(s.ratioMinExc,T.ratioMinExc))){T.ratioMinExc=s.ratioMinExc;T.haveRatioMin=true;}
    if(s.haveR&&(!T.haveR||lessF(T.maxR,s.maxR))){T.maxR=s.maxR;T.haveR=true;}
    if(s.haveAfter&&(!T.haveAfter||lessF(T.maxAfter,s.maxAfter))){T.maxAfter=s.maxAfter;T.haveAfter=true;for(int i=0;i<8;i++)T.afterSet[i]=s.afterSet[i];}
    for(auto&kv:s.retShape) T.retShape[kv.first]+=kv.second; T.descPrefix+=s.descPrefix; T.excTotal+=s.excTotal;
  }
  if(DUMP) return 0;
  printf("POP K=%d Q=%lld M=%lld sets=%lld maxlen=%lld moveLimitHit=%lld maxR=%lld/%lld\n",K,Q,M,T.sets,T.maxlen,T.limitHit,T.maxR.n,T.maxR.d);
  printf("  chain length hist:"); for(size_t i=0;i<T.lenHist.size();i++) if(T.lenHist[i]) printf(" %zu:%lld",i,T.lenHist[i]); printf("\n");
  printf("  ADDITIVE LAW (first return of the setter x after its setting; sum_{s} x/w_s > 3): returns tested=%lld violations=%lld  min(S/3)=%lld/%lld at set",T.returnsTested,T.addViol,T.minS3.n,T.minS3.d);
  for(int i=0;i<K;i++) printf(" %lld",T.minSet[i]); printf(" (x=#%lld set at move %lld, in the way at state %lld)\n",T.minInfo[0],T.minInfo[1],T.minInfo[2]);
  printf("  ENTRY LAW (y first in the way at state k: sum_{s<k} y/w_s > 7/2 - y/2): entries tested=%lld violations=%lld min(lhs/(7/2))=%lld/%lld\n",T.entriesTested,T.entryViol,T.minEntry.n,T.minEntry.d);
  printf("  slowest in the way: hist"); for(size_t i=0;i<T.slowVisitHist.size();i++) if(T.slowVisitHist[i]) printf(" %zu:%lld",i,T.slowVisitHist[i]); printf("  (sets with >=2 visits: %lld)\n",T.slowMulti);
  if(T.slowMulti){
    printf("  between consecutive visits of the slowest: distinct OTHER readings hist"); for(size_t i=0;i<T.distinctHist.size();i++) if(T.distinctHist[i]) printf(" %zu:%lld",i,T.distinctHist[i]); printf("\n");
    printf("  candidate '>=4 distinct other readings between visits': violations=%lld ; candidate 'all K-1 other readings': violations=%lld\n",T.distinctViol4,T.allOthersViol);
    printf("  exceptional sets: smallest slowest reading=%lld/%lld ; max/min ratio window=[%lld/%lld , %lld/%lld]; first K-1 setters after the slowest = descending order in %lld of %lld\n",T.aminExc.n,T.aminExc.d,T.ratioMinExc.n,T.ratioMinExc.d,T.ratioMaxExc.n,T.ratioMaxExc.d,T.descPrefix,T.excTotal);
  }
  printf("  weight a/y summed over ALL moves after the first setting of the slowest a: max = %lld/%lld at set",T.maxAfter.n,T.maxAfter.d); for(int i=0;i<K;i++) printf(" %lld",T.afterSet[i]); printf("\n");
  printf("  return shapes (faster-setter moves, slower-setter moves) between a setting of x and its first visit: "); for(auto&kv:T.retShape) printf("(%d,%d):%lld ",kv.first.first,kv.first.second,kv.second); printf("\n");
}
"""

TMP = tempfile.mkdtemp(prefix="ladder5_")
SRC = os.path.join(TMP, "laws.cpp"); BIN = os.path.join(TMP, "laws")
open(SRC, "w").write(CPP)
r = subprocess.run(["g++", "-O2", "-std=c++17", "-pthread", "-o", BIN, SRC], capture_output=True, text=True)
if r.returncode != 0:
    print(r.stderr); sys.exit(1)

def run_pop(K, Q, M, dump=False):
    args = [BIN, str(K), str(Q), str(M)] + (["dump"] if dump else [])
    out = subprocess.run(args, capture_output=True, text=True, timeout=1100)
    return out.stdout

# ------------------------------------------------------------------ exact Python cascade (R coordinate, unit m = 1, R_0 = 1)
def rnd(y): return math.floor(y + F(1, 2))
def inway(x, R):
    y = x * R / 8
    return abs(y - rnd(y)) < F(1, 8)
def trace(E, maxmoves=500):
    R = F(1); moves = []; states = [R]
    for _ in range(maxmoves):
        blk = []
        for x in E:
            y = x * R / 8; n = rnd(y)
            if abs(y - n) < F(1, 8): blk.append((x, n))
        if not blk: return moves, states
        best = max(blk, key=lambda b: (8 * b[1] + 1) / b[0])
        moves.append((R, best[0], best[1], [b[0] for b in blk]))
        R = F(8 * best[1] + 1) / best[0]; states.append(R)
    raise Exception("move limit")

def Fp(P): return P / (P - 2) if P >= 9 else F(9, 7)

def analyse(E):
    """E sorted ascending (rank 0 = slowest).  Returns dict for the first two visits of the slowest."""
    moves, states = trace(E); a = E[0]; K = len(E)
    w = [E.index(m[1]) for m in moves]
    vis = [n for n in range(len(states)) if inway(a, states[n])]
    if len(vis) < 2: return None
    v1, v2 = vis[0], vis[1]
    seg = w[v1:v2]
    lap1 = rnd(a * states[v1] / 8); lap2 = rnd(a * states[v2] / 8)
    d = dict(set=E, word=seg, v1=v1, v2=v2, lap1=lap1, lap2=lap2, setting=(w[v1] == 0), moves=moves, states=states, w=w)
    if w[v1] == 0:
        inter = list(range(v1 + 1, v2))
        S = sum(a / E[w[s]] for s in inter)
        N = 8 * lap1 + 1
        prod = F(1)
        for s in inter:
            y = E[w[s]]; lp = moves[s][2]
            assert lp >= 1
            prod *= Fp(y / a * N)
        d.update(S=S, inter=inter, prodratio=prod / F(N + 6, N))
        # exact identity: sum_s g_s a/y_s + g_k = 8 (a returns on the next lap), g = N_s - y R_s
        if lap2 == lap1 + 1:
            g = lambda s: (8 * moves[s][2] + 1) - E[w[s]] * states[s]
            gk = (8 * lap2 + 1) - a * states[v2]
            d["identity"] = (sum(g(s) * a / E[w[s]] for s in inter) + gk == 8)
    return d

def fmt(x): return str(x) if x.denominator != 1 else str(x.numerator)

def section(t): print("\n" + "=" * 100 + "\n" + t + "\n" + "=" * 100)

# =================================================================== 1. populations
section("1. POPULATIONS (C++ exact integers).  Readings p/Q with Q <= p <= M*Q, relative to the unit d_min = 1; cascade from R = 1.")
print("Laws tested on EVERY set: additive budget law (budget_sum), first-entry law (entry_budget).")
POPS = [(3, 60, 8), (4, 36, 8), (4, 12, 20), (5, 12, 10), (5, 8, 14), (5, 6, 30), (6, 6, 10)]
for (K, Q, M) in POPS:
    print(run_pop(K, Q, M).rstrip())

# =================================================================== 2. exceptional sets
section("2. EXCEPTIONAL SETS, K = 5 (the slowest reading in the way at two states).  Rank 0 = slowest, rank 4 = fastest.")
def exceptional(K, Q, M):
    txt = run_pop(K, Q, M, dump=True)
    return [[F(int(t), Q) for t in line.split()] for line in txt.strip().split("\n") if line.strip()]

for (K, Q, M, full) in [(5, 12, 10, True), (5, 8, 14, True), (5, 6, 30, False)]:
    ex = exceptional(K, Q, M)
    print("\n-- population K=%d Q=%d M=%d : %d exceptional sets" % (K, Q, M, len(ex)))
    res = [analyse(E) for E in ex]
    cnt_words = Counter(tuple(r["word"]) for r in res)
    cnt_laps = Counter((r["lap1"], r["lap2"], r["setting"]) for r in res)
    print("   distinct segment words (setter ranks from the first visit to the move before the second visit):", len(cnt_words))
    for wd, c in sorted(cnt_words.items(), key=lambda kv: -kv[1])[:12]:
        print("     ", wd, c)
    print("   (lap of the slowest at first visit, at second visit, first visit is its setting):", sorted(cnt_laps.items()))
    sett = [r for r in res if r["setting"]]
    Smin = min(r["S"] for r in sett); Smax = max(r["S"] for r in sett)
    print("   budget used at the return, S = sum a/y over the intermediate setters: min %s = %.6f, max %s = %.6f  (law: S > 3); sets with the first visit a setting: %d of %d"
          % (fmt(Smin), float(Smin), fmt(Smax), float(Smax), len(sett), len(res)))
    print("   AU product form prod Fp / ((N+6)/N): min = %s (%.6f)  [> 1 required]" % (fmt(min(r["prodratio"] for r in sett)), float(min(r["prodratio"] for r in sett))))
    idn = [r["identity"] for r in sett if "identity" in r]
    print("   exact identity  sum_s g_s a/y_s + g_k = 8  (return on the next lap): holds in %d of %d such sets" % (sum(idn), len(idn)))
    nd = Counter(len(set(r["word"]) - {0}) for r in res)
    print("   distinct OTHER readings in the segment:", sorted(nd.items()))
    print("   smallest slowest reading a = %s ; ratio window max/min = [%s, %s]" % (fmt(min(r["set"][0] for r in res)), fmt(min(r["set"][-1] / r["set"][0] for r in res)), fmt(max(r["set"][-1] / r["set"][0] for r in res))))
    pre = Counter()
    for r in res:
        s2 = r["word"][1:] if r["setting"] else r["word"]
        pre[tuple(s2[:K - 1])] += 1
    print("   first K-1 setters after the slowest (or from the first visit):", sorted(pre.items(), key=lambda kv: -kv[1])[:10])
    if full:
        print("   LIST: set (p/Q)  |  setters from the first visit to the second visit (rank)  |  laps j -> j'  |  S = sum a/y  | S/3")
        for r in res:
            E = r["set"]
            print("    {%s}  %s  lap %d->%d  %s  %s  %.4f" % (" ".join(fmt(e) for e in E), "".join(map(str, r["word"])), r["lap1"], r["lap2"],
                  "S=" + (fmt(r["S"]) if "S" in r else "n/a"), "", float(r["S"] / 3) if "S" in r else float("nan")))

# worked chain of the AU example
section("2b. WORKED CHAIN: readings {49,62,70,79,85}/12 (AU's example), exact")
E = [F(x, 12) for x in (49, 62, 70, 79, 85)]
moves, states = trace(E)
for n, m in enumerate(moves):
    print("  move %2d  R=%-12s setter %-6s (rank %d) lap %d  in the way: %s   g = %s" %
          (n, fmt(m[0]), fmt(m[1]), E.index(m[1]), m[2], [E.index(x) for x in m[3]], fmt((8 * m[2] + 1) - m[1] * m[0])))
print("  final R =", fmt(states[-1]))
d = analyse(E)
print("  slowest a=49/12 sets at move %d, lap %d; second visit at state %d, lap %d; intermediates %s; S=%s (%.5f) > 3; identity: %s"
      % (d["v1"], d["lap1"], d["v2"], d["lap2"], d["inter"], fmt(d["S"]), float(d["S"]), d.get("identity")))

# =================================================================== 3. candidate laws on the whole population
section("3. CANDIDATE LAWS (statement, population test, exact counterexample if any)")
print("""
C1  'between two visits of the slowest at least FOUR distinct other readings set'  -- section 1: 0 violations in every K = 5 and K = 6 population above.
C2  'between two visits of the slowest EVERY other reading sets'  -- K = 5: 0 violations (it is C1 there); K = 6: violated (section 1 counts 159 sets).""")
ex6 = exceptional(6, 6, 10)
bad = None
for E in ex6:
    d = analyse(E)
    if d and len(set(d["word"]) - {0}) < 5:
        bad = d; break
print("   exact counterexample to C2 at K = 6:  set", [fmt(e) for e in bad["set"]], " segment ranks", bad["word"], " (laps %d -> %d)" % (bad["lap1"], bad["lap2"]))
print("""
C3  'after the slowest sets, the next K-1 setters are K-1, K-2, ..., 1 (strictly descending speed)'  -- section 1: K = 5 Q = 12, Q = 8 : 303/303, 286/286;
    K = 5 Q = 6 M = 30: 4459 of 5664 only.  Counterexamples (exact):""")
seen = set()
for E in exceptional(5, 6, 30):
    d = analyse(E)
    s2 = tuple((d["word"][1:] if d["setting"] else d["word"])[:4])
    if s2 != (4, 3, 2, 1) and s2 not in seen and d["setting"]:
        seen.add(s2); print("     set", [fmt(e) for e in E], "first four setters after the slowest:", s2)
    if len(seen) >= 4: break
print("""
C4  'first K-1 setters after the slowest are K-1 distinct readings'  -- fails: the prefix (4,3,2,4) occurs 37 times at K = 5 Q = 6 M = 30 (see C3 list).
C5  'the number of intermediate moves between the visits is bounded by a function of the budget'  -- a COUNT; [OBS] only (rule 7): intermediates observed 4 to 7
    (K = 5 Q = 6 M = 30) and 6 (Q = 12, Q = 8); it is not offered as a law.""")

# =================================================================== 4. hypothesis audit
section("4. HYPOTHESIS AUDIT (REQUIRED / NOT REQUIRED / UNDECIDED), exact counterexamples")
print("budget_sum, hypothesis 'x is the SETTER at n' -- REQUIRED.  Replace it by 'x is in the way at seq n':")
Ex = [F(7, 4), F(1, 2)]
t = F(57, 32)
def nxt(x, t): n = rnd(x * t); return (n + F(1, 8)) / x
inw = lambda x, t: abs(x * t - rnd(x * t)) < F(1, 8)
ox, oy = nxt(F(7, 4), t), nxt(F(1, 2), t)
print("   E = {7/4, 1/2}, seq 0 = 57/32: both in the way (7/4 on lap %d, 1/2 on lap %d); openings %s (x=7/4) and %s (y=1/2): the setter is y;" % (rnd(F(7,4)*t), rnd(F(1,2)*t), ox, oy))
print("   seq 1 = %s ; 7/4 is in the way at seq 1 on lap %d: the intermediate sum is EMPTY (k = n+1), 3 < 0 fails.  Exact check:" % (oy, rnd(F(7,4)*oy)), inw(F(7, 4), t), inw(F(1, 2), t), inw(F(7, 4), oy))
print("return_after_four, hypothesis 'every intermediate setter >= x' -- REQUIRED: a return after ONE move (x y x, 3y < x) occurs:")
E = [F(17, 4), F(25, 4), F(59, 4), F(16)]   # first 4-subset of {p/4 : 4 <= p <= 64} in lexicographic order with a reading returning after one move
mv, st = trace(E)
w = [E.index(m[1]) for m in mv]
n = next(i for i in range(len(w) - 2) if w[i] == w[i + 2])
print("   set", [fmt(e) for e in E], "setters (rank)", w, "-> reading", fmt(E[w[n]]), "sets at move", n, "and again at move", n + 2, "with", fmt(E[w[n+1]]), "between (ratio %s > 3, so 3y < x)" % fmt(E[w[n]] / E[w[n+1]]))
print("""
Hypotheses NOT used by budget_sum (the Lean statement does not mention them, so they are NOT REQUIRED): 0 < seq 0, a lower bound on laps,
ordering of the readings, a base m, integrality or commensurability, seq 0 = 1/(8m).  Used and REQUIRED as stated: 0 < every disparity
(the proof divides by x and w s; a negative disparity reduces to its absolute value by distInt_abs_mul), the cascade moves, n < k.
The constant 3 is not attained in the populations (min S/3 in section 1 is above 1); whether it is the infimum is UNDECIDED.
budget_product: 0 < seq 0 and 'laps of the intermediate setters >= 1' are used by the proof; whether the statement fails without them is UNDECIDED.
entry_budget: 0 < m and m <= d (lap >= 1; Ladder.audit_lower_bound), seq 0 = 1/(8m): used, REQUIRED by the proof; necessity of the exact equality UNDECIDED.""")

# =================================================================== 5. budget laws are necessary, not sufficient
section("5. THE BUDGET INEQUALITIES ARE NECESSARY, NOT SUFFICIENT")
print("Word  a | v t u v | (a in the way again):  a = slowest, t <= u < v.  Budget inequalities: v returns: v/t + v/u > 3 ; a returns: 2a/v + a/t + a/u > 3.")
a, tt, u, v = F(1), F(10005, 10000), F(12, 10), F(17, 10)
print("   a=1, t=1.0005, u=1.2, v=1.7 :  v/t + v/u = %.5f > 3 : %s ;  2a/v + a/t + a/u = %.5f > 3 : %s" %
      (float(v/tt + v/u), v/tt + v/u > 3, float(2*a/v + a/tt + a/u), 2*a/v + a/tt + a/u > 3))
print("   so these inequalities alone do not exclude a three-reading word; a is not even set in the cascade of a scaled copy:")
for scale in (F(3), F(5), F(9, 2)):
    E = sorted([a*scale, tt*scale, u*scale, v*scale])
    mv, st = trace(E)
    print("     scale %s: readings %s : setters (rank) %s, final R = %s" % (scale, [fmt(e) for e in E], [E.index(m[1]) for m in mv], fmt(st[-1])))
print("   (K = 4: 0 sets with the slowest in the way twice in 166,695,375 + 111,607,501 + 5,563,251 sets, section 1.  The law that excludes the word is a law of POSITION (which zone a landing is in), owed.)")
print("\nDONE")
