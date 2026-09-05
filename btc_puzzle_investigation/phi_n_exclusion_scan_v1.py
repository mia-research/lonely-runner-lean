#!/usr/bin/env python3
"""
Beyond aggregate MI: look for EXCLUSIONS / negative correlations — a residue value
of (X,Y) that DEPLETES or FORBIDS a value of n/k/D. That's what actually reduces a
search (ruling candidates out), and MI (unsigned, averaged) barely sees a single
depleted cell.

Per channel (feature F, target T), contingency O[a][b], expected E=row·col/N,
standardized residual r=(O−E)/sqrt(E). We track:
  - min residual  (most DEPLETED cell = strongest exclusion / negative corr)
  - empty cells with E>=5 (a FORBIDDEN combo)
  - max residual  (strongest enrichment)
Analytic triage (min-r ranking), then permutation null on the extremes.

CROSS-REFERENCE-AGAINST-ITSELF = positive controls that MUST fire:
  n mod q vs k mod q  (gcd(n,k)=1 forbids (0,0) when q|n) — proves the test works.
Then the honest (X,Y)→{n,k,D} scan with a clean permutation null.
Signal path exact int; residual/permutation are the ranked statistics.
Subset N>=64 (dense cells); n,k,D exact from d.
"""
import csv, random, math
from math import gcd, isqrt
random.seed(20260710); NMAX=256
p_field=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
def best_nk(d,N):
    A=1<<(N-1); num=d-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A)
        if k<0:k=0
        if k>n:k=n
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    if g>1: n//=g; k//=g
    return n,k
def table_stats(fa,tb):
    """return (min_resid, max_resid, n_empty_big) for the F×T contingency."""
    O={}; ra={}; cb={}
    for a,b in zip(fa,tb):
        O[(a,b)]=O.get((a,b),0)+1; ra[a]=ra.get(a,0)+1; cb[b]=cb.get(b,0)+1
    N=len(fa); mn=1e9; mx=-1e9; empty=0                     # noqa: float
    for a in ra:
        for b in cb:
            E=ra[a]*cb[b]/N                                  # noqa: float
            o=O.get((a,b),0)
            r=(o-E)/math.sqrt(E) if E>0 else 0.0            # noqa: float
            if r<mn: mn=r
            if r>mx: mx=r
            if o==0 and E>=5: empty+=1
    return mn,mx,empty
def perm_min(fa,tb,B=400):
    """permutation null for the most-depleted-cell residual (min)."""
    obs,_,_=table_stats(fa,tb); tb=tb[:]; le=0; nulls=[]
    for _ in range(B):
        random.shuffle(tb); m,_,_=table_stats(fa,tb); nulls.append(m)
        if m<=obs: le+=1     # null at least as depleted
    return obs,(le+1)/(B+1)                                  # noqa: float

BITS=[];DS=[];XS=[];YS=[]
with open("constructed_keys_1to160_100k.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"])
        if N<64: continue
        BITS.append(N); DS.append(int(r["d"])); XS.append(int(r["X"],16)); YS.append(int(r["Y"],16))
M=len(XS); NS=[];KS=[];DD=[];SG=[]
for i in range(M):
    n,k=best_nk(DS[i],BITS[i]); A=1<<(BITS[i]-1); NS.append(n); KS.append(k)
    D=DS[i]-(A+(A*k)//n); DD.append(D); SG.append(1 if D>=0 else 0)
print(f"N>=64 keys: {M}\n")

# ---------- POSITIVE CONTROLS (must fire) ----------
print("POSITIVE CONTROLS (method must detect these exclusions):")
for q in (2,3,5,7):
    fa=[n%q for n in NS]; tb=[k%q for k in KS]
    obs,pp=perm_min(fa,tb,B=400)
    _,_,emp=table_stats(fa,tb)
    print(f"  n mod {q} vs k mod {q}: min-resid={obs:+.2f} empty(E>=5)={emp} perm p={pp:.3f}")
print()

# ---------- (X,Y) EXCLUSION SCAN ----------
print("(X,Y) -> {n,k,D,sign D} exclusion scan (min-resid = most depleted cell):")
feat_kinds={
 "Xmodq":lambda x,y,q:x%q,"Ymodq":lambda x,y,q:y%q,
 "(X+Y)modq":lambda x,y,q:(x+y)%q,"(X*Y)modq":lambda x,y,q:(x*y)%q,
}
QF=[2,3,4,5,6,7,8,9,12,16]
tgts={"n":NS,"k":KS,"D":DD}
scan=[]
for q in QF:
    feats={fn:[f(XS[i],YS[i],q) for i in range(M)] for fn,f in feat_kinds.items()}
    for tn,tv in tgts.items():
        tb=[v%q for v in tv]
        for fn,fa in feats.items():
            mn,mx,emp=table_stats(fa,tb)
            scan.append((mn,fn,q,tn,mx,emp))
scan.sort(key=lambda r:r[0])   # most negative (depleted) first
print("  most-depleted 8 channels (analytic triage):")
for mn,fn,q,tn,mx,emp in scan[:8]:
    print(f"    {fn:10s} q={q:<2d} vs {tn}: min-resid={mn:+.2f} max={mx:+.2f} empty(E>=5)={emp}")
print("  permutation-confirm the 3 most depleted:")
for mn,fn,q,tn,mx,emp in scan[:3]:
    fa=[feat_kinds[fn](XS[i],YS[i],q) for i in range(M)]; tb=[dict(tgts)[tn][i]%q for i in range(M)]
    obs,pp=perm_min(fa,tb,B=400)
    print(f"    {fn:10s} q={q:<2d} vs {tn}: min-resid={obs:+.2f} perm p={pp:.3f}")

# ---------- signed 2x2 anti-correlations (bit channels) ----------
print("\nSigned 2x2 anti-correlations (odds ratio <1 = negative corr):")
def legendre(x): return 1 if pow(x,(p_field-1)//2,p_field)==1 else 0
bf={"X&1":[x&1 for x in XS],"Yparity":[y&1 for y in YS],"Legendre(X)":[legendre(x) for x in XS]}
bt={"n&1":[n&1 for n in NS],"k&1":[k&1 for k in KS],"sign(D)":SG}
for fn,fa in bf.items():
    parts=[]
    for tn,tb in bt.items():
        c=[[0,0],[0,0]]
        for a,b in zip(fa,tb): c[a][b]+=1
        # odds ratio (c00*c11)/(c01*c10)
        num=c[0][0]*c[1][1]; den=c[0][1]*c[1][0]
        orr=num/den if den else 0.0                         # noqa: float
        parts.append(f"{tn}:OR={orr:.3f}")
    print(f"  {fn:12s} " + "  ".join(parts))
print("\n(OR≈1 => no signed association; positive controls above confirm the test "
      "detects real exclusions when present.)")
