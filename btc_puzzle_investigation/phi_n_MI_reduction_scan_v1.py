#!/usr/bin/env python3
"""
Does ANY residue/resonance channel of (X,Y) reduce the entropy of n, k, or D —
even by a tiny nominal amount?  Measure it directly in BITS via mutual information.

Method (honest for 'any tiny reduction'):
  - MI(feature(X,Y) ; target(n/k/D)) = expected bits of the target pinned by that
    feature.  This IS the reduction we care about.
  - Raw MI is biased UP at finite N (every channel shows a spurious positive). So
    report BIAS-CORRECTED MI = MI_obs − df/(2N) (nats; df=(|F|−1)(|T|−1)), and for
    the top channels a permutation null + split-half replication.
  - Report the DETECTION FLOOR (sd of bias-corrected MI across the null channels,
    in bits) = the smallest real per-channel reduction we could have seen.

Signal path (residues, n,k,D) is EXACT int. MI uses log only as the ranked
statistic (allowed by the no-float rule); those lines are localized + noqa'd.
Subset: N>=64 (large-d, uniform points). n,k,D recomputed EXACTLY from d.
"""
import csv, random, math
from math import gcd
from fractions import Fraction
random.seed(20260710)
NMAX=256

def factorize(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d += 1 if d==2 else 2
    if m>1: f[m]=f.get(m,0)+1
    return f
def omega(m): return 0 if m<=1 else len(factorize(m))
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

def mi_nats(joint):
    """MI in nats from an exact integer joint-count dict. log = ranked statistic."""
    N=sum(joint.values())
    ca={}; cb={}
    for (a,b),c in joint.items():
        ca[a]=ca.get(a,0)+c; cb[b]=cb.get(b,0)+c
    mi=0.0
    for (a,b),c in joint.items():
        mi += (c/N)*math.log((c*N)/(ca[a]*cb[b]))     # noqa: float
    return mi, len(ca), len(cb)
def mi_bc_bits(fa, tb):
    """bias-corrected MI in bits for two aligned integer label lists."""
    joint={}
    for a,b in zip(fa,tb):
        joint[(a,b)]=joint.get((a,b),0)+1
    mi,na,nb=mi_nats(joint); N=len(fa)
    bias=((na-1)*(nb-1))/(2*N)                          # noqa: float
    return (mi-bias)/math.log(2), na, nb                # noqa: float
def perm_floor_bits(fa, tb, B=300):
    """mean/sd of bias-corrected MI (bits) under shuffled target = null."""
    tb=tb[:]; vals=[]
    for _ in range(B):
        random.shuffle(tb)
        v,_,_=mi_bc_bits(fa,tb); vals.append(v)
    m=sum(vals)/B                                       # noqa: float
    sd=(sum((v-m)**2 for v in vals)/B)**0.5             # noqa: float
    return m,sd

# ---------- load + exact decomposition (N>=64) ----------
BITS=[];DS=[];XS=[];YS=[]
with open("constructed_keys_1to160_100k.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"])
        if N<64: continue
        BITS.append(N); DS.append(int(r["d"]))
        XS.append(int(r["X"],16)); YS.append(int(r["Y"],16))
M=len(XS)
NS=[];KS=[];DD=[];SGN=[];OMP=[]
for i in range(M):
    n,k=best_nk(DS[i],BITS[i]); A=1<<(BITS[i]-1); base=A+(A*k)//n; D=DS[i]-base
    NS.append(n); KS.append(k); DD.append(D)
    SGN.append(1 if D>=0 else 0); OMP.append(omega(n)%2)
print(f"N>=64 keys: {M}\n")

# ---------- Block A: resonance scan (matched modulus) ----------
QF=[2,3,4,5,6,7,8,9,11,13,16,17,19,23,25,29,31,32,37,41,43,47,53,59,61,64,30,210]
feat_kinds={
    "Xmodq":   lambda x,y,q: x%q,
    "Ymodq":   lambda x,y,q: y%q,
    "(X+Y)modq":lambda x,y,q:(x+y)%q,
    "(X*Y)modq":lambda x,y,q:(x*y)%q,
}
tgt_kinds={"n%q":NS,"k%q":KS,"D%q":DD}
scan=[]
for q in QF:
    for fn_name,fn in feat_kinds.items():
        fa=[fn(XS[i],YS[i],q) for i in range(M)]
        for tn,tv in tgt_kinds.items():
            tb=[v%q for v in tv]
            bc,na,nb=mi_bc_bits(fa,tb)
            scan.append((bc,fn_name,q,tn,na,nb))
scan.sort(key=lambda r:-r[0])
allbc=[r[0] for r in scan]
mean_bc=sum(allbc)/len(allbc)                           # noqa: float
sd_bc=(sum((v-mean_bc)**2 for v in allbc)/len(allbc))**0.5  # noqa: float
print(f"Block A resonance scan: {len(scan)} channels")
print(f"  bias-corrected MI across channels: mean={mean_bc:.2e} bits, "
      f"sd(floor)={sd_bc:.2e} bits, max={allbc[0]:.2e} bits")
print("  top-6 channels by bias-corrected MI (bits):")
for bc,fn,q,tn,na,nb in scan[:6]:
    print(f"    {fn:10s} q={q:<3d} vs {tn:4s}: MI_bc={bc:.2e} bits  (|F|={na},|T|={nb})")

# ---------- rigor on top-3: permutation null + split-half ----------
print("\n  rigor on top-3 (permutation floor + split-half replication):")
for bc,fn,q,tn,na,nb in scan[:3]:
    fa=[feat_kinds[fn](XS[i],YS[i],q) for i in range(M)]
    tb=[dict(tgt_kinds)[tn][i]%q for i in range(M)]
    m0,s0=perm_floor_bits(fa,tb,B=300)
    z=(bc-m0)/s0 if s0>0 else 0.0                       # noqa: float
    h=M//2
    b1,_,_=mi_bc_bits(fa[:h],tb[:h]); b2,_,_=mi_bc_bits(fa[h:],tb[h:])
    print(f"    {fn:10s} q={q:<3d} vs {tn:4s}: MI_bc={bc:.2e}  perm z={z:+.2f}  "
          f"half1={b1:.2e} half2={b2:.2e} bits")

# ---------- Block B: 1-bit feature x 1-bit target (cheap, full permutation) ----------
print("\nBlock B: single-bit channels (exact permutation p, B=1000):")
def legendre(x):
    p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
    return 1 if pow(x,(p-1)//2,p)==1 else 0
bit_feats={
    "X&1":[x&1 for x in XS],
    "Yparity":[y&1 for y in YS],
    "Legendre(X)":[legendre(x) for x in XS],
}
bit_tgts={"n&1":[n&1 for n in NS],"k&1":[k&1 for k in KS],
          "D&1":[abs(d)&1 for d in DD],"sign(D)":SGN}
def perm_p_bits(fa,tb,obs,B=1000):
    tb=tb[:]; ge=0
    for _ in range(B):
        random.shuffle(tb)
        v,_,_=mi_bc_bits(fa,tb)
        if v>=obs: ge+=1
    return (ge+1)/(B+1)                                 # noqa: float
for fn,fa in bit_feats.items():
    line=[]
    for tn,tb in bit_tgts.items():
        bc,_,_=mi_bc_bits(fa,tb)
        pp=perm_p_bits(fa,tb,bc,B=1000)
        line.append(f"{tn}:MI_bc={bc:+.2e}(p={pp:.3f})")
    print(f"  {fn:12s} " + "  ".join(line))
print("\nfloor => any real per-channel reduction is below ~sd(floor) bits unless "
      "perm z is large AND it replicates across halves.")
